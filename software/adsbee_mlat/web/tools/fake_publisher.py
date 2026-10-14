#!/usr/bin/env python3
"""Publishes synthetic (or recorded) MLAT core output to Redis for developing and testing the web app.

Synthetic mode flies aircraft around a center point and publishes on the same channels as the
MLAT core: ADS-B fixes at --adsb-hz, MLAT fixes (with position noise matching err_m) at --mlat-hz,
aircraft batches every --batch-ms, receivers and stats every second, and the snapshot key.

  fake_publisher.py --aircraft 200 --mlat-fraction 0.5
  fake_publisher.py --record traffic.jsonl --duration 60
  fake_publisher.py --replay traffic.jsonl

Recordings are JSON lines {"t": unix_s, "ch": channel, "data": message}. Replay shifts every
timestamp so the recording plays as live traffic and loops at the end.
"""

import argparse
import json
import math
import random
import sys
import time

import redis

AIRCRAFT_CHANNEL = "mlat:aircraft"
RECEIVERS_CHANNEL = "mlat:receivers"
STATS_CHANNEL = "mlat:stats"
SNAPSHOT_KEY = "mlat:snapshot"
SNAPSHOT_TTL_S = 30

M_PER_DEG = 111_320.0
KT_TO_MPS = 0.514444
FPM_TO_FPS = 1 / 60
CALLSIGN_PREFIXES = ["UAL", "SWA", "DAL", "AAL", "ASA", "SKW", "JBU", "FDX", "UPS", "N"]


def offset(lat, lon, north_m, east_m):
    return lat + north_m / M_PER_DEG, lon + east_m / (M_PER_DEG * math.cos(math.radians(lat)))


def distance_m(lat1, lon1, lat2, lon2):
    dn = (lat2 - lat1) * M_PER_DEG
    de = (lon2 - lon1) * M_PER_DEG * math.cos(math.radians((lat1 + lat2) / 2))
    return math.hypot(dn, de)


class Aircraft:
    def __init__(self, rng, center, radius_m, mlat, rate_hz, now):
        self.rng = rng
        self.center = center
        self.radius_m = radius_m
        self.icao = f"{rng.randrange(0x100000, 0xFFFFFF):06x}"
        r = radius_m * math.sqrt(rng.random())
        a = rng.uniform(0, 2 * math.pi)
        self.lat, self.lon = offset(*center, r * math.cos(a), r * math.sin(a))
        self.alt_ft = rng.choice([rng.uniform(1000, 12000), rng.uniform(12000, 41000)])
        self.gs_kt = 120 + self.alt_ft / 41000 * 360 + rng.uniform(-30, 30)
        self.track = rng.uniform(0, 360)
        self.turn_dps = 0.0
        self.vr_fpm = 0.0
        self.mlat = mlat
        self.period = 1 / rate_hz
        self.next_fix = now + rng.uniform(0, self.period)
        self.t_state = now
        prefix = rng.choice(CALLSIGN_PREFIXES)
        self.callsign = None if (mlat and rng.random() < 0.3) else f"{prefix}{rng.randrange(1, 9999)}"
        self.squawk = f"{rng.randrange(0, 0o10000):04o}"

    def step(self, dt):
        rng = self.rng
        if rng.random() < dt / 30:
            self.turn_dps = rng.choice([0, 0, rng.uniform(-3, 3)])
        if rng.random() < dt / 60:
            self.vr_fpm = rng.choice([0, 0, rng.uniform(-2000, 2000)])
        if distance_m(self.lat, self.lon, *self.center) > self.radius_m:
            home = math.degrees(math.atan2(
                (self.center[1] - self.lon) * math.cos(math.radians(self.lat)), self.center[0] - self.lat))
            diff = (home - self.track + 540) % 360 - 180
            self.turn_dps = 3 if diff > 0 else -3
        self.track = (self.track + self.turn_dps * dt) % 360
        self.alt_ft = min(43000, max(500, self.alt_ft + self.vr_fpm * FPM_TO_FPS * dt))
        if self.alt_ft in (500, 43000):
            self.vr_fpm = 0
        v = self.gs_kt * KT_TO_MPS * dt
        self.lat, self.lon = offset(self.lat, self.lon, v * math.cos(math.radians(self.track)),
                                    v * math.sin(math.radians(self.track)))

    def fix(self, t, receivers):
        fix = {"icao": self.icao, "src": "mlat" if self.mlat else "adsb", "lat": self.lat, "lon": self.lon,
               "alt_ft": round(self.alt_ft / 25) * 25, "gs_kt": self.gs_kt, "track_deg": self.track,
               "vr_fpm": round(self.vr_fpm / 64) * 64, "callsign": self.callsign, "squawk": self.squawk,
               "t": t, "err_m": None, "nrecv": None, "gdop": None}
        if self.mlat:
            near = sorted(distance_m(self.lat, self.lon, r["lat"], r["lon"]) for r in receivers)
            nrecv = max(3, sum(1 for d in near if d < 350_000))
            gdop = 1.2 + distance_m(self.lat, self.lon, *self.center) / 60_000 + 4 / nrecv
            err = 15 * gdop
            fix["lat"], fix["lon"] = offset(self.lat, self.lon, self.rng.gauss(0, err), self.rng.gauss(0, err))
            fix["gs_kt"] += self.rng.gauss(0, 3)
            fix["track_deg"] = (self.track + self.rng.gauss(0, 1.5)) % 360
            fix.update(err_m=round(err, 1), nrecv=nrecv, gdop=round(gdop, 2))
        return fix


def make_receivers(rng, center, radius_m, n):
    receivers = []
    for i in range(n):
        a = 2 * math.pi * i / n + rng.uniform(-0.2, 0.2)
        r = radius_m * (0.25 + 0.5 * rng.random()) if i else 0
        lat, lon = offset(*center, r * math.cos(a), r * math.sin(a))
        receivers.append({"id": f"bee-{i:02d}", "name": f"Receiver {i + 1}", "lat": round(lat, 6),
                          "lon": round(lon, 6), "alt_m": round(rng.uniform(5, 400), 1),
                          "pos_src": rng.choice(["gnss", "gnss", "fixed", "config"]),
                          "clock_hz": rng.choice([12_000_000, 48_000_000]), "msg_rate": 0.0,
                          "sync_ok": True, "clock_err_ns": 0.0, "peers": []})
    return receivers


def update_receivers(rng, receivers, t):
    for i, r in enumerate(receivers):
        # Receiver 1 (if present) loses sync now and then.
        r["sync_ok"] = not (i == 1 and int(t) % 20 < 5)
        r["clock_err_ns"] = round(abs(rng.gauss(0, 15)), 1) if r["sync_ok"] else None
        r["msg_rate"] = round(rng.uniform(150, 900), 1)
    synced = [r for r in receivers if r["sync_ok"]]
    for r in receivers:
        r["peers"] = [p["id"] for p in synced if p is not r and r["sync_ok"]
                      and distance_m(r["lat"], r["lon"], p["lat"], p["lon"]) < 300_000]
    return {"t": t, "receivers": receivers}


class Sink:
    def __init__(self, client, record):
        self.client = client
        self.record = record

    def publish(self, ch, msg):
        data = json.dumps(msg, separators=(",", ":"))
        self.client.publish(ch, data)
        if self.record:
            self.record.write(json.dumps({"t": time.time(), "ch": ch, "data": msg}) + "\n")

    def snapshot(self, msg):
        self.client.set(SNAPSHOT_KEY, json.dumps(msg, separators=(",", ":")), ex=SNAPSHOT_TTL_S)


def run_synthetic(args, sink):
    rng = random.Random(args.seed)
    center = tuple(float(v) for v in args.center.split(","))
    radius = args.radius_km * 1000
    now = time.time()
    receivers = make_receivers(rng, center, radius, args.receivers)
    n_mlat = round(args.aircraft * args.mlat_fraction)
    fleet = [Aircraft(rng, center, radius, i < n_mlat, args.mlat_hz if i < n_mlat else args.adsb_hz, now)
             for i in range(args.aircraft)]
    latest = {}
    next_second = now
    next_snapshot = now
    fixes_this_second = 0
    end = now + args.duration if args.duration else math.inf
    batch_s = args.batch_ms / 1000
    while time.time() < end:
        now = time.time()
        batch = []
        for ac in fleet:
            # Step each aircraft to every fix time due in this batch so fixes carry exact times.
            while ac.next_fix <= now:
                ac.step(ac.next_fix - ac.t_state)
                ac.t_state = ac.next_fix
                fix = ac.fix(ac.next_fix, receivers)
                batch.append(fix)
                latest[ac.icao] = fix
                ac.next_fix += ac.period * rng.uniform(0.85, 1.15)
        fixes_this_second += sum(1 for f in batch if f["src"] == "mlat")
        if batch:
            sink.publish(AIRCRAFT_CHANNEL, {"t": now, "aircraft": batch})
        if now >= next_snapshot:
            sink.snapshot({"t": now, "aircraft": list(latest.values())})
            next_snapshot = now + 0.5
        if now >= next_second:
            sink.publish(RECEIVERS_CHANNEL, update_receivers(rng, receivers, now))
            sink.publish(STATS_CHANNEL, {"t": now, "solves_per_s": fixes_this_second,
                                         "latency_ms": round(rng.uniform(60, 140), 1),
                                         "residual_m": round(rng.uniform(25, 60), 1),
                                         "aircraft": len(latest), "receivers": len(receivers)})
            fixes_this_second = 0
            next_second = now + 1
        time.sleep(max(0.0, batch_s - (time.time() - now)))


def shift_times(ch, msg, dt):
    msg = json.loads(json.dumps(msg))
    msg["t"] = msg.get("t", 0) + dt
    for a in msg.get("aircraft", ()) if ch == AIRCRAFT_CHANNEL else ():
        if a.get("t") is not None:
            a["t"] += dt
    return msg


def run_replay(args, sink):
    with open(args.replay) as f:
        records = [json.loads(line) for line in f if line.strip()]
    if not records:
        sys.exit("empty recording")
    t0 = records[0]["t"]
    span = records[-1]["t"] - t0 + 0.1
    loop = 0
    latest = {}
    while True:
        start = time.time()
        for rec in records:
            delay = rec["t"] - t0 - (time.time() - start)
            if delay > 0:
                time.sleep(delay)
            dt = start - t0
            msg = shift_times(rec["ch"], rec["data"], dt)
            sink.publish(rec["ch"], msg)
            if rec["ch"] == AIRCRAFT_CHANNEL:
                latest.update((a["icao"], a) for a in msg["aircraft"])
                sink.snapshot({"t": msg["t"], "aircraft": list(latest.values())})
        loop += 1
        if args.duration and loop * span >= args.duration:
            return


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--redis", default="redis://localhost:6379/0")
    p.add_argument("--aircraft", type=int, default=150)
    p.add_argument("--mlat-fraction", type=float, default=0.5)
    p.add_argument("--receivers", type=int, default=8)
    p.add_argument("--center", default="37.40,-122.05", help="lat,lon")
    p.add_argument("--radius-km", type=float, default=200)
    p.add_argument("--adsb-hz", type=float, default=2)
    p.add_argument("--mlat-hz", type=float, default=5)
    p.add_argument("--batch-ms", type=float, default=100)
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--duration", type=float, default=0, help="seconds; 0 runs forever")
    p.add_argument("--record", help="also write published messages to this JSONL file")
    p.add_argument("--replay", help="publish a JSONL recording instead of synthetic traffic")
    args = p.parse_args()

    client = redis.Redis.from_url(args.redis)
    for _ in range(30):
        try:
            client.ping()
            break
        except redis.ConnectionError:
            time.sleep(1)
    record = open(args.record, "w") if args.record else None
    try:
        sink = Sink(client, record)
        (run_replay if args.replay else run_synthetic)(args, sink)
    except KeyboardInterrupt:
        pass
    finally:
        if record:
            record.close()


if __name__ == "__main__":
    main()
