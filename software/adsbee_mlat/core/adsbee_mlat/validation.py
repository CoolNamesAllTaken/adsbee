"""Runs the engine on simulated traffic (package adsbee_mlat_sim) and compares fixes with the truth."""

import math
from collections import defaultdict

import numpy as np

from . import geo
from .engine import Engine


def receiver_info(rx):
    """Receiver info fields (as in a receiver info frame) for a simulated receiver."""
    return {"v": 1, "id": rx.id, "name": rx.name, "clk": int(rx.clock_hz), "ep": "1", "lat": rx.reported_lat,
            "lon": rx.reported_lon, "alt": rx.reported_alt_m, "src": "gnss" if rx.pos_src == "gnss" else "fixed"}


class TruthCollector:
    """Collects MLAT track updates and published fixes, and scores them against the simulated aircraft."""

    def __init__(self, scenario):
        self.sc = scenario
        self.by_icao = {a.icao: a for a in scenario.aircraft}
        self.updates = []  # (icao, t_unix, lat, lon, h, err_m, nrecv, adsb)
        self.published = []
        self.time_shift = []  # Unix time map minus true time, sampled per read [s].

    def on_mlat(self, ac, tr, extra):
        lat, lon, h = tr.llh()
        self.updates.append((ac.icao, extra["t"], float(lat), float(lon), float(h), tr.horizontal_error_m(),
                             extra["nrecv"], ac.adsb_t is not None))

    def on_fix(self, entry):
        self.published.append(entry)

    @property
    def shift(self):
        return float(np.median(self.time_shift)) if self.time_shift else 0.0

    def published_errors(self, src="mlat", settle_s=0.0):
        """Errors of published fixes (entries of mlat:aircraft) of one source: rows like errors()."""
        out = []
        for e in self.published:
            if e["src"] != src:
                continue
            out.append((int(e["icao"], 16), e["t"], e["lat"], e["lon"], e.get("_h"), e["err_m"], e["nrecv"], False))
        rows = []
        for icao, t, lat, lon, _, err, nrecv, adsb in out:
            a = self.by_icao.get(icao)
            ts = t - self.sc.t0_unix - self.shift
            if a is None or ts < settle_s:
                continue
            tlat, tlon, _ = a.position(ts)
            rows.append((icao, ts, geo.distance_m(lat, lon, float(tlat), float(tlon)), 0.0, err or 0.0, nrecv, adsb))
        return rows

    def errors(self, settle_s=0.0):
        """Per update: horizontal and vertical error against the true position at emission [m]."""
        rows = []
        for icao, t, lat, lon, h, err, nrecv, adsb in self.updates:
            a = self.by_icao.get(icao)
            if a is None:
                continue
            ts = t - self.sc.t0_unix - self.shift
            if ts < settle_s:
                continue
            # The update time is the first reception: step back by the propagation time to the emission.
            tlat, tlon, th = a.position(ts)
            p = geo.llh_to_ecef(lat, lon, h)
            q = geo.llh_to_ecef(float(tlat), float(tlon), float(th))
            e = geo.enu_basis(float(tlat), float(tlon)) @ (p - q)
            rows.append((icao, ts, math.hypot(e[0], e[1]), e[2], err, nrecv, adsb))
        return rows


def run(scenario, duration_s, latency_s=0.05, chunk_s=0.02, group_window_s=0.2, engine=None, frames=None):
    """Drives an Engine directly with simulated time. Returns (engine, collector)."""
    col = TruthCollector(scenario)
    eng = engine or Engine(group_window_s=group_window_s, publish_mlat_for_adsb=True, on_fix=col.on_fix,
                           on_mlat=col.on_mlat, adsb_mlat_fraction=1.0)
    if engine is not None:
        eng.on_fix, eng.on_mlat = col.on_fix, col.on_mlat
    for rx in scenario.receivers:
        eng.apply_info(receiver_info(rx))
    t0 = scenario.t0_unix
    pending = defaultdict(list)
    next_flush = None
    for f in frames if frames is not None else scenario.frames(duration_s):
        if next_flush is None:
            next_flush = f.t_arrival + chunk_s
        while f.t_arrival >= next_flush:
            wall = t0 + next_flush + latency_s
            _flush(eng, pending, wall, col)
            eng.tick(wall)
            next_flush += chunk_s
        pending[f.rx_id].append(((f.ticks % (1 << 48)) or 1, 0x80, f.msg, f.t_unix))
    if next_flush is not None:
        wall = t0 + next_flush + latency_s
        _flush(eng, pending, wall, col)
        for k in range(int(1.0 / chunk_s) + 2):
            eng.tick(wall + k * chunk_s)
    return eng, col


def _flush(eng, pending, wall, col):
    for rid, frames in pending.items():
        if frames:
            rx = eng.receivers[rid]
            eng.add_frames(rx, [f[:3] for f in frames], wall)
            if len(col.time_shift) < 20000 and rx._last_raw is not None:
                u = rx.to_unix((rx._last_raw + rx._wraps - rx._base) / rx.clock_hz)
                if u is not None:
                    col.time_shift.append(u - frames[-1][3])
    pending.clear()


def summarize(rows, duration_s=None):
    """Error percentiles and update rates from TruthCollector.errors() rows."""
    if not rows:
        return {"n": 0}
    h = np.array([r[2] for r in rows])
    v = np.abs(np.array([r[3] for r in rows]))
    per_ac = defaultdict(list)
    for r in rows:
        per_ac[r[0]].append(r[1])
    rates = []
    for ts in per_ac.values():
        if len(ts) > 5:
            span = max(ts) - min(ts)
            if span > 5:
                rates.append((len(ts) - 1) / span)
    est = np.array([r[4] for r in rows])
    return {
        "n": len(rows),
        "aircraft": len(per_ac),
        "h_p50": float(np.percentile(h, 50)), "h_p68": float(np.percentile(h, 68)),
        "h_p95": float(np.percentile(h, 95)), "v_p50": float(np.percentile(v, 50)),
        "v_p95": float(np.percentile(v, 95)),
        "rate_hz_median": float(np.median(rates)) if rates else None,
        "est_err_p50": float(np.median(est)),
        "within_est_1sigma": float(np.mean(h <= est)),
    }


def mapping_shift(eng, frames):
    """Median error of the engine's receiver-to-Unix time maps against the truth, from a sample of frames."""
    out = []
    for f in frames:
        rx = eng.receivers.get(f.rx_id)
        if rx is None or rx._base is None:
            continue
        t_rx = (f.ticks - rx._base) / rx.clock_hz
        u = rx.to_unix(t_rx)
        if u is not None:
            out.append(u - f.t_unix)
    return float(np.median(out)) if out else 0.0


async def stream(scenario, frames, host, port, udp=False, batch_s=0.01, bad_info=None):
    """Sends pre-generated frames to a server in real time, one TCP connection (or UDP socket) per receiver.

    frames must come from scenario.frames() after scenario.t0_unix was set to a time shortly in the future.
    """
    import asyncio
    import socket
    import time

    from . import beast

    infos = {rx.id: beast.build_info(**receiver_info(rx)) for rx in scenario.receivers}
    writers = {}
    socks = {}
    for rx in scenario.receivers:
        if udp:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.connect((host, port))
            socks[rx.id] = s
        else:
            _, w = await asyncio.open_connection(host, port)
            w.write(infos[rx.id])
            writers[rx.id] = w
    pending = defaultdict(list)
    i = 0
    n = len(frames)
    while i < n:
        t_next = frames[i].t_unix + batch_s
        delay = t_next - time.time()
        if delay > 0:
            await asyncio.sleep(delay)
        while i < n and frames[i].t_unix <= t_next:
            f = frames[i]
            pending[f.rx_id].append(beast.build_mode_s(f.ticks, f.msg))
            i += 1
        for rid, chunks in pending.items():
            if not chunks:
                continue
            if udp:
                buf = infos[rid]
                for c in chunks:
                    if len(buf) + len(c) > 1400:
                        socks[rid].send(buf)
                        buf = infos[rid]
                    buf += c
                socks[rid].send(buf)
            else:
                writers[rid].write(b"".join(chunks))
        pending.clear()
        for w in writers.values():
            await w.drain()
    for w in writers.values():
        w.close()
    for s in socks.values():
        s.close()


def random_array(sim, center_lat, center_lon, n, radius_m, clock_hz=48e6, receiver_type="adsbee_1090", seed=0,
                 gnss_sigma_m=None):
    """n simulated receivers spread uniformly over a disk."""
    rng = np.random.default_rng([seed, 20])
    out = []
    for k in range(n):
        r = radius_m * math.sqrt(rng.uniform())
        lat, lon = sim.destination(center_lat, center_lon, rng.uniform(0, 360), r)
        rx = sim.Receiver(id=f"rx{k}", lat=float(lat), lon=float(lon), alt_m=float(rng.uniform(10, 300)),
                          timing=sim.RECEIVER_TYPES[receiver_type](),
                          clock=sim.Clock(clock_hz=clock_hz, offset_s=rng.uniform(0, 1000), ppm=rng.normal(0, 10),
                                          seed=int(rng.integers(1 << 31))),
                          pos_src="fixed" if gnss_sigma_m is None else "gnss")
        if gnss_sigma_m is not None:
            rx.add_position_noise(rng, gnss_sigma_m, 2 * gnss_sigma_m)
        out.append(rx)
    return out
