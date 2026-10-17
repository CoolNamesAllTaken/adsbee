"""Accuracy validation on simulated traffic: array sizes, clock rates, receiver types, GNSS position noise and bad
clocks. Writes one JSON file per scenario into an output directory (input for bench/report.py).

python bench/validate.py OUTDIR [--duration 180] [--jobs 4] [--only NAME]
"""

import argparse
import asyncio
import json
import math
import multiprocessing as mp
import os
import time

import numpy as np

CENTER = (47.6, -122.3)


def scenarios():
    out = []
    for kind, clock in (("adsbee_1090", 48e6), ("adsbee_1090", 12e6), ("rtlsdr", 12e6)):
        for n in (3, 4, 5, 6, 8):
            out.append(dict(name=f"size-{kind}-{int(clock / 1e6)}-{n}", group="size", kind=kind, clock=clock, n=n))
    out.append(dict(name="m1421-48-5", group="type", kind="adsbee_1421", clock=48e6, n=5))
    for g in (2.0, 5.0, 10.0):
        out.append(dict(name=f"gnss-{g:g}", group="gnss", kind="adsbee_1090", clock=48e6, n=5, gnss=g))
    for bad in ("walk", "jitter", "wander", "reset", "steps"):
        out.append(dict(name=f"bad-{bad}", group="bad", kind="adsbee_1090", clock=48e6, n=6, bad=bad))
    for b in (10e3, 20e3, 50e3):
        out.append(dict(name=f"baseline-{int(b / 1e3)}", group="baseline", kind="adsbee_1090", clock=48e6, n=5,
                        baseline=b))
    return out


def build(spec, seed=7):
    import adsbee_mlat_sim as sim

    rng = np.random.default_rng([seed, 11])
    rxs = sim.make_array(*CENTER, spec["n"], spec.get("baseline", 30e3), clock_hz=spec["clock"],
                         receiver_type=spec["kind"], seed=seed, gnss_sigma_m=spec.get("gnss"))
    acs = sim.random_traffic(rng, *CENTER, 50, 150e3, adsb_share=0.6)
    sc = sim.Scenario(receivers=rxs, aircraft=acs, seed=seed)
    bad = spec.get("bad")
    r = sc.receivers[2] if bad else None
    if bad == "walk":
        r.clock.random_walk_ppm = 0.5
    elif bad == "jitter":
        r.timing.jitter_ns = 400.0
    elif bad == "wander":
        r.clock.wander_ppm = 2.0
        r.clock.wander_period_s = 60.0
    elif bad == "reset":
        r.clock.resets = [70.0]
    elif bad == "steps":
        r.clock.steps = [(60.0, 3e-6), (100.0, -7e-6)]
    return sc


def run(spec, duration, settle):
    from adsbee_mlat import validation

    sc = build(spec)
    t = time.time()
    eng, col = validation.run(sc, duration)
    rows = col.errors(settle_s=settle)
    adsb = {a.icao: a.adsb for a in sc.aircraft}
    res = {"spec": spec, "cpu_s": round(time.time() - t, 1), "duration_s": duration, "settle_s": settle,
           "summary": validation.summarize(rows),
           "summary_modes_only": validation.summarize([r for r in rows if not adsb[r[0]]]),
           "stats": eng.stats,
           "receivers": eng.receivers_status(),
           "rows": [[r[0], round(r[1], 3), round(r[2], 2), round(r[3], 2), round(r[4], 2), r[5], adsb[r[0]]]
                    for r in rows]}
    # Range of each aircraft from the array center, at the middle of the run.
    from adsbee_mlat import geo

    res["range_km"] = {str(a.icao): geo.distance_m(*CENTER, *map(float, a.position(duration / 2)[:2])) / 1e3
                       for a in sc.aircraft}
    # Messages each aircraft sent and how many receivers decoded them, for the update rate context.
    return res


def run_socket(duration, out):
    """Real time over TCP: latency from emission to publication, and fix rates."""
    from adsbee_mlat import validation
    from adsbee_mlat.config import Config
    from adsbee_mlat.server import Publisher, Server

    spec = dict(name="socket-48-5", group="socket", kind="adsbee_1090", clock=48e6, n=5)
    sc = build(spec)
    published = []

    class P(Publisher):
        def add_fix(self, e):
            super().add_fix(e)
            published.append((time.time(), e))

    async def go():
        pub = P()
        pub.keep_sent = True
        server = Server(Config(listen_host="127.0.0.1", listen_port=0, sbs_port=None, redis_url=None), pub)
        await server.start()
        sc.t0_unix = time.time() + 2.0
        frames = list(sc.frames(duration))
        await validation.stream(sc, frames, "127.0.0.1", server.port)
        await asyncio.sleep(1.0)
        shift = validation.mapping_shift(server.engine, frames[-3000:])
        stats = [p for c, p in pub.sent if c == "mlat:stats"]
        await server.stop()
        return shift, stats

    shift, stats = asyncio.run(go())
    col = validation.TruthCollector(sc)
    col.time_shift = [shift]
    col.published = [e for _, e in published]
    by = {a.icao: a for a in sc.aircraft}
    lat = {"mlat": [], "adsb": []}
    for wall, e in published:
        a = by[int(e["icao"], 16)]
        # Emission time: the fix time is the first reception mapped to Unix time; correct it by the map's error.
        lat[e["src"]].append(wall - (e["t"] - shift))
    rows = col.published_errors("mlat", settle_s=20)
    res = {"spec": spec, "duration_s": duration, "latency_s": {k: v for k, v in lat.items()},
           "summary": validation.summarize(rows), "stats": stats[-5:], "map_shift_s": shift,
           "published": {"mlat": len(lat["mlat"]), "adsb": len(lat["adsb"])},
           "rows": [[r[0], round(r[1], 3), round(r[2], 2), 0, round(r[4], 2), r[5], False] for r in rows]}
    with open(os.path.join(out, "socket-48-5.json"), "w") as f:
        json.dump(res, f)
    print("socket", res["summary"], "latency p50", np.median(lat["mlat"]))


def _job(args):
    spec, duration, settle, out = args
    try:
        res = run(spec, duration, settle)
    except Exception:
        import traceback

        traceback.print_exc()
        return
    with open(os.path.join(out, spec["name"] + ".json"), "w") as f:
        json.dump(res, f)
    s = res["summary"]
    print(f"{spec['name']}: n={s.get('n')} h50={s.get('h_p50', math.nan):.1f} h95={s.get('h_p95', math.nan):.1f} "
          f"rate={s.get('rate_hz_median')} cpu={res['cpu_s']}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--duration", type=float, default=180.0)
    ap.add_argument("--settle", type=float, default=30.0)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--only")
    ap.add_argument("--socket", type=float, default=0.0, help="Also run a real time socket test this long")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    specs = [s for s in scenarios() if not args.only or args.only in s["name"]]
    with mp.Pool(args.jobs) as pool:
        list(pool.imap_unordered(_job, [(s, args.duration, args.settle, args.out) for s in specs]))
    if args.socket:
        run_socket(args.socket, args.out)


if __name__ == "__main__":
    main()
