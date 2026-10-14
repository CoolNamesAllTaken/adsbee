"""Single fix (each message solved alone) and tracked errors for 12 vs 48 MHz timestamps at long range.

python bench/clockrate.py OUT.json [--duration 150]
"""

import argparse
import json
import multiprocessing as mp

import numpy as np

CENTER = (47.6, -122.3)


def run(case):
    import adsbee_mlat_sim as sim

    from adsbee_mlat import geo, solver, validation

    n, clock, bias, jitter_scale, seed, duration = case
    rng = np.random.default_rng([seed, 11])
    rxs = sim.make_array(*CENTER, n, 30e3, clock_hz=clock, seed=seed, center_receiver=False)
    for r in rxs:
        r.timing.jitter_ns *= jitter_scale
    acs = sim.random_traffic(rng, *CENTER, 60, 200e3, adsb_share=0.6)
    sc = sim.Scenario(receivers=rxs, aircraft=acs, seed=seed)
    if not bias:
        sc._pair_bias[:] = 0.0
    by = {a.icao: a for a in acs}
    single = []

    def on_meas(ac, rx_ecef, times, sigmas, alt, t_unix):
        if len(times) < 4 or ac.track is None:
            return
        fix = solver.solve(rx_ecef, times, sigmas, alt, guess=ac.track.x[:3])
        if fix is None:
            return
        single.append((ac.icao, t_unix, *map(float, geo.ecef_to_llh(fix.ecef))))

    from adsbee_mlat.engine import Engine

    eng = Engine(group_window_s=0.2, publish_mlat_for_adsb=True, adsb_mlat_fraction=1.0)
    eng.on_measurement = on_meas
    eng, col = validation.run(sc, duration, engine=eng)
    shift = col.shift

    def errs(rows, settle=30.0):
        out = []
        for icao, t, lat, lon, h in rows:
            ts = t - sc.t0_unix - shift
            if ts < settle:
                continue
            a = by[icao]
            tlat, tlon, _ = a.position(ts)
            rng_km = geo.distance_m(*CENTER, float(tlat), float(tlon)) / 1e3
            out.append((rng_km, geo.distance_m(lat, lon, float(tlat), float(tlon))))
        return np.array(out)

    tracked = errs([(u[0], u[1], u[2], u[3], u[4]) for u in col.updates])
    single_e = errs(single)
    res = {"n": n, "clock_mhz": int(clock / 1e6), "bias": bias, "jitter_scale": jitter_scale}
    for name, e in (("single", single_e), ("tracked", tracked)):
        for lo, hi in ((100, 200), (50, 100)):
            sel = e[(e[:, 0] >= lo) & (e[:, 0] < hi), 1] if len(e) else np.array([])
            res[f"{name}_{lo}_{hi}_p50"] = float(np.median(sel)) if len(sel) else None
            res[f"{name}_{lo}_{hi}_rms"] = float(np.sqrt(np.mean(sel**2))) if len(sel) else None
            res[f"{name}_{lo}_{hi}_n"] = int(len(sel))
    res["jitter_est_ns"] = [round(r.jitter_s * 1e9, 1) for r in eng.by_index]
    res["clock_hz_used"] = sorted({r.clock_hz for r in eng.by_index})
    print(json.dumps(res), flush=True)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--duration", type=float, default=150.0)
    ap.add_argument("--jobs", type=int, default=4)
    args = ap.parse_args()
    cases = [(n, clk, bias, 1.0, 5, args.duration) for n in (4, 6) for bias in (True, False) for clk in (48e6, 12e6)]
    with mp.Pool(args.jobs) as pool:
        res = pool.map(run, cases)
    with open(args.out, "w") as f:
        json.dump(res, f, indent=1)


if __name__ == "__main__":
    main()
