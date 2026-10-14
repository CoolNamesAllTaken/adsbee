"""Runs the 12 vs 48 MHz timestamp study and writes results.json (plus the inputs for the report charts)."""

import json
import sys
from dataclasses import asdict, replace
from multiprocessing import Pool

import numpy as np

import crlb
import mc

OUT = sys.argv[1] if len(sys.argv) > 1 else "results.json"
CENTER = (47.6, -122.3)
RANGE_BINS = {"50": (35, 65), "100": (80, 120), "200": (170, 230)}
SEEDS = (0, 1, 2)


def summarize(cfg):
    r = mc.run(cfg)
    sc, em, rec, f, tg = r["sc"], r["em"], r["rec"], r["fixes"], r["targets"]
    n_rx = len(sc.receivers)
    tab = np.full((len(em), n_rx), np.nan)
    tab[rec.emission, rec.rx] = rec.t_arrival
    clock0 = sc.receivers[0].clock
    sig = []
    for i in range(n_rx):
        h = np.isfinite(r["t_common"][:, i])
        e = r["t_common"][h, i] - clock0.local_time(tab[tg[h], i])
        e = e - np.median(e)
        sig.append(float(np.std(e[np.abs(e) < 300e-9]) * 1e9))
    rx = np.array([x.reported_ecef for x in sc.receivers])
    s = np.array(sig) * 1e-9
    pred = np.full(len(f["herr"]), np.nan)
    for k in range(len(f["herr"])):
        _, cov = crlb.horizontal_sigma(f["truth"][k:k + 1], rx[f["mask"][k]], s[f["mask"][k]], cfg.alt_sigma_m,
                                       return_cov=True)  # fmt: skip
        if np.all(np.isfinite(cov[0])):
            pred[k] = crlb.median_radius(cov[0], n=400, seed=k)
    bins = {}
    for name, (lo, hi) in RANGE_BINS.items():
        m = (f["range_km"] >= lo) & (f["range_km"] < hi) & (f["nrx"] == n_rx)
        if m.sum() < 20:
            continue
        bins[name] = dict(n=int(m.sum()), median_m=float(np.median(f["herr"][m])),
                          p95_m=float(np.percentile(f["herr"][m], 95)), crlb_median_m=float(np.nanmedian(pred[m])), ratio_median=float(np.nanmedian(f['herr'][m] / pred[m])))  # fmt: skip
    se = np.concatenate(r["sync_err"]) * 1e9
    return dict(cfg=asdict(cfg), sigma_ns=sig, sync_rms_ns=float(np.sqrt(np.mean(se**2))),
                sync_bias_ns=[float(np.mean(e) * 1e9) for e in r["sync_err"]], bins=bins, fixes=int(len(f["herr"])))  # fmt: skip


SCENARIOS = {
    "base": dict(),
    "gnss_positions": dict(gnss_sigma_m=2.0),
    "no_tropo_model": dict(tropo_n0_model=None),
    "sparse_adsb": dict(adsb_share=0.1),
    "poor_oscillator": dict(random_walk_ppm=0.02),
    "mixed_rtlsdr": dict(mixed_types=("adsbee_1090", "rtlsdr", "adsbee_1090", "rtlsdr")),
    "m1421": dict(receiver_type="adsbee_1421"),
    "five_rx_50km": dict(n_rx=5, aperture_m=50e3),
}


def mc_jobs():
    jobs = []
    for name, kw in SCENARIOS.items():
        for hz in (12e6, 48e6):
            for seed in SEEDS:
                jobs.append((name, hz, seed, replace(mc.Config(clock_hz=hz, seed=seed, duration_s=120, n_aircraft=150), **kw)))
    return jobs


def run_job(job):
    name, hz, seed, cfg = job
    return name, hz, seed, summarize(cfg)


def crlb_study(sigma):
    out = {"sigma_ns": sigma}
    # Accuracy vs range, median over azimuth, aircraft at 10 km.
    ranges = np.concatenate([np.arange(2, 20, 2), np.arange(20, 260, 10)]) * 1e3
    curves = {}
    for n in (3, 4, 5):
        for ap in (5e3, 10e3, 20e3, 50e3):
            rx = mc.ring(n, ap)
            for clock, s in sigma.items():
                for alt_sigma in (50.0, None):
                    med = []
                    for rng in ranges:
                        _, t, up = crlb.ring_targets(*CENTER, rng, 10_000.0, n_az=36)
                        h = crlb.horizontal_sigma(t, rx, s * 1e-9, alt_sigma, up)
                        h = np.where(h > 1e6, np.nan, h)
                        med.append(float(np.nanmedian(h)) if np.isfinite(h).any() else None)
                    curves[f"{n}|{int(ap)}|{clock}|{alt_sigma}"] = med
    out["ranges_km"] = (ranges / 1e3).tolist()
    out["curves"] = curves
    # Smallest aperture for a target accuracy.
    apertures = np.geomspace(1e3, 400e3, 120)
    table = []
    for n in (3, 4, 5):
        for alt_sigma in (50.0, None):
            if n == 3 and alt_sigma is None:
                continue
            for rng in (50e3, 100e3, 200e3):
                _, t, up = crlb.ring_targets(*CENTER, rng, 10_000.0, n_az=36)
                errs = {c: [] for c in sigma}
                for ap in apertures:
                    rx = mc.ring(n, ap)
                    for clock, s in sigma.items():
                        h = crlb.horizontal_sigma(t, rx, s * 1e-9, alt_sigma, up)
                        errs[clock].append(float(np.nanmedian(np.where(h > 1e6, np.nan, h))))
                for goal in (100.0, 250.0):
                    row = dict(n=n, alt=alt_sigma is not None, range_km=rng / 1e3, goal_m=goal)
                    for clock in sigma:
                        e = np.array(errs[clock])
                        ok = np.nonzero(e <= goal)[0]
                        row[clock] = float(apertures[ok[0]] / 1e3) if len(ok) else None
                    table.append(row)
    out["min_aperture"] = table
    # Heatmaps: 20 km aperture, 10 km altitude, +-250 km.
    maps = {}
    for n in (3, 4, 5):
        rx = mc.ring(n, 20e3)
        for clock, s in sigma.items():
            for alt_sigma in (50.0, None):
                ax, t, up = crlb.grid_targets(*CENTER, 250e3, 101, 10_000.0)
                h = crlb.horizontal_sigma(t, rx, s * 1e-9, alt_sigma, up)
                maps[f"{n}|{clock}|{alt_sigma}"] = np.where(h > 1e6, np.nan, h).reshape(101, 101).tolist()
        maps[f"rx|{n}"] = (np.array([[np.dot(p - mc.ring(1, 0)[0], b) for b in crlb_basis()[:2]] for p in rx]) / 1e3).tolist()
    out["maps"] = maps
    out["map_axis_km"] = (ax / 1e3).tolist()
    return out


def crlb_basis():
    from adsbee_mlat_sim.geodesy import enu_basis

    return enu_basis(*CENTER)


if __name__ == "__main__":
    with Pool(6) as pool:
        res = pool.map(run_job, mc_jobs())
    mc_out = {}
    for name, hz, seed, s in res:
        mc_out.setdefault(name, {}).setdefault(str(int(hz / 1e6)), []).append(s)
    # Per-receiver timing error of the base scenario sets the CRLB inputs.
    sigma = {c: float(np.mean([np.mean(s["sigma_ns"]) for s in mc_out["base"][c]])) for c in ("12", "48")}
    out = dict(mc=mc_out, crlb=crlb_study(sigma))
    with open(OUT, "w") as fh:
        json.dump(out, fh)
    print("sigma", sigma)
