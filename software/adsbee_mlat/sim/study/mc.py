"""Monte Carlo check: simulate, synchronize clocks from ADS-B reference aircraft, multilaterate, compare to truth.

This is a minimal reference server for the study: messages are grouped by their true emission, the solver starts
near the truth (as a tracker would) and the altitude measurement is the true height plus a per-aircraft error.
"""

from dataclasses import dataclass

import numpy as np

import adsbee_mlat_sim as sim
from adsbee_mlat_sim.geodesy import C_M_PER_S, FT_TO_M, ecef_to_lla, enu_basis, lla_to_ecef
from adsbee_mlat_sim.scenario import KINDS

POS = KINDS.index("pos")


@dataclass
class Config:
    n_rx: int = 4
    aperture_m: float = 20e3  # Largest distance between two receivers (receivers on a ring).
    clock_hz: float = 48e6
    receiver_type: str = "adsbee_1090"
    duration_s: float = 120.0
    n_aircraft: int = 80
    radius_m: float = 250e3
    adsb_share: float = 0.6
    gnss_sigma_m: float | None = None  # Receiver position error (horizontal, per axis); None: surveyed.
    tropo_n0_true: float = 340.0  # Refractivity of the simulated atmosphere.
    tropo_n0_model: float | None = 315.0  # Refractivity the server assumes; None: no correction.
    alt_sigma_m: float | None = 50.0  # Altitude measurement error; None: solve without altitude.
    sync_window_s: float = 2.0  # Half width of the clock fit window.
    random_walk_ppm: float = 0.002
    seed: int = 0
    center: tuple = (47.6, -122.3)
    mixed_types: tuple | None = None  # Receiver type per receiver, overrides receiver_type.


def chord_for_aperture(n, aperture_m):
    """Neighbor spacing of an n-receiver ring whose largest receiver separation is aperture_m."""
    return aperture_m * np.sin(np.pi / n) / np.sin((n // 2) * np.pi / n)


def ring(n, aperture_m, center=(47.6, -122.3)):
    return np.array([r.ecef for r in sim.make_array(*center, n, chord_for_aperture(n, aperture_m), center_receiver=False)])


def build(cfg: Config):
    rng = np.random.default_rng([cfg.seed, 100])
    receivers = sim.make_array(*cfg.center, cfg.n_rx, chord_for_aperture(cfg.n_rx, cfg.aperture_m), clock_hz=cfg.clock_hz,
                               receiver_type=cfg.receiver_type, seed=cfg.seed, gnss_sigma_m=cfg.gnss_sigma_m,
                               random_walk_ppm=cfg.random_walk_ppm, center_receiver=False)  # fmt: skip
    if cfg.mixed_types:
        for r, t in zip(receivers, cfg.mixed_types):
            r.timing = sim.RECEIVER_TYPES[t]()
            if t == "rtlsdr":  # dump1090 timestamps are always 12 MHz.
                r.clock.clock_hz = 12e6
    aircraft = sim.random_traffic(rng, *cfg.center, cfg.n_aircraft, cfg.radius_m, adsb_share=cfg.adsb_share)
    return sim.Scenario(receivers=receivers, aircraft=aircraft, seed=cfg.seed, tropo_n0=cfg.tropo_n0_true)


def tropo_model(sc, cfg, rx, target_ecef):
    if cfg.tropo_n0_model is None:
        return np.zeros(len(target_ecef))
    n0 = sc.tropo_n0
    sc.tropo_n0 = cfg.tropo_n0_model
    try:
        return sc.tropo_delay_s(rx.reported_ecef, rx.reported_alt_m, target_ecef)
    finally:
        sc.tropo_n0 = n0


def sliding_fit(x, y, xq, half_width):
    """Local linear fit of y(x) within +-half_width around each query; returns value at xq and points used."""
    order = np.argsort(x)
    x, y = x[order], y[order]
    xc = x - x[0]
    cs = [np.concatenate([[0], np.cumsum(v)]) for v in (np.ones_like(xc), xc, y, xc * y, xc * xc)]
    lo = np.searchsorted(x, xq - half_width)
    hi = np.searchsorted(x, xq + half_width)
    n, sx, sy, sxy, sxx = (c[hi] - c[lo] for c in cs)
    with np.errstate(invalid="ignore", divide="ignore"):
        den = sxx - sx * sx / n
        slope = np.where(den > 0, (sxy - sx * sy / n) / den, 0.0)
        mean_x, mean_y = sx / n, sy / n
    q = xq - x[0]
    return mean_y + slope * (q - mean_x), n


def run(cfg: Config):
    sc = build(cfg)
    em, rec = sc.simulate(cfg.duration_s)
    n_rx = len(sc.receivers)
    hz = np.array([r.clock_hz for r in sc.receivers], float)
    local = rec.ticks / hz[rec.rx] + 0.5 / hz[rec.rx]  # Receiver time in seconds, center of the tick.

    # Arrival table: local time per (emission, receiver), NaN where not received.
    table = np.full((len(em), n_rx), np.nan)
    table[rec.emission, rec.rx] = local
    t_true = np.full((len(em), n_rx), np.nan)
    t_true[rec.emission, rec.rx] = rec.t_arrival

    # Reported position of reference aircraft (CPR quantization is ignored: about 5 m, averaged by many messages).
    is_ref = em.kind == POS
    alt_q = np.round(em.alt_m / FT_TO_M / 25) * 25 * FT_TO_M
    ref_ecef = lla_to_ecef(em.rep_lat, em.rep_lon, alt_q)
    rx_rep = np.array([r.reported_ecef for r in sc.receivers])

    # Emission time in each receiver's clock: local arrival minus predicted propagation.
    def predicted(ecef, rows):
        out = np.zeros((len(rows), n_rx))
        for i, r in enumerate(sc.receivers):
            out[:, i] = np.linalg.norm(ecef - rx_rep[i], axis=1) / C_M_PER_S + tropo_model(sc, cfg, r, ecef)
        return out

    ref_rows = np.nonzero(is_ref)[0]
    e_ref = table[ref_rows] - predicted(ref_ecef[ref_rows], ref_rows)

    # Clock sync to receiver 0: offset_i(local_i) = E_0 - E_i, fitted in a sliding window with outlier removal.
    targets = np.nonzero(~np.array([sc.aircraft[a].adsb for a in em.aircraft]))[0]
    t_common = sync(cfg, e_ref, table[ref_rows], table, targets, n_rx)
    sync_err = []

    # True sync error: clock offset implied by the fit minus the true clock offset at the frame's true arrival.
    clocks = [r.clock for r in sc.receivers]
    for i in range(1, n_rx):
        has = np.isfinite(t_common[:, i]) & np.isfinite(t_common[:, 0])
        tt = t_true[targets[has], i]
        true_off = clocks[0].local_time(tt) - clocks[i].local_time(tt)
        sync_err.append((t_common[has, i] - table[targets[has], i]) - true_off)

    fixes = solve(sc, cfg, em, targets, t_common, rx_rep)
    return dict(cfg=cfg, sc=sc, em=em, rec=rec, targets=targets, t_common=t_common, sync_err=sync_err, fixes=fixes)


def sync(cfg, e_ref, arrival_ref, table, targets, n_rx):
    """Map each receiver's local arrival times into receiver 0's clock.

    The offset y = E_0 - E_i (emission time seen by each clock) is a function of receiver i's local arrival time.
    Using the arrival time as the regressor keeps the frequency difference from scaling the propagation delay.
    """
    t_common = np.full((len(targets), n_rx), np.nan)
    t_common[:, 0] = table[targets, 0]
    for i in range(1, n_rx):
        ok = np.isfinite(e_ref[:, 0]) & np.isfinite(e_ref[:, i])
        x, y = arrival_ref[ok, i], e_ref[ok, 0] - e_ref[ok, i]
        if len(x) < 10:
            continue
        x0 = x.min()
        trend = np.polyfit(x - x0, y, 1)
        yr = y - np.polyval(trend, x - x0)
        for _ in range(2):
            fit, _ = sliding_fit(x, yr, x, cfg.sync_window_s)
            res = yr - fit
            mad = np.median(np.abs(res - np.median(res))) * 1.4826
            keep = np.abs(res) < 5 * max(mad, 1e-9)
            x, yr = x[keep], yr[keep]
        xq = table[targets, i]
        has = np.isfinite(xq)
        fit, n = sliding_fit(x, yr, xq[has], cfg.sync_window_s)
        off = np.where(n >= 4, fit + np.polyval(trend, xq[has] - x0), np.nan)
        col = np.full(len(xq), np.nan)
        col[has] = xq[has] + off
        t_common[:, i] = col
    return t_common


def solve(sc, cfg, em, targets, t_common, rx_rep, iterations=25):
    """Batched Gauss-Newton on (position, emission time) with an optional altitude measurement."""
    rng = np.random.default_rng([cfg.seed, 200])
    mask = np.isfinite(t_common)
    min_rx = 3 if cfg.alt_sigma_m is not None else 4
    use = mask.sum(1) >= min_rx
    idx = np.nonzero(use)[0]
    T = np.where(mask[idx], t_common[idx], 0.0) * C_M_PER_S
    W = mask[idx].astype(float)
    truth = em.ecef[targets[idx]]
    lat_t, lon_t, alt_t = em.lat[targets[idx]], em.lon[targets[idx]], em.alt_m[targets[idx]]
    # Altitude measurement: per-aircraft error (pressure altitude correction) plus 25 ft steps.
    ac = em.aircraft[targets[idx]]
    alt_err = rng.normal(0, cfg.alt_sigma_m or 0, len(sc.aircraft))[ac]
    alt_meas = np.round((alt_t + alt_err) / FT_TO_M / 25) * 25 * FT_TO_M
    # Start near the truth, as a tracker would: 2 km horizontal, 300 m vertical.
    start = np.stack([enu_basis(a, b) for a, b in zip(lat_t, lon_t)])  # (n, 3, 3)
    off = rng.normal(0, [2000, 2000, 300], (len(idx), 3))
    x = truth + np.einsum("ni,nij->nj", off, start)
    # Emission time (meters) start: mean of arrival minus range.
    rng_m = np.linalg.norm(x[:, None, :] - rx_rep[None], axis=2)
    ct0 = ((T - rng_m) * W).sum(1) / W.sum(1)
    sig_m = 30e-9 * C_M_PER_S  # Weights only matter relative to the altitude term.
    for _ in range(iterations):
        d = x[:, None, :] - rx_rep[None]
        r = np.linalg.norm(d, axis=2)
        u = d / r[..., None]
        res = (T - r - ct0[:, None]) * W  # (n, m)
        J = np.concatenate([u, np.ones(u.shape[:2] + (1,))], axis=2) * W[..., None]
        A = np.einsum("nmi,nmj->nij", J, J) / sig_m**2
        b = np.einsum("nmi,nm->ni", J, res) / sig_m**2
        if cfg.alt_sigma_m is not None:
            lat, lon, h = ecef_to_lla(x)
            up = np.stack([np.cos(np.radians(lat)) * np.cos(np.radians(lon)),
                           np.cos(np.radians(lat)) * np.sin(np.radians(lon)), np.sin(np.radians(lat))], axis=1)  # fmt: skip
            ja = np.concatenate([up, np.zeros((len(idx), 1))], axis=1)
            A = A + np.einsum("ni,nj->nij", ja, ja) / cfg.alt_sigma_m**2
            b = b + ja * ((alt_meas - h) / cfg.alt_sigma_m**2)[:, None]
        step = np.linalg.solve(A + np.eye(4) * 1e-12, b[..., None])[..., 0]
        x = x + step[:, :3]
        ct0 = ct0 + step[:, 3]
    # Residual check: drop the worst receiver of fixes with a large residual and an extra receiver to spare.
    d = x[:, None, :] - rx_rep[None]
    res = (T - np.linalg.norm(d, axis=2) - ct0[:, None]) * W
    rms_ns = np.sqrt((res**2).sum(1) / np.maximum(W.sum(1) - (3 if cfg.alt_sigma_m else 4), 1)) / C_M_PER_S * 1e9
    enu_err = np.einsum("nij,nj->ni", start, x - truth)
    center = lla_to_ecef(*cfg.center, 0.0)
    rng_km = np.linalg.norm(truth - center, axis=1) / 1e3
    return dict(idx=idx, nrx=W.sum(1).astype(int), herr=np.hypot(enu_err[:, 0], enu_err[:, 1]), verr=enu_err[:, 2],
                range_km=rng_km, rms_ns=rms_ns, truth=truth, solution=x, mask=mask[idx])  # fmt: skip
