import numpy as np
import pytest

from adsbee_mlat import geo, solver, tracker

C = geo.C


def _setup(n=5, seed=0, sigma=20e-9):
    rng = np.random.default_rng(seed)
    rx_llh = [(47.6 + rng.uniform(-0.2, 0.2), -122.3 + rng.uniform(-0.3, 0.3), 50.0) for _ in range(n)]
    rx = np.array([geo.llh_to_ecef(*p) for p in rx_llh])
    target = geo.llh_to_ecef(47.9, -122.0, 9000.0)
    t_emit = 123.456
    times = t_emit + np.linalg.norm(rx - target, axis=1) / C + rng.normal(0, sigma, n)
    return rx, target, times, np.full(n, sigma)


def test_solve_four_receivers():
    rx, target, times, sig = _setup(5)
    fix = solver.solve(rx, times, sig)
    assert fix is not None
    assert np.linalg.norm(fix.ecef - target) < 200
    assert fix.gdop is not None and fix.gdop > 1
    assert fix.horizontal_error_m() < 500


def test_solve_three_receivers_with_altitude():
    rx, target, times, sig = _setup(3, seed=1)
    fix = solver.solve(rx, times, sig, altitude=(9000.0, 30.0))
    assert fix is not None
    assert np.linalg.norm(fix.ecef - target) < 3 * np.sqrt(np.trace(fix.cov))
    lat, lon, h = fix.llh
    assert h == pytest.approx(9000.0, abs=100)


def test_underdetermined():
    rx, target, times, sig = _setup(3)
    assert solver.solve(rx, times, sig) is None


def test_covariance_matches_scatter():
    errs = []
    covs = []
    for seed in range(200):
        rx, target, times, sig = _setup(6, seed=100 + seed % 1, sigma=30e-9)
        rng = np.random.default_rng(seed)
        times = times + rng.normal(0, 30e-9, len(times))
        fix = solver.solve(rx, times, np.full(len(times), np.hypot(20e-9, 30e-9)))
        errs.append(fix.ecef - target)
        covs.append(fix.cov)
    errs = np.array(errs)
    emp = np.cov(errs.T)
    pred = np.mean(covs, axis=0)
    assert np.trace(emp) == pytest.approx(np.trace(pred), rel=0.35)


def test_track_converges_with_two_receiver_updates():
    # A track started from a fix keeps improving with updates from any two receivers plus altitude.
    rng = np.random.default_rng(5)
    rx, _, _, _ = _setup(5)
    vel = np.array([150.0, -100.0, 0.0])
    p0 = geo.llh_to_ecef(47.9, -122.0, 9000.0)
    track = None
    for k in range(200):
        t = k * 0.2
        p = p0 + vel * t
        idx = rng.choice(5, 2 if k else 5, replace=False)
        times = 1.0 + t + np.linalg.norm(rx[idx] - p, axis=1) / C + rng.normal(0, 20e-9, len(idx))
        _, _, h = geo.ecef_to_llh(p)
        alt = (float(h), 20.0)
        sig = np.full(len(idx), 20e-9)
        if track is None:
            track, _ = tracker.init_track(rx[idx], times, sig, alt, t)
            continue
        track.predict(t)
        track.update_tdoa(rx[idx], times, sig, alt)
    assert np.linalg.norm(track.x[:3] - p) < 300
    assert np.linalg.norm(track.x[3:] - vel) < 30
