import numpy as np
import pytest

from adsbee_mlat.clocksync import ClockSync, PairSync


def _clock(t, offset, ppm):
    return offset + t * (1 + ppm * 1e-6)


def test_pair_tracks_offset_and_rate():
    rng = np.random.default_rng(1)
    p = PairSync(0, 1)
    for t in np.arange(0, 60, 0.05):
        ei = _clock(t, 100.0, 3.0) + rng.normal(0, 20e-9)
        ej = _clock(t, 250.0, -12.0) + rng.normal(0, 20e-9)
        p.update(ei, ej, 2 * (20e-9) ** 2, wall=t)
    assert p.valid
    assert p.b == pytest.approx(-15e-6 / (1 + 3e-6), abs=1e-8)
    t = 60.0
    off, var = p.predict(_clock(t, 100.0, 3.0))
    assert off == pytest.approx(_clock(t, 250.0, -12.0) - _clock(t, 100.0, 3.0), abs=10e-9)
    assert var**0.5 < 10e-9


def test_outliers_rejected_and_step_recovered():
    rng = np.random.default_rng(2)
    p = PairSync(0, 1)
    step = 0.0
    rejected = 0
    for k, t in enumerate(np.arange(0, 40, 0.1)):
        if k == 200:
            step = 5e-6  # The second clock jumps by 5 us.
        ej = _clock(t, 10.0, 1.0) + step + rng.normal(0, 20e-9)
        if k % 37 == 5:
            ej += 2e-6  # A multipath outlier.
        ok = p.update(_clock(t, 0.0, 0.0), ej, 2 * (20e-9) ** 2, wall=t)
        rejected += not ok
    assert rejected >= 6
    off, _ = p.predict(39.9)
    assert off == pytest.approx(10.0 + 39.9e-6 + 5e-6, abs=30e-9)


def test_conversion_both_directions_and_through_graph():
    sync = ClockSync()
    rng = np.random.default_rng(3)
    clocks = {0: (5.0, 2.0), 1: (17.0, -8.0), 2: (-3.0, 20.0)}
    for t in np.arange(0, 20, 0.05):
        # Pairs 0-1 and 1-2 only: 0 reaches 2 through 1.
        for a, b in ((0, 1), (1, 2)):
            ea = _clock(t, *clocks[a]) + rng.normal(0, 10e-9)
            eb = _clock(t, *clocks[b]) + rng.normal(0, 10e-9)
            sync.add_event([a, b], [ea, eb], [(10e-9) ** 2] * 2, wall=t)
    t = 19.0
    for base, other in ((0, 1), (1, 0), (0, 2), (2, 0)):
        r = sync.to_base(base, other, _clock(t, *clocks[other]), wall=t)
        assert r is not None, (base, other)
        assert r[0] == pytest.approx(_clock(t, *clocks[base]), abs=20e-9)
    assert sync.paths_from(0, t)[2] == [0, 1, 2]


def test_reset_receiver_drops_pairs():
    sync = ClockSync()
    for t in range(10):
        sync.add_event([0, 1, 2], [t, t + 1.0, t + 2.0], [1e-16] * 3, wall=float(t))
    assert len(sync.pairs) == 3
    sync.reset_receiver(1)
    assert set(sync.pairs) == {(0, 2)}
    assert sync.to_base(0, 1, 5.0, 100.0) is None


def test_jitter_estimate_finds_noisy_receiver():
    sync = ClockSync()
    rng = np.random.default_rng(4)
    sig = [20e-9, 20e-9, 20e-9, 300e-9]
    for t in np.arange(0, 120, 0.05):
        e = [t + 10 * k + rng.normal(0, s) for k, s in enumerate(sig)]
        sync.add_event([0, 1, 2, 3], e, [s * s for s in sig], wall=t)
    est = sync.estimate_jitter(None)
    assert est[3] == pytest.approx(300e-9, rel=0.3)
    assert est[0] < 60e-9
