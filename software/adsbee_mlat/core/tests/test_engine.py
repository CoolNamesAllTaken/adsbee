"""Engine on simulated traffic, driven directly with simulated time."""

import pytest

sim = pytest.importorskip("adsbee_mlat_sim")

from adsbee_mlat import validation  # noqa: E402
from adsbee_mlat.receiver import Receiver  # noqa: E402


def _scenario(clock_hz=48e6, seed=2, n=6):
    return sim.example_scenario(n_receivers=n, baseline_m=30e3, n_aircraft=30, radius_m=100e3, clock_hz=clock_hz,
                                seed=seed)


@pytest.mark.parametrize("clock_hz", [12e6, 48e6])
def test_accuracy_and_rate(clock_hz):
    sc = _scenario(clock_hz)
    eng, col = validation.run(sc, 60)
    s = validation.summarize(col.errors(settle_s=20))
    assert s["h_p50"] < 100, s
    assert s["rate_hz_median"] > 3.0, s  # Every message heard by two synchronized receivers updates the track.
    assert 0.4 < s["within_est_1sigma"] < 0.9, s


def test_bad_clock_receiver_is_excluded():
    sc = _scenario()
    sc.receivers[2].clock.random_walk_ppm = 0.5
    eng, col = validation.run(sc, 60)
    status = {r["id"]: r for r in eng.receivers_status()}
    assert not status["rx2"]["sync_ok"]
    assert all(r["sync_ok"] for k, r in status.items() if k != "rx2")
    assert validation.summarize(col.errors(settle_s=20))["h_p50"] < 120


def test_counter_reset_recovers():
    sc = _scenario()
    sc.receivers[1].clock.resets = [30.0]
    eng, col = validation.run(sc, 60)
    assert eng.receivers["rx1"].resets == 1
    late = [r for r in col.errors() if r[1] > 45]
    assert validation.summarize(late)["h_p50"] < 100
    assert "rx1" in {p for r in eng.receivers_status() for p in r["peers"]}


def test_unstamped_frames_decode_but_skip_mlat():
    sc = _scenario(n=4)
    frames = list(sc.frames(30))
    for f in frames:
        f.ticks = 0  # Every frame without a timestamp, as an m1421 sends when it cannot stamp.
    eng, col = validation.run(sc, 30, frames=frames)
    assert eng.stats["adsb_fixes"] > 100
    assert eng.stats["tdoa_updates"] == 0 and not col.updates


def test_timestamp_unwrap_and_jump():
    rx = Receiver("r", 0, 12_000_000)
    top = (1 << 48) - 12_000_000
    t1 = rx.to_seconds(top)
    assert rx.observe_wall(t1, 1000.0)
    t2 = rx.to_seconds(12_000_000)  # Wrapped after 2 s.
    assert t2 - t1 == pytest.approx(2.0)
    assert rx.observe_wall(t2, 1002.0)
    t3 = rx.to_seconds(500 * 12_000_000)  # 498 s later in counter time, 0.1 s later in wall time: restarted.
    assert not rx.observe_wall(t3, 1002.1)
    assert rx.resets == 1
