import numpy as np
import pytest

import adsbee_mlat_sim as sim
from adsbee_mlat_sim import modes
from adsbee_mlat_sim.geodesy import C_M_PER_S, ecef_to_lla, lla_to_ecef


def test_geodesy_round_trip():
    lat, lon, alt = ecef_to_lla(lla_to_ecef(47.6, -122.3, 10_000.0))
    assert lat == pytest.approx(47.6, abs=1e-9) and lon == pytest.approx(-122.3, abs=1e-9)
    assert alt == pytest.approx(10_000.0, abs=1e-4)


def test_crc_of_known_frame():
    # DF17 identification of KLM1023 (pyModeS documentation example): parity of the whole frame is zero.
    frame = bytes.fromhex("8D4840D6202CC371C32CE0576098")
    assert modes.crc24(frame[:-3]) == int.from_bytes(frame[-3:], "big")


def test_frames_decode():
    pms = pytest.importorskip("pyModeS")
    sc = sim.example_scenario(n_aircraft=10)
    frames = list(sc.frames(20))
    assert frames
    for f in frames:
        h = f.msg.hex()
        assert int(pms.icao(h), 16) == f.icao
        if f.df in (11, 17):
            assert pms.crc(h) == 0
    by_icao = {}
    for f in frames:
        if f.df == 17 and pms.adsb.typecode(f.msg.hex()) == 11:
            by_icao.setdefault((f.icao, pms.adsb.oe_flag(f.msg.hex())), f)
    pairs = [(by_icao[(i, 0)], by_icao[(i, 1)]) for i, o in by_icao if o == 0 and (i, 1) in by_icao]
    assert pairs
    for even, odd in pairs:
        lat, lon = pms.adsb.position(even.msg.hex(), odd.msg.hex(), even.t_emit, odd.t_emit)
        # Reported position error (NACp, latency, time between the pair) stays within a few hundred meters.
        assert abs(lat - odd.lat) < 0.01 and abs(lon - odd.lon) < 0.015


def test_frames_sorted_and_match_simulate():
    sc = sim.example_scenario(n_aircraft=8)
    frames = list(sc.frames(12))
    em, rec = sc.simulate(12)
    assert len(frames) == len(rec)
    assert np.all(np.diff([f.t_arrival for f in frames]) >= 0)
    assert [f.ticks for f in frames[:50]] == list(rec.ticks[:50])


def test_ticks_follow_geometry_and_clock():
    sc = sim.example_scenario(n_aircraft=6, clock_hz=12e6)
    for r in sc.receivers:
        r.timing = sim.TimingModel(jitter_ns=0, pair_bias_ns=0, multipath_prob=0)
    sc.__post_init__()
    sc.tropo = False
    for f in sc.frames(5):
        rx = sc.receivers[sc.receiver_index(f.rx_id)]
        dist = np.linalg.norm(np.array(f.ecef) - rx.ecef)
        assert f.t_arrival == pytest.approx(f.t_emit + 64e-6 + dist / C_M_PER_S, abs=1e-12)
        local = rx.clock.local_time(f.t_arrival)
        assert f.ticks == int(np.floor(local * 12e6))


def test_clock_reset_and_step():
    c = sim.Clock(clock_hz=48e6, offset_s=100.0, random_walk_ppm=0, steps=[(2.0, 1e-6)], resets=[5.0])
    assert c.local_time(1.0) == pytest.approx(101.0)
    assert c.local_time(3.0) == pytest.approx(103.0 + 1e-6)
    assert c.local_time(6.0) == pytest.approx(1.0)


def test_beast_escape():
    f = sim.Frame(rx_id="a", ticks=0x1A1A1A1A1A1A, clock_hz=12_000_000, msg=bytes.fromhex("5d1a0000000000"),
                  signal_dbm=-50, icao=0, df=11, t_emit=0, t_arrival=0, t_unix=0, lat=0, lon=0, alt_m=0,
                  ecef=(0, 0, 0), err_ns=0)  # fmt: skip
    b = f.beast()
    assert b[:2] == b"\x1a\x32"
    assert b[2:].replace(b"\x1a\x1a", b"\x1a")[:6] == bytes([0x1A] * 6)
    assert b.count(b"\x1a\x1a") == 7
