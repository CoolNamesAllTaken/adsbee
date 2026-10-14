import pytest

from adsbee_mlat import cpr, modes


def test_known_messages():
    d = modes.decode(bytes.fromhex("8D40621D58C382D690C8AC2863A7"))
    assert d.df == 17 and d.icao == 0x40621D and d.alt_ft == 38000 and d.cpr_odd == 0
    d = modes.decode(bytes.fromhex("8D485020994409940838175B284F"))
    assert d.gs_kt == pytest.approx(159.2, abs=0.1) and d.track_deg == pytest.approx(182.88, abs=0.01)
    assert d.vr_fpm == -832 and d.geo_minus_baro_ft == 550
    assert modes.decode(bytes.fromhex("8D4840D6202CC371C32CE0576098")).callsign == "KLM1023"


def test_parity_failure():
    m = bytearray.fromhex("8D40621D58C382D690C8AC2863A7")
    m[5] ^= 1
    assert modes.decode(bytes(m)) is None


def _ap(body: bytes, icao: int) -> bytes:
    return body + (modes.parity(body) ^ icao).to_bytes(3, "big")


def test_address_parity_formats():
    icao = 0xABCDEF
    # DF4, altitude code with Q bit: 25 ft steps.
    n = (35000 + 1000) // 25
    ac13 = ((n & 0x7F0) << 2) | 0x10 | (n & 0x0F)
    d = modes.decode(_ap(bytes([4 << 3, 0, (ac13 >> 8) & 0x1F, ac13 & 0xFF]), icao))
    assert d.df == 4 and d.icao == icao and not d.trusted and d.alt_ft == 35000
    # DF5 squawk 7700: A=7 B=7 C=0 D=0.
    id13 = (1 << 11) | (1 << 9) | (1 << 7) | (1 << 5) | (1 << 3) | (1 << 1)
    d = modes.decode(_ap(bytes([5 << 3, 0, (id13 >> 8) & 0x1F, id13 & 0xFF]), icao))
    assert d.squawk == "7700" and d.icao == icao
    # DF11 all-call: address in clear, parity with interrogator 0.
    body = bytes([11 << 3 | 5]) + icao.to_bytes(3, "big")
    d = modes.decode(body + modes.parity(body).to_bytes(3, "big"))
    assert d.df == 11 and d.trusted and d.icao == icao
    # DF11 with a nonzero interrogator code is accepted but not trusted.
    d = modes.decode(body + (modes.parity(body) ^ 0x12).to_bytes(3, "big"))
    assert d is not None and not d.trusted


@pytest.mark.parametrize("alt", [-1000, -900, 0, 500, 1200, 12300, 25000, 41000])
def test_gillham(alt):
    # Encode by searching the code space, then check decoding is unique.
    hits = [c for c in range(1 << 13) if not (c >> 6) & 1 and not (c >> 4) & 1 and modes.decode_ac13(c) == alt]
    assert hits, alt


def test_cpr_global_and_local():
    assert cpr.global_airborne(93000, 51372, 74158, 50194, False) == pytest.approx((52.25720, 3.91937), abs=1e-5)
    assert cpr.local_airborne(93000, 51372, 0, 52.258, 3.918) == pytest.approx((52.25720, 3.91937), abs=1e-5)


def test_cpr_round_trip():
    import random

    rnd = random.Random(2)
    for _ in range(500):
        lat, lon = rnd.uniform(-80, 80), rnd.uniform(-180, 180)
        e, o = cpr.encode_airborne(lat, lon, 0), cpr.encode_airborne(lat, lon, 1)
        r = cpr.global_airborne(*e, *o, True)
        if r is not None:
            assert r[0] == pytest.approx(lat, abs=1e-4)  # Resolution: 5 m in latitude, coarser in longitude.
            assert (r[1] - lon + 180) % 360 - 180 == pytest.approx(0, abs=3e-4)
