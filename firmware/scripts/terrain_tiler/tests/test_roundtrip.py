"""Stdlib-only round-trip test for the .map binary format.

Validates that pack.py's TileHeader layout matches terrain_tile.hh (size + field
order) and that pack -> unpack reproduces the values, including CRC16. Run with:
    python -m pytest tests/  (or)  python tests/test_roundtrip.py
No geo dependencies required.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from terrain_tiler import pack  # noqa: E402


def test_header_size():
    # Must match sizeof(TileHeader) in terrain_tile.hh (v2, verified 74 bytes packed).
    assert pack.HEADER_SIZE == 74, f"HEADER_SIZE={pack.HEADER_SIZE}, expected 74"


def test_crc16_known_vector():
    # CRC-16/CCITT-FALSE of "123456789" is 0x29B1; firmware swaps bytes -> 0xB129.
    assert pack.crc16(b"123456789") == 0xB129


def test_roundtrip():
    # A tiny synthetic tile: 4x4 elevation grid, one water polyline, one city.
    w, h = 4, 4
    elev = bytes([0, 1, 2, 3] * 4)  # 16 codes
    water = pack.pack_vec_record(pack.VEC_COASTLINE, [(0, 0), (100, 200), (300, 400)])
    city = pack.pack_vec_record(pack.VEC_CITY_POINT, [(32768, 32768)], name="TESTVILLE")
    mask = bytes([0b10110001, 0b01000010])  # 4x4 1-bit mask = 2 bytes (ceil(4/8)=1/row)

    blob = pack.pack_tile(
        tile_lat0_e6=47_000000, tile_lon0_e6=-122_000000, tile_span_e3=1000,
        elev_bytes=elev, elev_grid_w=w, elev_grid_h=h,
        elev_base_m=-10, elev_step_m=40, elev_bytes_per_sample=1,
        water_records=water, water_count=1,
        road_records=city, road_count=1,
        water_mask_bytes=mask, water_mask_w=w, water_mask_h=h,
    )

    hdr = pack.unpack_header(blob)
    assert hdr["_magic_ok"], "magic mismatch"
    assert hdr["_version_ok"], "version mismatch"
    assert hdr["_header_crc_ok"], "header CRC mismatch"
    assert hdr["tile_lat0_e6"] == 47_000000
    assert hdr["tile_lon0_e6"] == -122_000000
    assert hdr["elev_grid_w"] == w and hdr["elev_grid_h"] == h
    assert hdr["elev_base_m"] == -10 and hdr["elev_step_m"] == 40
    assert hdr["water_count"] == 1 and hdr["road_count"] == 1
    assert hdr["water_mask_w"] == w and hdr["water_mask_h"] == h
    assert hdr["water_mask_len"] == len(mask)

    # Layer offsets must land on the right bytes.
    assert hdr["elev_offset"] == pack.HEADER_SIZE
    assert blob[hdr["elev_offset"]:hdr["elev_offset"] + hdr["elev_len"]] == elev
    assert blob[hdr["water_offset"]:hdr["water_offset"] + hdr["water_len"]] == water
    assert blob[hdr["road_offset"]:hdr["road_offset"] + hdr["road_len"]] == city
    assert blob[hdr["water_mask_offset"]:hdr["water_mask_offset"] + hdr["water_mask_len"]] == mask

    # Payload CRC covers all four layers concatenated (elev + water + road + mask).
    assert hdr["payload_crc16"] == pack.crc16(elev + water + city + mask)


if __name__ == "__main__":
    test_header_size()
    test_crc16_known_vector()
    test_roundtrip()
    print("all round-trip tests passed")
