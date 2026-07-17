"""Tests for the reserved water elevation code (mapfmt.ELEV_WATER_CODE) and its
propagation through the pyramid.

The device draws water==0xFE as a flat grid-fill and cannot derive water from
elevation (ocean and sea-level land both quantize to code 0), so the host burns
0xFE into the L0 lattice from Natural Earth ocean/lakes/rivers and relies on the
2:1 decimation carrying it to every coarser level. These tests pin that contract
without needing the (large) shapefiles: they burn a synthetic water pattern and
assert the reserved code and its decimation behavior.

Run: python -m pytest tests/test_water.py  (or)  python tests/test_water.py
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from terrain_tiler import mapfmt, pyramid  # noqa: E402


def test_reserved_codes_distinct():
    # Void and water are distinct reserved codes above the land range [0, 253].
    assert mapfmt.ELEV_VOID_CODE == 0xFF
    assert mapfmt.ELEV_WATER_CODE == 0xFE
    assert mapfmt.ELEV_WATER_CODE != mapfmt.ELEV_VOID_CODE


def test_water_survives_decimation():
    # A water sample burned at an EVEN (row, col) of the L0 lattice coincides with
    # a coarser-level lattice point (level_codes does [::2^L, ::2^L]), so it still
    # reads as water after decimation — this is why burning at L0 alone suffices.
    l0 = np.zeros((129, 129), np.uint8)  # 4*32+1 => decimates cleanly for L1/L2
    l0[64, 64] = mapfmt.ELEV_WATER_CODE  # even/even => present at L1 and L2
    l0[65, 65] = mapfmt.ELEV_WATER_CODE  # odd/odd  => not on the coarse lattice

    l1 = l0[::2, ::2]  # the stride level_codes applies for level 1
    l2 = l0[::4, ::4]  # ... and level 2
    assert l1[32, 32] == mapfmt.ELEV_WATER_CODE       # (64,64) survives to L1
    assert l2[16, 16] == mapfmt.ELEV_WATER_CODE       # and to L2
    # exactly the even/even water sample lands on the L1 lattice (odd/odd dropped)
    assert int((l1 == mapfmt.ELEV_WATER_CODE).sum()) == 1


def test_encode_constant_water_block():
    # A fully-flooded block encodes as a constant block with fill == water code,
    # zero payload — the common ocean case stays free on-device.
    blk = np.full((mapfmt.BLOCK_DIM, mapfmt.BLOCK_DIM),
                  mapfmt.ELEV_WATER_CODE, np.uint8)
    codec, stored, fill = mapfmt.encode_block(blk)
    assert codec == mapfmt.BLOCK_CONSTANT
    assert stored == b""
    assert fill == mapfmt.ELEV_WATER_CODE
    dec = mapfmt.decode_block(codec, stored, fill)
    assert np.array_equal(dec, blk)


def test_mixed_water_land_block_roundtrips():
    # Water mixed with land must round-trip through the codec so the device sees
    # the exact per-sample water bits (0xFE) alongside land codes.
    rng = np.random.default_rng(3)
    blk = rng.integers(0, 200, (64, 64), dtype=np.uint8)
    blk[:, :20] = mapfmt.ELEV_WATER_CODE     # a coastline down the block
    codec, stored, fill = mapfmt.encode_block(blk)
    dec = mapfmt.decode_block(codec, stored, fill)
    assert np.array_equal(dec, blk)
    assert (dec == mapfmt.ELEV_WATER_CODE).any()


def _run():
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for fn in fns:
        fn()
        print(f"  ok {fn.__name__}")
    print("all water tests passed")


if __name__ == "__main__":
    _run()
