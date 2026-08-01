"""Round-trip tests for the world.map archive format (mapfmt.py).

Validates the frozen struct sizes (which the future terrain_tile.hh static_asserts
must match), the block codec (constant / deflate / predictor+deflate) via the
Python reference decoder, and header/level/directory serialization. Also checks a
mini in-memory pyramid's seam continuity + provenance.

Needs numpy (host build dependency). Run:
    python -m pytest tests/test_mapfmt.py  (or)  python tests/test_mapfmt.py
"""
import io
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from terrain_tiler import mapfmt  # noqa: E402


def test_struct_sizes():
    # These numbers are the single source of truth; the firmware's
    # static_assert(sizeof(...)==N) must match them exactly.
    assert mapfmt.PYR_HEADER_SIZE == 52
    assert mapfmt.LEVEL_DESC_SIZE == 32
    assert mapfmt.BLOCK_DIR_ENTRY_SIZE == 12
    assert mapfmt.VEC_RECORD_HDR_SIZE == 6
    assert mapfmt.VEC_POINT_SIZE == 8


def test_block_codec_roundtrip():
    rng = np.random.default_rng(0)
    cases = {
        "constant": np.full((64, 64), 7, np.uint8),
        "gradient": np.tile(np.arange(64, dtype=np.uint8), (64, 1)),
        "random": rng.integers(0, 255, (64, 64), dtype=np.uint8),
        "smooth": (np.add.outer(np.arange(64), np.arange(64)) // 2 % 255).astype(np.uint8),
        "void_mix": np.where(rng.random((64, 64)) < 0.3, 255,
                             rng.integers(0, 50, (64, 64))).astype(np.uint8),
    }
    for name, blk in cases.items():
        codec, stored, fill = mapfmt.encode_block(blk)
        dec = mapfmt.decode_block(codec, stored, fill)
        assert np.array_equal(dec, blk), f"{name} did not round-trip"
    # constant blocks must dedup to zero payload
    codec, stored, fill = mapfmt.encode_block(cases["constant"])
    assert codec == mapfmt.BLOCK_CONSTANT and stored == b"" and fill == 7


def test_predictor_reference_integer_only():
    # The device decode path is inflate + predictor_unfilter; verify unfilter is
    # an exact inverse (integer-only) for a smooth block that picks the predictor.
    blk = (np.add.outer(np.arange(64), np.arange(64)) // 3 % 200).astype(np.uint8)
    filt = mapfmt.predictor_filter(blk)
    back = mapfmt.predictor_unfilter(filt, 64, 64)
    assert np.array_equal(back, blk)


def test_header_and_level_roundtrip():
    hdr = mapfmt.pack_pyramid_header(8, 172_000, 360_000, vec_index_offset=1 << 30,
                                     provenance_offset=52, provenance_len=100,
                                     dir_crc16=0xBEEF)
    h = mapfmt.unpack_pyramid_header(hdr)
    assert h["_magic_ok"] and h["_header_crc_ok"]
    assert h["num_levels"] == 8 and h["dir_crc16"] == 0xBEEF
    assert h["vec_index_offset"] == (1 << 30)

    ld = mapfmt.pack_level_desc(46081, 22017, 732, 350, 4096,
                                mapfmt.nm_per_sample(0), -12)
    lv = mapfmt.unpack_level_desc(ld)
    assert lv["samples_w"] == 46081 and lv["blocks_x"] == 732
    assert abs(lv["nm_per_sample"] - 0.469) < 0.01

    de = mapfmt.pack_block_dir_entry(1000, 234, 4096, mapfmt.BLOCK_PRED_DEFLATE, 0)
    e = mapfmt.unpack_block_dir_entry(de)
    assert e["offset"] == 1000 and e["codec"] == mapfmt.BLOCK_PRED_DEFLATE


def test_level_geometry_nesting():
    # n*2^L + 1 dims so coarse samples coincide with fine ones (no drift).
    w0, h0 = mapfmt.level_dims(0, 8)
    assert w0 == 46081 and h0 == 22017
    for L in range(1, 8):
        w, h = mapfmt.level_dims(L, 8)
        # decimating L0 by 2^L yields exactly this level's dims
        assert w == (46080 >> L) + 1
        assert h == (22016 >> L) + 1


def test_mini_pyramid_seam_and_provenance():
    """Build a 2-block-wide mini level in memory, write via the archive path's
    directory logic, and confirm shared edges match + provenance round-trips."""
    from terrain_tiler import pyramid, archive, provenance

    # A synthetic L-array 127 wide (=> 2 shared-edge blocks) x 64 tall.
    codes = (np.add.outer(np.arange(64), np.arange(127)) % 200).astype(np.uint8)

    buf = io.BytesIO()
    prov = provenance.collect("data/ETOPO_2022_v1_30s_N90W180_surface.tif",
                              "data/10m_physical", "data/10m_cultural", "2026-01-01",
                              format_version=1, num_levels=1,
                              finest_samples_per_deg=128, elev_step_m=40)
    prov_blob = provenance.to_blob(prov)

    # single-level archive using the block iterator directly
    w = archive.ArchiveWriter(buf, num_levels=1, jobs=1)
    # inline single-process build (avoid the pool for a unit test)
    w._reserve_front(prov_blob)
    dim = mapfmt.BLOCK_DIM
    blocks_x = mapfmt.blocks_across(codes.shape[1])
    dir_offset = buf.tell()
    payload_offset = dir_offset + blocks_x * mapfmt.BLOCK_DIR_ENTRY_SIZE
    buf.seek(payload_offset)
    entries = [None] * blocks_x
    written = payload_offset
    for by, bx, codec, stored, fill, raw in pyramid.iter_level_blocks(codes):
        if codec == mapfmt.BLOCK_CONSTANT:
            entries[bx] = mapfmt.pack_block_dir_entry(0, 0, raw, codec, fill)
        else:
            buf.write(stored)
            entries[bx] = mapfmt.pack_block_dir_entry(written, len(stored), raw, codec, fill)
            written += len(stored)
    buf.seek(dir_offset)
    buf.write(b"".join(entries))

    # decode the two blocks and check the shared column
    def load(bx):
        buf.seek(dir_offset + bx * mapfmt.BLOCK_DIR_ENTRY_SIZE)
        e = mapfmt.unpack_block_dir_entry(buf.read(mapfmt.BLOCK_DIR_ENTRY_SIZE))
        if e["stored_len"] == 0:
            return np.full((dim, dim), e["fill"], np.uint8)
        buf.seek(e["offset"])
        return mapfmt.decode_block(e["codec"], buf.read(e["stored_len"]), e["fill"])

    b0, b1 = load(0), load(1)
    assert np.array_equal(b0[:, -1], b1[:, 0]), "block seam mismatch"

    # provenance blob round-trips + carries the versions
    import json
    p = json.loads(prov_blob)
    assert p["vectors"]["physical_version"] == "5.1.1"
    assert p["vectors"]["cultural_version"] == "5.1.2"
    assert p["elevation"]["variant"] == "30s surface"


def _run():
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for fn in fns:
        fn()
        print(f"  ok {fn.__name__}")
    print("all mapfmt tests passed")


if __name__ == "__main__":
    _run()
