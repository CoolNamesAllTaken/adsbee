"""Tests for Visvalingam-Whyatt importance ordering + the world.map vector record
(vecsimplify.py / vecpack.py).

Proves the property that makes the "one encoding, arbitrary zoom" vector scheme
work: importance is monotone in removal order, so any threshold prefix (re-sorted
by original sequence) is a valid connected simplification with endpoints intact.

Run: python -m pytest tests/test_vectors_vw.py  (or)  python tests/test_vectors_vw.py
"""
import os
import struct
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from terrain_tiler import mapfmt, vecsimplify, vecpack  # noqa: E402


def test_endpoints_are_infinite():
    pts = [(0, 0), (1, 1), (2, 0), (3, 1), (4, 0)]
    imp = vecsimplify.effective_areas(pts)
    assert imp[0] == float("inf") and imp[-1] == float("inf")


def test_big_detour_survives_small_wiggle_dropped():
    pts = [(0, 0), (1, 0.1), (2, -0.1), (3, 0.05), (4, 5), (5, 0.05),
           (6, -0.1), (7, 0.1), (8, 0)]
    imp = vecsimplify.effective_areas(pts)
    ordered = vecsimplify.order_by_importance(pts, imp)

    def simplify(thr):
        keep = [o for o in ordered if o[3] >= thr]
        keep.sort(key=lambda o: o[2])
        return [(o[0], o[1]) for o in keep]

    assert simplify(float("inf")) == [(0, 0), (8, 0)]      # endpoints only
    assert (4, 5) in simplify(1.0)                          # the spike survives
    assert (1, 0.1) not in simplify(1.0)                    # a wiggle is dropped


def test_prefix_is_nested():
    # Coarser (higher threshold) sets must be subsets of finer ones.
    import random
    random.seed(1)
    pts = [(i, random.uniform(-1, 1)) for i in range(40)]
    imp = vecsimplify.effective_areas(pts)
    ordered = vecsimplify.order_by_importance(pts, imp)

    def keep_seqs(thr):
        return {o[2] for o in ordered if o[3] >= thr}

    fine = keep_seqs(0.0)
    mid = keep_seqs(0.1)
    coarse = keep_seqs(1.0)
    assert coarse <= mid <= fine


def test_record_roundtrip_and_progressive():
    coords = [(0.5, 40.5), (1.0, 40.6), (1.5, 40.55), (2.0, 41.0),
              (2.5, 40.5), (3.0, 42.0), (3.5, 40.4), (4.0, 40.5)]
    rec = vecpack.encode_polyline(coords, lon0=0, lat0=40,
                                  feature_type=vecpack.VEC_COASTLINE)
    ft, flags, npts, hint = struct.unpack(
        mapfmt._VEC_REC_FMT, rec[:mapfmt.VEC_RECORD_HDR_SIZE])
    assert ft == vecpack.VEC_COASTLINE
    assert flags & vecpack.VEC_FLAG_IMPORTANCE_SORTED

    pts = []
    off = mapfmt.VEC_RECORD_HDR_SIZE
    for _ in range(npts):
        u, v, seq, imp, _pad = struct.unpack(
            mapfmt._VEC_POINT_FMT, rec[off:off + mapfmt.VEC_POINT_SIZE])
        off += mapfmt.VEC_POINT_SIZE
        pts.append((u, v, seq, imp))

    imps = [p[3] for p in pts]
    assert imps == sorted(imps, reverse=True), "stored order must be importance-desc"

    def draw(thr):
        k = [p for p in pts if p[3] >= thr]
        k.sort(key=lambda p: p[2])
        return k

    full, coarse = draw(0), draw(200)
    assert full[0][:2] == coarse[0][:2] and full[-1][:2] == coarse[-1][:2]  # endpoints
    assert len(coarse) < len(full)


def test_supercell_geometry():
    assert vecpack.CELL_COLS == 45
    assert vecpack.CELL_ROWS == 22
    # a coordinate maps into the expected cell
    ci = vecpack.cell_index(0, 0)
    lat0, lon0, lat1, lon1 = vecpack.cell_bounds(0, 0)
    assert (lat0, lon0) == (-86, -180)


def _run():
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for fn in fns:
        fn()
        print(f"  ok {fn.__name__}")
    print("all vector VW tests passed")


if __name__ == "__main__":
    _run()
