"""Vector layer for `world.map`: importance-ordered, super-cell-indexed features.

Unlike the old per-1-degree-tile clipping (which cut every polyline at each tile
edge), features here are stored WHOLE within coarse 8-degree super-cells, clipped
only at the super-cell boundary. Coordinates are super-cell-local fixed point
(u,v in 0..65535 over the 8-degree cell ~= 0.7 m/unit), so a coastline crossing a
1-degree line is one unbroken polyline -> no seams from tiling.

Each polyline's vertices are stored sorted by descending Visvalingam-Whyatt
importance (see vecsimplify), each carrying its original sequence index, so the
device reads a threshold prefix and re-sorts by seq to draw a valid simplified
line at any zoom. Importance is log-quantized to 8 bits.

A super-cell index (grid of 8-degree cells) lets the device open only the cells
overlapping the view, so far zoom touches few cells. Cells are stored coarsest-
feature-first is unnecessary here because importance thresholding handles detail;
the index just bounds *which* cells to read.

Layout appended at the archive's vec_index_offset:
  [VecIndexHeader]
  [VecCellEntry[num_cells]]      (offset+len per super-cell; 0 = empty)
  [per-cell: VecRecordV3 records back to back]
"""
import struct

import numpy as np

from . import mapfmt
from . import vecsimplify
from .vectors import NE_THEMES, ROAD_MAX_SCALERANK

# Super-cell grid over the -86..+86 lat band, full lon. 8-degree cells.
SUPERCELL_DEG = 8
CELL_COLS = 360 // SUPERCELL_DEG            # 45
CELL_ROWS = (2 * 86 + SUPERCELL_DEG - 1) // SUPERCELL_DEG  # ceil(172/8) = 22
CELL_LAT0 = -86
CELL_LON0 = -180

# feature types (match pack.py's VEC_* so the renderer enum is stable)
VEC_COASTLINE = 0
VEC_LAKE = 1
VEC_RIVER = 2
VEC_ROAD_MAJOR = 3
VEC_CITY_POINT = 5

VEC_FLAG_CLOSED = 1 << 0
VEC_FLAG_IMPORTANCE_SORTED = 1 << 1

# VecIndexHeader: magic, version, supercell_deg, cell_cols, cell_rows,
#   cell_lat0_e6, cell_lon0_e6, num_records(u32), header_crc16
_VEC_IDX_FMT = "<IHHHHiiIH"
VEC_INDEX_HEADER_SIZE = struct.calcsize(_VEC_IDX_FMT)
# VecCellEntry: offset(u32 from archive start), len(u32), num_records(u16), pad(u16)
_VEC_CELL_FMT = "<IIHH"
VEC_CELL_ENTRY_SIZE = struct.calcsize(_VEC_CELL_FMT)
VEC_INDEX_MAGIC = 0x43455654  # 'TVEC'

# importance quantization: log-scale to 8 bits. Endpoints -> 255.
_IMP_MAX = 254


def quantize_importance(imp_values):
    """Map VW effective areas -> uint8 (log scale). inf -> 255 (endpoints)."""
    out = []
    finite = [a for a in imp_values if a != float("inf") and a > 0]
    if finite:
        lo = np.log1p(min(finite))
        hi = np.log1p(max(finite))
        span = (hi - lo) or 1.0
    for a in imp_values:
        if a == float("inf"):
            out.append(255)
        elif a <= 0:
            out.append(0)
        else:
            q = int(round((np.log1p(a) - lo) / span * _IMP_MAX))
            out.append(max(0, min(_IMP_MAX, q)))
    return out


def cell_index(cell_row, cell_col):
    return cell_row * CELL_COLS + cell_col


def cell_bounds(cell_row, cell_col):
    lat0 = CELL_LAT0 + cell_row * SUPERCELL_DEG
    lon0 = CELL_LON0 + cell_col * SUPERCELL_DEG
    return lat0, lon0, lat0 + SUPERCELL_DEG, lon0 + SUPERCELL_DEG


def _to_uv(lon, lat, lon0, lat0):
    """Super-cell-local uint16. u across lon, v across lat (v grows north)."""
    u = int(round((lon - lon0) / SUPERCELL_DEG * 65535))
    v = int(round((lat - lat0) / SUPERCELL_DEG * 65535))
    return max(0, min(65535, u)), max(0, min(65535, v))


def pack_record(feature_type, uv_seq_imp, closed=False):
    """uv_seq_imp: list of (u, v, seq, importance_u8) already sorted by
    descending importance. Returns bytes: VecRecordHeaderV3 + VecPointV3[]."""
    flags = VEC_FLAG_IMPORTANCE_SORTED | (VEC_FLAG_CLOSED if closed else 0)
    # importance_hint: importance of the vertex at the 25th percentile of the
    # sorted list, a coarse seek aid (device can binary-search around it).
    n = len(uv_seq_imp)
    hint = uv_seq_imp[min(n - 1, n // 4)][3] if n else 0
    out = struct.pack(mapfmt._VEC_REC_FMT, feature_type, flags, n, hint)
    for (u, v, seq, imp) in uv_seq_imp:
        out += struct.pack(mapfmt._VEC_POINT_FMT, u, v, seq, imp, 0)
    return out


def encode_polyline(coords, lon0, lat0, feature_type, closed=False):
    """coords: list of (lon,lat) within one super-cell. Returns record bytes or
    None if <2 points. Computes VW importance in super-cell-local uv space so the
    area metric matches the coordinates the device thresholds against."""
    uv = [_to_uv(lon, lat, lon0, lat0) for (lon, lat) in coords]
    # dedupe consecutive identical uv (clip can produce them)
    dedup = [uv[0]]
    for p in uv[1:]:
        if p != dedup[-1]:
            dedup.append(p)
    if len(dedup) < 2:
        return None
    imp = vecsimplify.effective_areas(dedup)
    qimp = quantize_importance(imp)
    ordered = sorted(
        [(dedup[i][0], dedup[i][1], i, qimp[i]) for i in range(len(dedup))],
        key=lambda t: t[3], reverse=True)
    return pack_record(feature_type, ordered, closed=closed)


# ---- super-cell binning + archive integration -----------------------------
def _line_parts(geom):
    """Yield lists of (lon,lat) for each LineString in a (Multi)LineString /
    polygon boundary geometry."""
    if geom is None or geom.is_empty:
        return
    gt = geom.geom_type
    if gt == "LineString":
        yield list(geom.coords)
    elif gt == "MultiLineString":
        for p in geom.geoms:
            yield list(p.coords)
    elif gt == "Polygon":
        yield list(geom.exterior.coords)
        for r in geom.interiors:
            yield list(r.coords)
    elif gt == "MultiPolygon":
        for poly in geom.geoms:
            yield list(poly.exterior.coords)
            for r in poly.interiors:
                yield list(r.coords)


def build_vector_records(vec_sources):
    """Clip NE line/poly themes into super-cells and encode importance-ordered
    records. Returns {cell_index: [record_bytes, ...]}.

    vec_sources: a vectors.VectorSources (already loads coastline/lakes/rivers/
    roads/cities with spatial indexes)."""
    from shapely.geometry import box

    cells = {}   # cell_index -> list of record bytes

    themes = [
        ("coastline", VEC_COASTLINE, False),
        ("lakes", VEC_LAKE, True),
        ("rivers", VEC_RIVER, False),
        ("roads", VEC_ROAD_MAJOR, False),
    ]

    for cr in range(CELL_ROWS):
        for cc in range(CELL_COLS):
            lat0, lon0, lat1, lon1 = cell_bounds(cr, cc)
            if lat1 > 86:
                lat1 = 86
            cbox = box(lon0, lat0, lon1, lat1)
            recs = []
            for key, ftype, closed in themes:
                gdf = vec_sources.layers.get(key)
                if gdf is None or len(gdf) == 0:
                    continue
                hits = gdf.iloc[list(gdf.sindex.query(cbox, predicate="intersects"))]
                for geom in hits.geometry:
                    clipped = geom.intersection(cbox)
                    for part in _line_parts(clipped):
                        rec = encode_polyline(part, lon0, lat0, ftype, closed=closed)
                        if rec:
                            recs.append(rec)
            # city points (single-vertex records, importance=max)
            cities = vec_sources.layers.get("cities")
            if cities is not None and len(cities):
                chits = cities.iloc[list(cities.sindex.query(cbox, predicate="intersects"))]
                for _, row in chits.iterrows():
                    pt = row.geometry
                    if pt is None or pt.is_empty or pt.geom_type != "Point":
                        continue
                    u, v = _to_uv(pt.x, pt.y, lon0, lat0)
                    recs.append(pack_record(VEC_CITY_POINT, [(u, v, 0, 255)]))
            if recs:
                cells[cell_index(cr, cc)] = recs
    return cells


def pack_index_header(num_records, dir_crc_placeholder=0):
    body = struct.pack(_VEC_IDX_FMT, VEC_INDEX_MAGIC, 1, SUPERCELL_DEG,
                       CELL_COLS, CELL_ROWS, CELL_LAT0 * 1_000_000,
                       CELL_LON0 * 1_000_000, num_records, 0)
    crc = mapfmt.crc16(body[:-2])
    return body[:-2] + struct.pack("<H", crc)


def unpack_index_header(buf):
    (magic, ver, sdeg, cols, rows, lat0, lon0, nrec, crc) = struct.unpack(
        _VEC_IDX_FMT, buf[:VEC_INDEX_HEADER_SIZE])
    return dict(magic=magic, version=ver, supercell_deg=sdeg, cell_cols=cols,
                cell_rows=rows, cell_lat0_e6=lat0, cell_lon0_e6=lon0,
                num_records=nrec, header_crc16=crc,
                _magic_ok=(magic == VEC_INDEX_MAGIC))


def write_vectors(f, start_offset, cells):
    """Append the vector index + records at start_offset. Returns end offset.

    Layout: [VecIndexHeader][VecCellEntry * num_cells][records...]."""
    num_cells = CELL_ROWS * CELL_COLS
    num_records = sum(len(v) for v in cells.values())

    index_pos = start_offset
    entries_pos = index_pos + VEC_INDEX_HEADER_SIZE
    records_pos = entries_pos + num_cells * VEC_CELL_ENTRY_SIZE

    # write records, remember per-cell (offset,len,count)
    f.seek(records_pos)
    cell_meta = {}
    cursor = records_pos
    for ci in range(num_cells):
        recs = cells.get(ci)
        if not recs:
            cell_meta[ci] = (0, 0, 0)
            continue
        blob = b"".join(recs)
        f.write(blob)
        cell_meta[ci] = (cursor, len(blob), len(recs))
        cursor += len(blob)
    end = f.tell()

    # entries
    f.seek(entries_pos)
    for ci in range(num_cells):
        off, ln, cnt = cell_meta[ci]
        f.write(struct.pack(_VEC_CELL_FMT, off, ln, cnt, 0))

    # header
    f.seek(index_pos)
    f.write(pack_index_header(num_records))
    f.seek(end)
    return end, num_records
