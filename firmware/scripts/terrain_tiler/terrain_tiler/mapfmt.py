"""World terrain archive format (`world.map`) — single-file, seekable, multi-LOD.

Replaces the 61,920 per-tile `.map` files with ONE archive holding a global
coarse-to-fine elevation pyramid plus importance-ordered vectors. The device
seeks a block directory and reads only the blocks overlapping the view at the
level its zoom needs — arbitrary zoom (2..2000 NM) from one continuous pyramid,
no baked LOD presets.

This module is the single source of truth for the on-disk layout. Every packed
struct below has an explicit `*_SIZE` the future C `static_assert(sizeof==N)`
must match (mirrored in terrain_tile.hh in the later firmware pass).

Block codec (chosen by prototype #1 bake-off on real ETOPO 8-bit codes):
  per block, take the SMALLER of {plain raw-DEFLATE, PNG-row-predictor + DEFLATE};
  uniform blocks collapse to a 1-byte fill (constant-block dedup). Decode is
  integer-only (ROM `tinfl` inflate + trivial predictor reversal) — no float.

All fields little-endian; CRC-16/CCITT-FALSE+swap16 shared with the firmware
(`crc16`, identical to buffer_utils.cpp CalculateCRC16).
"""
import struct
import zlib

import numpy as np

from .pack import crc16  # reuse the firmware-matching CRC

# ---- format identity -------------------------------------------------------
MAP_MAGIC = 0x504D4154  # 'TMAP' little-endian
MAP_FORMAT_VERSION = 1

# elevation quantization (mirrors dem.quantize_grid)
ELEV_STEP_M = 40
# Reserved elevation codes. 0xFF = void (no-data), 0xFE = water. The host burns
# ELEV_WATER_CODE into the L0 lattice wherever Natural Earth ocean/lakes/rivers
# cover the sample (see pyramid.build_l0_water); it decimates through every
# pyramid level for free. Land codes therefore occupy [0, 253]. The device draws
# water==0xFE as a flat grid-fill (dots + shoreline), so losing the true
# elevation under water is intentional. Mirrored on-device as kElevWaterCode.
ELEV_VOID_CODE = 0xFF
ELEV_WATER_CODE = 0xFE

# geometry defaults (grid-registered pyramid; see plan)
FINEST_SAMPLES_PER_DEG = 128
BLOCK_DIM = 64                 # samples per block side
BLOCK_STRIDE = BLOCK_DIM - 1   # 63: adjacent blocks share their boundary row/col
WORLD_LAT0_E6 = -86_000_000
WORLD_LON0_E6 = -180_000_000

# block codecs (BlockDirEntry.codec)
BLOCK_CONSTANT = 0   # no payload; fill code in dir entry
BLOCK_DEFLATE = 1    # raw DEFLATE of the 8-bit codes
BLOCK_PRED_DEFLATE = 2  # PNG-row-predictor then raw DEFLATE

# ---- frozen struct formats + sizes (pin the C static_asserts) --------------
# PyramidHeader: magic,version,num_levels,block_dim,block_stride,
#   finest_samples_per_deg,elev_bytes_per_sample,flags,
#   world_lat0_e6,world_lon0_e6,world_span_lat_e3,world_span_lon_e3,
#   vec_index_offset(u64), provenance_offset(u32), provenance_len(u32),
#   dir_crc16, header_crc16
_PYR_BODY_FMT = "<IHHHHHBBiiIIQII"
PYR_HEADER_BODY_SIZE = struct.calcsize(_PYR_BODY_FMT)   # 48
_PYR_TAIL_FMT = "<HH"
PYR_HEADER_SIZE = PYR_HEADER_BODY_SIZE + struct.calcsize(_PYR_TAIL_FMT)  # 52

# LevelDesc: samples_w,samples_h,blocks_x,blocks_y(u32), dir_offset(u64),
#   nm_per_sample_e4(u32), elev_base_m(i16), elev_step_m(u8), pad(u8)
_LEVEL_FMT = "<IIIIQIhBB"
LEVEL_DESC_SIZE = struct.calcsize(_LEVEL_FMT)   # expect 32

# BlockDirEntry: offset(u32), stored_len(u32), raw_len(u16), codec(u8), fill(u8)
_BLOCK_DIR_FMT = "<IIHBB"
BLOCK_DIR_ENTRY_SIZE = struct.calcsize(_BLOCK_DIR_FMT)   # expect 12

# Vector structs (frozen now, consumed by vectors.py + later firmware).
# VecRecordHeaderV3: feature_type(u8), flags(u8), num_points(u16), importance_hint(u16)
_VEC_REC_FMT = "<BBHH"
VEC_RECORD_HDR_SIZE = struct.calcsize(_VEC_REC_FMT)   # expect 6
# VecPointV3: u(u16), v(u16), seq(u16), importance(u8), pad(u8)
_VEC_POINT_FMT = "<HHHBB"
VEC_POINT_SIZE = struct.calcsize(_VEC_POINT_FMT)   # expect 8

# Expected sizes, asserted at import so a struct typo fails loudly and the
# firmware pass can copy these numbers verbatim into static_asserts.
_EXPECTED_SIZES = {
    "PYR_HEADER_SIZE": (PYR_HEADER_SIZE, 52),
    "LEVEL_DESC_SIZE": (LEVEL_DESC_SIZE, 32),
    "BLOCK_DIR_ENTRY_SIZE": (BLOCK_DIR_ENTRY_SIZE, 12),
    "VEC_RECORD_HDR_SIZE": (VEC_RECORD_HDR_SIZE, 6),
    "VEC_POINT_SIZE": (VEC_POINT_SIZE, 8),
}
for _name, (_got, _want) in _EXPECTED_SIZES.items():
    assert _got == _want, f"{_name} = {_got}, expected {_want} (struct drift!)"


# ---- row predictor (PNG-style) --------------------------------------------
# Encoder picks, per row, the filter (none/sub/up/avg/paeth) minimizing sum of
# abs residuals; decoder reverses. Residuals are mod-256. Integer-only both ways.
_FILT_NONE, _FILT_SUB, _FILT_UP, _FILT_AVG, _FILT_PAETH = range(5)


def _paeth(a, b, c):
    p = a + b - c
    pa, pb, pc = np.abs(p - a), np.abs(p - b), np.abs(p - c)
    return np.where((pa <= pb) & (pa <= pc), a, np.where(pb <= pc, b, c))


def predictor_filter(block):
    """block: (h,w) uint8. Returns filtered bytes: per row [filter_type][residuals]."""
    a = block.astype(np.int16)
    h, w = a.shape
    out = bytearray()
    for y in range(h):
        row = a[y]
        up = a[y - 1] if y > 0 else np.zeros(w, np.int16)
        left = np.concatenate([[0], row[:-1]])
        upleft = np.concatenate([[0], up[:-1]])
        cands = {
            _FILT_NONE: row,
            _FILT_SUB: row - left,
            _FILT_UP: row - up,
            _FILT_AVG: row - ((left + up) // 2),
            _FILT_PAETH: row - _paeth(left, up, upleft),
        }
        best = min(cands, key=lambda k: int(np.abs(cands[k]).sum()))
        out.append(best)
        out += bytes((cands[best] & 0xFF).astype(np.uint8).tobytes())
    return bytes(out)


def predictor_unfilter(data, h, w):
    """Reverse predictor_filter -> (h,w) uint8 array. This is the reference for
    the device-side decode (inflate first, then this)."""
    out = np.zeros((h, w), np.int16)
    pos = 0
    for y in range(h):
        ft = data[pos]; pos += 1
        resid = np.frombuffer(data[pos:pos + w], dtype=np.uint8).astype(np.int16)
        pos += w
        up = out[y - 1] if y > 0 else np.zeros(w, np.int16)
        row = np.zeros(w, np.int16)
        if ft == _FILT_NONE:
            row = resid.copy()
        elif ft == _FILT_UP:
            row = (resid + up) & 0xFF
        else:
            # sub/avg/paeth need left neighbor -> sequential
            upleft = 0
            for x in range(w):
                left = row[x - 1] if x > 0 else 0
                u = up[x]
                ul = up[x - 1] if x > 0 else 0
                if ft == _FILT_SUB:
                    pred = left
                elif ft == _FILT_AVG:
                    pred = (left + u) // 2
                else:  # paeth
                    p = left + u - ul
                    pa, pb, pc = abs(p - left), abs(p - u), abs(p - ul)
                    pred = left if (pa <= pb and pa <= pc) else (u if pb <= pc else ul)
                row[x] = (resid[x] + pred) & 0xFF
        out[y] = row & 0xFF
    return out.astype(np.uint8)


def _deflate(data):
    c = zlib.compressobj(9, zlib.DEFLATED, -15)
    return c.compress(data) + c.flush()


def _inflate(data):
    d = zlib.decompressobj(-15)
    return d.decompress(data) + d.flush()


# ---- block codec -----------------------------------------------------------
def encode_block(block):
    """block: (BLOCK_DIM,BLOCK_DIM) uint8. Returns (codec, stored_bytes, fill).

    Picks the smallest of {constant, plain deflate, predictor+deflate}. For a
    constant block, stored_bytes is empty and fill holds the single code."""
    vals = block.reshape(-1)
    vmin, vmax = int(vals.min()), int(vals.max())
    if vmin == vmax:
        return BLOCK_CONSTANT, b"", vmin

    raw = block.tobytes()
    plain = _deflate(raw)
    pred = _deflate(predictor_filter(block))
    if len(pred) < len(plain):
        return BLOCK_PRED_DEFLATE, pred, 0
    return BLOCK_DEFLATE, plain, 0


def decode_block(codec, stored, fill, h=BLOCK_DIM, w=BLOCK_DIM):
    """Reference decoder (stands in for the ESP32). Integer-only path."""
    if codec == BLOCK_CONSTANT:
        return np.full((h, w), fill, np.uint8)
    if codec == BLOCK_DEFLATE:
        return np.frombuffer(_inflate(stored), np.uint8).reshape(h, w).copy()
    if codec == BLOCK_PRED_DEFLATE:
        return predictor_unfilter(_inflate(stored), h, w)
    raise ValueError(f"unknown block codec {codec}")


# ---- directory + header serialization -------------------------------------
def pack_block_dir_entry(offset, stored_len, raw_len, codec, fill):
    return struct.pack(_BLOCK_DIR_FMT, offset, stored_len, raw_len, codec, fill)


def unpack_block_dir_entry(buf):
    offset, stored_len, raw_len, codec, fill = struct.unpack(_BLOCK_DIR_FMT, buf)
    return dict(offset=offset, stored_len=stored_len, raw_len=raw_len,
                codec=codec, fill=fill)


def pack_level_desc(samples_w, samples_h, blocks_x, blocks_y, dir_offset,
                    nm_per_sample, elev_base_m, elev_step_m=ELEV_STEP_M):
    return struct.pack(_LEVEL_FMT, samples_w, samples_h, blocks_x, blocks_y,
                       dir_offset, int(round(nm_per_sample * 1e4)),
                       elev_base_m, elev_step_m, 0)


def unpack_level_desc(buf):
    (sw, sh, bx, by, doff, nmps_e4, base, step, _pad) = struct.unpack(_LEVEL_FMT, buf)
    return dict(samples_w=sw, samples_h=sh, blocks_x=bx, blocks_y=by,
                dir_offset=doff, nm_per_sample=nmps_e4 / 1e4,
                elev_base_m=base, elev_step_m=step)


def pack_pyramid_header(num_levels, world_span_lat_e3, world_span_lon_e3,
                        vec_index_offset, provenance_offset, provenance_len,
                        dir_crc16, flags=0, elev_bytes_per_sample=1):
    body = struct.pack(
        _PYR_BODY_FMT,
        MAP_MAGIC, MAP_FORMAT_VERSION, num_levels, BLOCK_DIM, BLOCK_STRIDE,
        FINEST_SAMPLES_PER_DEG, elev_bytes_per_sample, flags,
        WORLD_LAT0_E6, WORLD_LON0_E6, world_span_lat_e3, world_span_lon_e3,
        vec_index_offset, provenance_offset, provenance_len,
    )
    header_crc = crc16(body)
    return body + struct.pack(_PYR_TAIL_FMT, dir_crc16, header_crc)


def unpack_pyramid_header(buf):
    fields = struct.unpack(_PYR_BODY_FMT, buf[:PYR_HEADER_BODY_SIZE])
    dir_crc, header_crc = struct.unpack(
        _PYR_TAIL_FMT, buf[PYR_HEADER_BODY_SIZE:PYR_HEADER_SIZE])
    keys = ["magic", "version", "num_levels", "block_dim", "block_stride",
            "finest_samples_per_deg", "elev_bytes_per_sample", "flags",
            "world_lat0_e6", "world_lon0_e6", "world_span_lat_e3", "world_span_lon_e3",
            "vec_index_offset", "provenance_offset", "provenance_len"]
    hdr = dict(zip(keys, fields))
    hdr["dir_crc16"] = dir_crc
    hdr["header_crc16"] = header_crc
    hdr["_magic_ok"] = hdr["magic"] == MAP_MAGIC
    hdr["_header_crc_ok"] = crc16(buf[:PYR_HEADER_BODY_SIZE]) == header_crc
    return hdr


# ---- level geometry helpers (grid-registered, n*2^L + 1) -------------------
def level_dims(level, num_levels):
    """Return (samples_w, samples_h) for pyramid level. L0 = finest. Dimensions
    are n*2^L + 1 so a coarse sample coincides exactly with a fine one (no
    half-pixel drift between levels)."""
    span_lon = 360
    span_lat = (WORLD_LAT0_E6 * -2) // 1_000_000  # 172 (band -86..+86)
    base_w = span_lon * FINEST_SAMPLES_PER_DEG
    base_h = span_lat * FINEST_SAMPLES_PER_DEG
    factor = 1 << level
    w = base_w // factor + 1
    h = base_h // factor + 1
    return w, h


def blocks_across(n_samples):
    """Number of shared-edge blocks (stride BLOCK_STRIDE) to cover n_samples."""
    if n_samples <= BLOCK_DIM:
        return 1
    return (n_samples - BLOCK_DIM + BLOCK_STRIDE - 1) // BLOCK_STRIDE + 1


def nm_per_sample(level):
    """Great-circle NM per sample at the equator for this level."""
    deg_per_sample = (1.0 / FINEST_SAMPLES_PER_DEG) * (1 << level)
    return deg_per_sample * 60.0  # 1 deg latitude = 60 NM
