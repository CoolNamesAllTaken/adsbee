"""Binary packing for terrain .map tiles.

The struct layouts here MUST stay in lock-step with
firmware/adsbee_1090/esp/main/peripherals/terrain/terrain_tile.hh. All fields are
little-endian, matching the firmware's direct-memcpy parse.

TileHeader layout (packed, 74 bytes), field order identical to terrain_tile.hh:
    uint32 magic
    uint16 version
    uint16 flags
    int32  tile_lat0_e6
    int32  tile_lon0_e6
    uint16 tile_span_e3
    uint16 elev_grid_w
    uint16 elev_grid_h
    int16  elev_base_m
    uint8  elev_step_m
    uint8  elev_bytes_per_sample
    uint32 elev_offset
    uint32 elev_len
    uint32 elev_raw_len
    uint32 water_offset
    uint32 water_len
    uint16 water_count
    uint32 road_offset
    uint32 road_len
    uint16 road_count
    uint16 header_crc16
    uint16 payload_crc16
"""
import struct

# ---- Format constants (mirror terrain_tile.hh) ----------------------------
TILE_MAGIC = 0x4C495454  # 'TTIL' little-endian
TILE_FORMAT_VERSION = 2  # v2 adds the water-mask layer; grid is 128

FLAG_ELEV_COMPRESSED = 1 << 0
FLAG_ELEV_16BIT = 1 << 1
FLAG_VEC_DELTA = 1 << 2

ELEV_VOID_CODE = 0xFF
ELEV_GRID_DIM = 128

VEC_COASTLINE = 0
VEC_LAKE = 1
VEC_RIVER = 2
VEC_ROAD_MAJOR = 3
VEC_ROAD_SECONDARY = 4
VEC_CITY_POINT = 5

VEC_FLAG_CLOSED = 1 << 0
VEC_FLAG_HAS_NAME = 1 << 1

# Header: everything up to (not including) header_crc16 / payload_crc16, then the
# two CRC fields. We build the header in two parts so the header CRC covers only
# the leading bytes (matching terrain_tile.hh: "over the header up to this field").
# v2 adds the water-mask fields (water_mask_w/h/offset/len) after road_count.
_HDR_BODY_FMT = "<IHHiiHHHhBBIIIIIHIIH" + "HHII"  # ...road_count + water_mask w,h,offset,len
_HDR_TAIL_FMT = "<HH"                             # header_crc16, payload_crc16
HEADER_SIZE = struct.calcsize(_HDR_BODY_FMT) + struct.calcsize(_HDR_TAIL_FMT)

VEC_RECORD_HDR_FMT = "<BBH"   # feature_type, flags, num_points
VEC_POINT_FMT = "<HH"         # u, v


def crc16(data: bytes) -> int:
    """Replicates firmware CalculateCRC16 (CRC-16/CCITT-FALSE, init 0xFFFF,
    poly 0x1021) with the firmware's final byte-swap."""
    crc = 0xFFFF
    for b in data:
        x = ((crc >> 8) ^ b) & 0xFF
        x ^= x >> 4
        crc = ((crc << 8) ^ (x << 12) ^ (x << 5) ^ x) & 0xFFFF
    # firmware returns swap16(crc)
    return ((crc << 8) | (crc >> 8)) & 0xFFFF


def pack_vec_record(feature_type, points, closed=False, name=None):
    """points: list of (u, v) uint16 tile-local coords. name: optional str (cities)."""
    flags = 0
    if closed:
        flags |= VEC_FLAG_CLOSED
    name_bytes = b""
    if name is not None:
        flags |= VEC_FLAG_HAS_NAME
        nb = name.encode("ascii", "replace")[:255]
        name_bytes = struct.pack("<B", len(nb)) + nb
    out = struct.pack(VEC_RECORD_HDR_FMT, feature_type, flags, len(points))
    out += name_bytes
    for (u, v) in points:
        out += struct.pack(VEC_POINT_FMT, u & 0xFFFF, v & 0xFFFF)
    return out


def pack_tile(tile_lat0_e6, tile_lon0_e6, tile_span_e3,
              elev_bytes, elev_grid_w, elev_grid_h,
              elev_base_m, elev_step_m, elev_bytes_per_sample,
              water_records, water_count,
              road_records, road_count,
              water_mask_bytes=b"", water_mask_w=0, water_mask_h=0,
              flags=0, elev_raw_len=None):
    """Assemble a full tile file (header + layer blocks) as bytes.

    Layer order after the header: elevation, water vectors, road/city vectors,
    water mask (1-bit). elev_bytes / *_records / water_mask_bytes are raw bytes.
    """
    if elev_raw_len is None:
        elev_raw_len = len(elev_bytes)

    elev_offset = HEADER_SIZE
    water_offset = elev_offset + len(elev_bytes)
    road_offset = water_offset + len(water_records)
    water_mask_offset = road_offset + len(road_records)

    payload = elev_bytes + water_records + road_records + water_mask_bytes
    payload_crc = crc16(payload) if payload else 0

    body = struct.pack(
        _HDR_BODY_FMT,
        TILE_MAGIC,
        TILE_FORMAT_VERSION,
        flags,
        tile_lat0_e6,
        tile_lon0_e6,
        tile_span_e3,
        elev_grid_w,
        elev_grid_h,
        elev_base_m,
        elev_step_m,
        elev_bytes_per_sample,
        elev_offset,
        len(elev_bytes),
        elev_raw_len,
        water_offset,
        len(water_records),
        water_count,
        road_offset,
        len(road_records),
        road_count,
        water_mask_w,
        water_mask_h,
        water_mask_offset if water_mask_bytes else 0,
        len(water_mask_bytes),
    )
    header_crc = crc16(body)
    tail = struct.pack(_HDR_TAIL_FMT, header_crc, payload_crc)
    return body + tail + payload


def unpack_header(buf: bytes):
    """Decode a TileHeader from the start of buf. Returns a dict + validates
    magic/version/header_crc. Used by the round-trip test."""
    body_size = struct.calcsize(_HDR_BODY_FMT)
    fields = struct.unpack(_HDR_BODY_FMT, buf[:body_size])
    header_crc, payload_crc = struct.unpack(_HDR_TAIL_FMT, buf[body_size:HEADER_SIZE])
    keys = [
        "magic", "version", "flags", "tile_lat0_e6", "tile_lon0_e6", "tile_span_e3",
        "elev_grid_w", "elev_grid_h", "elev_base_m", "elev_step_m", "elev_bytes_per_sample",
        "elev_offset", "elev_len", "elev_raw_len", "water_offset", "water_len", "water_count",
        "road_offset", "road_len", "road_count",
        "water_mask_w", "water_mask_h", "water_mask_offset", "water_mask_len",
    ]
    hdr = dict(zip(keys, fields))
    hdr["header_crc16"] = header_crc
    hdr["payload_crc16"] = payload_crc
    hdr["_header_crc_ok"] = (crc16(buf[:body_size]) == header_crc)
    hdr["_magic_ok"] = (hdr["magic"] == TILE_MAGIC)
    hdr["_version_ok"] = (hdr["version"] == TILE_FORMAT_VERSION)
    return hdr
