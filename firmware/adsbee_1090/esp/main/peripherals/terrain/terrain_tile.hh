#pragma once

#include <cstdint>

// On-disk format for terrain map tiles stored on the microSD card at
// /sd/tiles/<RRR>/<CCC>.map (RRR = tile row hex, CCC = tile col hex).
//
// This header is the SINGLE SOURCE OF TRUTH for the tile binary layout, shared
// between the host tiler (firmware/scripts/terrain_tiler, which packs the same
// fields via Python struct) and the on-device loader (TerrainLoader). Keep the
// Python packer's struct format strings in lock-step with the structs below.
//
// All multi-byte fields are LITTLE-ENDIAN (host and ESP32-S3 are both LE, so the
// device parses by direct memcpy/struct overlay with no byte-swapping — same
// assumption as common/settings/settings.hh). Bump kTileFormatVersion whenever
// any on-disk layout changes.
//
// A tile packs three layers after the header, in this order:
//   [elevation grid][water vector records][road/city vector records]
// Each layer's byte offset (from file start) and length live in the header, so
// layers can be seeked independently and the format can grow behind `version`.

namespace winglet_terrain {

// ---- Tile grid geometry (whole world, fixed lat/lon grid) -----------------
// 1x1 degree tiles, latitude clamped to [-86, +86] (poles omitted). Every tile
// in the grid exists on the card (ocean tiles carry a flat/zero elevation grid
// and no vector records), so the loader builds paths directly with no manifest.
constexpr int kTileStepDeg = 1;
constexpr int kTileLatMinDeg = -86;
constexpr int kTileLatMaxDeg = 86;
constexpr int kNumTileRows = (kTileLatMaxDeg - kTileLatMinDeg) / kTileStepDeg;  // 172
constexpr int kNumTileCols = 360 / kTileStepDeg;                               // 360

// Terrain is only drawn/loaded at close zoom, where the small (4-tile) overlap
// set can actually cover the screen. Above this map range (NM) the visible area
// spans far more than 4 one-degree tiles, so terrain is skipped (rings/traffic
// only). Shared by the loader (skip loading) and the renderer (skip drawing).
constexpr float kTerrainMaxRangeNm = 40.0f;

// ---- Format identity ------------------------------------------------------
// 'TTIL' little-endian ("TTIL" bytes T,T,I,L -> 0x4C495454).
constexpr uint32_t kTileMagic = 0x4C495454u;
constexpr uint16_t kTileFormatVersion = 2;  // v2 adds the water-mask layer; grid is 128

// ---- Header flags ---------------------------------------------------------
enum TileFlags : uint16_t {
    kTileFlagElevCompressed = 1 << 0,  // elevation block is zlib-compressed (reserved; unused in P2)
    kTileFlagElev16Bit = 1 << 1,       // elevation samples are int16 (else 8-bit quantized codes)
    kTileFlagVecDelta = 1 << 2,        // vector vertices are delta-encoded (reserved; unused in P2)
};

// ---- Elevation quantization ------------------------------------------------
// 8-bit path (default): sample_m = elev_base_m + code * elev_step_m, where
// code is a uint8 in [0, 254]. code == kElevVoidCode marks no-data (skip).
constexpr uint8_t kElevVoidCode = 0xFF;
constexpr int kElevGridDim = 128;  // default samples per side (128x128 ~= 868 m/sample at 1 deg)

// ---- Vector feature types --------------------------------------------------
enum VecFeatureType : uint8_t {
    kVecCoastline = 0,
    kVecLake = 1,
    kVecRiver = 2,
    kVecRoadMajor = 3,
    kVecRoadSecondary = 4,
    kVecCityPoint = 5,
};

// ---- Vector record flags ---------------------------------------------------
enum VecRecordFlags : uint8_t {
    kVecFlagClosed = 1 << 0,   // polygon ring (closed) rather than an open polyline
    kVecFlagHasName = 1 << 1,  // record is followed by a name (cities): uint8 len + chars
};

// ---- Per-tile file header --------------------------------------------------
struct __attribute__((packed)) TileHeader {
    uint32_t magic;    // kTileMagic
    uint16_t version;  // kTileFormatVersion (first-checked after magic)
    uint16_t flags;    // TileFlags bitmask

    // Tile SW (south-west) corner, in 1e-6 degrees (integer, LE).
    int32_t tile_lat0_e6;
    int32_t tile_lon0_e6;
    uint16_t tile_span_e3;  // tile size in 1e-3 deg (=1000 for 1 degree)

    // Elevation layer.
    uint16_t elev_grid_w;           // samples across (e.g. 256)
    uint16_t elev_grid_h;           // samples down
    int16_t elev_base_m;            // quantization base (meters)
    uint8_t elev_step_m;            // quantization step (meters, e.g. 40)
    uint8_t elev_bytes_per_sample;  // 1 (quantized) or 2 (int16, if kTileFlagElev16Bit)
    uint32_t elev_offset;           // byte offset from file start to elevation block
    uint32_t elev_len;              // stored length (compressed if flagged, else raw)
    uint32_t elev_raw_len;          // uncompressed length (for decompressor sizing)

    // Vector layers (water; roads+cities).
    uint32_t water_offset;
    uint32_t water_len;
    uint16_t water_count;
    uint32_t road_offset;
    uint32_t road_len;
    uint16_t road_count;

    // Water mask layer (v2+): 1 bit/pixel, 1 = water, at elevation-grid resolution.
    // Row-major, north->south rows, west->east; ceil(w/8) bytes/row, MSB-first.
    // Drives the interior water texture fill; the vector records still supply the
    // solid shoreline strokes. water_mask_len == 0 means "no mask" (v1 tiles).
    uint16_t water_mask_w;
    uint16_t water_mask_h;
    uint32_t water_mask_offset;
    uint32_t water_mask_len;

    // Integrity.
    uint16_t header_crc16;   // CalculateCRC16 over the header up to (not incl.) this field
    uint16_t payload_crc16;  // CalculateCRC16 over all layer bytes; 0 = not present
};

// ---- Vector record header (streamable; one at a time) ----------------------
// Followed by (optionally) a name (uint8 name_len + name_len chars) when
// kVecFlagHasName is set, then num_points * VecPoint. Coordinates are tile-local
// fixed-point: u,v in [0, 65535] spanning the tile's 1-degree extent.
struct __attribute__((packed)) VecRecordHeader {
    uint8_t feature_type;  // VecFeatureType
    uint8_t flags;         // VecRecordFlags
    uint16_t num_points;   // vertex count (1 for a city point)
};

struct __attribute__((packed)) VecPoint {
    uint16_t u;  // (lon - tile_lon0) / tile_span * 65535
    uint16_t v;  // (lat - tile_lat0) / tile_span * 65535
};

}  // namespace winglet_terrain
