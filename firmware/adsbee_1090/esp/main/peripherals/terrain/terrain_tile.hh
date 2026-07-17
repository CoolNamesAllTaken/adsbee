#pragma once

#include <cstdint>

// On-disk format for the single-file world terrain archive stored on the microSD
// card at /sd/world.map.
//
// This header is the SINGLE SOURCE OF TRUTH for the archive binary layout on the
// device side, and it is kept byte-for-byte in lock-step with the host packer
// (firmware/scripts/terrain_tiler/terrain_tiler/mapfmt.py + vecpack.py). The
// static_assert(sizeof(...)==N) below pin the frozen sizes; if the host struct
// formats change, these fail loudly at compile time.
//
// Replaces the legacy 61,920-file per-tile set (/sd/tiles/<RRR>/<CCC>.map). The
// archive is ONE seekable file: a global coarse-to-fine elevation pyramid plus
// importance-ordered vectors. The device seeks a per-level block directory and
// reads only the blocks overlapping the view at the level its zoom needs, so
// arbitrary zoom (2..2000 NM) is served from one continuous pyramid — no baked
// zoom presets, no per-tile files.
//
// All multi-byte fields are LITTLE-ENDIAN (host and ESP32-S3 are both LE, so the
// device parses by direct struct overlay with no byte-swapping). Every struct is
// __attribute__((packed)); PyramidHeader in particular REQUIRES it, or the u64
// vec_index_offset would 8-byte-align and pad the struct past 52 bytes.
//
// File layout:
//   [PyramidHeader 52B]
//   [LevelDesc[num_levels] * 32B]         fixed table, right after the header
//   [provenance JSON blob]                opaque to the device (source versions)
//   [per level: BlockDirEntry[blocks_x*blocks_y] * 12B, then block payloads]
//   [vector index: VecIndexHeader + VecCellEntry[cols*rows] + records]

namespace winglet_terrain {

// ---- Format identity ------------------------------------------------------
constexpr uint32_t kMapMagic = 0x504D4154u;      // 'TMAP' little-endian
constexpr uint16_t kMapFormatVersion = 1;
constexpr uint32_t kVecIndexMagic = 0x43455654u;  // 'TVEC' little-endian

// ---- Pyramid / block geometry (grid-registered, north-up) -----------------
// Each level is one global equirectangular raster of samples_w x samples_h,
// dims n*2^L+1 so coarse samples coincide exactly with fine ones (no drift).
// Tiled into shared-edge 64x64 blocks with STRIDE 63: adjacent blocks duplicate
// their shared boundary row/col, so a feature crossing a block edge is
// continuous. Block (bx,by) covers global samples
//   [bx*63 .. bx*63+63] x [by*63 .. by*63+63].
constexpr int kBlockDim = 64;
constexpr int kBlockStride = 63;
constexpr int kBlockRawLen = kBlockDim * kBlockDim;  // 4096 decoded codes/block
constexpr int kFinestSamplesPerDeg = 128;
constexpr int32_t kWorldLat0E6 = -86000000;   // world band is lat [-86, +86]
constexpr int32_t kWorldLon0E6 = -180000000;  // ... lon [-180, +180]

// ---- Elevation quantization -----------------------------------------------
// sample_m = elev_base_m + code * elev_step_m. Two reserved codes above the
// land range [0, 253]: 0xFF = void (no-data, skip), 0xFE = water (drawn as a
// flat grid-fill; the host burns it from Natural Earth ocean/lakes/rivers). The
// device cannot derive water from elevation because ocean and sea-level land
// both quantize to code 0, so this reserved code IS the water signal.
constexpr uint8_t kElevVoidCode = 0xFF;
constexpr uint8_t kElevWaterCode = 0xFE;

// ---- Block codec (BlockDirEntry.codec) ------------------------------------
enum BlockCodec : uint8_t {
    kCodecConstant = 0,     // no payload; the single fill code is in the entry
    kCodecDeflate = 1,      // raw DEFLATE of the 8-bit codes
    kCodecPredDeflate = 2,  // PNG-row-predictor then raw DEFLATE
};

// ---- Vector feature types (match vecpack.py) ------------------------------
enum VecFeatureType : uint8_t {
    kVecCoastline = 0,
    kVecLake = 1,
    kVecRiver = 2,
    kVecRoadMajor = 3,
    kVecRoadSecondary = 4,
    kVecCityPoint = 5,
};

// ---- Vector record flags --------------------------------------------------
enum VecRecordFlags : uint8_t {
    kVecFlagClosed = 1 << 0,            // polygon ring (closed) vs open polyline
    kVecFlagImportanceSorted = 1 << 1,  // points sorted by descending importance
};

// ---- Vector super-cell grid (vecpack.py) ----------------------------------
// Features live whole in 8x8-degree super-cells with cell-local uint16 (u,v);
// the device opens only the cells overlapping the view.
constexpr int kSupercellDeg = 8;
constexpr int kCellCols = 45;   // 360 / 8
constexpr int kCellRows = 22;   // ceil(172 / 8)
constexpr int32_t kCellLat0E6 = -86000000;
constexpr int32_t kCellLon0E6 = -180000000;

// ---- Archive header (once, at file start) ---------------------------------
struct __attribute__((packed)) PyramidHeader {
    uint32_t magic;                    // kMapMagic
    uint16_t version;                  // kMapFormatVersion
    uint16_t num_levels;               // pyramid level count (L0 = finest)
    uint16_t block_dim;                // = kBlockDim (64)
    uint16_t block_stride;             // = kBlockStride (63)
    uint16_t finest_samples_per_deg;   // = kFinestSamplesPerDeg (128)
    uint8_t elev_bytes_per_sample;     // = 1 (8-bit codes)
    uint8_t flags;
    int32_t world_lat0_e6;             // = kWorldLat0E6 (-86e6)
    int32_t world_lon0_e6;             // = kWorldLon0E6 (-180e6)
    uint32_t world_span_lat_e3;        // world lat span in 1e-3 deg (=172000)
    uint32_t world_span_lon_e3;        // world lon span in 1e-3 deg (=360000)
    uint64_t vec_index_offset;         // byte offset to the vector index section
    uint32_t provenance_offset;        // byte offset to the JSON provenance blob
    uint32_t provenance_len;           // provenance blob length (0 = none)
    uint16_t dir_crc16;                // CRC over all per-level block directories
    uint16_t header_crc16;             // CRC over the 48-byte body (up to here)
};
static_assert(sizeof(PyramidHeader) == 52, "PyramidHeader must be 52 bytes (mapfmt.py)");

// Per-level descriptor (fixed table right after the header). Fully self-
// describing so the device derives zoom->level at runtime (no baked presets).
struct __attribute__((packed)) LevelDesc {
    uint32_t samples_w;        // level raster width in samples
    uint32_t samples_h;        // level raster height in samples
    uint32_t blocks_x;         // shared-edge blocks across
    uint32_t blocks_y;         // shared-edge blocks down
    uint64_t dir_offset;       // byte offset to this level's BlockDirEntry table
    uint32_t nm_per_sample_e4;  // nm/sample at the equator, x1e4 (see NmPerSample)
    int16_t elev_base_m;       // quantization base (meters)
    uint8_t elev_step_m;       // quantization step (meters, e.g. 40)
    uint8_t pad;

    float NmPerSample() const { return nm_per_sample_e4 / 1e4f; }
};
static_assert(sizeof(LevelDesc) == 32, "LevelDesc must be 32 bytes (mapfmt.py)");

// One directory entry per block, indexed by*blocks_x+bx.
struct __attribute__((packed)) BlockDirEntry {
    uint32_t offset;      // byte offset (from archive start) to the payload
    uint32_t stored_len;  // stored payload length; 0 => constant block (no payload)
    uint16_t raw_len;     // decoded length (= kBlockRawLen, 4096)
    uint8_t codec;        // BlockCodec
    uint8_t fill;         // fill code when constant (else 0)
};
static_assert(sizeof(BlockDirEntry) == 12, "BlockDirEntry must be 12 bytes (mapfmt.py)");

// ---- Vector index ---------------------------------------------------------
struct __attribute__((packed)) VecIndexHeader {
    uint32_t magic;         // kVecIndexMagic
    uint16_t version;
    uint16_t supercell_deg;  // = kSupercellDeg (8)
    uint16_t cell_cols;      // = kCellCols (45)
    uint16_t cell_rows;      // = kCellRows (22)
    int32_t cell_lat0_e6;    // = kCellLat0E6
    int32_t cell_lon0_e6;    // = kCellLon0E6
    uint32_t num_records;
    uint16_t header_crc16;   // CRC over the 24-byte body (up to here)
};
static_assert(sizeof(VecIndexHeader) == 26, "VecIndexHeader must be 26 bytes (vecpack.py)");

// One per super-cell, indexed cell_row*cell_cols+cell_col.
struct __attribute__((packed)) VecCellEntry {
    uint32_t offset;       // byte offset (from archive start); 0 = empty cell
    uint32_t len;          // total bytes of this cell's records
    uint16_t num_records;
    uint16_t pad;
};
static_assert(sizeof(VecCellEntry) == 12, "VecCellEntry must be 12 bytes (vecpack.py)");

// ---- Vector record (streamable; one at a time) ----------------------------
// Followed by num_points * VecPointV3. Coordinates are super-cell-local fixed
// point: u,v in [0, 65535] spanning the 8-degree cell (v grows north). Points
// are stored SORTED BY DESCENDING importance; the device takes the prefix with
// importance >= a zoom-derived threshold, re-sorts by seq, and draws.
struct __attribute__((packed)) VecRecordHeaderV3 {
    uint8_t feature_type;     // VecFeatureType
    uint8_t flags;            // VecRecordFlags
    uint16_t num_points;      // vertex count (1 for a city point)
    uint16_t importance_hint;  // coarse seek aid (25th-percentile importance)
};
static_assert(sizeof(VecRecordHeaderV3) == 6, "VecRecordHeaderV3 must be 6 bytes (vecpack.py)");

struct __attribute__((packed)) VecPointV3 {
    uint16_t u;          // (lon - cell_lon0) / 8 * 65535
    uint16_t v;          // (lat - cell_lat0) / 8 * 65535  (v grows north)
    uint16_t seq;        // original sequence index (re-sort key for draw order)
    uint8_t importance;  // VW effective-area importance, log-quantized (255 = keep)
    uint8_t pad;
};
static_assert(sizeof(VecPointV3) == 8, "VecPointV3 must be 8 bytes (vecpack.py)");

}  // namespace winglet_terrain
