#pragma once

#include <cstdio>

#include "peripherals/sd_card.hh"
#include "terrain_tile.hh"
#include "terrain_types.hh"

// Loads the single-file world terrain archive (/sd/world.map) for the Phase-3
// renderer. The archive is opened ONCE and its FILE* held open for the device's
// life; the header + per-level descriptors + vector cell index live resident in
// PSRAM. Elevation blocks and vector super-cells are read on demand into small
// PSRAM LRU caches.
//
// Design: loads are CHANGE-TRIGGERED and spread over time — Update() is a no-op
// unless the view (selected level or overlapping block/cell set) changes, and it
// performs at most ONE seek+decode per call, so a multi-block refresh spreads
// across main-loop iterations and never blocks a render frame. All SD access is
// guarded on SdCard::IsMounted().
//
// Zoom -> level is chosen at runtime from the level descriptors (no baked zoom
// presets): the coarsest level whose nm/sample <= nm/pixel. The renderer asks the
// loader for SelectedLevel() so both stay in lockstep against one archive.

namespace winglet_terrain {

class TerrainLoader {
   public:
    // Whole far-zoom view (~8x8 blocks) resident: 64 * 4096 B = 256 KB PSRAM.
    static constexpr int kCacheSize = 64;
    static constexpr int kMaxViewBlocks = 64;
    static constexpr int kMaxLevels = 16;
    static constexpr int kVecCacheSize = 8;
    static constexpr int kMaxViewCells = 16;

    // Records the SD driver; no I/O here. Safe to call before a card is present.
    bool Init(SdCard* sd);

    // Poll for ownship/zoom change; open the archive if needed, select the level
    // for this range, and load at most one missing overlapping block or vector
    // cell per call. Cheap no-op when the view is unchanged. Call from the main loop.
    void Update(bool ownship_valid, float ownship_lat_deg, float ownship_lon_deg, float range_nm);

    bool Ready() const { return sd_ != nullptr; }
    bool ArchiveOpen() const { return file_ != nullptr; }

    // The pyramid level selected for the last Update()'s range (or -1). The
    // renderer must render this same level.
    int SelectedLevel() const { return selected_level_; }
    int NumLevels() const { return num_levels_; }
    const LevelDesc* GetLevelDesc(int level) const {
        return (level >= 0 && level < num_levels_) ? &levels_[level] : nullptr;
    }

    // The decoded blocks currently overlapping the view (cached only), at the
    // selected level. Returns the number written to `out` (<= max_out).
    int GetOverlappingBlocks(const ParsedBlock** out, int max_out) const;

    // The vector super-cells currently overlapping the view (cached only).
    int GetOverlappingVecCells(const VecCellBlob** out, int max_out) const;

    // ---- static geo helpers (renderer reuses the exact mapping) -------------
    // Degrees per sample at a level (equirectangular, uniform per axis).
    static float DegPerSample(int level) {
        return (1.0f / kFinestSamplesPerDeg) * (float)(1 << level);
    }
    // Global sample (sx, sy) -> lat/lon. Row 0 = north (lat +86), sy grows south.
    static void SampleToLatLon(int level, int sx, int sy, float* lat, float* lon) {
        float dps = DegPerSample(level);
        *lon = (kWorldLon0E6 / 1e6f) + sx * dps;             // -180 + sx*dps
        *lat = (-(float)kWorldLat0E6 / 1e6f) - sy * dps;     // +86 - sy*dps
    }
    // Block (bx, by) local sample (lx, ly) -> lat/lon (shared-edge stride 63).
    static void BlockLocalToLatLon(int level, int bx, int by, int lx, int ly,
                                   float* lat, float* lon) {
        SampleToLatLon(level, bx * kBlockStride + lx, by * kBlockStride + ly, lat, lon);
    }

   private:
    struct BlockSlot {
        ParsedBlock block;
    };
    struct VecSlot {
        VecCellBlob cell;
    };

    bool EnsureOpen();
    void CloseArchive();

    // Level select from range: coarsest level with nm/sample <= nm/pixel.
    int SelectLevel(float range_nm) const;

    // Compute the (bx,by) blocks overlapping the view at `level`. Returns count.
    int ComputeViewBlocks(int level, float lat, float lon, float range_nm,
                          int* bxs, int* bys, int max) const;
    // Compute the super-cell indices overlapping the view. Returns count.
    int ComputeViewCells(float lat, float lon, float range_nm, int* cells, int max) const;

    bool ReadDirEntry(int level, int bx, int by, BlockDirEntry* out);
    bool LoadBlock(int level, int bx, int by, ParsedBlock* dst);
    bool LoadVecCell(int cell_index, VecCellBlob* dst);

    ParsedBlock* FindCachedBlock(int level, int bx, int by);
    ParsedBlock* EvictAndClaimBlock();
    void FreeBlock(ParsedBlock* b);

    VecCellBlob* FindCachedCell(int cell_index);
    VecCellBlob* EvictAndClaimCell();
    void FreeCell(VecCellBlob* c);

    SdCard* sd_ = nullptr;
    FILE* file_ = nullptr;
    bool open_failed_ = false;   // latch a failed open so we don't retry every call

    PyramidHeader header_ = {};
    LevelDesc levels_[kMaxLevels] = {};
    int num_levels_ = 0;

    // Resident vector cell index (VecCellEntry table), read once at open.
    VecIndexHeader vec_index_ = {};
    VecCellEntry* vec_cells_ = nullptr;  // PSRAM, kCellCols*kCellRows entries

    // Reused PSRAM buffers: compressed payload input + codec-2 inflate scratch +
    // the ~11 KB tinfl decompressor state (kept off the stack, see terrain_codec).
    uint8_t* payload_buf_ = nullptr;
    uint8_t* decode_scratch_ = nullptr;
    uint8_t* decompressor_ = nullptr;

    BlockSlot cache_[kCacheSize];
    VecSlot vec_cache_[kVecCacheSize];
    uint32_t lru_counter_ = 0;
    uint32_t vec_lru_counter_ = 0;

    int selected_level_ = -1;

    // Last-evaluated view (to make Update a no-op when unchanged).
    bool have_last_ = false;
    int last_level_ = -1;
    int last_bx_[kMaxViewBlocks];
    int last_by_[kMaxViewBlocks];
    int last_nblocks_ = 0;
    int last_cells_[kMaxViewCells];
    int last_ncells_ = 0;
};

}  // namespace winglet_terrain
