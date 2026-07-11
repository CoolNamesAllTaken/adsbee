#pragma once

#include "peripherals/sd_card.hh"
#include "terrain_tile.hh"
#include "terrain_types.hh"

// Loads terrain map tiles from the microSD card (/sd/tiles/<RRR>/<CCC>.map) into a
// small PSRAM-backed LRU cache, for the Phase-3 renderer to consume. Tiles are
// self-describing (no manifest); the loader builds paths directly from tile
// indices.
//
// Design: loads are CHANGE-TRIGGERED and spread over time — Update() is a no-op
// unless ownship crosses a tile boundary or zoom changes, and it loads at most one
// tile per call, so a multi-tile refresh spreads across main-loop iterations and
// never blocks a render frame. All SD access is guarded on SdCard::IsMounted().

namespace winglet_terrain {

class TerrainLoader {
   public:
    static constexpr int kCacheSize = 4;      // ~4 tiles overlap the window worst-case
    static constexpr int kMaxOverlap = 4;

    // Records the SD driver; no I/O here. Safe to call before a card is present.
    bool Init(SdCard* sd);

    // Poll for ownship/zoom change; load at most one missing overlapping tile per
    // call. Cheap no-op when the overlap set is unchanged. Call from the main loop.
    void Update(bool ownship_valid, float ownship_lat_deg, float ownship_lon_deg, float range_nm);

    // Phase-3 accessors: the tiles currently overlapping the window (cached only).
    // Returns the number written to `out` (<= max_out).
    int GetOverlappingTiles(const ParsedTile** out, int max_out) const;
    const ParsedTile* GetTile(int row, int col) const;

    bool Ready() const { return sd_ != nullptr; }

    // Compute the tile row/col containing a lat/lon (clamped to the grid). Static
    // so the renderer can reuse the exact same indexing.
    static bool TileIndexForLatLon(float lat_deg, float lon_deg, int* row, int* col);

   private:
    struct CacheEntry {
        ParsedTile tile;
        uint32_t lru_stamp = 0;  // higher = more recently used
    };

    // Compute the set of tile indices overlapping the current window.
    int ComputeOverlap(float lat, float lon, float range_nm, int (*rows)[kMaxOverlap],
                       int (*cols)[kMaxOverlap]) const;

    ParsedTile* FindCached(int row, int col);
    ParsedTile* EvictAndClaim();           // free the LRU slot, return it
    bool LoadTile(int row, int col, ParsedTile* dst);  // fopen + parse into dst (PSRAM)
    void FreeTile(ParsedTile* t);

    SdCard* sd_ = nullptr;
    CacheEntry cache_[kCacheSize];
    uint32_t lru_counter_ = 0;

    // Last-evaluated window (to make Update a no-op when unchanged).
    bool have_last_ = false;
    int last_rows_[kMaxOverlap];
    int last_cols_[kMaxOverlap];
    int last_n_ = 0;
};

}  // namespace winglet_terrain

// End-to-end validation self-test (compiled only when TERRAIN_SELF_TEST is
// defined). Loads a known tile and logs header, bounds, grid min/max, record
// counts, bytes, and measured MB/s. Single removable unit.
#ifdef TERRAIN_SELF_TEST
namespace winglet_terrain {
void RunTerrainSelfTest(TerrainLoader& loader, SdCard& sd, int row, int col);
}
#endif
