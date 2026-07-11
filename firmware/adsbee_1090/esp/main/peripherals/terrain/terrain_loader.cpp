#include "terrain_loader.hh"

#include <cmath>
#include <cstddef>  // offsetof
#include <cstdio>
#include <cstring>

#include "buffer_utils.hh"  // CalculateCRC16
#include "esp_heap_caps.h"
#include "esp_log.h"
#include "esp_timer.h"

namespace winglet_terrain {

namespace {
constexpr char kTag[] = "terrain";
constexpr float kPi = 3.14159265358979323846f;
constexpr float kNmPerDegLat = 60.0f;
// Half-window in ring-radii. The visible map (center to a corner) is about 2
// ring-radii, so 2.2 covers the screen with a small margin. Tiles are then
// selected NEAREST-FIRST (see ComputeOverlap), so the exact window size only
// bounds the candidate set, not which tiles win the cap.
constexpr float kHalfWindowRings = 2.2f;

// Allocate in PSRAM; fall back to internal RAM if PSRAM is absent/full.
uint8_t* PsramAlloc(uint32_t len) {
    if (len == 0) return nullptr;
    uint8_t* p = (uint8_t*)heap_caps_malloc(len, MALLOC_CAP_SPIRAM);
    if (!p) p = (uint8_t*)heap_caps_malloc(len, MALLOC_CAP_8BIT);
    return p;
}
}  // namespace

bool TerrainLoader::Init(SdCard* sd) {
    sd_ = sd;
    for (auto& e : cache_) {
        e.tile.in_use = false;
        e.lru_stamp = 0;
    }
    have_last_ = false;
    last_n_ = 0;
    return true;
}

// ---- tile indexing --------------------------------------------------------
bool TerrainLoader::TileIndexForLatLon(float lat_deg, float lon_deg, int* row, int* col) {
    if (lat_deg < kTileLatMinDeg || lat_deg >= kTileLatMaxDeg) return false;  // poles omitted
    // Normalize lon to [-180, 180).
    while (lon_deg < -180.0f) lon_deg += 360.0f;
    while (lon_deg >= 180.0f) lon_deg -= 360.0f;
    int r = (int)floorf((lat_deg - kTileLatMinDeg) / kTileStepDeg);
    int c = (int)floorf((lon_deg + 180.0f) / kTileStepDeg);
    if (r < 0) r = 0;
    if (r >= kNumTileRows) r = kNumTileRows - 1;
    c = ((c % kNumTileCols) + kNumTileCols) % kNumTileCols;
    *row = r;
    *col = c;
    return true;
}

int TerrainLoader::ComputeOverlap(float lat, float lon, float range_nm,
                                  int (*rows)[kMaxOverlap], int (*cols)[kMaxOverlap]) const {
    float half_nm = kHalfWindowRings * range_nm;
    float coslat = cosf(lat * kPi / 180.0f);
    if (coslat < 0.05f) coslat = 0.05f;  // guard near the (already-clamped) poles
    float dlat = half_nm / kNmPerDegLat;
    float dlon = half_nm / (kNmPerDegLat * coslat);

    int r_lo, r_hi;
    // Latitude range (clamped to grid).
    float lat_lo = lat - dlat, lat_hi = lat + dlat;
    if (lat_lo < kTileLatMinDeg) lat_lo = kTileLatMinDeg;
    if (lat_hi >= kTileLatMaxDeg) lat_hi = kTileLatMaxDeg - 0.0001f;
    r_lo = (int)floorf((lat_lo - kTileLatMinDeg) / kTileStepDeg);
    r_hi = (int)floorf((lat_hi - kTileLatMinDeg) / kTileStepDeg);
    // Longitude range in tile-col units (may wrap).
    int c_lo = (int)floorf((lon - dlon + 180.0f) / kTileStepDeg);
    int c_hi = (int)floorf((lon + dlon + 180.0f) / kTileStepDeg);

    // Keep the kMaxOverlap tiles NEAREST the ownship (by tile-center distance in
    // screen-space nm), so the ownship's own tile always wins the cap instead of
    // whichever row is iterated first. Insertion into a small sorted-by-distance
    // top-N array.
    float best_d2[kMaxOverlap];
    int n = 0;
    for (int r = r_lo; r <= r_hi; r++) {
        if (r < 0 || r >= kNumTileRows) continue;
        float tile_center_lat = kTileLatMinDeg + (r + 0.5f) * kTileStepDeg;
        float dnm_n = (tile_center_lat - lat) * kNmPerDegLat;
        for (int c = c_lo; c <= c_hi; c++) {
            int cc = ((c % kNumTileCols) + kNumTileCols) % kNumTileCols;
            // Dedup (wrap can repeat a col).
            bool dup = false;
            for (int k = 0; k < n; k++)
                if ((*rows)[k] == r && (*cols)[k] == cc) { dup = true; break; }
            if (dup) continue;

            // Tile center longitude uses the un-wrapped c so the delta to ownship
            // is correct across the antimeridian.
            float tile_center_lon = -180.0f + (c + 0.5f) * kTileStepDeg;
            float dnm_e = (tile_center_lon - lon) * kNmPerDegLat * coslat;
            float d2 = dnm_n * dnm_n + dnm_e * dnm_e;

            // Insert into the top-N nearest (ascending d2), capped at kMaxOverlap.
            if (n < kMaxOverlap) {
                int k = n++;
                while (k > 0 && best_d2[k - 1] > d2) {
                    best_d2[k] = best_d2[k - 1];
                    (*rows)[k] = (*rows)[k - 1];
                    (*cols)[k] = (*cols)[k - 1];
                    k--;
                }
                best_d2[k] = d2; (*rows)[k] = r; (*cols)[k] = cc;
            } else if (d2 < best_d2[kMaxOverlap - 1]) {
                int k = kMaxOverlap - 1;
                while (k > 0 && best_d2[k - 1] > d2) {
                    best_d2[k] = best_d2[k - 1];
                    (*rows)[k] = (*rows)[k - 1];
                    (*cols)[k] = (*cols)[k - 1];
                    k--;
                }
                best_d2[k] = d2; (*rows)[k] = r; (*cols)[k] = cc;
            }
        }
    }
    return n;
}

// ---- cache management ------------------------------------------------------
ParsedTile* TerrainLoader::FindCached(int row, int col) {
    for (auto& e : cache_) {
        if (e.tile.in_use && e.tile.row == row && e.tile.col == col) {
            e.lru_stamp = ++lru_counter_;
            return &e.tile;
        }
    }
    return nullptr;
}

ParsedTile* TerrainLoader::EvictAndClaim() {
    // Prefer a free slot; else evict the least-recently-used.
    CacheEntry* victim = nullptr;
    for (auto& e : cache_) {
        if (!e.tile.in_use) { victim = &e; break; }
    }
    if (!victim) {
        victim = &cache_[0];
        for (auto& e : cache_)
            if (e.lru_stamp < victim->lru_stamp) victim = &e;
        FreeTile(&victim->tile);
    }
    victim->lru_stamp = ++lru_counter_;
    return &victim->tile;
}

void TerrainLoader::FreeTile(ParsedTile* t) {
    if (t->elev) heap_caps_free(t->elev);
    if (t->vec_water) heap_caps_free(t->vec_water);
    if (t->vec_road) heap_caps_free(t->vec_road);
    if (t->water_mask) heap_caps_free(t->water_mask);
    *t = ParsedTile{};
}

// ---- load path -------------------------------------------------------------
bool TerrainLoader::LoadTile(int row, int col, ParsedTile* dst) {
    if (!sd_ || !sd_->IsMounted()) return false;

    char path[48];
    snprintf(path, sizeof path, "/sd/tiles/%03X/%03X.map", row, col);

    FILE* f = fopen(path, "rb");
    if (!f) {
        ESP_LOGW(kTag, "open failed: %s", path);
        return false;
    }

    // Read the header.
    TileHeader hdr;
    int64_t t0 = esp_timer_get_time();
    size_t hn = fread(&hdr, 1, sizeof(hdr), f);
    if (hn != sizeof(hdr)) {
        ESP_LOGW(kTag, "short header: %s", path);
        fclose(f);
        return false;
    }
    if (hdr.magic != kTileMagic || hdr.version != kTileFormatVersion) {
        ESP_LOGW(kTag, "bad magic/version: %s (magic=0x%08lX ver=%u)", path,
                 (unsigned long)hdr.magic, hdr.version);
        fclose(f);
        return false;
    }
    // Header CRC covers everything up to header_crc16.
    uint16_t hdr_body_len = (uint16_t)(offsetof(TileHeader, header_crc16));
    if (CalculateCRC16((const uint8_t*)&hdr, hdr_body_len) != hdr.header_crc16) {
        ESP_LOGW(kTag, "header CRC mismatch: %s", path);
        fclose(f);
        return false;
    }

    // Allocate + read each layer (elevation raw for Phase 2). Timed for the
    // organic throughput measurement the user requested.
    uint8_t* elev = PsramAlloc(hdr.elev_len);
    uint8_t* water = PsramAlloc(hdr.water_len);
    uint8_t* road = PsramAlloc(hdr.road_len);
    uint8_t* mask = PsramAlloc(hdr.water_mask_len);
    bool alloc_ok = (hdr.elev_len == 0 || elev) && (hdr.water_len == 0 || water) &&
                    (hdr.road_len == 0 || road) && (hdr.water_mask_len == 0 || mask);
    if (!alloc_ok) {
        ESP_LOGE(kTag, "PSRAM alloc failed for %s", path);
        if (elev) heap_caps_free(elev);
        if (water) heap_caps_free(water);
        if (road) heap_caps_free(road);
        if (mask) heap_caps_free(mask);
        fclose(f);
        return false;
    }

    size_t total = hn;
    bool read_ok = true;
    auto read_block = [&](uint32_t off, uint32_t len, uint8_t* buf) {
        if (len == 0) return;
        if (fseek(f, off, SEEK_SET) != 0) { read_ok = false; return; }
        size_t n = fread(buf, 1, len, f);
        total += n;
        if (n != len) read_ok = false;
    };
    read_block(hdr.elev_offset, hdr.elev_len, elev);
    read_block(hdr.water_offset, hdr.water_len, water);
    read_block(hdr.road_offset, hdr.road_len, road);
    read_block(hdr.water_mask_offset, hdr.water_mask_len, mask);
    int64_t dt = esp_timer_get_time() - t0;
    fclose(f);

    if (!read_ok) {
        ESP_LOGW(kTag, "short read: %s", path);
        if (elev) heap_caps_free(elev);
        if (water) heap_caps_free(water);
        if (road) heap_caps_free(road);
        if (mask) heap_caps_free(mask);
        return false;
    }

    float mbps = (dt > 0) ? ((float)total / 1e6f) / ((float)dt / 1e6f) : 0.0f;
    ESP_LOGI(kTag, "tile %03X/%03X: %u B in %lld us = %.2f MB/s", row, col, (unsigned)total,
             (long long)dt, mbps);

    dst->in_use = true;
    dst->row = row;
    dst->col = col;
    dst->hdr = hdr;
    dst->elev = elev;
    dst->elev_len = hdr.elev_len;
    dst->vec_water = water;
    dst->vec_water_len = hdr.water_len;
    dst->water_count = hdr.water_count;
    dst->vec_road = road;
    dst->vec_road_len = hdr.road_len;
    dst->road_count = hdr.road_count;
    dst->water_mask = mask;
    dst->water_mask_len = hdr.water_mask_len;
    dst->mask_w = hdr.water_mask_w;
    dst->mask_h = hdr.water_mask_h;
    return true;
}

// ---- update / accessors ----------------------------------------------------
void TerrainLoader::Update(bool ownship_valid, float lat, float lon, float range_nm) {
    if (!sd_ || !sd_->IsMounted() || !ownship_valid || range_nm <= 0.01f) return;
    // Too zoomed out for the 4-tile set to cover the screen: don't load terrain.
    if (range_nm > kTerrainMaxRangeNm) { have_last_ = false; last_n_ = 0; return; }

    int rows[kMaxOverlap], cols[kMaxOverlap];
    int n = ComputeOverlap(lat, lon, range_nm, &rows, &cols);

    // No-op if the overlap set is identical to last time.
    if (have_last_ && n == last_n_) {
        bool same = true;
        for (int i = 0; i < n && same; i++) {
            bool found = false;
            for (int j = 0; j < last_n_; j++)
                if (last_rows_[j] == rows[i] && last_cols_[j] == cols[i]) { found = true; break; }
            if (!found) same = false;
        }
        if (same) return;
    }

    // Load at most ONE missing tile this call (spread I/O across loop iterations).
    for (int i = 0; i < n; i++) {
        if (FindCached(rows[i], cols[i])) continue;
        ParsedTile* slot = EvictAndClaim();
        if (!LoadTile(rows[i], cols[i], slot)) {
            slot->in_use = false;  // failed; leave slot free
        }
        break;  // one per call
    }

    // Record the window once every needed tile is cached (so we keep trying until
    // the set is fully loaded, then latch it to become a no-op).
    bool all_cached = true;
    for (int i = 0; i < n; i++)
        if (!FindCached(rows[i], cols[i])) { all_cached = false; break; }
    if (all_cached) {
        for (int i = 0; i < n; i++) { last_rows_[i] = rows[i]; last_cols_[i] = cols[i]; }
        last_n_ = n;
        have_last_ = true;
    } else {
        have_last_ = false;  // keep loading next call
    }
}

int TerrainLoader::GetOverlappingTiles(const ParsedTile** out, int max_out) const {
    int n = 0;
    for (int i = 0; i < last_n_ && n < max_out; i++) {
        for (const auto& e : cache_) {
            if (e.tile.in_use && e.tile.row == last_rows_[i] && e.tile.col == last_cols_[i]) {
                out[n++] = &e.tile;
                break;
            }
        }
    }
    return n;
}

const ParsedTile* TerrainLoader::GetTile(int row, int col) const {
    for (const auto& e : cache_) {
        if (e.tile.in_use && e.tile.row == row && e.tile.col == col) return &e.tile;
    }
    return nullptr;
}

}  // namespace winglet_terrain

// ---------------------------------------------------------------------------
// Validation self-test (single removable block).
// ---------------------------------------------------------------------------
#ifdef TERRAIN_SELF_TEST
namespace winglet_terrain {

void RunTerrainSelfTest(TerrainLoader& loader, SdCard& sd, int row, int col) {
    const char* kTagT = "terrain_test";
    if (!sd.IsMounted()) {
        ESP_LOGW(kTagT, "self-test skipped: no card");
        return;
    }
    // Load directly into a scratch ParsedTile via the loader's public path by
    // forcing an Update at the tile's center... simplest: reuse LoadTile through
    // a cached fetch. We call Update with a synthetic ownship at the tile center.
    float lat0 = (float)(kTileLatMinDeg + row);
    float lon0 = (float)(-180 + col);
    loader.Update(true, lat0 + 0.5f, lon0 + 0.5f, 20.0f);  // a real (close) ladder range
    const ParsedTile* t = loader.GetTile(row, col);
    if (!t) {
        ESP_LOGE(kTagT, "self-test FAIL: tile %03X/%03X did not load", row, col);
        return;
    }
    // Elevation min/max.
    int32_t emin = INT32_MAX, emax = INT32_MIN;
    for (int gy = 0; gy < t->hdr.elev_grid_h; gy++) {
        for (int gx = 0; gx < t->hdr.elev_grid_w; gx++) {
            int32_t m = t->SampleMeters(gx, gy);
            if (m == INT32_MIN) continue;
            if (m < emin) emin = m;
            if (m > emax) emax = m;
        }
    }
    ESP_LOGI(kTagT, "TILE OK %03X/%03X: ver=%u grid=%ux%u base=%dm step=%dm",
             row, col, t->hdr.version, t->hdr.elev_grid_w, t->hdr.elev_grid_h,
             t->hdr.elev_base_m, t->hdr.elev_step_m);
    ESP_LOGI(kTagT, "  bounds lat0=%.4f lon0=%.4f elev[min=%dm max=%dm] water=%u roads/cities=%u",
             t->hdr.tile_lat0_e6 / 1e6, t->hdr.tile_lon0_e6 / 1e6,
             (emin == INT32_MAX ? 0 : emin), (emax == INT32_MIN ? 0 : emax),
             t->water_count, t->road_count);
    // Water-mask stats (a non-zero count over a coastal tile confirms the mask).
    uint32_t water_bits = 0;
    for (int gy = 0; gy < t->mask_h; gy++)
        for (int gx = 0; gx < t->mask_w; gx++)
            if (t->IsWater(gx, gy)) water_bits++;
    ESP_LOGI(kTagT, "  water-mask %ux%u: %lu/%lu cells water", t->mask_w, t->mask_h,
             (unsigned long)water_bits, (unsigned long)((uint32_t)t->mask_w * t->mask_h));
}

}  // namespace winglet_terrain
#endif  // TERRAIN_SELF_TEST
