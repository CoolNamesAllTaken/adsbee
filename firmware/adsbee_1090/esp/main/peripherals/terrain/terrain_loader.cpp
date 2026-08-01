#include "terrain_loader.hh"

#include <cmath>
#include <cstddef>  // offsetof
#include <cstring>

#include "buffer_utils.hh"  // CalculateCRC16
#include "esp_heap_caps.h"
#include "esp_log.h"
#include "esp_timer.h"
#include "terrain_codec.hh"

namespace winglet_terrain {

namespace {
constexpr char kTag[] = "terrain";
constexpr float kPi = 3.14159265358979323846f;
constexpr float kNmPerDegLat = 60.0f;
// Half-window in ring-radii. The visible map (center to a corner) is ~2 ring-
// radii, so 2.2 covers the screen with a small margin.
constexpr float kHalfWindowRings = 2.2f;
// Matches the renderer's px_per_nm = kOuterRingRadiusPx / range_nm.
constexpr float kOuterRingRadiusPx = 70.0f;

// Max stored payload we accept for one block. The host picks the smaller of
// {plain deflate, predictor+deflate}; DEFLATE's stored-block worst case is raw +
// ~0.1% + 5 B/32KB, so raw+256 is a safe ceiling for a 4KB (or 4160B filtered)
// block. Anything larger is treated as corrupt.
constexpr uint32_t kMaxStoredLen = kBlockDecodeScratchLen + 256;

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
    for (auto& s : cache_) {
        s.block.in_use = false;
        s.block.lru_stamp = 0;
    }
    for (auto& s : vec_cache_) {
        s.cell.in_use = false;
        s.cell.lru_stamp = 0;
    }
    have_last_ = false;
    last_nblocks_ = 0;
    last_ncells_ = 0;
    selected_level_ = -1;
    return true;
}

// ---- archive open ----------------------------------------------------------
bool TerrainLoader::EnsureOpen() {
    if (file_) return true;
    if (open_failed_) return false;
    if (!sd_ || !sd_->IsMounted()) return false;

    FILE* f = fopen("/sd/world.map", "rb");
    if (!f) {
        ESP_LOGW(kTag, "open failed: /sd/world.map");
        open_failed_ = true;
        return false;
    }

    // Header.
    if (fread(&header_, 1, sizeof(header_), f) != sizeof(header_)) {
        ESP_LOGW(kTag, "short header");
        fclose(f);
        open_failed_ = true;
        return false;
    }
    if (header_.magic != kMapMagic || header_.version != kMapFormatVersion ||
        header_.block_dim != kBlockDim || header_.block_stride != kBlockStride) {
        ESP_LOGW(kTag, "bad header (magic=0x%08lX ver=%u dim=%u stride=%u)",
                 (unsigned long)header_.magic, header_.version, header_.block_dim,
                 header_.block_stride);
        fclose(f);
        open_failed_ = true;
        return false;
    }
    // Host computes header_crc16 over the 48-byte body BEFORE both CRC u16s
    // (dir_crc16 is at offset 48, header_crc16 at 50), so CRC covers [0, 48).
    uint16_t hdr_body = (uint16_t)offsetof(PyramidHeader, dir_crc16);
    if (CalculateCRC16((const uint8_t*)&header_, hdr_body) != header_.header_crc16) {
        ESP_LOGW(kTag, "header CRC mismatch");
        fclose(f);
        open_failed_ = true;
        return false;
    }
    if (header_.num_levels == 0 || header_.num_levels > kMaxLevels) {
        ESP_LOGW(kTag, "num_levels %u out of range", header_.num_levels);
        fclose(f);
        open_failed_ = true;
        return false;
    }
    num_levels_ = header_.num_levels;

    // Level descriptors (fixed table right after the header).
    if (fread(levels_, 1, (size_t)num_levels_ * sizeof(LevelDesc), f) !=
        (size_t)num_levels_ * sizeof(LevelDesc)) {
        ESP_LOGW(kTag, "short level table");
        fclose(f);
        open_failed_ = true;
        return false;
    }

    // Vector index header + cell table.
    if (fseek(f, (long)header_.vec_index_offset, SEEK_SET) != 0 ||
        fread(&vec_index_, 1, sizeof(vec_index_), f) != sizeof(vec_index_)) {
        ESP_LOGW(kTag, "short vec index header");
        fclose(f);
        open_failed_ = true;
        return false;
    }
    if (vec_index_.magic == kVecIndexMagic &&
        (vec_index_.cell_cols != kCellCols || vec_index_.cell_rows != kCellRows)) {
        // The cell table is sized from the file but indexed with the compile-time
        // grid (kCellCols/kCellRows); a mismatch would allow OOB indexing.
        ESP_LOGW(kTag, "vec cell grid %ux%u != %dx%d (vectors disabled)",
                 vec_index_.cell_cols, vec_index_.cell_rows, kCellCols, kCellRows);
        vec_index_.magic = 0;
    }
    if (vec_index_.magic == kVecIndexMagic) {
        uint16_t vi_body = (uint16_t)offsetof(VecIndexHeader, header_crc16);
        if (CalculateCRC16((const uint8_t*)&vec_index_, vi_body) != vec_index_.header_crc16) {
            ESP_LOGW(kTag, "vec index CRC mismatch (vectors disabled)");
            vec_index_.magic = 0;  // treat as no vectors
        } else {
            uint32_t n_cells = (uint32_t)vec_index_.cell_cols * vec_index_.cell_rows;
            vec_cells_ = (VecCellEntry*)PsramAlloc(n_cells * sizeof(VecCellEntry));
            if (vec_cells_ &&
                fread(vec_cells_, 1, n_cells * sizeof(VecCellEntry), f) !=
                    n_cells * sizeof(VecCellEntry)) {
                ESP_LOGW(kTag, "short vec cell table (vectors disabled)");
                heap_caps_free(vec_cells_);
                vec_cells_ = nullptr;
            }
        }
    } else {
        ESP_LOGW(kTag, "no vector index (magic=0x%08lX)", (unsigned long)vec_index_.magic);
    }

    payload_buf_ = PsramAlloc(kMaxStoredLen);
    decode_scratch_ = PsramAlloc(kBlockDecodeScratchLen);
    decompressor_ = PsramAlloc(kTinflDecompressorSize);

    file_ = f;
    ESP_LOGI(kTag, "world.map open: %u levels, %u vec records",
             num_levels_, (unsigned)(vec_cells_ ? vec_index_.num_records : 0));
    return true;
}

void TerrainLoader::CloseArchive() {
    if (file_) {
        fclose(file_);
        file_ = nullptr;
    }
    for (auto& s : cache_) FreeBlock(&s.block);
    for (auto& s : vec_cache_) FreeCell(&s.cell);
    if (vec_cells_) {
        heap_caps_free(vec_cells_);
        vec_cells_ = nullptr;
    }
    if (payload_buf_) {
        heap_caps_free(payload_buf_);
        payload_buf_ = nullptr;
    }
    if (decode_scratch_) {
        heap_caps_free(decode_scratch_);
        decode_scratch_ = nullptr;
    }
    if (decompressor_) {
        heap_caps_free(decompressor_);
        decompressor_ = nullptr;
    }
    num_levels_ = 0;
    have_last_ = false;
    selected_level_ = -1;
}

// ---- level select ----------------------------------------------------------
int TerrainLoader::SelectLevel(float range_nm) const {
    if (num_levels_ <= 0) return -1;
    float nm_per_px = range_nm / kOuterRingRadiusPx;
    // Coarsest level whose nm/sample <= nm/pixel (samples stay >= 1 px apart).
    int selected = 0;
    for (int l = 0; l < num_levels_; l++) {
        if (levels_[l].NmPerSample() <= nm_per_px) selected = l;
    }
    return selected;
}

// ---- view -> blocks --------------------------------------------------------
int TerrainLoader::ComputeViewBlocks(int level, float lat, float lon, float range_nm,
                                     int* bxs, int* bys, int max) const {
    const LevelDesc& L = levels_[level];
    float half_nm = kHalfWindowRings * range_nm;
    float coslat = cosf(lat * kPi / 180.0f);
    if (coslat < 0.05f) coslat = 0.05f;
    float dlat = half_nm / kNmPerDegLat;
    float dlon = half_nm / (kNmPerDegLat * coslat);

    float lat_lo = lat - dlat, lat_hi = lat + dlat;
    float lon_lo = lon - dlon, lon_hi = lon + dlon;

    float dps = DegPerSample(level);
    float lon0 = kWorldLon0E6 / 1e6f;        // -180
    float lat_top = -(float)kWorldLat0E6 / 1e6f;  // +86

    // Sample-index extents. sy grows south, so lat_hi -> smaller sy.
    auto sx_of = [&](float lo) { return (int)floorf((lo - lon0) / dps); };
    auto sy_of = [&](float la) { return (int)floorf((lat_top - la) / dps); };
    int sx0 = sx_of(lon_lo), sx1 = sx_of(lon_hi);
    int sy0 = sy_of(lat_hi), sy1 = sy_of(lat_lo);  // sy0 (north) <= sy1 (south)
    if (sx0 > sx1) { int t = sx0; sx0 = sx1; sx1 = t; }
    if (sy0 > sy1) { int t = sy0; sy0 = sy1; sy1 = t; }
    if (sx0 < 0) sx0 = 0;
    if (sy0 < 0) sy0 = 0;
    if (sx1 > (int)L.samples_w - 1) sx1 = (int)L.samples_w - 1;
    if (sy1 > (int)L.samples_h - 1) sy1 = (int)L.samples_h - 1;
    if (sx1 < sx0 || sy1 < sy0) return 0;

    // Sample -> block (shared-edge stride 63). A sample can belong to two blocks
    // (the shared edge); include the block on each side so seams are covered.
    int bx0 = sx0 / kBlockStride, bx1 = sx1 / kBlockStride;
    int by0 = sy0 / kBlockStride, by1 = sy1 / kBlockStride;
    if (bx1 > (int)L.blocks_x - 1) bx1 = (int)L.blocks_x - 1;
    if (by1 > (int)L.blocks_y - 1) by1 = (int)L.blocks_y - 1;

    int n = 0;
    for (int by = by0; by <= by1 && n < max; by++) {
        for (int bx = bx0; bx <= bx1 && n < max; bx++) {
            bxs[n] = bx;
            bys[n] = by;
            n++;
        }
    }
    return n;
}

int TerrainLoader::ComputeViewCells(float lat, float lon, float range_nm,
                                    int* cells, int max) const {
    float half_nm = kHalfWindowRings * range_nm;
    float coslat = cosf(lat * kPi / 180.0f);
    if (coslat < 0.05f) coslat = 0.05f;
    float dlat = half_nm / kNmPerDegLat;
    float dlon = half_nm / (kNmPerDegLat * coslat);

    float lat0 = kCellLat0E6 / 1e6f;   // -86
    float lon0 = kCellLon0E6 / 1e6f;   // -180
    auto row_of = [&](float la) { return (int)floorf((la - lat0) / kSupercellDeg); };
    auto col_of = [&](float lo) { return (int)floorf((lo - lon0) / kSupercellDeg); };
    int r0 = row_of(lat - dlat), r1 = row_of(lat + dlat);
    int c0 = col_of(lon - dlon), c1 = col_of(lon + dlon);
    if (r0 < 0) r0 = 0;
    if (r1 > kCellRows - 1) r1 = kCellRows - 1;
    if (c0 < 0) c0 = 0;
    if (c1 > kCellCols - 1) c1 = kCellCols - 1;

    int n = 0;
    for (int r = r0; r <= r1 && n < max; r++) {
        for (int c = c0; c <= c1 && n < max; c++) {
            cells[n++] = r * kCellCols + c;
        }
    }
    return n;
}

// ---- block load ------------------------------------------------------------
bool TerrainLoader::ReadDirEntry(int level, int bx, int by, BlockDirEntry* out) {
    const LevelDesc& L = levels_[level];
    uint64_t off = L.dir_offset + (uint64_t)((uint32_t)by * L.blocks_x + bx) * sizeof(BlockDirEntry);
    if (fseek(file_, (long)off, SEEK_SET) != 0) return false;
    return fread(out, 1, sizeof(BlockDirEntry), file_) == sizeof(BlockDirEntry);
}

bool TerrainLoader::LoadBlock(int level, int bx, int by, ParsedBlock* dst) {
    if (!EnsureOpen()) return false;

    BlockDirEntry e;
    if (!ReadDirEntry(level, bx, by, &e)) {
        ESP_LOGW(kTag, "dir read fail L%d (%d,%d)", level, bx, by);
        return false;
    }

    if (!dst->codes) {
        dst->codes = PsramAlloc(kBlockRawLen);
        if (!dst->codes) {
            ESP_LOGE(kTag, "PSRAM alloc failed for block codes");
            return false;
        }
    }

    bool ok;
    if (e.codec == kCodecConstant || e.stored_len == 0) {
        ok = DecodeBlock(kCodecConstant, e.fill, nullptr, 0, dst->codes, kBlockRawLen, nullptr,
                         nullptr);
    } else if (e.stored_len > kMaxStoredLen || !payload_buf_ || !decode_scratch_ ||
               !decompressor_) {
        ESP_LOGW(kTag, "stored_len %u too large L%d (%d,%d)", (unsigned)e.stored_len,
                 level, bx, by);
        memset(dst->codes, kElevVoidCode, kBlockRawLen);
        ok = false;
    } else if (fseek(file_, (long)e.offset, SEEK_SET) != 0 ||
               fread(payload_buf_, 1, e.stored_len, file_) != e.stored_len) {
        ESP_LOGW(kTag, "payload read fail L%d (%d,%d)", level, bx, by);
        memset(dst->codes, kElevVoidCode, kBlockRawLen);
        ok = false;
    } else {
        // Compressed input in payload_buf_, inflate scratch in decode_scratch_
        // (codec 2 inflates the filtered stream there, then unfilters into codes);
        // the ~11 KB tinfl state lives in decompressor_ (PSRAM), off the stack.
        ok = DecodeBlock(e.codec, e.fill, payload_buf_, e.stored_len, dst->codes, kBlockRawLen,
                         decode_scratch_, decompressor_);
        if (!ok) memset(dst->codes, kElevVoidCode, kBlockRawLen);
    }

    dst->in_use = true;
    dst->level = level;
    dst->bx = bx;
    dst->by = by;
    dst->elev_base_m = levels_[level].elev_base_m;
    dst->elev_step_m = levels_[level].elev_step_m;
    return ok;
}

bool TerrainLoader::LoadVecCell(int cell_index, VecCellBlob* dst) {
    if (!vec_cells_) return false;
    const VecCellEntry& e = vec_cells_[cell_index];
    dst->cell_index = cell_index;
    dst->cell_row = cell_index / kCellCols;
    dst->cell_col = cell_index % kCellCols;
    dst->num_records = e.num_records;
    if (e.offset == 0 || e.len == 0) {
        // Empty cell: mark loaded with no data so we don't retry it.
        dst->data = nullptr;
        dst->len = 0;
        dst->in_use = true;
        return true;
    }
    dst->data = PsramAlloc(e.len);
    if (!dst->data) return false;
    if (fseek(file_, (long)e.offset, SEEK_SET) != 0 ||
        fread(dst->data, 1, e.len, file_) != e.len) {
        heap_caps_free(dst->data);
        dst->data = nullptr;
        return false;
    }
    dst->len = e.len;
    dst->in_use = true;
    return true;
}

// ---- block cache -----------------------------------------------------------
ParsedBlock* TerrainLoader::FindCachedBlock(int level, int bx, int by) {
    for (auto& s : cache_) {
        if (s.block.in_use && s.block.level == level && s.block.bx == bx && s.block.by == by) {
            s.block.lru_stamp = ++lru_counter_;
            return &s.block;
        }
    }
    return nullptr;
}

ParsedBlock* TerrainLoader::EvictAndClaimBlock() {
    BlockSlot* victim = nullptr;
    for (auto& s : cache_) {
        if (!s.block.in_use) { victim = &s; break; }
    }
    if (!victim) {
        victim = &cache_[0];
        for (auto& s : cache_)
            if (s.block.lru_stamp < victim->block.lru_stamp) victim = &s;
        // Keep the codes buffer; just mark free so LoadBlock reuses it.
        uint8_t* keep = victim->block.codes;
        victim->block = ParsedBlock{};
        victim->block.codes = keep;
    }
    victim->block.lru_stamp = ++lru_counter_;
    return &victim->block;
}

void TerrainLoader::FreeBlock(ParsedBlock* b) {
    if (b->codes) heap_caps_free(b->codes);
    *b = ParsedBlock{};
}

// ---- vec cell cache --------------------------------------------------------
VecCellBlob* TerrainLoader::FindCachedCell(int cell_index) {
    for (auto& s : vec_cache_) {
        if (s.cell.in_use && s.cell.cell_index == cell_index) {
            s.cell.lru_stamp = ++vec_lru_counter_;
            return &s.cell;
        }
    }
    return nullptr;
}

VecCellBlob* TerrainLoader::EvictAndClaimCell() {
    VecSlot* victim = nullptr;
    for (auto& s : vec_cache_) {
        if (!s.cell.in_use) { victim = &s; break; }
    }
    if (!victim) {
        victim = &vec_cache_[0];
        for (auto& s : vec_cache_)
            if (s.cell.lru_stamp < victim->cell.lru_stamp) victim = &s;
        FreeCell(&victim->cell);
    }
    victim->cell.lru_stamp = ++vec_lru_counter_;
    return &victim->cell;
}

void TerrainLoader::FreeCell(VecCellBlob* c) {
    if (c->data) heap_caps_free(c->data);
    *c = VecCellBlob{};
}

// ---- update ----------------------------------------------------------------
void TerrainLoader::Update(bool ownship_valid, float lat, float lon, float range_nm) {
    if (!sd_ || !sd_->IsMounted() || !ownship_valid || range_nm <= 0.01f) return;
    if (!EnsureOpen()) return;

    int level = SelectLevel(range_nm);
    if (level < 0) return;
    selected_level_ = level;

    int bxs[kMaxViewBlocks], bys[kMaxViewBlocks];
    int nb = ComputeViewBlocks(level, lat, lon, range_nm, bxs, bys, kMaxViewBlocks);
    int cells[kMaxViewCells];
    int nc = ComputeViewCells(lat, lon, range_nm, cells, kMaxViewCells);

    // No-op if the view (level + block set + cell set) is identical to last time.
    if (have_last_ && level == last_level_ && nb == last_nblocks_ && nc == last_ncells_) {
        bool same = true;
        for (int i = 0; i < nb && same; i++) {
            bool found = false;
            for (int j = 0; j < last_nblocks_; j++)
                if (last_bx_[j] == bxs[i] && last_by_[j] == bys[i]) { found = true; break; }
            if (!found) same = false;
        }
        for (int i = 0; i < nc && same; i++) {
            bool found = false;
            for (int j = 0; j < last_ncells_; j++)
                if (last_cells_[j] == cells[i]) { found = true; break; }
            if (!found) same = false;
        }
        if (same) return;
    }

    // Load at most ONE missing I/O item (block or vec cell) this call, to spread
    // I/O across loop iterations and never block a render frame.
    bool did_io = false;
    for (int i = 0; i < nb && !did_io; i++) {
        if (FindCachedBlock(level, bxs[i], bys[i])) continue;
        ParsedBlock* slot = EvictAndClaimBlock();
        if (!LoadBlock(level, bxs[i], bys[i], slot)) slot->in_use = false;
        did_io = true;
    }
    if (!did_io && vec_cells_) {
        for (int i = 0; i < nc && !did_io; i++) {
            if (FindCachedCell(cells[i])) continue;
            VecCellBlob* slot = EvictAndClaimCell();
            if (!LoadVecCell(cells[i], slot)) slot->in_use = false;
            did_io = true;
        }
    }

    // Latch the view once every needed block + cell is cached (keep trying until
    // fully loaded, then latch to a no-op).
    bool all_cached = true;
    for (int i = 0; i < nb && all_cached; i++)
        if (!FindCachedBlock(level, bxs[i], bys[i])) all_cached = false;
    if (all_cached && vec_cells_)
        for (int i = 0; i < nc && all_cached; i++)
            if (!FindCachedCell(cells[i])) all_cached = false;

    if (all_cached) {
        last_level_ = level;
        for (int i = 0; i < nb; i++) { last_bx_[i] = bxs[i]; last_by_[i] = bys[i]; }
        last_nblocks_ = nb;
        for (int i = 0; i < nc; i++) last_cells_[i] = cells[i];
        last_ncells_ = nc;
        have_last_ = true;
    } else {
        have_last_ = false;
    }
}

// ---- accessors -------------------------------------------------------------
int TerrainLoader::GetOverlappingBlocks(const ParsedBlock** out, int max_out) const {
    int n = 0;
    for (int i = 0; i < last_nblocks_ && n < max_out; i++) {
        for (const auto& s : cache_) {
            if (s.block.in_use && s.block.level == last_level_ &&
                s.block.bx == last_bx_[i] && s.block.by == last_by_[i]) {
                out[n++] = &s.block;
                break;
            }
        }
    }
    return n;
}

int TerrainLoader::GetOverlappingVecCells(const VecCellBlob** out, int max_out) const {
    int n = 0;
    for (int i = 0; i < last_ncells_ && n < max_out; i++) {
        for (const auto& s : vec_cache_) {
            if (s.cell.in_use && s.cell.cell_index == last_cells_[i]) {
                out[n++] = &s.cell;
                break;
            }
        }
    }
    return n;
}

}  // namespace winglet_terrain
