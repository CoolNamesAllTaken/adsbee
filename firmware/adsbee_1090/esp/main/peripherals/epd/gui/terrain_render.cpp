#include "terrain_render.hh"

#include <cmath>
#include <cstdint>
#include <cstring>

#include "canvas.hh"
#include "esp_heap_caps.h"
#include "esp_log.h"
#include "peripherals/terrain/terrain_tile.hh"
#include "ui_primitives.hh"

namespace winglet_ui {

namespace {
constexpr float kPi = 3.14159265358979323846f;
inline int IRound(float v) { return (int)lroundf(v); }

using winglet_terrain::ParsedBlock;
using winglet_terrain::TerrainLoader;
using winglet_terrain::VecCellBlob;
using winglet_terrain::VecPointV3;
using winglet_terrain::VecRecordHeaderV3;

// Max vertices we re-sort per record (importance-threshold prefix). Generous for
// the aviation zoom budget; longer records are truncated at this prefix.
constexpr int kMaxPrefixPoints = 256;

// ---- vector record streamer ----------------------------------------------
struct VecCursor {
    const uint8_t* p;
    const uint8_t* end;
};

// Decode the next V3 record: 6-byte header then num_points * 8-byte points (no
// name field in V3). Returns false at end / on truncation. `pts` points into the
// blob (little-endian VecPointV3).
bool NextRecord(VecCursor& c, VecRecordHeaderV3& h, const VecPointV3** pts) {
    if (c.p + sizeof(VecRecordHeaderV3) > c.end) return false;
    __builtin_memcpy(&h, c.p, sizeof(h));
    const uint8_t* pt_start = c.p + sizeof(VecRecordHeaderV3);
    const uint8_t* q = pt_start + (size_t)h.num_points * sizeof(VecPointV3);
    if (q > c.end) return false;
    *pts = reinterpret_cast<const VecPointV3*>(pt_start);
    c.p = q;
    return true;
}

// ---- city mark (haloed 7x7 ring + 3x3 center) ----------------------------
struct CityCtx { int cx, cy; };
void CityDraw(Canvas& canvas, int dx, int dy, uint16_t color, void* ctx) {
    auto* c = static_cast<CityCtx*>(ctx);
    int cx = c->cx + dx, cy = c->cy + dy;
    for (int i = -3; i <= 3; i++) {  // 7x7 outline
        SetPixelSafe(canvas, cx + i, cy - 3, color);
        SetPixelSafe(canvas, cx + i, cy + 3, color);
        SetPixelSafe(canvas, cx - 3, cy + i, color);
        SetPixelSafe(canvas, cx + 3, cy + i, color);
    }
    FillRectSafe(canvas, cx - 1, cy - 1, 3, 3, color);  // solid 3x3 center
}
void DrawCityMark(Canvas& canvas, int cx, int cy) {
    CityCtx ctx{cx, cy};
    DrawOutlined(canvas, CityDraw, &ctx, kBlack);  // 8 white halo copies + 1 ink
}

// ---- water grid-fill from a block's water samples -------------------------
// Reproduces the legacy DrawWaterMask look: for each water sample, fill the
// screen rect it projects to. Interior samples (all 4 neighbors water) get the
// sparse dot pattern in SCREEN space; boundary samples (a land neighbor) get a
// solid edge so the shoreline reads crisp. Water comes from the reserved
// elevation code (kElevWaterCode), burned by the host.
void DrawBlockWater(Canvas& canvas, const ParsedBlock& b, const BlockProjection& bp) {
    if (!b.codes) return;
    const int dim = winglet_terrain::kBlockDim;
    // A neighbor is "land" only if it is IN this block and not water. Off-block
    // neighbors (lx/ly at an edge) are treated as water, NOT land, so we don't
    // paint a false solid shoreline down every shared block edge — the adjacent
    // block (where that neighbor IS in-block) draws the real edge instead.
    auto land_neighbor = [&](int nx, int ny) {
        if (nx < 0 || ny < 0 || nx >= dim || ny >= dim) return false;  // off-block => not land
        return !b.SampleIsWater(nx, ny);
    };
    for (int ly = 0; ly < dim; ly++) {
        for (int lx = 0; lx < dim; lx++) {
            if (!b.SampleIsWater(lx, ly)) continue;
            int x0, y0, x1, y1;
            bp.LocalToPixel(lx, ly, &x0, &y0);
            bp.LocalToPixel(lx + 1, ly + 1, &x1, &y1);
            int xa = x0 < x1 ? x0 : x1, xb = x0 < x1 ? x1 : x0;
            int ya = y0 < y1 ? y0 : y1, yb = y0 < y1 ? y1 : y0;
            if (xb < 0 || xa >= canvas.width() || yb < 0 || ya >= canvas.height()) continue;
            bool boundary = land_neighbor(lx - 1, ly) || land_neighbor(lx + 1, ly) ||
                            land_neighbor(lx, ly - 1) || land_neighbor(lx, ly + 1);
            for (int sy = ya; sy < yb; sy++) {
                for (int sx = xa; sx < xb; sx++) {
                    if (boundary) {
                        SetPixelSafe(canvas, sx, sy, kBlack);            // solid shoreline
                    } else if ((sx & 3) == 1 && (sy & 3) == 1) {
                        SetPixelSafe(canvas, sx, sy, kBlack);            // sparse interior dots
                    }
                }
            }
        }
    }
}

// ---- vector rendering with importance thresholding ------------------------
// Take the prefix of points with importance >= threshold (points are stored
// descending), re-sort that prefix by seq, and draw in seq order. Returns the
// number of prefix points collected into `idx` (indices into pts).
int CollectPrefix(const VecPointV3* pts, int num_points, uint8_t threshold, int* idx) {
    int n = 0;
    for (int i = 0; i < num_points && n < kMaxPrefixPoints; i++) {
        if (pts[i].importance < threshold) break;  // sorted desc: rest are smaller
        idx[n++] = i;
    }
    // Insertion sort the prefix by seq ascending (small n).
    for (int i = 1; i < n; i++) {
        int v = idx[i];
        uint16_t vs = pts[v].seq;
        int j = i - 1;
        while (j >= 0 && pts[idx[j]].seq > vs) { idx[j + 1] = idx[j]; j--; }
        idx[j + 1] = v;
    }
    return n;
}

void DrawVecCell(Canvas& canvas, const VecCellBlob& cell, const CellProjection& cp,
                 uint8_t threshold) {
    if (!cell.data || cell.len == 0) return;
    VecCursor c{cell.data, cell.data + cell.len};
    VecRecordHeaderV3 h;
    const VecPointV3* pts;
    int idx[kMaxPrefixPoints];
    while (NextRecord(c, h, &pts)) {
        if (h.feature_type == winglet_terrain::kVecCityPoint) {
            if (h.num_points >= 1) {
                int px, py;
                cp.UVToPixel(pts[0].u, pts[0].v, &px, &py);
                DrawCityMark(canvas, px, py);
            }
            continue;
        }
        if (h.num_points < 2) continue;
        int n = CollectPrefix(pts, h.num_points, threshold, idx);
        if (n < 2) continue;

        bool road = (h.feature_type == winglet_terrain::kVecRoadMajor ||
                     h.feature_type == winglet_terrain::kVecRoadSecondary);
        int px0, py0;
        cp.UVToPixel(pts[idx[0]].u, pts[idx[0]].v, &px0, &py0);
        int phase = 0;
        for (int i = 1; i < n; i++) {
            int px1, py1;
            cp.UVToPixel(pts[idx[i]].u, pts[idx[i]].v, &px1, &py1);
            if (road) {
                phase = DrawDashedLine(canvas, px0, py0, px1, py1, /*on=*/3, /*off=*/2, kBlack, phase);
            } else {
                DrawLineClipped(canvas, px0, py0, px1, py1, kBlack);
            }
            px0 = px1; py0 = py1;
        }
        if ((h.flags & winglet_terrain::kVecFlagClosed) && !road) {  // close the ring
            int px1, py1;
            cp.UVToPixel(pts[idx[0]].u, pts[idx[0]].v, &px1, &py1);
            DrawLineClipped(canvas, px0, py0, px1, py1, kBlack);
        }
    }
}
}  // namespace

// ---- MapProjection --------------------------------------------------------
MapProjection MapProjection::FromData(const MapScreenData& d) {
    MapProjection m;
    m.ownship_lat = d.ownship_lat_deg;
    m.ownship_lon = d.ownship_lon_deg;
    m.coslat = cosf(d.ownship_lat_deg * kPi / 180.0f);
    m.px_per_nm = (d.range_nm > 0.01f) ? (kOuterRingRadiusPx / d.range_nm) : 0.0f;
    m.valid = d.ownship_valid && m.px_per_nm > 0.0f;
    return m;
}

void MapProjection::GeoToPixel(float lat_deg, float lon_deg, int* px, int* py) const {
    float dnm_n = (lat_deg - ownship_lat) * kNmPerDegLat;
    float dnm_e = (lon_deg - ownship_lon) * kNmPerDegLat * coslat;
    *px = kMapCenterX + IRound(dnm_e * px_per_nm);
    *py = kMapCenterY - IRound(dnm_n * px_per_nm);
}

// ---- BlockProjection (affine block-local sample -> pixel) -----------------
BlockProjection BlockProjection::FromBlock(const winglet_terrain::ParsedBlock& b,
                                           const MapProjection& mp) {
    // NW (top-left) sample lat/lon of the block is the affine bias.
    float lat_nw, lon_nw;
    TerrainLoader::BlockLocalToLatLon(b.level, b.bx, b.by, 0, 0, &lat_nw, &lon_nw);
    float dps = TerrainLoader::DegPerSample(b.level);

    float k_e = kNmPerDegLat * mp.coslat * mp.px_per_nm;
    float k_n = kNmPerDegLat * mp.px_per_nm;

    BlockProjection bp;
    // lon(lx) = lon_nw + lx*dps ; px = kMapCenterX + (lon-olon)*k_e
    bp.px_per_lx = k_e * dps;
    bp.px_bias = kMapCenterX + k_e * (lon_nw - mp.ownship_lon);
    // lat(ly) = lat_nw - ly*dps (row 0 = north) ; py = kMapCenterY - (lat-olat)*k_n
    bp.py_per_ly = k_n * dps;  // +: ly increases south => py increases
    bp.py_bias = kMapCenterY - k_n * (lat_nw - mp.ownship_lat);
    return bp;
}

void BlockProjection::LocalToPixel(int lx, int ly, int* px, int* py) const {
    *px = IRound(px_bias + lx * px_per_lx);
    *py = IRound(py_bias + ly * py_per_ly);
}

// ---- CellProjection (affine super-cell u,v -> pixel) ----------------------
CellProjection CellProjection::FromCell(int cell_row, int cell_col, const MapProjection& mp) {
    float lat0 = winglet_terrain::kCellLat0E6 / 1e6f + cell_row * winglet_terrain::kSupercellDeg;
    float lon0 = winglet_terrain::kCellLon0E6 / 1e6f + cell_col * winglet_terrain::kSupercellDeg;
    float span = winglet_terrain::kSupercellDeg;

    float k_e = kNmPerDegLat * mp.coslat * mp.px_per_nm;
    float k_n = kNmPerDegLat * mp.px_per_nm;
    float dlon_per_u = span / 65535.0f;
    float dlat_per_v = span / 65535.0f;

    CellProjection cp;
    cp.px_per_u = k_e * dlon_per_u;
    cp.px_bias = kMapCenterX + k_e * (lon0 - mp.ownship_lon);
    cp.py_per_v = -k_n * dlat_per_v;  // v grows north => py decreases
    cp.py_bias = kMapCenterY - k_n * (lat0 - mp.ownship_lat);
    return cp;
}

void CellProjection::UVToPixel(uint16_t u, uint16_t v, int* px, int* py) const {
    *px = IRound(px_bias + u * px_per_u);
    *py = IRound(py_bias + v * py_per_v);
}

// Importance threshold (8-bit) from zoom: coarser zoom keeps only high-importance
// vertices so on-screen vertex density stays roughly constant. Importance is
// host-log-quantized to 0..255 (endpoints/cities = 255, always kept). We map the
// zoom range onto that domain monotonically: at the closest ladder zoom keep
// nearly all vertices, and raise the cut as we zoom out. The scale constant is a
// visual-quality tuning knob to refine on the real 1-bit e-paper (per the plan).
static uint8_t ImportanceThreshold(float range_nm) {
    // px per nm; smaller (far zoom) => higher threshold. Reference the closest
    // ladder stop (~20 NM) as "keep most" and grow ~log-linearly with range.
    // threshold ~= k * log2(range/20), clamped to [0, 254].
    float ratio = range_nm / 20.0f;
    if (ratio < 1.0f) ratio = 1.0f;
    float t = 24.0f * log2f(ratio);  // 20NM->0, 40NM->24, 80->48, 160->72, ...
    int q = (int)lroundf(t);
    if (q < 0) q = 0;
    if (q > 254) q = 254;
    return (uint8_t)q;
}

// Rasterize every overlapping block's water fill + every overlapping vector cell.
// Layer order: water fill (background) -> vector strokes (coastline/lake/river)
// -> roads (dashed) -> city marks (haloed, on top).
static void RasterizeTerrain(Canvas& canvas, const MapScreenData& data,
                             const TerrainLoader& loader, const MapProjection& mp) {
    // Water grid-fill from the overlapping blocks at the selected level.
    const ParsedBlock* blocks[TerrainLoader::kMaxViewBlocks];
    int nb = loader.GetOverlappingBlocks(blocks, TerrainLoader::kMaxViewBlocks);
    for (int i = 0; i < nb; i++) {
        BlockProjection bp = BlockProjection::FromBlock(*blocks[i], mp);
        DrawBlockWater(canvas, *blocks[i], bp);
    }

    // Vector strokes from the overlapping super-cells.
    const VecCellBlob* cells[TerrainLoader::kMaxViewCells];
    int nc = loader.GetOverlappingVecCells(cells, TerrainLoader::kMaxViewCells);
    uint8_t threshold = ImportanceThreshold(data.range_nm);
    for (int i = 0; i < nc; i++) {
        CellProjection cp = CellProjection::FromCell(cells[i]->cell_row, cells[i]->cell_col, mp);
        DrawVecCell(canvas, *cells[i], cp, threshold);
    }
}

// ---- Terrain cache --------------------------------------------------------
// Rasterizing terrain is expensive (water scan + vector streaming over many
// blocks/cells) but the result only changes when the ownship pan / zoom / level /
// overlapping-set crosses a threshold. Cache the raster in a PSRAM 1-bit
// framebuffer and, every frame, just memcpy it. The expensive path runs only on
// invalidation.
class TerrainCache {
   public:
    ~TerrainCache() { delete cache_; }

    void DrawInto(Canvas& target, const MapScreenData& data, const TerrainLoader& loader,
                  const MapProjection& mp) {
        if (cache_ == nullptr || cache_->byte_size() != target.byte_size()) {
            delete cache_;
            cache_ = new Canvas(target.CreateCompatible(MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT));
            if (!cache_->ok()) {
                delete cache_;
                cache_ = new Canvas(target.CreateCompatible(MALLOC_CAP_8BIT));
            }
            valid_ = false;
        }
        if (!cache_->ok()) {  // alloc failed -> rasterize live into the target
            RasterizeTerrain(target, data, loader, mp);
            return;
        }

        // Invalidation key: selected level + overlapping block-set + vec-cell-set
        // signatures + quantized pan + quantized zoom.
        int level = loader.SelectedLevel();
        int32_t lat_q = (int32_t)lroundf(data.ownship_lat_deg * mp.px_per_nm * kNmPerDegLat);
        int32_t lon_q = (int32_t)lroundf(data.ownship_lon_deg * mp.px_per_nm * kNmPerDegLat);

        uint32_t block_sig = 0;
        const ParsedBlock* blocks[TerrainLoader::kMaxViewBlocks];
        int nb = loader.GetOverlappingBlocks(blocks, TerrainLoader::kMaxViewBlocks);
        for (int i = 0; i < nb; i++)
            block_sig = block_sig * 131 + (uint32_t)(blocks[i]->bx * 4096 + blocks[i]->by) + 1;

        uint32_t cell_sig = 0;
        const VecCellBlob* cells[TerrainLoader::kMaxViewCells];
        int nc = loader.GetOverlappingVecCells(cells, TerrainLoader::kMaxViewCells);
        for (int i = 0; i < nc; i++)
            cell_sig = cell_sig * 131 + (uint32_t)cells[i]->cell_index + 1;

        int32_t zoom_q = (int32_t)lroundf(mp.px_per_nm * 1000.0f);

        bool key_same = valid_ && level == key_level_ && lat_q == key_lat_q_ &&
                        lon_q == key_lon_q_ && block_sig == key_block_sig_ &&
                        cell_sig == key_cell_sig_ && zoom_q == key_zoom_q_;
        if (!key_same) {
            cache_->Clear(kWhite);
            RasterizeTerrain(*cache_, data, loader, mp);
            valid_ = true;
            key_level_ = level; key_lat_q_ = lat_q; key_lon_q_ = lon_q;
            key_block_sig_ = block_sig; key_cell_sig_ = cell_sig; key_zoom_q_ = zoom_q;
        }
        target.CopyFrom(*cache_);
    }

   private:
    Canvas* cache_ = nullptr;
    bool valid_ = false;
    int key_level_ = -1;
    int32_t key_lat_q_ = 0, key_lon_q_ = 0;
    uint32_t key_block_sig_ = 0, key_cell_sig_ = 0;
    int32_t key_zoom_q_ = -1;
};

static TerrainCache g_terrain_cache;

// ---- DrawTerrain ----------------------------------------------------------
void DrawTerrain(Canvas& target, const MapScreenData& data, const TerrainLoader& loader) {
    MapProjection mp = MapProjection::FromData(data);
    if (!mp.valid) return;
    // Terrain now renders at all zoom ranges (the 40 NM gate is removed): the
    // pyramid serves the right level for any zoom.
    g_terrain_cache.DrawInto(target, data, loader, mp);
}

}  // namespace winglet_ui
