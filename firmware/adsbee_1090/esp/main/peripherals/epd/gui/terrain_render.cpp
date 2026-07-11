#include "terrain_render.hh"

#include <cmath>
#include <cstdint>
#include <cstring>

#include "GUI_Paint.h"
#include "esp_heap_caps.h"
#include "esp_log.h"
#include "peripherals/terrain/terrain_tile.hh"
#include "ui_primitives.hh"

namespace winglet_ui {

namespace {
constexpr float kPi = 3.14159265358979323846f;
inline int IRound(float v) { return (int)lroundf(v); }

using winglet_terrain::ParsedTile;
using winglet_terrain::VecPoint;
using winglet_terrain::VecRecordHeader;

// ---- vector record streamer ----------------------------------------------
// Zero-copy cursor over a concatenated vector block.
struct VecCursor {
    const uint8_t* p;
    const uint8_t* end;
};

// Decode the next record: header + (optional name) + points. Returns false at
// end / on truncation. `pts` points into the block (little-endian VecPoint).
bool NextRecord(VecCursor& c, VecRecordHeader& h, const VecPoint** pts) {
    if (c.p + sizeof(VecRecordHeader) > c.end) return false;
    __builtin_memcpy(&h, c.p, sizeof(h));
    const uint8_t* q = c.p + sizeof(VecRecordHeader);
    if (h.flags & winglet_terrain::kVecFlagHasName) {
        if (q >= c.end) return false;
        uint8_t name_len = *q++;
        q += name_len;
    }
    const uint8_t* pt_start = q;
    q += (size_t)h.num_points * sizeof(VecPoint);
    if (q > c.end) return false;
    *pts = reinterpret_cast<const VecPoint*>(pt_start);
    c.p = q;
    return true;
}

// ---- city mark (haloed 7x7 ring + 3x3 center) ----------------------------
struct CityCtx { int cx, cy; };
void CityDraw(int dx, int dy, UWORD color, void* ctx) {
    auto* c = static_cast<CityCtx*>(ctx);
    int cx = c->cx + dx, cy = c->cy + dy;
    for (int i = -3; i <= 3; i++) {  // 7x7 outline
        SetPixelSafe(cx + i, cy - 3, color);
        SetPixelSafe(cx + i, cy + 3, color);
        SetPixelSafe(cx - 3, cy + i, color);
        SetPixelSafe(cx + 3, cy + i, color);
    }
    FillRectSafe(cx - 1, cy - 1, 3, 3, color);  // solid 3x3 center
}
void DrawCityMark(int cx, int cy) {
    CityCtx ctx{cx, cy};
    DrawOutlined(CityDraw, &ctx, BLACK);  // 8 white halo copies + 1 ink
}

// ---- water mask fill (interior sparse dots + solid shoreline) -------------
// Iterate the tile's water mask; for each water cell, fill the screen rect it
// projects to. Interior cells (all 4 neighbors water) get the sparse dot
// pattern in SCREEN space; boundary cells (a land neighbor) get a solid edge so
// the shoreline reads crisp. Coarse mask + dense screen => rects a few px wide.
void DrawWaterMask(const ParsedTile& t, const TileProjection& tp) {
    if (!t.water_mask) return;
    int gw = t.mask_w, gh = t.mask_h;
    for (int gy = 0; gy < gh; gy++) {
        for (int gx = 0; gx < gw; gx++) {
            if (!t.IsWater(gx, gy)) continue;
            // Screen rect for this cell: project this node and the +1,+1 node.
            int x0, y0, x1, y1;
            tp.GridToPixel(gx, gy, gw, gh, &x0, &y0);
            tp.GridToPixel(gx + 1, gy + 1, gw, gh, &x1, &y1);
            int xa = x0 < x1 ? x0 : x1, xb = x0 < x1 ? x1 : x0;
            int ya = y0 < y1 ? y0 : y1, yb = y0 < y1 ? y1 : y0;
            // Whole cell off-screen? skip cheaply.
            if (xb < 0 || xa >= kScreenWidth || yb < 0 || ya >= kScreenHeight) continue;
            bool boundary = !t.IsWater(gx - 1, gy) || !t.IsWater(gx + 1, gy) ||
                            !t.IsWater(gx, gy - 1) || !t.IsWater(gx, gy + 1);
            for (int sy = ya; sy < yb; sy++) {
                for (int sx = xa; sx < xb; sx++) {
                    if (boundary) {
                        SetPixelSafe(sx, sy, BLACK);            // solid shoreline
                    } else if ((sx & 3) == 1 && (sy & 3) == 1) {
                        SetPixelSafe(sx, sy, BLACK);            // sparse interior dots
                    }
                }
            }
        }
    }
}

// ---- water vectors: solid shoreline strokes -------------------------------
void DrawWaterVectors(const ParsedTile& t, const TileProjection& tp) {
    if (!t.vec_water) return;
    VecCursor c{t.vec_water, t.vec_water + t.vec_water_len};
    VecRecordHeader h;
    const VecPoint* pts;
    while (NextRecord(c, h, &pts)) {
        if (h.num_points < 2) continue;
        int px0, py0;
        tp.UVToPixel(pts[0].u, pts[0].v, &px0, &py0);
        for (uint16_t i = 1; i < h.num_points; i++) {
            int px1, py1;
            tp.UVToPixel(pts[i].u, pts[i].v, &px1, &py1);
            DrawLineClipped(px0, py0, px1, py1, BLACK);
            px0 = px1; py0 = py1;
        }
        if (h.flags & winglet_terrain::kVecFlagClosed) {  // close the ring
            int px1, py1;
            tp.UVToPixel(pts[0].u, pts[0].v, &px1, &py1);
            DrawLineClipped(px0, py0, px1, py1, BLACK);
        }
    }
}

// ---- roads (dashed, no smoothing) + city marks ----------------------------
void DrawRoadsAndCities(const ParsedTile& t, const TileProjection& tp) {
    if (!t.vec_road) return;
    VecCursor c{t.vec_road, t.vec_road + t.vec_road_len};
    VecRecordHeader h;
    const VecPoint* pts;
    while (NextRecord(c, h, &pts)) {
        if (h.feature_type == winglet_terrain::kVecCityPoint) {
            if (h.num_points >= 1) {
                int px, py;
                tp.UVToPixel(pts[0].u, pts[0].v, &px, &py);
                DrawCityMark(px, py);
            }
            continue;
        }
        // Roads: dashed polyline with a continuous dash phase across segments.
        if (h.num_points < 2) continue;
        int px0, py0;
        tp.UVToPixel(pts[0].u, pts[0].v, &px0, &py0);
        int phase = 0;
        for (uint16_t i = 1; i < h.num_points; i++) {
            int px1, py1;
            tp.UVToPixel(pts[i].u, pts[i].v, &px1, &py1);
            phase = DrawDashedLine(px0, py0, px1, py1, /*on=*/3, /*off=*/2, BLACK, phase);
            px0 = px1; py0 = py1;
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

// ---- TileProjection (affine u,v -> pixel) ---------------------------------
TileProjection TileProjection::FromTile(const winglet_terrain::ParsedTile& t,
                                        const MapProjection& mp) {
    float lat0 = t.hdr.tile_lat0_e6 * 1e-6f;   // SW corner
    float lon0 = t.hdr.tile_lon0_e6 * 1e-6f;
    float span = t.hdr.tile_span_e3 * 1e-3f;   // degrees (typically 1.0)

    // px = kMapCenterX + (lon - olon)*60*coslat*ppnm ; lon = lon0 + u/65535*span
    // py = kMapCenterY - (lat - olat)*60*ppnm        ; lat = lat0 + v/65535*span
    float k_e = kNmPerDegLat * mp.coslat * mp.px_per_nm;
    float k_n = kNmPerDegLat * mp.px_per_nm;
    float dlon_per_u = span / 65535.0f;
    float dlat_per_v = span / 65535.0f;

    TileProjection tp;
    tp.px_per_u = k_e * dlon_per_u;
    tp.px_bias = kMapCenterX + k_e * (lon0 - mp.ownship_lon);
    tp.py_per_v = -k_n * dlat_per_v;
    tp.py_bias = kMapCenterY - k_n * (lat0 - mp.ownship_lat);
    return tp;
}

void TileProjection::UVToPixel(uint16_t u, uint16_t v, int* px, int* py) const {
    *px = IRound(px_bias + u * px_per_u);
    *py = IRound(py_bias + v * py_per_v);
}

void TileProjection::GridToPixel(int gx, int gy, int grid_w, int grid_h, int* px, int* py) const {
    // Grid is row 0 = north (top), col 0 = west. u increases east with gx, v
    // increases north — but grid row 0 (gy=0) is north, so v = (grid_h-1-gy).
    float u = (grid_w > 1) ? (float)gx / (grid_w - 1) * 65535.0f : 0.0f;
    float v = (grid_h > 1) ? (float)(grid_h - 1 - gy) / (grid_h - 1) * 65535.0f : 0.0f;
    *px = IRound(px_bias + u * px_per_u);
    *py = IRound(py_bias + v * py_per_v);
}

// Rasterize every overlapping tile's terrain into the currently-selected Paint
// image. Layer order per tile: water fill (background texture) -> water
// shoreline strokes -> roads (dashed) -> city marks (haloed, on top).
static void RasterizeTerrain(const MapScreenData& data,
                             const winglet_terrain::TerrainLoader& loader,
                             const MapProjection& mp) {
    const winglet_terrain::ParsedTile* tiles[winglet_terrain::TerrainLoader::kMaxOverlap];
    int n = loader.GetOverlappingTiles(tiles, winglet_terrain::TerrainLoader::kMaxOverlap);
    for (int i = 0; i < n; i++) {
        const winglet_terrain::ParsedTile& t = *tiles[i];
        TileProjection tp = TileProjection::FromTile(t, mp);
        DrawWaterMask(t, tp);
        DrawWaterVectors(t, tp);
        DrawRoadsAndCities(t, tp);
    }
}

// ---- Terrain cache --------------------------------------------------------
// Rasterizing terrain is expensive (mask scan + vector streaming over up to 4
// tiles) but the result only changes when the ownship tile / zoom / pan crosses
// a threshold. Cache the raster in a PSRAM 1-bit framebuffer and, every frame,
// just memcpy it as the base. The expensive path runs only on invalidation.
class TerrainCache {
   public:
    // Rebuild if the key changed; then copy the cached layer into `dst`.
    void DrawInto(uint8_t* dst, int fb_bytes, const MapScreenData& data,
                  const winglet_terrain::TerrainLoader& loader, const MapProjection& mp) {
        if (fb_ == nullptr || fb_bytes_ != fb_bytes) {
            if (fb_) heap_caps_free(fb_);
            fb_ = (uint8_t*)heap_caps_malloc(fb_bytes, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
            if (!fb_) fb_ = (uint8_t*)heap_caps_malloc(fb_bytes, MALLOC_CAP_8BIT);
            fb_bytes_ = fb_bytes;
            valid_ = false;
        }
        if (!fb_) {  // alloc failed -> fall back to rasterizing live into dst
            RasterizeTerrain(data, loader, mp);
            return;
        }

        // Invalidation key. Quantize ownship to ~1 px of pan so small movement
        // still refreshes; also fold in the overlapping tile-set signature so a
        // late-loaded tile forces one rebuild.
        int row = -1, col = -1;
        winglet_terrain::TerrainLoader::TileIndexForLatLon(data.ownship_lat_deg,
                                                           data.ownship_lon_deg, &row, &col);
        int32_t lat_q = (int32_t)lroundf(data.ownship_lat_deg * mp.px_per_nm * kNmPerDegLat);
        int32_t lon_q = (int32_t)lroundf(data.ownship_lon_deg * mp.px_per_nm * kNmPerDegLat);
        uint32_t set_sig = 0;
        const winglet_terrain::ParsedTile* tiles[winglet_terrain::TerrainLoader::kMaxOverlap];
        int n = loader.GetOverlappingTiles(tiles, winglet_terrain::TerrainLoader::kMaxOverlap);
        for (int i = 0; i < n; i++)
            set_sig = set_sig * 131 + (uint32_t)(tiles[i]->row * 512 + tiles[i]->col) + 1;
        // Quantize the zoom scale so the key never depends on exact float equality.
        int32_t zoom_q = (int32_t)lroundf(mp.px_per_nm * 1000.0f);

        bool key_same = valid_ && row == key_row_ && col == key_col_ && lat_q == key_lat_q_ &&
                        lon_q == key_lon_q_ && set_sig == key_set_sig_ && zoom_q == key_zoom_q_;
        if (!key_same) {
            // Rebuild the cached terrain layer.
            uint8_t* prev = Paint.Image;
            Paint_SelectImage(fb_);
            Paint_Clear(WHITE);
            RasterizeTerrain(data, loader, mp);
            Paint_SelectImage(prev);
            valid_ = true;
            key_row_ = row; key_col_ = col; key_lat_q_ = lat_q; key_lon_q_ = lon_q;
            key_set_sig_ = set_sig; key_zoom_q_ = zoom_q;
        }
        memcpy(dst, fb_, fb_bytes_);
    }

   private:
    uint8_t* fb_ = nullptr;
    int fb_bytes_ = 0;
    bool valid_ = false;
    int key_row_ = -1, key_col_ = -1;
    int32_t key_lat_q_ = 0, key_lon_q_ = 0;
    uint32_t key_set_sig_ = 0;
    int32_t key_zoom_q_ = -1;
};

static TerrainCache g_terrain_cache;

// ---- DrawTerrain ----------------------------------------------------------
void DrawTerrain(const MapScreenData& data, const winglet_terrain::TerrainLoader& loader) {
    MapProjection mp = MapProjection::FromData(data);
    if (!mp.valid) return;
    // Only draw terrain at close zoom, where the 4-tile set can cover the screen.
    if (data.range_nm > winglet_terrain::kTerrainMaxRangeNm) return;
    int fb_bytes = Paint.WidthByte * Paint.HeightByte;
    g_terrain_cache.DrawInto(Paint.Image, fb_bytes, data, loader, mp);
}

}  // namespace winglet_ui
