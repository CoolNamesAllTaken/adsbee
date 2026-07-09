#include "map_screen.hh"

#include <cmath>
#include <cstdio>

#include "GUI_Paint.h"
#include "fonts.h"
#include "ui_primitives.hh"
#include "ui_sprites.hh"

namespace winglet_ui {

namespace {
constexpr float kPi = 3.14159265358979323846f;
constexpr float kNmPerDegLat = 60.0f;  // 1 deg latitude ~= 60 nautical miles.

// Radius (px) of the outer range ring. Chosen to sit inside the map window
// (between the rails, above the scale bar), so the full ring is visible.
constexpr float kOuterRingRadiusPx = 70.0f;

inline int IRound(float v) { return (int)lroundf(v); }

// Halo context + callback so the ownship crosshair can be drawn 9x (8 white
// neighbors + 1 ink) via DrawOutlined. (Arrows and the scale bar now use
// pre-baked sprites instead of live haloed drawing.)
struct CrossCtx {
    int cx, cy;
};
void CrossDraw(int dx, int dy, UWORD color, void* ctx) {
    auto* c = static_cast<CrossCtx*>(ctx);
    DrawCrosshair(c->cx + dx, c->cy + dy, color);
}

}  // namespace

void DrawMapScreen(const MapScreenData& data) {
    // ---- Map content (drawn first, then masked by the rail gutters) -------
    // Range rings: outer at range_nm, inner at half range. These replace the
    // decorative terrain from the mockup and give a real distance reference.
    DrawRing(kMapCenterX, kMapCenterY, kOuterRingRadiusPx, 0, BLACK);
    DrawRing(kMapCenterX, kMapCenterY, kOuterRingRadiusPx * 0.5f, 0, BLACK);

    // pixels-per-nm derived from the outer ring representing range_nm.
    float px_per_nm =
        (data.range_nm > 0.01f) ? (kOuterRingRadiusPx / data.range_nm) : 0.0f;

    // Traffic contacts, projected relative to ownship (equirectangular). Each
    // arrow gets a white halo so it lifts off the range rings.
    if (data.ownship_valid && px_per_nm > 0.0f && data.contacts) {
        float coslat = cosf(data.ownship_lat_deg * kPi / 180.0f);
        for (uint16_t i = 0; i < data.num_contacts; i++) {
            const UiContact& ct = data.contacts[i];
            float dnm_n = (ct.lat_deg - data.ownship_lat_deg) * kNmPerDegLat;
            float dnm_e = (ct.lon_deg - data.ownship_lon_deg) * kNmPerDegLat * coslat;
            int px = kMapCenterX + IRound(dnm_e * px_per_nm);   // east = +x
            int py = kMapCenterY - IRound(dnm_n * px_per_nm);   // north = -y
            // Skip contacts outside the map window so an off-edge arrow can't
            // land on the rails, scale bar, or zoom text.
            if (px < kLeftRailDividerX || px > kRightRailDividerX) continue;
            if (py < 0 || py >= kScreenHeight) continue;
            if (ct.selected) DrawRing(px, py, 8, 0, BLACK);
            // Blit the pre-rotated, pre-haloed arrow for this heading (1° steps)
            // instead of drawing a rotated polygon 9x.
            int heading = ((int)lroundf(ct.direction_deg) % 360 + 360) % 360;
            BlitSprite2bpp(px - kArrowSpriteCenterX, py - kArrowSpriteCenterY,
                           kArrowSprites[heading], /*ink=*/BLACK, /*halo=*/WHITE);
        }
    }

    // Ownship crosshair at map center (haloed).
    CrossCtx cctx{kMapCenterX, kMapCenterY};
    DrawOutlined(CrossDraw, &cctx, BLACK);

    // ---- Mask the rail gutters, then draw the dividers --------------------
    FillRectSafe(0, 0, kLeftRailDividerX, kScreenHeight, WHITE);
    FillRectSafe(kRightRailDividerX, 0, kScreenWidth - kRightRailDividerX, kScreenHeight, WHITE);
    FillRectSafe(kLeftRailDividerX, 0, 2, kScreenHeight, BLACK);
    FillRectSafe(kRightRailDividerX - 1, 0, 2, kScreenHeight, BLACK);

    // ---- Left rail: status values (right-justified, ink-centered on rows) --
    for (int i = 0; i < kNumRailRows; i++) {
        const char* v = data.rail[i];
        if (v && *v)
            DrawTextRightAlignedVCentered(kLeftRailDividerX, kLeftRailRowY[i], v, &Font16, BLACK);
    }

    // Battery value + glyph near the bottom of the left rail. The frame is a
    // pre-baked sprite; only the internal fill bar is drawn live from pct.
    if (data.batt_valid) {
        char buf[8];
        snprintf(buf, sizeof(buf), "%u", data.batt_pct);
        DrawTextRightAlignedVCentered(kLeftRailDividerX, kBatteryValueRowY, buf, &Font16, BLACK);
        BlitSprite(kBatteryGlyphX, kBatteryGlyphY, kBatteryFrameSprite, BLACK);
        // Fill bar: matches DrawBattery (bw=15, bh=9 -> inner fill at +2,+2).
        int fill = (int)lroundf((15 - 4) * (data.batt_pct / 100.0f));
        FillRectSafe(kBatteryGlyphX + 2, kBatteryGlyphY + 2, fill, 9 - 4, BLACK);
    }

    // ---- Right rail: icon column aligned to Up / OK / Down buttons ---------
    // Pre-baked sprites (centered), blitted instead of re-rasterized each frame.
    BlitSprite(kRightIconColumnX - kZoomInSprite.w / 2, kRightIconRowY[0] - kZoomInSprite.h / 2,
               kZoomInSprite, BLACK);  // zoom in
    BlitSprite(kRightIconColumnX - kGearSprite.w / 2, kRightIconRowY[1] - kGearSprite.h / 2,
               kGearSprite, BLACK);  // menu
    BlitSprite(kRightIconColumnX - kZoomOutSprite.w / 2, kRightIconRowY[2] - kZoomOutSprite.h / 2,
               kZoomOutSprite, BLACK);  // zoom out

    // ---- Zoom label + scale bar (bottom right, haloed) --------------------
    const char* zoom = data.zoom_label ? data.zoom_label : "5NM";
    // haloed text: draw white glyph copies at the 8 offsets, then black.
    for (int oy = -1; oy <= 1; oy++)
        for (int ox = -1; ox <= 1; ox++) {
            if (ox == 0 && oy == 0) continue;
            DrawTextRightAligned(kZoomTextX + ox, kZoomTextY + oy, zoom, &Font12, WHITE);
        }
    DrawTextRightAligned(kZoomTextX, kZoomTextY, zoom, &Font12, BLACK);

    // Scale bar: pre-baked haloed sprite. Its origin offset maps the sprite's
    // top-left to the (x1, bar_y) reference the live drawer used.
    int scale_x1 = kScaleBarEndX - kScaleBarWidth;
    BlitSprite2bpp(scale_x1 - kScaleBarSpriteOriginX, kScaleBarY - kScaleBarSpriteOriginY,
                   kScaleBarSprite, /*ink=*/BLACK, /*halo=*/WHITE);
}

}  // namespace winglet_ui
