#ifndef UI_DATA_HH_
#define UI_DATA_HH_

#include <cstdint>

namespace winglet_terrain {
class TerrainLoader;  // fwd decl; keeps the UI layer light (no terrain headers here)
}

// Shared data structures and layout constants for the Winglet UI screens.
//
// The UI is rendered at the device's native e-paper resolution in the
// ROTATE_270 drawing space, which presents as 264 wide x 176 tall with upright
// text (see Paint_NewImage() in app_main). All coordinates below are in that
// space and are carried verbatim from the Claude Design reference renderer
// (winglet-draw.js, WD.productExp).

namespace winglet_ui {

// ---- Screen geometry ------------------------------------------------------
constexpr int kScreenWidth = 264;
constexpr int kScreenHeight = 176;

// Vertical dividers separating the left status rail and right icon rail from
// the central map. Each is a 2px-wide full-height black bar.
constexpr int kLeftRailDividerX = 28;
constexpr int kRightRailDividerX = 236;

// Ownship / map center.
constexpr int kMapCenterX = 132;
constexpr int kMapCenterY = 84;

// Map projection scale: the outer range ring's radius (px) represents range_nm,
// so pixels-per-nm = kOuterRingRadiusPx / range_nm. Shared by the map screen and
// the terrain renderer so both use one identical projection.
constexpr float kOuterRingRadiusPx = 70.0f;
constexpr float kNmPerDegLat = 60.0f;  // 1 deg latitude ~= 60 nautical miles

// Left-rail value rows align to the etched port labels (CO / GNSS / SUBG /
// 2.4G / 1090) on the physical device.
constexpr int kLeftRailRowY[5] = {9, 40, 71, 101, 133};

// Right-rail icon rows align to the physical Up / OK / Down buttons.
constexpr int kRightIconRowY[3] = {22, 88, 154};
constexpr int kRightIconColumnX = (kRightRailDividerX + kScreenWidth) / 2;  // 250

// Battery indicator: value ink-centered on a row mirrored from the top port
// spacing, glyph sitting just above it.
constexpr int kBatteryGlyphX = kLeftRailDividerX - 19;  // 9
constexpr int kBatteryGlyphY = 148;
constexpr int kBatteryValueRowY = kScreenHeight - kLeftRailRowY[0];  // 167

// Zoom-level text and scale bar (bottom right of the map, left of the divider).
constexpr int kZoomTextX = kRightRailDividerX - 4;  // 232
constexpr int kZoomTextY = 162;
constexpr int kScaleBarWidth = 42;
// Moved left (was -31 = 205) to make room for the 3-digit zoom label ("200NM",
// left edge ~x177), settled halfway between the original and the fully-left
// position. Bar now spans 145..187.
constexpr int kScaleBarEndX = kRightRailDividerX - 49;  // 187
constexpr int kScaleBarY = 170;

constexpr int kNumRailRows = 5;

// ---- Screen selection -----------------------------------------------------
enum class UiScreen {
    kMap,       // WD.productExp render: moving-map / radar scope with traffic.
    kSettings,  // WD.settings render (stubbed for now).
    kDebug,     // Existing sensor telemetry dump (kept, made navigable).
};

// ---- Zoom ladder ----------------------------------------------------------
// Fixed map ranges (outer-ring radius in nautical miles), aviation-relevant.
// Up button = zoom in (smaller index), Down = zoom out (larger index).
constexpr float kZoomLadderNm[] = {20.0f, 40.0f, 80.0f, 150.0f, 200.0f};
constexpr int kNumZoomLevels = (int)(sizeof(kZoomLadderNm) / sizeof(kZoomLadderNm[0]));
constexpr int kDefaultZoomIndex = 0;  // 20 NM (closest)

// ---- Map screen data ------------------------------------------------------
// One traffic contact to plot. Positions are geographic; the map screen
// projects them relative to ownship at render time.
struct UiContact {
    float lat_deg;
    float lon_deg;
    float direction_deg;    // Track, or heading if dir_is_heading.
    bool dir_is_heading;
    bool selected;
};

// Everything the map screen needs to render one frame. The caller
// (app_main) fills this from live sources each loop; the draw function owns
// the geographic->pixel projection.
struct MapScreenData {
    const UiContact* contacts;
    uint16_t num_contacts;  // No UI cap; the aircraft dictionary self-bounds.

    bool ownship_valid;     // False when no receiver position fix is available.
    float ownship_lat_deg;
    float ownship_lon_deg;

    float range_nm;         // Map radius represented by the outer range ring.
    const char* zoom_label;  // e.g. "5NM"; shown next to the scale bar.

    // Left-rail status strings (CO / GNSS / SUBG / 2.4G / 1090), pre-formatted
    // by the caller. Any entry may be nullptr/empty to skip that row.
    const char* rail[kNumRailRows];

    uint8_t batt_pct;
    bool batt_valid;

    // Terrain source (null => skip terrain). Set by app_main from the loader.
    const winglet_terrain::TerrainLoader* terrain = nullptr;
};

}  // namespace winglet_ui

#endif  // UI_DATA_HH_
