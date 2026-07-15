#ifndef SCREEN_MANAGER_HH_
#define SCREEN_MANAGER_HH_

#include <cstdint>

#include "canvas.hh"        // For Canvas (draw target).
#include "debug_screen.hh"  // For DebugScreenSources.
#include "ui_data.hh"       // For UiScreen, zoom ladder, MapScreenData.

// Forward declarations to keep this header light; the .cpp includes the full
// headers for the ADS-B dictionary and terrain loader.
class AircraftDictionary;
namespace winglet_terrain {
class TerrainLoader;
}

namespace winglet_ui {

// Everything the map screen needs from the application, in raw form. The
// ScreenManager marshals this into a MapScreenData (contact list, rail strings,
// zoom label) at draw time. Kept as a plain bundle so app_main only has to
// gather values, not build the UI struct.
struct MapDataSources {
    const AircraftDictionary& dict;  // Traffic contacts + Mode S / UAT metrics.

    bool ownship_valid;              // Receiver position fix available.
    float ownship_lat_deg;
    float ownship_lon_deg;

    uint8_t gnss_num_satellites;     // From the RP2040 metrics (forwarded over SPI).
    bool wifi_up;                    // Wi-Fi link state (STA has IP or AP has clients).

    uint8_t batt_pct;
    bool batt_valid;

    const winglet_terrain::TerrainLoader* terrain;  // null => skip terrain.
};

// Owns the Winglet UI navigation state (current screen + zoom level), the
// button handling that drives it, and the per-frame marshalling + dispatch to
// the individual screens. Constructed once by the application.
class ScreenManager {
   public:
    ScreenManager() = default;

    // Advances navigation from the raw active-low front-panel button inputs
    // (Expander B bits 0-3: bit0=Enter/Back, bit1=Down/zoom-out, bit2=OK,
    // bit3=Up/zoom-in). Edge-triggered: fires once per press.
    void HandleButtons(uint8_t button_bits);

    // Renders the current screen into `c`. Clears the canvas, builds
    // MapScreenData from `map_src`, and dispatches to the map / settings / debug
    // screen. `debug_src` supplies the debug screen's live sensor references.
    void Draw(Canvas& c, const MapDataSources& map_src, const DebugScreenSources& debug_src);

    UiScreen current_screen() const { return current_screen_; }
    int zoom_index() const { return zoom_index_; }

   private:
    UiScreen current_screen_ = UiScreen::kMap;
    int      zoom_index_     = kDefaultZoomIndex;
    uint8_t  prev_buttons_   = 0xFF;  // all released (active-low)
};

}  // namespace winglet_ui

#endif  // SCREEN_MANAGER_HH_
