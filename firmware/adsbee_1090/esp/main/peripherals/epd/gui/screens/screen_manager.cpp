#include "screen_manager.hh"

#include <cstdio>
#include <variant>

#include "GUI_Paint.h"
#include "aircraft_dictionary.hh"
#include "map_screen.hh"
#include "settings_screen.hh"
// debug_screen.hh comes in via screen_manager.hh.

namespace winglet_ui {

void ScreenManager::HandleButtons(uint8_t button_bits) {
    // Active-low: a press is a 1->0 transition on that bit. Fire once per press.
    uint8_t pressed = (uint8_t)(prev_buttons_ & ~button_bits);  // bits that went 0
    if (pressed & (1 << 3)) {  // Up -> zoom in (toward closest range)
        if (zoom_index_ > 0) zoom_index_--;
    }
    if (pressed & (1 << 1)) {  // Down -> zoom out (toward farthest range)
        if (zoom_index_ < kNumZoomLevels - 1) zoom_index_++;
    }
    if (pressed & (1 << 2)) current_screen_ = UiScreen::kDebug;  // OK
    if (pressed & (1 << 0)) current_screen_ = UiScreen::kMap;    // Enter/Back
    prev_buttons_ = button_bits;
}

void ScreenManager::Draw(const MapDataSources& map_src, const DebugScreenSources& debug_src) {
    Paint_Clear(WHITE);

    switch (current_screen_) {
        case UiScreen::kMap: {
            // Collect plottable traffic contacts from the ADS-B dictionary into a
            // static buffer sized to the dictionary's own cap (no extra cap).
            static UiContact ui_contacts[AircraftDictionary::kMaxNumAircraft];
            uint16_t num_contacts = 0;
            for (const auto& itr : map_src.dict.dict) {
                if (num_contacts >= AircraftDictionary::kMaxNumAircraft) break;
                const float* lat = nullptr;
                const float* lon = nullptr;
                float dir = 0.0f;
                bool dir_is_heading = false;
                if (const ModeSAircraft* a = std::get_if<ModeSAircraft>(&itr.second)) {
                    if (!a->HasBitFlag(ModeSAircraft::kBitFlagPositionValid)) continue;
                    lat = &a->latitude_deg;
                    lon = &a->longitude_deg;
                    dir = a->direction_deg;
                    dir_is_heading = a->HasBitFlag(ModeSAircraft::kBitFlagDirectionIsHeading);
                } else if (const UATAircraft* u = std::get_if<UATAircraft>(&itr.second)) {
                    if (!u->HasBitFlag(UATAircraft::kBitFlagPositionValid)) continue;
                    lat = &u->latitude_deg;
                    lon = &u->longitude_deg;
                    dir = u->direction_deg;
                    dir_is_heading = u->HasBitFlag(UATAircraft::kBitFlagDirectionIsHeading);
                } else {
                    continue;
                }
                ui_contacts[num_contacts++] = {*lat, *lon, dir, dir_is_heading, /*selected=*/false};
            }

            // Left-rail port status strings, one per etched port: CO / GNSS /
            // SUBG / 2.4G / 1090.
            static char rail_bufs[kNumRailRows][12];
            const auto& adsb_metrics = map_src.dict.metrics;
            // CO: no CO sensor wired on the ESP yet — hard-coded to 0 for now.
            snprintf(rail_bufs[0], sizeof rail_bufs[0], "0");
            // GNSS: satellites used in the current fix (from the RP2040 metrics).
            snprintf(rail_bufs[1], sizeof rail_bufs[1], "%u",
                     (unsigned)map_src.gnss_num_satellites);
            // SUBG: aircraft tracked via the sub-GHz (UAT) receiver.
            snprintf(rail_bufs[2], sizeof rail_bufs[2], "%u",
                     (unsigned)adsb_metrics.num_uat_aircraft);
            // 2.4G: Wi-Fi link state.
            snprintf(rail_bufs[3], sizeof rail_bufs[3], "%s", map_src.wifi_up ? "UP" : "DN");
            // 1090: aircraft tracked via the 1090 MHz (Mode S) receiver.
            snprintf(rail_bufs[4], sizeof rail_bufs[4], "%u",
                     (unsigned)adsb_metrics.num_mode_s_aircraft);

            static char zoom_label_buf[8];
            snprintf(zoom_label_buf, sizeof zoom_label_buf, "%dNM",
                     (int)kZoomLadderNm[zoom_index_]);

            MapScreenData map_data{};
            map_data.contacts = ui_contacts;
            map_data.num_contacts = num_contacts;
            map_data.ownship_valid = map_src.ownship_valid;
            map_data.ownship_lat_deg = map_src.ownship_lat_deg;
            map_data.ownship_lon_deg = map_src.ownship_lon_deg;
            map_data.range_nm = kZoomLadderNm[zoom_index_];
            map_data.zoom_label = zoom_label_buf;
            for (int i = 0; i < kNumRailRows; i++) map_data.rail[i] = rail_bufs[i];
            map_data.batt_pct = map_src.batt_pct;
            map_data.batt_valid = map_src.batt_valid;
            map_data.terrain = map_src.terrain;

            DrawMapScreen(map_data);
            break;
        }
        case UiScreen::kSettings:
            DrawSettingsScreen();
            break;
        case UiScreen::kDebug:
            DrawDebugScreen(debug_src);
            break;
    }
}

}  // namespace winglet_ui
