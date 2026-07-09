#ifndef UI_SCREENS_HH_
#define UI_SCREENS_HH_

#include "ui_data.hh"

// Forward declarations of the sensor drivers used by the debug screen, so this
// header stays lightweight. Their headers are included in ui_screens.cpp.
class Ltr329;
class Aht20;
class Spl06003;
class Mmc5603;
class Mp2722;
class Bq27427;
class Lsm6dsv;
class SensorFusion;

namespace winglet_ui {

// Bundle of live sensor references the debug screen renders. Populated by
// app_main from its local driver instances.
struct DebugScreenSources {
    Ltr329& ltr;
    Aht20& aht;
    Spl06003& spl;
    Mmc5603& mmc;
    Mp2722& mp;
    Bq27427& bq;
    Lsm6dsv& imu;
    SensorFusion& fusion;
};

// Settings screen (WD.settings) — stubbed until the menu system lands.
void DrawSettingsScreen();

// Debug screen — the original sensor telemetry dump (unchanged behavior),
// kept and made selectable.
void DrawDebugScreen(const DebugScreenSources& src);

// Renders the currently-selected screen into the (already selected + cleared)
// Paint framebuffer. Buttons are not wired yet, so app_main holds `screen`
// fixed at kMap for now.
void DrawCurrentScreen(UiScreen screen, const MapScreenData& map_data,
                       const DebugScreenSources& debug_src);

}  // namespace winglet_ui

#endif  // UI_SCREENS_HH_
