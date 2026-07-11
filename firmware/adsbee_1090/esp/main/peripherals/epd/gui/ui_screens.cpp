#include "ui_screens.hh"

#include <cstdio>

#include "GUI_Paint.h"
#include "fonts.h"
#include "map_screen.hh"
#include "ui_primitives.hh"

// Sensor driver + helper headers (reachable via the "peripherals" include dir).
#include "aht20.hh"
#include "bq27427.hh"
#include "compass.hh"
#include "lsm6dsv.hh"
#include "ltr_329.hh"
#include "mmc5603.hh"
#include "mp2722.hh"
#include "orientation_cube.hh"
#include "sensor_fusion.hh"
#include "spa06_003.hh"

namespace winglet_ui {

void DrawSettingsScreen() {
    // Placeholder until the settings menu (WD.settings) and button navigation
    // are implemented.
    DrawText(kLeftRailDividerX + 6, 4, "SETTINGS", &Font16, BLACK);
    FillRectSafe(kLeftRailDividerX + 2, 22, kRightRailDividerX - kLeftRailDividerX - 4, 1, BLACK);
    DrawTextCentered(kScreenWidth / 2, kScreenHeight / 2 - 6, "(coming soon)", &Font12, BLACK);
}

// Original bring-up telemetry dump, factored out of app_main unchanged. Draws
// ~11 sensor lines plus the orientation cube and mag compass.
void DrawDebugScreen(const DebugScreenSources& s) {
    char line[64];
    int y = 0;
    constexpr int kLineH = 13;  // Font12 height 12 + 1 px gap
    auto draw = [&](const char* str) {
        Paint_DrawString_EN(0, y, str, &Font12, WHITE, BLACK);
        y += kLineH;
    };

    snprintf(line, sizeof line, "Lux:%.1f c0:%u c1:%u", s.ltr.GetLux(), s.ltr.GetCh0Raw(),
             s.ltr.GetCh1Raw());
    draw(line);
    snprintf(line, sizeof line, "AHT T:%.2fC H:%.1f%%", s.aht.GetTemperatureCelsius(),
             s.aht.GetRelativeHumidity());
    draw(line);
    snprintf(line, sizeof line, "SPL P:%.1fhPa T:%.2fC", s.spl.GetPressureHpa(),
             s.spl.GetTemperatureCelsius());
    draw(line);
    snprintf(line, sizeof line, "Alt:%.2fm", s.spl.GetAltitudeMeters());
    draw(line);
    snprintf(line, sizeof line, "Mag X:%.1f Y:%.1f Z:%.1fuT", s.mmc.GetMagneticFieldXUt(),
             s.mmc.GetMagneticFieldYUt(), s.mmc.GetMagneticFieldZUt());
    draw(line);
    snprintf(line, sizeof line, "PwrGood:%d", s.mp.IsPowerGood() ? 1 : 0);
    draw(line);
    snprintf(line, sizeof line, "Batt:%s%u%% %s%dmW", s.bq.IsDataValid() ? "" : "?",
             s.bq.GetStateOfChargePct(), s.bq.IsDataValid() ? "" : "?", s.bq.GetAveragePowerMw());
    draw(line);
    int32_t tte = s.bq.GetTimeToEmptyMinutes();
    if (tte >= 0) {
        snprintf(line, sizeof line, "TTE:%ldh%02ldm", (long)(tte / 60), (long)(tte % 60));
    } else {
        snprintf(line, sizeof line, "TTE:--");
    }
    draw(line);
    snprintf(line, sizeof line, "Quat %s", s.imu.IsQuaternionValid() ? "ok" : "--");
    draw(line);
    snprintf(line, sizeof line, " w:%.3f x:%.3f", s.imu.GetQuaternion().w, s.imu.GetQuaternion().x);
    draw(line);
    snprintf(line, sizeof line, " y:%.3f z:%.3f", s.imu.GetQuaternion().y, s.imu.GetQuaternion().z);
    draw(line);
    snprintf(line, sizeof line, "Hdg:%.0f P:%.0f R:%.0f%s", s.fusion.GetHeadingDeg(),
             s.fusion.GetPitchDeg(), s.fusion.GetRollDeg(), s.fusion.IsCalibrated() ? "" : "*");
    draw(line);

    if (s.fusion.IsValid()) {
        DrawOrientationCube(198, 132, 22.f, s.fusion.GetFusedQuaternion());
    }
    DrawCompass(222, 52, 26, s.fusion.GetMagHeadingLevelDeg(), s.fusion.GetMagHeadingFlatDeg(),
                s.fusion.IsMagHeadingValid());
}

void DrawCurrentScreen(UiScreen screen, const MapScreenData& map_data,
                       const DebugScreenSources& debug_src) {
    switch (screen) {
        case UiScreen::kMap:
            DrawMapScreen(map_data);
            break;
        case UiScreen::kSettings:
            DrawSettingsScreen();
            break;
        case UiScreen::kDebug:
            DrawDebugScreen(debug_src);
            break;
    }
}

}  // namespace winglet_ui
