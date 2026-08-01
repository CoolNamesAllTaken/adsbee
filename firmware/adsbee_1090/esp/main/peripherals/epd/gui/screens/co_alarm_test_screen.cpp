#include "co_alarm_test_screen.hh"

#include <cstdio>

#include "co_sensor.hh"
#include "fonts.h"
#include "ui_data.hh"
#include "ui_primitives.hh"

namespace winglet_ui {

void DrawCoAlarmTestScreen(Canvas& c, const CoSensor& co, bool siren_active) {
    // Title + divider.
    DrawText(c, 10, 4, "CO ALARM TEST", &Font16, kBlack);
    FillRectSafe(c, 6, 26, kScreenWidth - 12, 1, kBlack);

    // Live CO reading (large).
    char line[32];
    if (co.IsDataValid()) {
        snprintf(line, sizeof line, "%.0f ppm", co.GetCoPpm());
    } else {
        snprintf(line, sizeof line, "-- ppm");
    }
    DrawTextCentered(c, kScreenWidth / 2, 44, line, &Font20, kBlack);

    // Prompt / status. When the siren is active, show it inverted so it stands out.
    if (siren_active) {
        const int barY = 96;
        const int barH = 30;
        FillRectSafe(c, 6, barY, kScreenWidth - 12, barH, kBlack);
        DrawTextCentered(c, kScreenWidth / 2, barY + 6, "SOUNDING", &Font20, kWhite);
    } else {
        DrawTextCentered(c, kScreenWidth / 2, 100, "Hold OK to test alarm", &Font12, kBlack);
    }

    DrawTextCentered(c, kScreenWidth / 2, kScreenHeight - 16, "Back to exit", &Font12, kBlack);
}

}  // namespace winglet_ui
