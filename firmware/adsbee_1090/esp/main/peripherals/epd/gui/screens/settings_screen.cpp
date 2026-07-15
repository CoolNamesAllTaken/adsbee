#include "settings_screen.hh"

#include "canvas.hh"
#include "fonts.h"
#include "ui_data.hh"
#include "ui_primitives.hh"

namespace winglet_ui {

void DrawSettingsScreen(Canvas& c) {
    // Placeholder until the settings menu (WD.settings) and button navigation
    // are implemented.
    DrawText(c, kLeftRailDividerX + 6, 4, "SETTINGS", &Font16, kBlack);
    FillRectSafe(c, kLeftRailDividerX + 2, 22, kRightRailDividerX - kLeftRailDividerX - 4, 1, kBlack);
    DrawTextCentered(c, kScreenWidth / 2, kScreenHeight / 2 - 6, "(coming soon)", &Font12, kBlack);
}

}  // namespace winglet_ui
