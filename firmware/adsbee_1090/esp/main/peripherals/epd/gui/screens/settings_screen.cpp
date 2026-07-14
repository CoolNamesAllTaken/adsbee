#include "settings_screen.hh"

#include "GUI_Paint.h"
#include "fonts.h"
#include "ui_data.hh"
#include "ui_primitives.hh"

namespace winglet_ui {

void DrawSettingsScreen() {
    // Placeholder until the settings menu (WD.settings) and button navigation
    // are implemented.
    DrawText(kLeftRailDividerX + 6, 4, "SETTINGS", &Font16, BLACK);
    FillRectSafe(kLeftRailDividerX + 2, 22, kRightRailDividerX - kLeftRailDividerX - 4, 1, BLACK);
    DrawTextCentered(kScreenWidth / 2, kScreenHeight / 2 - 6, "(coming soon)", &Font12, BLACK);
}

}  // namespace winglet_ui
