#include "home_screen.hh"

#include "fonts.h"
#include "ui_data.hh"
#include "ui_primitives.hh"

namespace winglet_ui {

// Layout constants for the Home menu.
static constexpr int kTitleY      = 4;
static constexpr int kDividerY    = 26;
static constexpr int kMenuTopY    = 34;   // first row top
static constexpr int kRowHeight   = 28;   // Font20 is 20px tall + padding
static constexpr int kRowPadX     = 10;   // text inset within a row
static constexpr int kRowTextDy   = 4;    // vertical inset of text within a row
static constexpr int kMenuMarginX = 6;    // left/right margin of the highlight bar

void DrawHomeScreen(Canvas& c, int selected) {
    // Title + divider (mirrors the settings-screen idiom).
    DrawText(c, kMenuMarginX + 4, kTitleY, "MENU", &Font16, kBlack);
    FillRectSafe(c, kMenuMarginX, kDividerY, kScreenWidth - 2 * kMenuMarginX, 1, kBlack);

    const int rowW = kScreenWidth - 2 * kMenuMarginX;
    for (int i = 0; i < kHomeMenuCount; i++) {
        const int y = kMenuTopY + i * kRowHeight;
        if (i == selected) {
            // Selected row: inverse (black bar + white text).
            FillRectSafe(c, kMenuMarginX, y, rowW, kRowHeight, kBlack);
            DrawText(c, kMenuMarginX + kRowPadX, y + kRowTextDy, kHomeMenu[i].label, &Font20, kWhite);
        } else {
            DrawText(c, kMenuMarginX + kRowPadX, y + kRowTextDy, kHomeMenu[i].label, &Font20, kBlack);
        }
    }
}

}  // namespace winglet_ui
