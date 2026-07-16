#ifndef HOME_SCREEN_HH_
#define HOME_SCREEN_HH_

#include "canvas.hh"

namespace winglet_ui {

// Home menu screen. Renders the kHomeMenu entries (ui_data.hh) in large text, with the `selected`
// row highlighted in inverse colors. The caller must have already cleared the canvas.
void DrawHomeScreen(Canvas& c, int selected);

}  // namespace winglet_ui

#endif  // HOME_SCREEN_HH_
