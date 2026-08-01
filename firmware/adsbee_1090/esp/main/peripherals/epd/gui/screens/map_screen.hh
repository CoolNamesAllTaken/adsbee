#ifndef MAP_SCREEN_HH_
#define MAP_SCREEN_HH_

#include "canvas.hh"
#include "ui_data.hh"

// Renders the Winglet moving-map / radar-scope screen (the Claude Design
// "Product Render v2" / WD.productExp view) into the given Canvas.
//
// The caller must have already cleared the canvas. This function draws the full
// screen: left status rail, right icon rail, range rings, ownship crosshair, and
// haloed traffic arrows. Geographic contact positions are projected relative to
// ownship internally.
namespace winglet_ui {

void DrawMapScreen(Canvas& c, const MapScreenData& data);

}  // namespace winglet_ui

#endif  // MAP_SCREEN_HH_
