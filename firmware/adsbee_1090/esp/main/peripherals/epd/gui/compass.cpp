#include "compass.hh"

#include <cmath>
#include <cstdint>

#include "GUI_Paint.h"  // BLACK/WHITE, Paint_DrawCircle/Line/String_EN, Font8

namespace {

constexpr float kPi = 3.14159265358979323846f;

// Clamp to the in-bounds range Paint accepts (it rejects endpoints > Width/Height;
// unsigned wrap also rejects negatives).
UWORD ClampX(float v) {
  int i = static_cast<int>(lroundf(v));
  if (i < 0) i = 0;
  if (i > static_cast<int>(Paint.Width)) i = Paint.Width;
  return static_cast<UWORD>(i);
}
UWORD ClampY(float v) {
  int i = static_cast<int>(lroundf(v));
  if (i < 0) i = 0;
  if (i > static_cast<int>(Paint.Height)) i = Paint.Height;
  return static_cast<UWORD>(i);
}

// Phone-compass bearing (0 = North = up, increasing CW) -> screen endpoint at the given
// length from center. Screen +Y is DOWN, so North (up) is -Y; CW on screen matches CW
// bearing when we measure the screen angle clockwise from up.
void BearingEndpoint(int cx, int cy, float bearing_deg, float len,
                     float* ex, float* ey) {
  const float a = bearing_deg * (kPi / 180.0f);
  *ex = cx + len * sinf(a);   // +x to the right (East at 90)
  *ey = cy - len * cosf(a);   // -y is up (North at 0)
}

void DrawNeedle(int cx, int cy, float bearing_deg, float len, LINE_STYLE style) {
  float ex, ey;
  BearingEndpoint(cx, cy, bearing_deg, len, &ex, &ey);
  Paint_DrawLine(ClampX(cx), ClampY(cy), ClampX(ex), ClampY(ey), BLACK, style,
                 DOT_PIXEL_1X1);
}

}  // namespace

void DrawCompass(int cx, int cy, int radius,
                 float heading_level_deg, float heading_flat_deg, bool valid) {
  // Dial outline.
  Paint_DrawCircle(static_cast<UWORD>(cx), static_cast<UWORD>(cy),
                   static_cast<UWORD>(radius), BLACK, DRAW_FILL_EMPTY, DOT_PIXEL_1X1);

  // N/E/S/W ticks: short radial marks at each cardinal bearing.
  const float tick_in = radius * 0.78f;
  for (int b = 0; b < 360; b += 90) {
    float ox, oy, ix, iy;
    BearingEndpoint(cx, cy, static_cast<float>(b), static_cast<float>(radius), &ox, &oy);
    BearingEndpoint(cx, cy, static_cast<float>(b), tick_in, &ix, &iy);
    Paint_DrawLine(ClampX(ix), ClampY(iy), ClampX(ox), ClampY(oy), BLACK,
                   LINE_STYLE_SOLID, DOT_PIXEL_1X1);
  }

  // "N" label just inside the top of the dial.
  Paint_DrawString_EN(ClampX(cx - 3), ClampY(cy - radius + 1), "N", &Font8, WHITE,
                      BLACK);

  if (!valid) {
    // Mag not calibrated yet: show a clear not-usable marker, no needles.
    Paint_DrawString_EN(ClampX(cx - 6), ClampY(cy - 3), "--", &Font8, WHITE, BLACK);
    return;
  }

  // Two needles toward magnetic North. Solid = tilt-compensated, dotted = flat (raw).
  DrawNeedle(cx, cy, heading_flat_deg, radius * 0.85f, LINE_STYLE_DOTTED);
  DrawNeedle(cx, cy, heading_level_deg, radius * 0.85f, LINE_STYLE_SOLID);

  // Numeric tilt-compensated heading under the dial.
  Paint_DrawNum(ClampX(cx - 10), ClampY(cy + radius + 2),
                static_cast<int32_t>(lroundf(heading_level_deg)), &Font8, WHITE, BLACK);
}
