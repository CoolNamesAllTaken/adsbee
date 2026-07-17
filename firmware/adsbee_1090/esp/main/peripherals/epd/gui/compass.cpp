#include "compass.hh"

#include <cmath>
#include <cstdint>

#include "canvas.hh"  // Canvas draw methods, colors, line styles.
#include "fonts.h"    // Font8

using winglet_ui::Canvas;

namespace {

constexpr float kPi = 3.14159265358979323846f;

// Clamp to the in-bounds range Canvas accepts (it rejects endpoints >
// width/height; negatives would wrap, so clamp them to 0 too).
int ClampX(const Canvas& c, float v) {
  int i = static_cast<int>(lroundf(v));
  if (i < 0) i = 0;
  if (i > c.width()) i = c.width();
  return i;
}
int ClampY(const Canvas& c, float v) {
  int i = static_cast<int>(lroundf(v));
  if (i < 0) i = 0;
  if (i > c.height()) i = c.height();
  return i;
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

void DrawNeedle(Canvas& canvas, int cx, int cy, float bearing_deg, float len,
                winglet_ui::LineStyle style) {
  float ex, ey;
  BearingEndpoint(cx, cy, bearing_deg, len, &ex, &ey);
  canvas.DrawLine(ClampX(canvas, cx), ClampY(canvas, cy), ClampX(canvas, ex), ClampY(canvas, ey),
                  winglet_ui::kBlack, style, 1);
}

}  // namespace

void DrawCompass(Canvas& canvas, int cx, int cy, int radius,
                 float heading_level_deg, float heading_flat_deg, bool valid) {
  // Dial outline.
  canvas.DrawCircle(cx, cy, radius, winglet_ui::kBlack, /*filled=*/false, 1);

  // N/E/S/W ticks: short radial marks at each cardinal bearing.
  const float tick_in = radius * 0.78f;
  for (int b = 0; b < 360; b += 90) {
    float ox, oy, ix, iy;
    BearingEndpoint(cx, cy, static_cast<float>(b), static_cast<float>(radius), &ox, &oy);
    BearingEndpoint(cx, cy, static_cast<float>(b), tick_in, &ix, &iy);
    canvas.DrawLine(ClampX(canvas, ix), ClampY(canvas, iy), ClampX(canvas, ox), ClampY(canvas, oy),
                    winglet_ui::kBlack, winglet_ui::kLineSolid, 1);
  }

  // "N" label just inside the top of the dial.
  canvas.DrawString(ClampX(canvas, cx - 3), ClampY(canvas, cy - radius + 1), "N", &Font8,
                    winglet_ui::kWhite, winglet_ui::kBlack);

  if (!valid) {
    // Mag not calibrated yet: show a clear not-usable marker, no needles.
    canvas.DrawString(ClampX(canvas, cx - 6), ClampY(canvas, cy - 3), "--", &Font8,
                      winglet_ui::kWhite, winglet_ui::kBlack);
    return;
  }

  // Two needles toward magnetic North. Solid = tilt-compensated, dotted = flat (raw).
  DrawNeedle(canvas, cx, cy, heading_flat_deg, radius * 0.85f, winglet_ui::kLineDotted);
  DrawNeedle(canvas, cx, cy, heading_level_deg, radius * 0.85f, winglet_ui::kLineSolid);

  // Numeric tilt-compensated heading under the dial.
  canvas.DrawNum(ClampX(canvas, cx - 10), ClampY(canvas, cy + radius + 2),
                 static_cast<int32_t>(lroundf(heading_level_deg)), &Font8, winglet_ui::kWhite,
                 winglet_ui::kBlack);
}
