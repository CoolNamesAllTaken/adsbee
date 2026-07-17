#ifndef UI_PRIMITIVES_HH_
#define UI_PRIMITIVES_HH_

#include <cstdint>

#include "canvas.hh"
#include "fonts.h"

// Low-level 1-bit drawing primitives ported from the Claude Design reference
// renderer (winglet-draw.js). Everything draws into the Canvas passed in.
//
// Porting rule: Canvas::SetPixel guards X>Width / Y>Height but NOT negatives, so
// every primitive here is built on the bounds-safe SetPixelSafe / FillRectSafe
// helpers, never on Canvas::DrawLine directly.

namespace winglet_ui {

// ---- Bounds-safe pixel/rect (the foundation everything else builds on) ----
void SetPixelSafe(Canvas& c, int x, int y, uint16_t color);
void FillRectSafe(Canvas& c, int x, int y, int w, int h, uint16_t color);

// ---- Shapes ---------------------------------------------------------------
// Filled square of side 2*r+1 centered on (cx,cy).
void DrawDot(Canvas& c, int cx, int cy, int r, uint16_t color);
// Gapped circle outline (gap>1 skips points to dot the ring; 0/1 => solid).
void DrawRing(Canvas& c, int cx, int cy, float r, int gap, uint16_t color);
// Solid (gap-free) circle outline via Bresenham midpoint.
void DrawCircleOutline(Canvas& c, int cx, int cy, int r, uint16_t color);
// Solid annulus (filled ring) by distance scan; gives gap-free icon rims.
void DrawAnnulus(Canvas& c, int cx, int cy, float r_out, float r_in, uint16_t color);

// ---- Lines (bounds-clipped, for terrain vectors) --------------------------
// Bresenham line via SetPixelSafe (off-screen pixels dropped, never wrapped).
// Cheap early-out when both endpoints are off the same screen edge.
void DrawLineClipped(Canvas& c, int x0, int y0, int x1, int y1, uint16_t color);
// Same, but dashed: `on` pixels drawn, `off` skipped, phase continuous along
// the line. Returns the ending dash phase so callers can chain segments with a
// continuous dash pattern.
int DrawDashedLine(Canvas& c, int x0, int y0, int x1, int y1, int on, int off, uint16_t color,
                   int phase = 0);

// ---- Icons ----------------------------------------------------------------
// Circle-plus (zoom in) / circle-minus (zoom out) toggled by `minus`.
void DrawPlusCircle(Canvas& c, int cx, int cy, float r, bool minus, uint16_t color);
// Settings gear: 8 teeth + rim + hub.
void DrawGear(Canvas& c, int cx, int cy, float r, uint16_t color);
// Ownship crosshair (center dot + 4 gapped arms).
void DrawCrosshair(Canvas& c, int cx, int cy, uint16_t color);
// Aircraft symbol: filled arrowhead pointing along `deg` (0 = up/north).
void DrawArrow(Canvas& c, int cx, int cy, float s, float deg, uint16_t color);
// Battery outline + fill; bw=15, bh=9 nominal, nub on the right.
void DrawBattery(Canvas& c, int bx, int by, uint8_t pct, uint16_t color);

// ---- Filled polygon (scanline) --------------------------------------------
// Fills an arbitrary simple polygon. Used by DrawArrow.
void FillPolygon(Canvas& c, const float* xs, const float* ys, int n, uint16_t color);

// ---- White-halo wrapper ---------------------------------------------------
// Draws `draw_fn` eight times in WHITE at the 8 neighbor offsets, then once in
// the requested ink color, so the shape lifts off whatever is beneath it. The
// callback receives (canvas, dx, dy, color) and must offset its own coordinates
// by (dx,dy) and draw in `color`.
typedef void (*OutlinedDrawFn)(Canvas& c, int dx, int dy, uint16_t color, void* ctx);
void DrawOutlined(Canvas& c, OutlinedDrawFn draw_fn, void* ctx, uint16_t ink_color);

// ---- Monospace text helpers -----------------------------------------------
// Width of a string in the given mono font (chars * Font->Width).
int TextWidth(const char* s, sFONT* font);
// Left/right/center-anchored text at a TOP y.
void DrawText(Canvas& c, int x_left, int y_top, const char* s, sFONT* font, uint16_t color);
void DrawTextRightAligned(Canvas& c, int x_right, int y_top, const char* s, sFONT* font,
                          uint16_t color);
void DrawTextCentered(Canvas& c, int x_center, int y_top, const char* s, sFONT* font,
                      uint16_t color);
// Vertically centered on y_center (uses the font cell height / 2).
void DrawTextRightAlignedVCentered(Canvas& c, int x_right, int y_center, const char* s, sFONT* font,
                                   uint16_t color);

}  // namespace winglet_ui

#endif  // UI_PRIMITIVES_HH_
