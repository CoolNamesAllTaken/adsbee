#ifndef UI_PRIMITIVES_HH_
#define UI_PRIMITIVES_HH_

#include "GUI_Paint.h"
#include "fonts.h"

// Low-level 1-bit drawing primitives ported from the Claude Design reference
// renderer (winglet-draw.js). Everything draws into the global Paint context.
//
// Porting rule: the JS engine's px() is bounds-checked, but Paint_DrawLine /
// Paint_DrawRectangle do NOT clip and Paint_SetPixel does not guard negative
// coordinates (they wrap as UWORD). So every primitive here is built on the
// bounds-safe SetPixelSafe / FillRectSafe helpers, never on Paint_DrawLine.

namespace winglet_ui {

// ---- Bounds-safe pixel/rect (the foundation everything else builds on) ----
void SetPixelSafe(int x, int y, UWORD color);
void FillRectSafe(int x, int y, int w, int h, UWORD color);

// ---- Shapes ---------------------------------------------------------------
// Filled square of side 2*r+1 centered on (cx,cy).
void DrawDot(int cx, int cy, int r, UWORD color);
// Gapped circle outline (gap>1 skips points to dot the ring; 0/1 => solid).
void DrawRing(int cx, int cy, float r, int gap, UWORD color);
// Solid (gap-free) circle outline via Bresenham midpoint.
void DrawCircleOutline(int cx, int cy, int r, UWORD color);
// Solid annulus (filled ring) by distance scan; gives gap-free icon rims.
void DrawAnnulus(int cx, int cy, float r_out, float r_in, UWORD color);

// ---- Lines (bounds-clipped, for terrain vectors) --------------------------
// Bresenham line via SetPixelSafe (off-screen pixels dropped, never wrapped).
// Cheap early-out when both endpoints are off the same screen edge.
void DrawLineClipped(int x0, int y0, int x1, int y1, UWORD color);
// Same, but dashed: `on` pixels drawn, `off` skipped, phase continuous along
// the line. Returns the ending dash phase so callers can chain segments with a
// continuous dash pattern.
int DrawDashedLine(int x0, int y0, int x1, int y1, int on, int off, UWORD color, int phase = 0);

// ---- Icons ----------------------------------------------------------------
// Circle-plus (zoom in) / circle-minus (zoom out) toggled by `minus`.
void DrawPlusCircle(int cx, int cy, float r, bool minus, UWORD color);
// Settings gear: 8 teeth + rim + hub.
void DrawGear(int cx, int cy, float r, UWORD color);
// Ownship crosshair (center dot + 4 gapped arms).
void DrawCrosshair(int cx, int cy, UWORD color);
// Aircraft symbol: filled arrowhead pointing along `deg` (0 = up/north).
void DrawArrow(int cx, int cy, float s, float deg, UWORD color);
// Battery outline + fill; bw=15, bh=9 nominal, nub on the right.
void DrawBattery(int bx, int by, uint8_t pct, UWORD color);

// ---- Filled polygon (scanline) --------------------------------------------
// Fills an arbitrary simple polygon. Used by DrawArrow.
void FillPolygon(const float* xs, const float* ys, int n, UWORD color);

// ---- White-halo wrapper ---------------------------------------------------
// Draws `draw_fn` eight times in WHITE at the 8 neighbor offsets, then once in
// the requested ink color, so the shape lifts off whatever is beneath it. The
// callback receives (dx, dy, color) and must offset its own coordinates by
// (dx,dy) and draw in `color`.
typedef void (*OutlinedDrawFn)(int dx, int dy, UWORD color, void* ctx);
void DrawOutlined(OutlinedDrawFn draw_fn, void* ctx, UWORD ink_color);

// ---- Monospace text helpers -----------------------------------------------
// Width of a string in the given mono font (chars * Font->Width).
int TextWidth(const char* s, sFONT* font);
// Left/right/center-anchored text at a TOP y.
void DrawText(int x_left, int y_top, const char* s, sFONT* font, UWORD color);
void DrawTextRightAligned(int x_right, int y_top, const char* s, sFONT* font, UWORD color);
void DrawTextCentered(int x_center, int y_top, const char* s, sFONT* font, UWORD color);
// Vertically centered on y_center (uses the font cell height / 2).
void DrawTextRightAlignedVCentered(int x_right, int y_center, const char* s, sFONT* font,
                                   UWORD color);

}  // namespace winglet_ui

#endif  // UI_PRIMITIVES_HH_
