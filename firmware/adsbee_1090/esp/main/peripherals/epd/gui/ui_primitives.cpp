#include "ui_primitives.hh"

#include <cmath>
#include <cstring>

#include "ui_data.hh"
#include "ui_sprites.hh"

namespace winglet_ui {

namespace {
constexpr float kPi = 3.14159265358979323846f;

inline int IRound(float v) { return (int)lroundf(v); }
}  // namespace

// ---- Bounds-safe pixel/rect ----------------------------------------------
// Canvas::SetPixel guards X>Width / Y>Height but NOT negatives (they wrap), so
// we guard the full [0,W)x[0,H) range here against the canvas's logical size.
void SetPixelSafe(Canvas& c, int x, int y, uint16_t color) {
    if (x < 0 || y < 0 || x >= c.width() || y >= c.height()) return;
    c.SetPixel(x, y, color);
}

void FillRectSafe(Canvas& c, int x, int y, int w, int h, uint16_t color) {
    if (w <= 0 || h <= 0) return;
    for (int yy = y; yy < y + h; yy++)
        for (int xx = x; xx < x + w; xx++) SetPixelSafe(c, xx, yy, color);
}

// ---- Sprite blitters ------------------------------------------------------
void BlitSprite(Canvas& c, int x, int y, const Sprite1bpp& s, uint16_t ink) {
    int stride = (s.w + 7) / 8;
    for (int row = 0; row < s.h; row++) {
        const uint8_t* p = s.bits + row * stride;
        for (int col = 0; col < s.w; col++) {
            if (p[col >> 3] & (0x80 >> (col & 7))) SetPixelSafe(c, x + col, y + row, ink);
        }
    }
}

void BlitSprite2bpp(Canvas& c, int x, int y, const Sprite2bpp& s, uint16_t ink, uint16_t halo) {
    int stride = (s.w * 2 + 7) / 8;
    for (int row = 0; row < s.h; row++) {
        const uint8_t* p = s.bits + row * stride;
        for (int col = 0; col < s.w; col++) {
            uint8_t val = (p[col >> 2] >> (6 - 2 * (col & 3))) & 0x3;
            if (val == 1)
                SetPixelSafe(c, x + col, y + row, ink);
            else if (val == 2)
                SetPixelSafe(c, x + col, y + row, halo);
        }
    }
}

// ---- Shapes ---------------------------------------------------------------
void DrawDot(Canvas& c, int cx, int cy, int r, uint16_t color) {
    if (r < 0) r = 0;
    FillRectSafe(c, cx - r, cy - r, 2 * r + 1, 2 * r + 1, color);
}

void DrawRing(Canvas& c, int cx, int cy, float r, int gap, uint16_t color) {
    int steps = (int)fmaxf(24.0f, roundf(2.0f * kPi * r));
    for (int i = 0; i < steps; i++) {
        if (gap > 1 && (i % gap) != 0) continue;
        float a = (float)i / steps * 2.0f * kPi;
        SetPixelSafe(c, IRound(cx + r * cosf(a)), IRound(cy + r * sinf(a)), color);
    }
}

void DrawCircleOutline(Canvas& c, int cx, int cy, int r, uint16_t color) {
    int xx = r, yy = 0, err = 0;
    while (xx >= yy) {
        const int pts[8][2] = {{xx, yy},   {yy, xx},   {-yy, xx},  {-xx, yy},
                               {-xx, -yy}, {-yy, -xx}, {yy, -xx},  {xx, -yy}};
        for (auto& p : pts) SetPixelSafe(c, cx + p[0], cy + p[1], color);
        yy++;
        if (err <= 0) err += 2 * yy + 1;
        if (err > 0) {
            xx--;
            err -= 2 * xx + 1;
        }
    }
}

void DrawAnnulus(Canvas& c, int cx, int cy, float r_out, float r_in, uint16_t color) {
    int R = (int)ceilf(r_out);
    for (int yy = -R; yy <= R; yy++)
        for (int xx = -R; xx <= R; xx++) {
            float d = sqrtf((float)(xx * xx + yy * yy));
            if (d <= r_out + 0.5f && d >= r_in - 0.5f) SetPixelSafe(c, cx + xx, cy + yy, color);
        }
}

// ---- Lines (bounds-clipped) ----------------------------------------------
namespace {
// Both endpoints off the same screen edge -> the whole line is off-screen.
bool LineTriviallyOffscreen(const Canvas& c, int x0, int y0, int x1, int y1) {
    return (x0 < 0 && x1 < 0) || (x0 >= c.width() && x1 >= c.width()) ||
           (y0 < 0 && y1 < 0) || (y0 >= c.height() && y1 >= c.height());
}

// Shared Bresenham. If on<=0, draws solid; else dashes with the given phase and
// returns the ending phase (for continuous dashing across chained segments).
int BresenhamLine(Canvas& c, int x0, int y0, int x1, int y1, int on, int off, uint16_t color,
                  int phase) {
    int dx = abs(x1 - x0), dy = abs(y1 - y0);
    int sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1;
    int err = dx - dy;
    int period = (on > 0) ? (on + off) : 1;
    int i = phase % period;
    while (true) {
        if (on <= 0 || (i % period) < on) SetPixelSafe(c, x0, y0, color);
        i++;
        if (x0 == x1 && y0 == y1) break;
        int e2 = 2 * err;
        if (e2 > -dy) { err -= dy; x0 += sx; }
        if (e2 < dx) { err += dx; y0 += sy; }
    }
    return i % period;
}
}  // namespace

void DrawLineClipped(Canvas& c, int x0, int y0, int x1, int y1, uint16_t color) {
    if (LineTriviallyOffscreen(c, x0, y0, x1, y1)) return;
    BresenhamLine(c, x0, y0, x1, y1, /*on=*/0, /*off=*/0, color, 0);
}

int DrawDashedLine(Canvas& c, int x0, int y0, int x1, int y1, int on, int off, uint16_t color,
                   int phase) {
    if (LineTriviallyOffscreen(c, x0, y0, x1, y1)) {
        // Still advance the phase by the (Chebyshev) step count so a dashed
        // polyline that briefly leaves the screen keeps a coherent pattern.
        int steps = abs(x1 - x0);
        int dysteps = abs(y1 - y0);
        if (dysteps > steps) steps = dysteps;
        int period = (on > 0) ? (on + off) : 1;
        return (phase + steps + 1) % period;
    }
    return BresenhamLine(c, x0, y0, x1, y1, on, off, color, phase);
}

// ---- Icons ----------------------------------------------------------------
void DrawPlusCircle(Canvas& c, int cx, int cy, float r, bool minus, uint16_t color) {
    DrawAnnulus(c, cx, cy, r, r - 1.8f, color);
    int arm = (int)(r - 4);
    FillRectSafe(c, cx - arm, cy - 1, arm * 2 + 1, 3, color);
    if (!minus) FillRectSafe(c, cx - 1, cy - arm, 3, arm * 2 + 1, color);
}

void DrawGear(Canvas& c, int cx, int cy, float r, uint16_t color) {
    for (int k = 0; k < 8; k++) {
        float a = k * kPi / 4.0f;
        int tx = IRound(cx + cosf(a) * (r + 1.4f));
        int ty = IRound(cy + sinf(a) * (r + 1.4f));
        FillRectSafe(c, tx - 1, ty - 1, 3, 3, color);
    }
    DrawAnnulus(c, cx, cy, r, r - 1.8f, color);
    DrawAnnulus(c, cx, cy, 2.7f, 1.3f, color);
}

void DrawCrosshair(Canvas& c, int cx, int cy, uint16_t color) {
    FillRectSafe(c, cx, cy, 1, 1, color);
    FillRectSafe(c, cx, cy - 9, 1, 6, color);
    FillRectSafe(c, cx, cy + 4, 1, 6, color);
    FillRectSafe(c, cx - 9, cy, 6, 1, color);
    FillRectSafe(c, cx + 4, cy, 6, 1, color);
}

// Aircraft arrowhead: a 4-point polygon (tip, left base, inner notch, right
// base) rotated by `deg` about (cx,cy). Matches winglet-draw.js arrow().
void DrawArrow(Canvas& c, int cx, int cy, float s, float deg, uint16_t color) {
    float a = deg * kPi / 180.0f;
    const float base[4][2] = {
        {0.0f, -s}, {-0.82f * s, 0.72f * s}, {0.0f, 0.30f * s}, {0.82f * s, 0.72f * s}};
    float xs[4], ys[4];
    for (int i = 0; i < 4; i++) {
        float X = base[i][0], Y = base[i][1];
        xs[i] = cx + X * cosf(a) - Y * sinf(a);
        ys[i] = cy + X * sinf(a) + Y * cosf(a);
    }
    FillPolygon(c, xs, ys, 4, color);
}

void DrawBattery(Canvas& c, int bx, int by, uint8_t pct, uint16_t color) {
    const int bw = 15, bh = 9;
    FillRectSafe(c, bx, by, bw, 1, color);              // top edge
    FillRectSafe(c, bx, by + bh - 1, bw, 1, color);     // bottom edge
    FillRectSafe(c, bx, by, 1, bh, color);              // left wall
    FillRectSafe(c, bx + bw - 1, by, 1, bh, color);     // right wall
    FillRectSafe(c, bx + bw, by + 2, 2, 5, color);      // nub
    int fill = IRound((bw - 4) * (pct / 100.0f));
    FillRectSafe(c, bx + 2, by + 2, fill, bh - 4, color);
}

// ---- Filled polygon (scanline) --------------------------------------------
void FillPolygon(Canvas& c, const float* xs, const float* ys, int n, uint16_t color) {
    if (n < 3) return;
    float min_yf = ys[0], max_yf = ys[0];
    for (int i = 1; i < n; i++) {
        if (ys[i] < min_yf) min_yf = ys[i];
        if (ys[i] > max_yf) max_yf = ys[i];
    }
    int y0 = (int)floorf(min_yf), y1 = (int)ceilf(max_yf);
    if (y0 < 0) y0 = 0;
    if (y1 >= c.height()) y1 = c.height() - 1;

    for (int y = y0; y <= y1; y++) {
        float yc = y + 0.5f;  // sample at pixel center
        // Collect edge crossings for this scanline.
        float xcross[8];
        int nc = 0;
        for (int i = 0; i < n && nc < 8; i++) {
            int j = (i + 1) % n;
            float yi = ys[i], yj = ys[j];
            if ((yi <= yc && yj > yc) || (yj <= yc && yi > yc)) {
                float t = (yc - yi) / (yj - yi);
                xcross[nc++] = xs[i] + t * (xs[j] - xs[i]);
            }
        }
        // Sort crossings ascending (small n, insertion sort).
        for (int i = 1; i < nc; i++) {
            float v = xcross[i];
            int k = i - 1;
            while (k >= 0 && xcross[k] > v) {
                xcross[k + 1] = xcross[k];
                k--;
            }
            xcross[k + 1] = v;
        }
        // Fill spans between crossing pairs.
        for (int i = 0; i + 1 < nc; i += 2) {
            int xa = (int)ceilf(xcross[i] - 0.5f);
            int xb = (int)floorf(xcross[i + 1] - 0.5f);
            for (int x = xa; x <= xb; x++) SetPixelSafe(c, x, y, color);
        }
    }
}

// ---- White-halo wrapper ---------------------------------------------------
void DrawOutlined(Canvas& c, OutlinedDrawFn draw_fn, void* ctx, uint16_t ink_color) {
    static const int kHalo[8][2] = {{-1, -1}, {0, -1}, {1, -1}, {-1, 0},
                                    {1, 0},   {-1, 1}, {0, 1},  {1, 1}};
    for (auto& o : kHalo) draw_fn(c, o[0], o[1], kWhite, ctx);
    draw_fn(c, 0, 0, ink_color, ctx);
}

// ---- Monospace text helpers -----------------------------------------------
int TextWidth(const char* s, sFONT* font) {
    if (!s) return 0;
    return (int)strlen(s) * font->Width;
}

// Draw one glyph's set pixels in `color` at a signed top-left, dropping any
// out-of-bounds pixels via SetPixelSafe (so negative/overrun coords clip
// instead of wrapping or shifting). Reads the sFONT bitmap rows top->bottom,
// ceil(Width/8) bytes/row, MSB-first.
static void DrawGlyph(Canvas& c, int x_left, int y_top, char ch, sFONT* font, uint16_t color) {
    if (ch < ' ' || ch > '~') return;
    int bytes_per_row = font->Width / 8 + (font->Width % 8 ? 1 : 0);
    const uint8_t* ptr = &font->table[(ch - ' ') * font->Height * bytes_per_row];
    for (int row = 0; row < font->Height; row++) {
        for (int col = 0; col < font->Width; col++) {
            if (ptr[col / 8] & (0x80 >> (col % 8))) SetPixelSafe(c, x_left + col, y_top + row, color);
        }
        ptr += bytes_per_row;
    }
}

// Draw glyphs in `color` with a transparent background, so text overlays the
// map without painting a cell rectangle behind it. Signed coordinates are
// honored exactly: off-screen columns/rows are dropped, not clamped-shifted
// (so right-aligned values never slide over the rail divider).
void DrawText(Canvas& c, int x_left, int y_top, const char* s, sFONT* font, uint16_t color) {
    if (!s) return;
    int x = x_left;
    for (const char* p = s; *p; p++) {
        DrawGlyph(c, x, y_top, *p, font, color);
        x += font->Width;
    }
}

void DrawTextRightAligned(Canvas& c, int x_right, int y_top, const char* s, sFONT* font,
                          uint16_t color) {
    DrawText(c, x_right - TextWidth(s, font), y_top, s, font, color);
}

void DrawTextCentered(Canvas& c, int x_center, int y_top, const char* s, sFONT* font,
                      uint16_t color) {
    DrawText(c, x_center - TextWidth(s, font) / 2, y_top, s, font, color);
}

// Find the first and last rows containing any set pixel across the glyphs of
// `s`, so we can center on actual ink rather than the (taller) font cell. This
// mirrors the reference renderer's txtMid/inkRows behavior.
static void InkRows(const char* s, sFONT* font, int* top, int* bot) {
    int t = font->Height, b = -1;
    int bytes_per_row = font->Width / 8 + (font->Width % 8 ? 1 : 0);
    for (const char* p = s; *p; p++) {
        if (*p < ' ' || *p > '~') continue;
        const uint8_t* base = &font->table[(*p - ' ') * font->Height * bytes_per_row];
        for (int row = 0; row < font->Height; row++) {
            bool any = false;
            for (int bcol = 0; bcol < bytes_per_row; bcol++)
                if (base[row * bytes_per_row + bcol]) {
                    any = true;
                    break;
                }
            if (any) {
                if (row < t) t = row;
                if (row > b) b = row;
            }
        }
    }
    if (b < 0) {  // empty / all-space string: fall back to full cell
        t = 0;
        b = font->Height - 1;
    }
    *top = t;
    *bot = b;
}

// Right-aligned text centered on y_center by its ink rows (matches the design's
// ink-centered rail/battery values, not the font cell).
void DrawTextRightAlignedVCentered(Canvas& c, int x_right, int y_center, const char* s, sFONT* font,
                                   uint16_t color) {
    if (!s || !*s) return;
    int top, bot;
    InkRows(s, font, &top, &bot);
    int ink_center = (top + bot + 1) / 2;  // center of the ink band, in cell rows
    DrawTextRightAligned(c, x_right, y_center - ink_center, s, font, color);
}

}  // namespace winglet_ui
