#ifndef CANVAS_HH_
#define CANVAS_HH_

#include <cstdint>

#include "esp_heap_caps.h"  // For MALLOC_CAP_* defaults.
#include "fonts.h"          // sFONT (glyph tables) for DrawChar/DrawString/DrawNum.

namespace winglet_ui {

// 1-bit color values (MSB-first framebuffer): a "black" bit is ink, "white" is
// background. Values match the vendor GUI_Paint BLACK/WHITE (0x00 / 0xFF) so the
// bit-packing math is identical.
enum Color : uint16_t {
    kWhite = 0xFF,
    kBlack = 0x00,
};

// Display rotation, in degrees. ROTATE_270 presents a 176x264 panel as a
// logical 264x176 drawing space with upright text.
enum Rotate : int {
    kRotate0   = 0,
    kRotate90  = 90,
    kRotate180 = 180,
    kRotate270 = 270,
};

// Framebuffer mirroring (applied after rotation in SetPixel).
enum Mirror : int {
    kMirrorNone       = 0,
    kMirrorHorizontal = 1,
    kMirrorVertical   = 2,
    kMirrorOrigin     = 3,
};

// Line dash style for DrawLine.
enum LineStyle : int {
    kLineSolid  = 0,
    kLineDotted = 1,
};

// An instantiable 1-bit drawing surface that owns its framebuffer. Replaces the
// former global `PAINT Paint` singleton: each Canvas holds its own image buffer
// + geometry and exposes all drawing operations as methods, so multiple draw
// targets can coexist (e.g. an off-screen terrain cache).
//
// The framebuffer is 1 bit/pixel, MSB-first, ceil(panel_w/8) bytes/row, in
// panel send-order (rotation/mirror are applied when addressing pixels, so the
// EPD driver streams the buffer out verbatim).
class Canvas {
   public:
    // Allocates a framebuffer for a panel_w x panel_h physical panel at the
    // given rotation and fills it with `fill`. `caps` selects the heap
    // (MALLOC_CAP_8BIT = internal DRAM by default; MALLOC_CAP_SPIRAM for PSRAM).
    // Check ok() after construction — allocation can fail.
    Canvas(int panel_w, int panel_h, int rotate, uint16_t fill,
           uint32_t caps = MALLOC_CAP_8BIT);
    ~Canvas();

    // Non-copyable (owns heap), movable (so factories can return by value).
    Canvas(const Canvas&)            = delete;
    Canvas& operator=(const Canvas&) = delete;
    Canvas(Canvas&& other) noexcept;
    Canvas& operator=(Canvas&& other) noexcept;

    bool ok() const { return image_ != nullptr; }

    // ---- Drawing (no-ops if !ok()) -----------------------------------------
    void Clear(uint16_t color);
    void SetPixel(int x, int y, uint16_t color);
    void DrawLine(int x0, int y0, int x1, int y1, uint16_t color,
                  LineStyle style = kLineSolid, int dot_pixel = 1);
    void DrawCircle(int cx, int cy, int radius, uint16_t color, bool filled,
                    int dot_pixel = 1);
    void DrawChar(int x, int y, char c, sFONT* font, uint16_t bg, uint16_t fg);
    void DrawString(int x, int y, const char* s, sFONT* font, uint16_t bg, uint16_t fg);
    void DrawNum(int x, int y, int32_t number, sFONT* font, uint16_t bg, uint16_t fg);

    // Full-frame composite: copies src's pixels into this canvas. src must have
    // identical geometry (same byte_size()); mismatched sizes are a no-op.
    void CopyFrom(const Canvas& src);

    // Allocates a new Canvas with identical geometry (dimensions / rotation /
    // bit-layout), optionally in a different heap. Guarantees CopyFrom()
    // compatibility without the caller re-specifying panel_w/h/rotate — used by
    // the terrain cache to make a matching PSRAM off-screen buffer.
    Canvas CreateCompatible(uint32_t caps = MALLOC_CAP_8BIT) const;

    // ---- Geometry / access --------------------------------------------------
    int      width()     const { return width_; }   // logical (post-rotate)
    int      height()    const { return height_; }  // logical (post-rotate)
    uint8_t* data()      const { return image_; }
    int      byte_size() const { return width_byte_ * height_byte_; }

   private:
    // Draws a single dot (dot_pixel size, filled-around style) — the internal
    // primitive DrawLine/DrawCircle build on, ported from Paint_DrawPoint.
    void DrawPoint(int x, int y, uint16_t color, int dot_pixel);

    uint8_t* image_ = nullptr;
    uint32_t caps_  = MALLOC_CAP_8BIT;  // heap the buffer came from (for realloc/free).
    int      width_ = 0, height_ = 0;   // logical dims (post-rotate).
    int      width_memory_ = 0, height_memory_ = 0;  // physical panel dims.
    int      rotate_ = 0, mirror_ = kMirrorNone;
    int      width_byte_ = 0, height_byte_ = 0;
};

}  // namespace winglet_ui

#endif  // CANVAS_HH_
