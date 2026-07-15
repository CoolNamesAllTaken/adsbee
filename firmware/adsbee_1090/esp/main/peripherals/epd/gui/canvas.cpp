#include "canvas.hh"

#include <cstdio>   // snprintf
#include <cstring>  // memcpy

// The drawing math (rotate/mirror/byte-addressing, Bresenham line/circle, glyph
// walk, number formatting) is ported verbatim from the vendor Waveshare
// GUI_Paint.cpp, reading `this->` members instead of the former global `Paint`.
// SetPixel is the single behavioral choke point — every primitive funnels here.

namespace winglet_ui {

Canvas::Canvas(int panel_w, int panel_h, int rotate, uint16_t fill, uint32_t caps)
    : caps_(caps),
      width_memory_(panel_w),
      height_memory_(panel_h),
      rotate_(rotate),
      mirror_(kMirrorNone) {
    width_byte_  = (panel_w % 8 == 0) ? (panel_w / 8) : (panel_w / 8 + 1);
    height_byte_ = panel_h;

    if (rotate_ == kRotate0 || rotate_ == kRotate180) {
        width_  = panel_w;
        height_ = panel_h;
    } else {
        width_  = panel_h;
        height_ = panel_w;
    }

    image_ = (uint8_t*)heap_caps_malloc((size_t)width_byte_ * height_byte_, caps_);
    if (image_) Clear(fill);
}

Canvas::~Canvas() {
    if (image_) heap_caps_free(image_);
}

Canvas::Canvas(Canvas&& o) noexcept
    : image_(o.image_),
      caps_(o.caps_),
      width_(o.width_),
      height_(o.height_),
      width_memory_(o.width_memory_),
      height_memory_(o.height_memory_),
      rotate_(o.rotate_),
      mirror_(o.mirror_),
      width_byte_(o.width_byte_),
      height_byte_(o.height_byte_) {
    o.image_ = nullptr;
}

Canvas& Canvas::operator=(Canvas&& o) noexcept {
    if (this != &o) {
        if (image_) heap_caps_free(image_);
        image_         = o.image_;
        caps_          = o.caps_;
        width_         = o.width_;
        height_        = o.height_;
        width_memory_  = o.width_memory_;
        height_memory_ = o.height_memory_;
        rotate_        = o.rotate_;
        mirror_        = o.mirror_;
        width_byte_    = o.width_byte_;
        height_byte_   = o.height_byte_;
        o.image_       = nullptr;
    }
    return *this;
}

Canvas Canvas::CreateCompatible(uint32_t caps) const {
    // Reconstruct from the physical panel dims + rotation so geometry is
    // byte-identical (guaranteeing CopyFrom compatibility).
    return Canvas(width_memory_, height_memory_, rotate_, kWhite, caps);
}

void Canvas::Clear(uint16_t color) {
    if (!image_) return;
    for (int y = 0; y < height_byte_; y++) {
        for (int x = 0; x < width_byte_; x++) {
            image_[x + y * width_byte_] = (uint8_t)color;
        }
    }
}

void Canvas::SetPixel(int x_point, int y_point, uint16_t color) {
    if (!image_) return;
    if (x_point > width_ || y_point > height_) return;

    int x, y;
    switch (rotate_) {
        case 0:
            x = x_point;
            y = y_point;
            break;
        case 90:
            x = width_memory_ - y_point - 1;
            y = x_point;
            break;
        case 180:
            x = width_memory_ - x_point - 1;
            y = height_memory_ - y_point - 1;
            break;
        case 270:
            x = y_point;
            y = height_memory_ - x_point - 1;
            break;
        default:
            return;
    }

    switch (mirror_) {
        case kMirrorNone:
            break;
        case kMirrorHorizontal:
            x = width_memory_ - x - 1;
            break;
        case kMirrorVertical:
            y = height_memory_ - y - 1;
            break;
        case kMirrorOrigin:
            x = width_memory_ - x - 1;
            y = height_memory_ - y - 1;
            break;
        default:
            return;
    }

    if (x > width_memory_ || y > height_memory_) return;

    uint32_t addr  = x / 8 + y * width_byte_;
    uint8_t  rdata = image_[addr];
    if (color == kBlack)
        image_[addr] = rdata & ~(0x80 >> (x % 8));
    else
        image_[addr] = rdata | (0x80 >> (x % 8));
}

void Canvas::DrawPoint(int x_point, int y_point, uint16_t color, int dot_pixel) {
    if (x_point > width_ || y_point > height_) return;
    // DOT_FILL_AROUND style (the vendor default), 2*dot_pixel-1 square.
    for (int xd = 0; xd < 2 * dot_pixel - 1; xd++) {
        for (int yd = 0; yd < 2 * dot_pixel - 1; yd++) {
            if (x_point + xd - dot_pixel < 0 || y_point + yd - dot_pixel < 0) break;
            SetPixel(x_point + xd - dot_pixel, y_point + yd - dot_pixel, color);
        }
    }
}

void Canvas::DrawLine(int x0, int y0, int x1, int y1, uint16_t color, LineStyle style,
                      int dot_pixel) {
    if (x0 > width_ || y0 > height_ || x1 > width_ || y1 > height_) return;

    int x = x0, y = y0;
    int dx = (x1 - x0 >= 0) ? (x1 - x0) : (x0 - x1);
    int dy = (y1 - y0 <= 0) ? (y1 - y0) : (y0 - y1);
    int x_add = x0 < x1 ? 1 : -1;
    int y_add = y0 < y1 ? 1 : -1;
    int esp = dx + dy;
    char dotted_len = 0;

    for (;;) {
        dotted_len++;
        if (style == kLineDotted && dotted_len % 3 == 0) {
            DrawPoint(x, y, kWhite, dot_pixel);
            dotted_len = 0;
        } else {
            DrawPoint(x, y, color, dot_pixel);
        }
        if (2 * esp >= dy) {
            if (x == x1) break;
            esp += dy;
            x += x_add;
        }
        if (2 * esp <= dx) {
            if (y == y1) break;
            esp += dx;
            y += y_add;
        }
    }
}

void Canvas::DrawCircle(int cx, int cy, int radius, uint16_t color, bool filled,
                        int dot_pixel) {
    if (cx > width_ || cy >= height_) return;

    int xc = 0, yc = radius;
    int esp = 3 - (radius << 1);
    if (filled) {
        while (xc <= yc) {
            for (int sy = xc; sy <= yc; sy++) {
                DrawPoint(cx + xc, cy + sy, color, 1);
                DrawPoint(cx - xc, cy + sy, color, 1);
                DrawPoint(cx - sy, cy + xc, color, 1);
                DrawPoint(cx - sy, cy - xc, color, 1);
                DrawPoint(cx - xc, cy - sy, color, 1);
                DrawPoint(cx + xc, cy - sy, color, 1);
                DrawPoint(cx + sy, cy - xc, color, 1);
                DrawPoint(cx + sy, cy + xc, color, 1);
            }
            if (esp < 0) {
                esp += 4 * xc + 6;
            } else {
                esp += 10 + 4 * (xc - yc);
                yc--;
            }
            xc++;
        }
    } else {
        while (xc <= yc) {
            DrawPoint(cx + xc, cy + yc, color, dot_pixel);
            DrawPoint(cx - xc, cy + yc, color, dot_pixel);
            DrawPoint(cx - yc, cy + xc, color, dot_pixel);
            DrawPoint(cx - yc, cy - xc, color, dot_pixel);
            DrawPoint(cx - xc, cy - yc, color, dot_pixel);
            DrawPoint(cx + xc, cy - yc, color, dot_pixel);
            DrawPoint(cx + yc, cy - xc, color, dot_pixel);
            DrawPoint(cx + yc, cy + xc, color, dot_pixel);
            if (esp < 0) {
                esp += 4 * xc + 6;
            } else {
                esp += 10 + 4 * (xc - yc);
                yc--;
            }
            xc++;
        }
    }
}

void Canvas::DrawChar(int x_point, int y_point, char ch, sFONT* font, uint16_t bg,
                      uint16_t fg) {
    if (x_point > width_ || y_point > height_) return;

    uint32_t char_offset =
        (ch - ' ') * font->Height * (font->Width / 8 + (font->Width % 8 ? 1 : 0));
    const unsigned char* ptr = &font->table[char_offset];

    for (int page = 0; page < font->Height; page++) {
        for (int column = 0; column < font->Width; column++) {
            if (kWhite == bg) {  // FONT_BACKGROUND == background: fast scan
                if (*ptr & (0x80 >> (column % 8))) SetPixel(x_point + column, y_point + page, fg);
            } else {
                if (*ptr & (0x80 >> (column % 8)))
                    SetPixel(x_point + column, y_point + page, fg);
                else
                    SetPixel(x_point + column, y_point + page, bg);
            }
            if (column % 8 == 7) ptr++;
        }
        if (font->Width % 8 != 0) ptr++;
    }
}

void Canvas::DrawString(int x_start, int y_start, const char* s, sFONT* font, uint16_t bg,
                        uint16_t fg) {
    if (x_start > width_ || y_start > height_) return;

    int x = x_start, y = y_start;
    while (*s != '\0') {
        if ((x + font->Width) > width_) {
            x = x_start;
            y += font->Height;
        }
        if ((y + font->Height) > height_) {
            x = x_start;
            y = y_start;
        }
        DrawChar(x, y, *s, font, bg, fg);
        s++;
        x += font->Width;
    }
}

void Canvas::DrawNum(int x, int y, int32_t number, sFONT* font, uint16_t bg, uint16_t fg) {
    char buf[16];
    // Match the vendor's base-10, no-padding formatting (handles 0 and negatives
    // are not produced by callers, but snprintf covers them safely).
    snprintf(buf, sizeof buf, "%ld", (long)number);
    DrawString(x, y, buf, font, bg, fg);
}

void Canvas::CopyFrom(const Canvas& src) {
    if (!image_ || !src.image_) return;
    if (src.byte_size() != byte_size()) return;  // geometry mismatch: no-op.
    memcpy(image_, src.image_, (size_t)byte_size());
}

}  // namespace winglet_ui
