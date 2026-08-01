#!/usr/bin/env python3
"""Bake the Winglet map UI's fixed-shape assets into C `const` sprite tables.

Emits `ui_sprites_data.cpp` containing:
  - 1bpp chrome sprites (ink-only, transparent elsewhere): the right-rail
    zoom-in / gear / zoom-out icons and the battery frame.
  - 2bpp haloed sprites (0=transparent, 1=ink/black, 2=halo/white): the scale
    bar and the 360 pre-rotated aircraft arrows (one per whole degree).

The rasterizers below MIRROR the C++ primitives in ui_primitives.cpp /
map_screen.cpp exactly, so the baked sprites are pixel-identical to what the
live code draws. If those primitives change, re-run:

  python gen_ui_sprites.py

(run from this dir; writes ../ui_sprites_data.cpp)

Sprite byte layout:
  1bpp: rows top->bottom, ceil(w/8) bytes/row, MSB-first (bit7 = leftmost).
  2bpp: rows top->bottom, ceil(w*2/8) bytes/row, 2 bits/pixel packed MSB-first
        (pixel p occupies bits [7-2*(p%4)-1 .. ], value 0..3).
"""
import math
import os

# ---- pixel-grid canvas -----------------------------------------------------
# Values: 0 transparent, 1 ink (black), 2 halo (white).
class Grid:
    def __init__(self, w, h):
        self.w, self.h = w, h
        self.px = [[0] * w for _ in range(h)]

    def set(self, x, y, v):
        if 0 <= x < self.w and 0 <= y < self.h:
            self.px[y][x] = v

    def fill_rect(self, x, y, w, h, v):
        for yy in range(y, y + h):
            for xx in range(x, x + w):
                self.set(xx, yy, v)


# ---- C++ primitive mirrors (ink only; halo added separately) ---------------
def annulus(g, cx, cy, r_out, r_in, v=1):
    R = math.ceil(r_out)
    for yy in range(-R, R + 1):
        for xx in range(-R, R + 1):
            d = math.sqrt(xx * xx + yy * yy)
            if d <= r_out + 0.5 and d >= r_in - 0.5:
                g.set(cx + xx, cy + yy, v)


def plus_circle(g, cx, cy, r, minus, v=1):
    annulus(g, cx, cy, r, r - 1.8, v)
    arm = int(r - 4)
    g.fill_rect(cx - arm, cy - 1, arm * 2 + 1, 3, v)
    if not minus:
        g.fill_rect(cx - 1, cy - arm, 3, arm * 2 + 1, v)


def gear(g, cx, cy, r, v=1):
    for k in range(8):
        a = k * math.pi / 4.0
        tx = round(cx + math.cos(a) * (r + 1.4))
        ty = round(cy + math.sin(a) * (r + 1.4))
        g.fill_rect(tx - 1, ty - 1, 3, 3, v)
    annulus(g, cx, cy, r, r - 1.8, v)
    annulus(g, cx, cy, 2.7, 1.3, v)


def battery_frame(g, bx, by, v=1):
    bw, bh = 15, 9
    g.fill_rect(bx, by, bw, 1, v)             # top
    g.fill_rect(bx, by + bh - 1, bw, 1, v)    # bottom
    g.fill_rect(bx, by, 1, bh, v)             # left
    g.fill_rect(bx + bw - 1, by, 1, bh, v)    # right
    g.fill_rect(bx + bw, by + 2, 2, 5, v)     # nub
    # (internal fill bar is drawn live from battery pct; not baked)


def fill_polygon(g, xs, ys, v=1):
    n = len(xs)
    y0 = math.floor(min(ys))
    y1 = math.ceil(max(ys))
    for y in range(y0, y1 + 1):
        yc = y + 0.5
        xcross = []
        for i in range(n):
            j = (i + 1) % n
            yi, yj = ys[i], ys[j]
            if (yi <= yc and yj > yc) or (yj <= yc and yi > yc):
                t = (yc - yi) / (yj - yi)
                xcross.append(xs[i] + t * (xs[j] - xs[i]))
        xcross.sort()
        for i in range(0, len(xcross) - 1, 2):
            xa = math.ceil(xcross[i] - 0.5)
            xb = math.floor(xcross[i + 1] - 0.5)
            for x in range(xa, xb + 1):
                g.set(x, y, v)


def arrow_ink(g, cx, cy, s, deg, v=1):
    a = deg * math.pi / 180.0
    base = [(0.0, -s), (-0.82 * s, 0.72 * s), (0.0, 0.30 * s), (0.82 * s, 0.72 * s)]
    xs, ys = [], []
    for (X, Y) in base:
        xs.append(cx + X * math.cos(a) - Y * math.sin(a))
        ys.append(cy + X * math.sin(a) + Y * math.cos(a))
    fill_polygon(g, xs, ys, v)


# ---- halo: add white (2) at the 8-neighbors of every ink (1) pixel ---------
HALO = [(-1, -1), (0, -1), (1, -1), (-1, 0), (1, 0), (-1, 1), (0, 1), (1, 1)]


def add_halo(g):
    ink = [(x, y) for y in range(g.h) for x in range(g.w) if g.px[y][x] == 1]
    for (x, y) in ink:
        for (dx, dy) in HALO:
            nx, ny = x + dx, y + dy
            if 0 <= nx < g.w and 0 <= ny < g.h and g.px[ny][nx] == 0:
                g.px[ny][nx] = 2  # halo only where nothing already drawn


# ---- packers ---------------------------------------------------------------
def pack_1bpp(g):
    """Ink (value 1) -> set bit; everything else -> clear."""
    stride = (g.w + 7) // 8
    out = bytearray()
    for y in range(g.h):
        row = bytearray(stride)
        for x in range(g.w):
            if g.px[y][x] == 1:
                row[x >> 3] |= 0x80 >> (x & 7)
        out += row
    return bytes(out), stride


def pack_2bpp(g):
    """2 bits/pixel, MSB-first: pixel p in byte p//4, shift 6-2*(p%4)."""
    stride = (g.w * 2 + 7) // 8
    out = bytearray()
    for y in range(g.h):
        row = bytearray(stride)
        for x in range(g.w):
            val = g.px[y][x] & 0x3
            byte_i = x >> 2
            shift = 6 - 2 * (x & 3)
            row[byte_i] |= val << shift
        out += row
    return bytes(out), stride


# ---- C emitters ------------------------------------------------------------
def bytes_literal(b):
    return ", ".join(f"0x{v:02x}" for v in b)


def emit_sprite_1bpp(name, g):
    data, stride = pack_1bpp(g)
    lines = [f"static const uint8_t {name}_bits[] = {{"]
    for r in range(g.h):
        row = data[r * stride:(r + 1) * stride]
        lines.append(f"  {bytes_literal(row)},")
    lines.append("};")
    lines.append(f"const Sprite1bpp {name} = {{ {name}_bits, {g.w}, {g.h} }};\n")
    return "\n".join(lines)


def emit_arrow_table(grids):
    # All arrows share w/h/stride; emit one flat byte table + a Sprite2bpp array.
    w, h = grids[0].w, grids[0].h
    _, stride = pack_2bpp(grids[0])
    frame_bytes = stride * h
    lines = ["static const uint8_t kArrowSprites_bits[] = {"]
    for i, g in enumerate(grids):
        data, _ = pack_2bpp(g)
        lines.append(f"  /* {i} deg */ {bytes_literal(data)},")
    lines.append("};")
    lines.append(f"const Sprite2bpp kArrowSprites[360] = {{")
    for i in range(360):
        off = i * frame_bytes
        lines.append(f"  {{ kArrowSprites_bits + {off}, {w}, {h} }},")
    lines.append("};\n")
    return "\n".join(lines), w, h


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    out_path = os.path.join(here, "..", "ui_sprites_data.cpp")

    parts = []

    # --- chrome icons: 1bpp, ink-only (no halo, matching the live icons) ----
    # Zoom-in plusCircle r=9 -> extent radius ~9, use 21x21 grid center (10,10).
    g = Grid(21, 21); plus_circle(g, 10, 10, 9, minus=False); parts.append(emit_sprite_1bpp("kZoomInSprite", g))
    # Gear r=7 (teeth reach r+1.4 ~ 8.4) -> 19x19 center (9,9).
    g = Grid(19, 19); gear(g, 9, 9, 7); parts.append(emit_sprite_1bpp("kGearSprite", g))
    # Zoom-out plusCircle r=9 minus -> 21x21 center (10,10).
    g = Grid(21, 21); plus_circle(g, 10, 10, 9, minus=True); parts.append(emit_sprite_1bpp("kZoomOutSprite", g))
    # Battery frame: bw=15 + nub 2 = 17 wide, bh=9 tall. Origin at (0,0).
    g = Grid(18, 9); battery_frame(g, 0, 0); parts.append(emit_sprite_1bpp("kBatteryFrameSprite", g))

    # --- scale bar: 2bpp haloed. Geometry from map_screen ScaleBarDraw:
    #     bar (x1..x2, 2px), start tick and end tick 7px tall starting 5px above.
    #     Width = 42 (kScaleBarWidth), plus 1px halo margin each side.
    sbw = 42
    g = Grid(sbw + 2, 14)  # +2 halo margin x; height 14 covers tick (y-5..y+2) + halo
    # place bar baseline so tick top (y-5) and bar bottom (y+2) fit with halo:
    bar_y = 7  # within-grid baseline
    x1, x2 = 1, 1 + sbw
    g.fill_rect(x1, bar_y, x2 - x1, 2, 1)       # bar
    g.fill_rect(x1, bar_y - 5, 2, 7, 1)         # start tick
    g.fill_rect(x2 - 2, bar_y - 5, 2, 7, 1)     # end tick
    add_halo(g)
    data, stride = pack_2bpp(g)
    sb_lines = [f"static const uint8_t kScaleBarSprite_bits[] = {{"]
    for r in range(g.h):
        sb_lines.append(f"  {bytes_literal(data[r*stride:(r+1)*stride])},")
    sb_lines.append("};")
    sb_lines.append(f"const Sprite2bpp kScaleBarSprite = {{ kScaleBarSprite_bits, {g.w}, {g.h} }};")
    sb_lines.append(f"// blit origin offset: bar (x1,bar_y) sits at grid ({x1},{bar_y})")
    sb_lines.append(f"const int kScaleBarSpriteOriginX = {x1};")
    sb_lines.append(f"const int kScaleBarSpriteOriginY = {bar_y};\n")
    parts.append("\n".join(sb_lines))

    # --- 360 aircraft arrows: 2bpp haloed, 20x20 center (10,10) --------------
    ARROW_W = ARROW_H = 20
    ARROW_CX = ARROW_CY = 10
    grids = []
    for deg in range(360):
        g = Grid(ARROW_W, ARROW_H)
        arrow_ink(g, ARROW_CX, ARROW_CY, 8.0, float(deg), 1)
        add_halo(g)
        grids.append(g)
    arrow_block, aw, ah = emit_arrow_table(grids)
    parts.append(arrow_block)

    header = (
        "// Generated by tools/gen_ui_sprites.py. Do not edit by hand.\n"
        "// Pixel-identical mirror of the primitives in ui_primitives.cpp /\n"
        "// map_screen.cpp. Re-run the generator if those change.\n"
        '#include "ui_sprites.hh"\n\n'
        "namespace winglet_ui {\n\n"
    )
    footer = (
        f"// Arrow sprite grid is {aw}x{ah}, ownship-arrow center at "
        f"({ARROW_CX},{ARROW_CY}); blit at (contact_x-{ARROW_CX}, contact_y-{ARROW_CY}).\n"
        f"const int kArrowSpriteCenterX = {ARROW_CX};\n"
        f"const int kArrowSpriteCenterY = {ARROW_CY};\n\n"
        "}  // namespace winglet_ui\n"
    )

    with open(out_path, "w") as f:
        f.write(header)
        f.write("\n".join(parts))
        f.write("\n")
        f.write(footer)

    total = sum(len(pack_2bpp(g)[0]) for g in grids)
    print(f"wrote {out_path}")
    print(f"  chrome: 4 x 1bpp icons; scale bar 2bpp {sbw + 2}x14")
    print(f"  arrows: 360 x 2bpp {aw}x{ah} = {total} bytes")


if __name__ == "__main__":
    main()
