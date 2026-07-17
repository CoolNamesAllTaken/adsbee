"""Build the global elevation pyramid inside `world.map`.

Each pyramid level is ONE global equirectangular raster (north-up) on a shared
grid-registered lattice of `n*2^L + 1` samples. We resample ETOPO to the L0
lattice ONCE (held in RAM, ~1 GB uint8) and derive every coarser level by exact
2:1 decimation (`codes[::2, ::2]`) — because the lattice is `n*2^L+1`, a coarse
sample coincides *exactly* with an L0 sample (true subset, zero half-pixel drift
-> no inter-level popping). This is both correct (perfect registration) and fast
(one ETOPO pass instead of a global resample per band).

Each level is tiled into shared-edge 64x64 blocks (stride 63: adjacent blocks
duplicate their boundary row/col) so features crossing a block edge stay
continuous. Blocks are encoded by mapfmt.encode_block (constant / deflate /
predictor+deflate, smallest wins).

Elevation quantization matches dem.quantize_grid: code = clamp(floor(elev/step),
0, 254), step=40 m, global base 0 (sea level clamped to 0), 0xFF = void.
"""
import numpy as np
from rasterio.windows import from_bounds
from rasterio.transform import from_bounds as transform_from_bounds
from rasterio.enums import Resampling
from rasterio.features import rasterize

from . import mapfmt

# Read ETOPO to the L0 lattice in latitude bands of this many rows, to bound the
# transient float32 buffer (full-globe float32 would be ~3.7 GB; a 512-row band
# is ~90 MB). The uint8 result accumulates into the full L0 array.
_L0_READ_BAND_ROWS = 512

# River centerlines are 0-width lines; buffer them (degrees) so they rasterize as
# a ~1-sample-wide water strip on the L0 lattice. Matches vectors.RIVER_BUFFER_DEG.
_RIVER_BUFFER_DEG = 0.004


def _quantize(arr_f32, step_m=mapfmt.ELEV_STEP_M):
    a = np.where(arr_f32 < 0, 0.0, arr_f32)
    return np.clip(np.floor(a / float(step_m)), 0, 254).astype(np.uint8)


def build_l0_codes(ds, num_levels, progress=None):
    """Resample ETOPO to the full L0 lattice, returning a (h, w) uint8 array.

    Row y -> latitude 86 - y/128; full -180..180 longitude. Read in bands to cap
    the float32 working buffer; each band is boundless (edge-filled) so partial
    edges stay valid."""
    w, h = mapfmt.level_dims(0, num_levels)
    codes = np.empty((h, w), np.uint8)
    spd = mapfmt.FINEST_SAMPLES_PER_DEG
    lat_top = 86.0
    y = 0
    while y < h:
        nrows = min(_L0_READ_BAND_ROWS, h - y)
        lat1 = lat_top - (y / spd)
        lat0 = lat_top - ((y + nrows) / spd)
        win = from_bounds(-180.0, lat0, 180.0, lat1, ds.transform)
        band = ds.read(1, window=win, out_shape=(nrows, w),
                       resampling=Resampling.bilinear, boundless=True,
                       fill_value=0).astype(np.float32)
        codes[y:y + nrows] = _quantize(band)
        y += nrows
        if progress:
            progress(min(y, h), h)
    return codes


def build_l0_water(vec_sources, num_levels, progress=None):
    """Rasterize a global L0 water mask (uint8 0/1) on the SAME L0 lattice as
    build_l0_codes: row 0 = north (lat +86), full -180..180 longitude.

    Water = Natural Earth ocean + lakes polygons + buffered river centerlines
    (the same union the legacy per-tile mask used, vectors.rasterize_water_mask).
    Built in latitude bands to bound the transient geometry set. The caller burns
    this into the L0 codes (codes[water==1] = ELEV_WATER_CODE) before decimation,
    so every coarser level inherits water for free via the [::2,::2] subset.
    """
    from shapely.geometry import box

    w, h = mapfmt.level_dims(0, num_levels)
    water = np.zeros((h, w), np.uint8)
    spd = mapfmt.FINEST_SAMPLES_PER_DEG
    lat_top = (mapfmt.WORLD_LAT0_E6 * -1) / 1_000_000.0  # +86
    ocean = vec_sources.layers.get("ocean")
    lakes = vec_sources.layers.get("lakes")
    rivers = vec_sources.layers.get("rivers")

    y = 0
    while y < h:
        nrows = min(_L0_READ_BAND_ROWS, h - y)
        lat1 = lat_top - (y / spd)             # north edge of the band
        lat0 = lat_top - ((y + nrows) / spd)   # south edge of the band
        bbox = box(-180.0, lat0, 180.0, lat1)
        geoms = []
        for gdf in (ocean, lakes):
            if gdf is None or len(gdf) == 0:
                continue
            for i in gdf.sindex.query(bbox, predicate="intersects"):
                g = gdf.geometry.iloc[i].intersection(bbox)
                if not g.is_empty:
                    geoms.append(g)
        if rivers is not None and len(rivers):
            for i in rivers.sindex.query(bbox, predicate="intersects"):
                g = rivers.geometry.iloc[i].intersection(bbox)
                if not g.is_empty:
                    geoms.append(g.buffer(_RIVER_BUFFER_DEG))
        if geoms:
            # north-up transform for this band: row 0 = lat1 (north).
            transform = transform_from_bounds(-180.0, lat0, 180.0, lat1, w, nrows)
            band = rasterize(((g, 1) for g in geoms), out_shape=(nrows, w),
                             transform=transform, fill=0, all_touched=True,
                             dtype=np.uint8)
            water[y:y + nrows] = band
        y += nrows
        if progress:
            progress(min(y, h), h)
    return water


def level_codes(l0_codes, level, num_levels):
    """Exact 2:1 decimation of L0 down to `level`. Returns (h_l, w_l) uint8 view.

    Slicing [::factor, ::factor] over an (n*2^0+1) array yields exactly
    (n*2^-level + 1) samples, each coinciding with an L0 lattice point."""
    factor = 1 << level
    sub = l0_codes[::factor, ::factor]
    w, h = mapfmt.level_dims(level, num_levels)
    # Slicing gives ceil dims; the registered target is exactly (w,h). They match
    # for n*2^L+1 lattices, but guard against off-by-one on the last sample.
    return np.ascontiguousarray(sub[:h, :w])


def iter_level_blocks(codes):
    """Yield (by, bx, codec, stored, fill, raw_len) for every shared-edge 64x64
    block of a level's code array, row-major. Partial edge blocks are padded by
    edge replication so every block is exactly 64x64."""
    stride = mapfmt.BLOCK_STRIDE
    dim = mapfmt.BLOCK_DIM
    h, w = codes.shape
    blocks_y = mapfmt.blocks_across(h)
    blocks_x = mapfmt.blocks_across(w)
    for by in range(blocks_y):
        y0 = by * stride
        rows = codes[y0:y0 + dim]
        if rows.shape[0] < dim:
            pad = np.empty((dim, w), np.uint8)
            pad[:rows.shape[0]] = rows
            pad[rows.shape[0]:] = rows[-1:]
            rows = pad
        for bx in range(blocks_x):
            x0 = bx * stride
            blk = rows[:, x0:x0 + dim]
            if blk.shape[1] < dim:
                p = np.empty((dim, dim), np.uint8)
                p[:, :blk.shape[1]] = blk
                p[:, blk.shape[1]:] = blk[:, -1:]
                blk = p
            codec, stored, fill = mapfmt.encode_block(np.ascontiguousarray(blk))
            yield by, bx, codec, stored, fill, dim * dim


def level_geometry(level, num_levels):
    """(w, h, blocks_x, blocks_y) for a level."""
    w, h = mapfmt.level_dims(level, num_levels)
    return w, h, mapfmt.blocks_across(w), mapfmt.blocks_across(h)
