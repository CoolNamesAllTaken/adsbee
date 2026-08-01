"""Elevation layer: read ETOPO 2022 global relief, resample per tile, quantize.

Produces the per-tile 8-bit elevation grid that the MCU contours at render time.
The grid is a little coarser than the closest map zoom's pixels (256x256 over a
1-degree tile ~= 434 m spacing at the equator); the device interpolates between
samples when marching contours.

Source: ETOPO 2022 (NOAA NCEI), public domain / free for commercial use.
  30 arc-second GeoTIFF (default): ~900 m native, EPSG:4326.
  60 arc-second (--fast): ~1.8 km, ~200 MB, for quick dry runs.
Download once (see README) into the data cache; this module only reads it.
"""
import numpy as np
import rasterio
from rasterio.enums import Resampling
from rasterio.windows import from_bounds

from . import pack


class DemSource:
    """Wraps a single global ETOPO GeoTIFF for windowed per-tile reads."""

    def __init__(self, geotiff_path):
        self.path = geotiff_path
        self._ds = rasterio.open(geotiff_path)

    def close(self):
        self._ds.close()

    def read_tile_grid(self, lat0, lon0, span_deg, grid_dim):
        """Read + resample the DEM for the tile whose SW corner is (lat0, lon0),
        returning a float32 array [grid_dim, grid_dim], row 0 = NORTH edge,
        col 0 = WEST edge (matches the renderer's north-up, y-down layout).

        Sea level and below is clamped to 0 (we only draw land relief)."""
        lat1 = lat0 + span_deg
        lon1 = lon0 + span_deg
        # Window in the source raster covering the tile bbox.
        window = from_bounds(lon0, lat0, lon1, lat1, self._ds.transform)
        # Read resampled to grid_dim x grid_dim. rasterio returns row 0 = north
        # (top of the window) because the source transform is north-up.
        arr = self._ds.read(
            1,
            window=window,
            out_shape=(grid_dim, grid_dim),
            resampling=Resampling.bilinear,
            boundless=True,
            fill_value=0,
        ).astype(np.float32)
        # Clamp ocean/below-sea-level to 0.
        arr = np.where(arr < 0, 0.0, arr)
        return arr


def quantize_grid(grid_f32, step_m=40):
    """Quantize a float32 elevation grid to 8-bit codes.

    sample_m = base + code*step ; code in [0,254] ; 255 = void.
    Returns (elev_bytes, base_m, step_m). base is the tile's min elevation.
    Flat/ocean tiles (all zero) yield an all-zero grid with base=0.
    """
    finite = np.isfinite(grid_f32)
    if not finite.any():
        base = 0
        codes = np.full(grid_f32.shape, pack.ELEV_VOID_CODE, dtype=np.uint8)
        return codes.tobytes(), base, step_m

    base = int(np.floor(np.nanmin(grid_f32[finite])))
    # Map to codes, clamp to [0, 254], mark non-finite as void.
    codes_f = np.floor((grid_f32 - base) / float(step_m))
    codes_f = np.clip(codes_f, 0, 254)
    codes = codes_f.astype(np.uint8)
    codes[~finite] = pack.ELEV_VOID_CODE
    # Row-major, north->south rows, west->east within a row (already so from read).
    return codes.tobytes(), base, step_m
