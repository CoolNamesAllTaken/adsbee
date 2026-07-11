"""terrain-tiler CLI: bake ETOPO + Natural Earth into /sd/tiles/<RRR>/<CCC>.map.

Tile grid mirrors terrain_tile.hh: 1x1-degree tiles, latitude clamped to
[-86, +86]. Row RR in [0,171] = floor((lat+90)/1) - (90-86)=... see tile_bounds().
Every tile in range is written (ocean tiles get a flat grid + no vectors).

Usage:
  poetry run terrain-tiler build --out ./out_sd/tiles \\
      --dem data/etopo_2022_30s.tif \\
      --ne-physical data/10m_physical --ne-cultural data/10m_cultural [--grid 256|512]
  poetry run terrain-tiler build --tile 137,58 ...     # single tile (dev loop)
"""
import argparse
import os
from concurrent.futures import ProcessPoolExecutor

from . import pack
from .dem import DemSource, quantize_grid
from .vectors import VectorSources

# Grid geometry (mirror terrain_tile.hh).
TILE_STEP_DEG = 1
LAT_MIN = -86
LAT_MAX = 86
NUM_ROWS = (LAT_MAX - LAT_MIN) // TILE_STEP_DEG  # 172
NUM_COLS = 360 // TILE_STEP_DEG                  # 360


def tile_bounds(row, col):
    """(lat0, lon0) SW corner for a tile index. row 0 = southernmost (lat -86)."""
    lat0 = LAT_MIN + row * TILE_STEP_DEG
    lon0 = -180 + col * TILE_STEP_DEG
    return lat0, lon0


def tile_path(out_dir, row, col):
    return os.path.join(out_dir, f"{row:03X}", f"{col:03X}.map")


def build_tile(out_dir, row, col, dem, vecs, grid_dim):
    lat0, lon0 = tile_bounds(row, col)
    span = TILE_STEP_DEG

    grid_f32 = dem.read_tile_grid(lat0, lon0, span, grid_dim)
    elev_bytes, base_m, step_m = quantize_grid(grid_f32)

    if vecs is not None:
        water_b, water_n, road_b, road_n = vecs.clip_tile(lat0, lon0, span)
        mask_b = vecs.rasterize_water_mask(lat0, lon0, span, grid_dim)
    else:
        water_b, water_n, road_b, road_n = b"", 0, b"", 0
        mask_b = b""

    blob = pack.pack_tile(
        tile_lat0_e6=int(round(lat0 * 1e6)),
        tile_lon0_e6=int(round(lon0 * 1e6)),
        tile_span_e3=span * 1000,
        elev_bytes=elev_bytes, elev_grid_w=grid_dim, elev_grid_h=grid_dim,
        elev_base_m=base_m, elev_step_m=step_m, elev_bytes_per_sample=1,
        water_records=water_b, water_count=water_n,
        road_records=road_b, road_count=road_n,
        water_mask_bytes=mask_b, water_mask_w=grid_dim, water_mask_h=grid_dim,
    )

    path = tile_path(out_dir, row, col)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "wb") as f:
        f.write(blob)
    return len(blob), water_n, road_n


# --- multiprocessing workers ---------------------------------------------
# The whole-world build is CPU-bound in Python (per-feature clip loops + record
# encoding), so the GIL caps thread speedup near 1x. We use processes instead.
# The catch: VectorSources is large (all NE layers + spatial indexes) and can't
# be cheaply pickled per task. So each worker loads DemSource + VectorSources
# ONCE in an initializer, stashes them in these module globals, and then chews
# through many (row, col) tasks — only the tiny tuples cross the process boundary.

_W = {}   # per-worker state: {"dem", "vecs", "out", "grid"}


def _worker_init(dem_path, ne_physical, ne_cultural, no_vectors, out_dir, grid_dim):
    _W["dem"] = DemSource(dem_path)
    _W["vecs"] = None if no_vectors else VectorSources(ne_physical, ne_cultural)
    _W["out"] = out_dir
    _W["grid"] = grid_dim


def _worker_build(rowcol):
    row, col = rowcol
    return build_tile(_W["out"], row, col, _W["dem"], _W["vecs"], _W["grid"])


def cmd_build(args):
    grid_dim = args.grid

    if args.tile:
        # Single tile: no pool, just build inline (dev loop).
        dem = DemSource(args.dem)
        vecs = None if args.no_vectors else VectorSources(args.ne_physical, args.ne_cultural)
        rr, cc = (int(x) for x in args.tile.split(","))
        size, wn, rn = build_tile(args.out, rr, cc, dem, vecs, grid_dim)
        print(f"tile {rr:03X}/{cc:03X}: {size} B, water={wn}, roads/cities={rn} "
              f"-> {tile_path(args.out, rr, cc)}")
        dem.close()
        return

    jobs = args.jobs if args.jobs and args.jobs > 0 else (os.cpu_count() or 1)

    init_args = (args.dem, args.ne_physical, args.ne_cultural,
                 args.no_vectors, args.out, grid_dim)

    # Stream every tile through one map() so workers stay saturated end to end
    # (no per-row barrier where fast workers idle waiting for the slowest tile).
    # Results come back in submission order, i.e. row-major, so we can still print
    # per-row progress as each row's last tile arrives. chunksize amortizes IPC.
    all_tiles = [(row, col) for row in range(NUM_ROWS) for col in range(NUM_COLS)]

    total_bytes = 0
    total_tiles = 0
    with ProcessPoolExecutor(max_workers=jobs,
                             initializer=_worker_init,
                             initargs=init_args) as pool:
        for size, _, _ in pool.map(_worker_build, all_tiles, chunksize=16):
            total_bytes += size
            total_tiles += 1
            if total_tiles % NUM_COLS == 0:      # finished a full row
                row = total_tiles // NUM_COLS
                print(f"row {row}/{NUM_ROWS} done "
                      f"({total_tiles} tiles, {total_bytes / 1e6:.1f} MB so far, "
                      f"{jobs} procs)")

    print(f"\nDONE: {total_tiles} tiles, {total_bytes / 1e9:.2f} GB total "
          f"(grid {grid_dim}x{grid_dim}). Copy {args.out} to the card as /sd/tiles/")


def main():
    ap = argparse.ArgumentParser(prog="terrain-tiler")
    sub = ap.add_subparsers(dest="cmd", required=True)

    b = sub.add_parser("build", help="build tiles")
    b.add_argument("--out", default="./out_sd/tiles", help="output tile root dir")
    b.add_argument("--dem", required=True, help="ETOPO global GeoTIFF path")
    b.add_argument("--ne-physical", default="data/10m_physical",
                   help="Natural Earth 10m physical vectors dir (coastline, lakes, rivers)")
    b.add_argument("--ne-cultural", default="data/10m_cultural",
                   help="Natural Earth 10m cultural vectors dir (roads, populated places)")
    b.add_argument("--grid", type=int, default=pack.ELEV_GRID_DIM, choices=[128, 256, 512],
                   help="elevation samples per tile side")
    b.add_argument("--tile", help="single tile 'ROW,COL' (dev loop) instead of whole world")
    b.add_argument("--no-vectors", action="store_true", help="elevation only (skip NE vectors)")
    b.add_argument("-j", "--jobs", type=int, default=0,
                   help="worker threads for the whole-world build (default: all cores). "
                        "Ignored for single --tile builds.")
    b.set_defaults(func=cmd_build)

    args = ap.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
