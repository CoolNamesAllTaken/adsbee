# terrain-tiler

Bakes whole-world terrain into `1°×1°` `.map` tiles for the ADSBee Winglet microSD
map (Phase 2 of the map-topography feature). Output is copied to the card as
`/sd/tiles/<RRR>/<CCC>.map` and read by the on-device `TerrainLoader`.

The on-disk format is defined by
`firmware/adsbee_1090/esp/main/peripherals/terrain/terrain_tile.hh` — the packer
(`terrain_tiler/pack.py`) mirrors those structs byte-for-byte (verified by
`tests/test_roundtrip.py`, which needs no geo libraries).

## Data sources (both public domain / free for commercial use)

Download once into a local `data/` cache; the tiler only reads them.

**Elevation — ETOPO 2022 (NOAA NCEI):**
- Default: 30 arc-second global GeoTIFF (~900 m, ~600 MB–1 GB).
- `--grid`/`--fast` dry runs can use the 60 arc-second variant (~200 MB).
- Product page: https://www.ncei.noaa.gov/products/etopo-global-relief-model
- The examples use `ETOPO_2022_v1_30s_N90W180_surface.tif` — the single global
  (`N90W180`) 30 arc-second **surface** tile. "Surface" (top of ice/canopy) is
  chosen over "bedrock" so terrain matches what a pilot sees; either works, since
  we clamp sea level and below to 0.
- Save the GeoTIFF and pass its path via `--dem`.

**Vectors — Natural Earth 1:10m (two separate downloads):**
- Physical: `ne_10m_coastline`, `ne_10m_lakes`, `ne_10m_rivers_lake_centerlines`
  from https://www.naturalearthdata.com/downloads/10m-physical-vectors/ —
  unzip into `data/10m_physical/` and pass via `--ne-physical`.
- Cultural: `ne_10m_roads`, `ne_10m_populated_places`
  from https://www.naturalearthdata.com/downloads/10m-cultural-vectors/ —
  unzip into `data/10m_cultural/` and pass via `--ne-cultural`.
- Each dir is searched recursively, so the extra nesting the NE zips unpack into
  (e.g. `data/10m_cultural/10m_cultural/…`) is fine — no need to flatten.

## Install & run

```bash
cd firmware/scripts/terrain_tiler
poetry install

# Fast format check (no geo libs, no downloads):
python tests/test_roundtrip.py

# Single tile end-to-end (dev loop). ROW,COL are tile indices:
#   row = lat + 86 (0..171), col = lon + 180 (0..359).
poetry run terrain-tiler build --tile 133,58 \
    --dem data/ETOPO_2022_v1_30s_N90W180_surface.tif \
    --ne-physical data/10m_physical --ne-cultural data/10m_cultural \
    --out ./out_sd/tiles

# Whole world (a few hours CPU; output ~2.3 GB at 256²).
# -j/--jobs fans the build across CPU cores (default: all of them):
poetry run terrain-tiler build -j 8 \
    --dem data/ETOPO_2022_v1_30s_N90W180_surface.tif \
    --ne-physical data/10m_physical --ne-cultural data/10m_cultural \
    --out ./out_sd/tiles

# Then copy the tiles to the microSD card:
cp -r out_sd/tiles /Volumes/<SDCARD>/tiles
```

## Notes

- `--grid {128,256,512}`: elevation samples per tile side (default 256 ≈ 434 m/sample
  at the equator). 512 is a "premium card" option; the device reads the grid dims from
  each tile header, so no firmware change is needed to switch.
- `--no-vectors`: elevation-only build (skips Natural Earth).
- `-j`/`--jobs N`: worker processes for the whole-world build (default: all cores).
  The build is CPU-bound in Python, so it uses processes, not threads. Each worker
  loads the Natural Earth layers once (~6 s) then streams tiles, so scaling is
  near-linear over the full 61,920-tile run. Ignored for single `--tile` builds.
- Elevation is stored raw/uncompressed for now (a header flag reserves zlib later).
- All tiles are written, including ocean (flat grid, no vector records), so the device
  never has to check for a missing file.
