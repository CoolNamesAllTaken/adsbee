# Terrain Map System — Theory of Operation

This document explains, end to end, how the ADSBee terrain map works: what raw
data goes in, how the host tiler transforms it into a single `world.map` archive,
exactly how that archive is laid out on disk, and how the device reads it to draw
terrain at any zoom. It covers the **current** `world.map` (pyramid) format; the
legacy per-1°-tile format is summarized at the end for context.

See `README.md` for build/usage. The Python module `terrain_tiler/mapfmt.py` is
the single source of truth for every on-disk struct; this document is
self-contained and does not depend on any external notes.

---

## 1. The problem this system solves

An ADSBee Winglet displays a moving-map with terrain relief on a **264×176 1-bit
e-paper** screen, driven by an **ESP32-S3** reading from a **microSD card**
(FATFS over SDMMC, 1-bit, ~1 MB/s effective). Requirements that shaped the design:

1. **Few files.** The old format wrote 61,920 individual `.map` files; the sheer
   file/directory count — not data volume — dominated the time to copy a card.
   → One archive file.
2. **Arbitrary zoom, ~2 to ~2000 NM view range,** served without loading a whole
   tile and without baking a separate copy per zoom level. → A single continuous
   pyramid the device reads at whatever resolution the zoom needs.
3. **Progressive vector detail.** Coastlines/roads should shed vertices as you
   zoom out so on-screen line density stays roughly constant. → Importance-ordered
   vertices, thresholded at draw time.
4. **Cheap on-device decode.** The ESP32 has no FPU budget to spare and only a
   DEFLATE decompressor in mask ROM. → Integer-only decode, DEFLATE via ROM.

The result is `world.map`: ~92 MB for the whole world, one file, seekable,
covering every zoom from one data structure.

---

## 2. Input data

Two public-domain sources, cached under `data/` (the tiler only reads them):

- **Elevation — ETOPO 2022, 30 arc-second, surface** (NOAA NCEI GeoTIFF,
  `ETOPO_2022_v1_30s_N90W180_surface.tif`). Global relief in meters, EPSG:4326.
- **Vectors — Natural Earth 1:10m** (physical v5.1.1 + cultural v5.1.2):
  ocean, coastline, lakes, rivers, roads, populated places.

`dem.py` wraps the GeoTIFF for windowed reads; `vectors.py` loads the Natural
Earth shapefiles (with spatial indexes) — its `VectorSources` is reused by the
new pipeline for both the water mask and the vector records.

The exact versions of all inputs are embedded in every `world.map` (see §6).

---

## 3. Elevation encoding: a global resolution pyramid

### 3.1 One lattice, eight levels, exact nesting

The whole world (the band −86°…+86° latitude, full longitude) is sampled onto a
single **grid-registered equirectangular lattice**, north-up. The finest level
(**L0**) is **128 samples per degree** (≈0.47 NM ≈ 868 m per sample at the
equator). Coarser levels each halve the resolution:

| Level | world samples (w×h) | nm/sample (eq.) | typical view range |
|------:|:--------------------|:----------------|:-------------------|
| L0 | 46081 × 22017 | 0.469 | 2–40 NM |
| L1 | 23041 × 11009 | 0.938 | 80 NM |
| L2 | 11521 × 5505  | 1.875 | 150–200 NM |
| L3 | 5761 × 2753   | 3.75  | 500 NM |
| L4 | 2881 × 1377   | 7.5   | 1000 NM |
| L5 | 1441 × 689    | 15    | 2000 NM |
| L6 | 721 × 345     | 30    | headroom |
| L7 | 361 × 173     | 60    | global |

The critical detail is the dimension formula: **`n·2^L + 1`** samples per side
(hence the `+1` — L0 width is `360·128 + 1 = 46081`). Because each level has one
more than a power-of-two multiple, **coarsening is an exact 2:1 subsample**:
`level_codes = L0[::2^L, ::2^L]` (see `pyramid.level_codes`). Every coarse sample
sits *exactly* on an L0 lattice point — there is no half-pixel drift between
levels, which is what prevents terrain from "popping" or shifting when the device
switches zoom levels. `mapfmt.level_dims()` computes these dimensions;
`mapfmt.nm_per_sample()` the resolution.

The "arbitrary zoom, no baked presets" property comes from this: the device is not
choosing among discrete pre-rendered LODs; it is choosing a **stride into one
continuous pyramid**. The "view range" column above is illustrative — the firmware
maps range→level at runtime (§7.1), so the same file serves any future zoom ladder.

### 3.2 Elevation quantization and reserved codes

Each sample is one byte. Elevation in meters maps to a code via
`code = clamp(floor(elev_m / 40), 0, 253)` — i.e. **40 m per step**, sea level and
below clamped to 0 (`_quantize` in `pyramid.py`). Two code values are **reserved**:

- **`0xFF` (`ELEV_VOID_CODE`)** — no-data / void.
- **`0xFE` (`ELEV_WATER_CODE`)** — the sample is water.

So land occupies `[0, 253]`. The water code is how the map knows sea/lake/river
extent *within the elevation grid itself*, without a separate mask layer per tile.

### 3.3 The water code (how water is baked in)

Before the pyramid is decimated, the host rasterizes a **global water mask** on
the L0 lattice and burns `0xFE` into every water sample:

1. `pyramid.build_l0_water(vec_sources, …)` rasterizes the union of Natural Earth
   **ocean + lakes polygons + buffered river centerlines** (rivers buffered by
   ~0.004° so 0-width lines become a ~1-sample strip) onto the exact same
   north-up L0 lattice as the elevation, in latitude bands to bound memory.
   Result: a `(h, w)` uint8 array, 1 = water.
2. In `cli.cmd_build_map`, right after building the L0 elevation codes:
   `l0[water == 1] = ELEV_WATER_CODE`.
3. **Then** decimation happens. Because water is already in L0 as `0xFE`, every
   coarser level inherits water for free through the `[::2^L]` subset — no
   per-level water pass, and water coastlines stay registered with the terrain at
   every zoom.

On the device, `0xFE` samples are drawn as a flat water fill (dots + shoreline)
rather than terrain relief. Losing the true seabed/lakebed elevation under water
is intentional — the map only draws land relief. Mirror this as `kElevWaterCode`
on the device.

### 3.4 Blocks: the seekable unit

Each level's lattice is tiled into **64×64-sample blocks**. Blocks use a **stride
of 63, not 64** (`BLOCK_STRIDE = BLOCK_DIM − 1`): adjacent blocks **duplicate
their shared boundary row/column**. This 1-sample overlap ("halo") means a contour
or shoreline crossing a block edge is continuous with no gap — the renderer can
draw any block self-contained and edges still meet. `mapfmt.blocks_across(n)`
gives the block count for a level of `n` samples; partial edge blocks are padded
by edge-replication so every stored block is exactly 64×64.

Blocks are the unit of seek and decode: the device reads only the ~few dozen
blocks overlapping the current view, at the current level.

### 3.5 Per-block codec (chosen by measurement)

Each block is encoded independently by `mapfmt.encode_block()`, which picks the
**smallest** of three options and records which was used:

- **`BLOCK_CONSTANT` (codec 0)** — the block is uniform (all one code, e.g. open
  ocean = all `0xFE`). Stored as **zero payload bytes**; the single fill code
  lives in the directory entry. ~65% of L0 blocks are constant — this
  "constant-block dedup" is why the archive is small.
- **`BLOCK_DEFLATE` (codec 1)** — raw DEFLATE of the 64×64 code bytes.
- **`BLOCK_PRED_DEFLATE` (codec 2)** — a **PNG-style row predictor**
  (per row, the encoder picks none/sub/up/avg/paeth to minimize residual
  magnitude) applied first, then DEFLATE. On smooth terrain this beats plain
  DEFLATE substantially.

This codec choice was made empirically: a bake-off on real ETOPO blocks found
LERC-style bit-packing (the original plan) *loses* to plain DEFLATE on already
8-bit data, and predictor+DEFLATE wins overall (~0.17× of raw at 64² blocks).
Both winners are **integer-only to decode**: inflate via ROM `tinfl`, then (for
codec 2) reverse the row predictor with integer adds. `mapfmt.decode_block()` and
`mapfmt.predictor_unfilter()` are the reference decoders the firmware mirrors.

DEFLATE is done with a **raw** stream (`wbits=−15`, no zlib header) so it matches
`tinfl` on the device with no header parsing.

---

## 4. Vector encoding: importance-ordered, super-cell-indexed

Vectors (coastline, lakes, rivers, roads, city points) are stored so the device
can draw a cleanly-simplified line at *any* zoom from one copy.

### 4.1 Super-cells (continuous coordinates, no tile seams)

The world is divided into **8°×8° super-cells** (45 columns × 22 rows). Features
are clipped **only** at super-cell boundaries — not at every 1° line as the legacy
format did — so a coastline is one unbroken polyline across a wide area, with no
seams to stitch. Within a super-cell, coordinates are **cell-local fixed point**:
`(u, v)` in `0..65535` across the 8° cell (≈0.7 m/unit), v increasing north.
`vecpack.py` holds this geometry (`SUPERCELL_DEG`, `CELL_COLS/ROWS`, `_to_uv`).

### 4.2 Visvalingam–Whyatt importance ordering

For each polyline, `vecsimplify.effective_areas()` computes each vertex's
**Visvalingam–Whyatt "effective area"** — the area of the triangle it forms with
its neighbors, i.e. how much shape is lost if it's removed. Vertices are removed
lowest-area-first; the area *at removal* is recorded as that vertex's
**importance**, carried forward monotonically so a vertex never has lower
importance than one removed after it. Endpoints get infinite importance.

This monotonicity is the key property: **any threshold prefix of the
importance-sorted vertices is a valid, connected simplification**. VW (over the
older Douglas–Peucker) is chosen because its area metric thins smoothly, which
reads better as line density on a 1-bit screen.

Each polyline is then stored as a `VecRecordV3`: a header
(`feature_type, flags, num_points, importance_hint`) followed by points **sorted
by descending importance**, each `VecPointV3 = (u, v, seq, importance)` where
`seq` is the original along-path index and `importance` is log-quantized to 8
bits (255 = endpoint). City points are single-vertex records.

### 4.3 Vector index

Records are grouped by super-cell. A `VecIndexHeader` + `VecCellEntry[cols*rows]`
table (offset/len/count per cell) lets the device open only the cells overlapping
the view, so far zoom reads few cells. Empty cells have a zero entry.

---

## 5. The host build pipeline (`build-map`)

`cli.cmd_build_map` orchestrates the whole thing:

1. **Provenance** (`provenance.collect`) — read the ETOPO filename and the NE
   `VERSION` files, git commit, build date; serialize to a JSON blob (§6).
2. **L0 elevation** (`pyramid.build_l0_codes`) — resample ETOPO to the full L0
   lattice (46081×22017 ≈ 1 GB uint8), in latitude bands to cap the float buffer.
   One ETOPO pass total.
3. **Water burn** (`pyramid.build_l0_water` → `l0[water==1] = 0xFE`) — rasterize
   the global water mask and stamp the water code into L0 *before* decimation
   (§3.3). Skipped under `--no-vectors`.
4. **Pyramid** (`archive.ArchiveWriter.build_pyramid`) — for each level 0..7:
   derive the level by `[::2^L]` decimation, publish it into **shared memory**,
   and fan block encoding across a `ProcessPoolExecutor` (block encode is
   CPU-bound; shared memory avoids copying the ~1 GB L0 to each worker). Blocks
   stream to the file; per-level directories are held in RAM.
5. **Vectors** (`vecpack.build_vector_records` → `write_vectors`) — clip NE
   line/poly themes into super-cells, VW-simplify, write the index + records at
   `vec_index_offset`.
6. **Finalize** (`ArchiveWriter.finalize`) — seek back and write the level table,
   the directory CRC (over all levels' directories), and the header. Assert the
   total is < 4 GiB (FAT32 file limit).

`--stats` then prints a per-level report predicting device load time (§7.3).
Block encoding is parallel (`-j`), so a full world build is minutes, not hours.

---

## 6. On-disk layout of `world.map`

All fields little-endian. CRC-16/CCITT-FALSE with a final byte-swap
(`mapfmt.crc16`, byte-identical to the firmware `CalculateCRC16`).

```
┌────────────────────────────────────────────────────────────────┐
│ PyramidHeader (52 B)                                            │  offset 0
│   magic 'TMAP', version, num_levels, block_dim=64,             │
│   block_stride=63, finest_samples_per_deg=128,                 │
│   elev_bytes_per_sample=1, flags,                              │
│   world_lat0_e6=-86e6, world_lon0_e6=-180e6,                   │
│   world_span_lat_e3, world_span_lon_e3,                        │
│   vec_index_offset (u64), provenance_offset, provenance_len,   │
│   dir_crc16, header_crc16                                       │
├────────────────────────────────────────────────────────────────┤
│ LevelDesc × num_levels (32 B each)                             │
│   samples_w, samples_h, blocks_x, blocks_y, dir_offset (u64),  │
│   nm_per_sample_e4, elev_base_m, elev_step_m                   │
├────────────────────────────────────────────────────────────────┤
│ provenance JSON blob (provenance_len bytes)                    │
├────────────────────────────────────────────────────────────────┤
│ For each level (L0..Ln):                                       │
│   BlockDirEntry × blocks_x*blocks_y (12 B each)               │  @ LevelDesc.dir_offset
│     offset (u32, 0 ⇒ constant), stored_len (u32),            │
│     raw_len (u16), codec (u8), fill (u8)                      │
│   block payloads (variable, only non-constant blocks)         │
├────────────────────────────────────────────────────────────────┤
│ Vector section                                                 │  @ vec_index_offset
│   VecIndexHeader (magic 'TVEC', supercell_deg=8, cols, rows…) │
│   VecCellEntry × cols*rows (offset, len, num_records)         │
│   per-cell VecRecordV3 records back to back                   │
└────────────────────────────────────────────────────────────────┘
```

**Frozen struct sizes** (asserted at import in `mapfmt.py`; the firmware's
`static_assert(sizeof(...)==N)` must match, using `__attribute__((packed))`):

| struct | size |
|---|---:|
| `PyramidHeader` | 52 |
| `LevelDesc` | 32 |
| `BlockDirEntry` | 12 |
| `VecRecordHeaderV3` | 6 |
| `VecPointV3` | 8 |

**Provenance blob** — compact JSON, e.g.: ETOPO variant + DOI + filename;
Natural Earth physical/cultural versions; tiler version + git commit + build
date; encoding params (levels, samples/deg, step, VW tolerance). Read from the
data cache at build time so it is never hand-typed.

---

## 7. How the device reads it

The device support is a later firmware pass; this section describes the intended
operation the format was designed for.

### 7.1 Level selection (zoom → stride)

From the view range, `nm_per_px = range_nm / 70` (70 px = outer ring radius).
Pick the **coarsest level whose `nm_per_sample ≤ nm_per_px`** — i.e. about one
sample per pixel, never oversampling. This is a pure runtime decision from the
`LevelDesc` table, so the zoom ladder is not baked into the file.

### 7.2 Loading a view

1. On first use, open `/sd/world.map` (the card root) once, read + CRC-check the
   `PyramidHeader`, cache the header and level table (and, ideally, the block
   directories) in PSRAM. Keep the `FILE*` open.
2. For the current view, compute which blocks of the chosen level overlap the
   screen (a small rectangle of block indices — the whole point of the pyramid is
   that this is bounded, ~a few dozen, at *every* zoom).
3. For each block, read its `BlockDirEntry`:
   - `stored_len == 0` → **constant block**: synthesize a 64×64 fill of `fill`
     (no I/O, no decode). Ocean at any zoom costs nothing.
   - else `fseek(offset)`, read `stored_len` bytes, and decode by `codec`:
     codec 1 = ROM `tinfl` inflate; codec 2 = inflate then reverse the row
     predictor (`predictor_unfilter`). Integer-only, no float.
4. Each decoded 64×64 block is a grid of codes. `0xFE` = water (flat fill),
   `0xFF` = void, else elevation `= code × 40 m`. The shared-edge halo (§3.4)
   makes adjacent blocks join seamlessly.
5. Vectors: from `vec_index_offset`, read the `VecCellEntry` for each super-cell
   overlapping the view; for each record, take the prefix of points with
   `importance ≥ threshold` (threshold derived from `px_per_nm`), re-sort that
   prefix by `seq`, and draw the polyline. Higher zoom-out ⇒ higher threshold ⇒
   fewer vertices ⇒ constant on-screen line density.

The renderer caches the rasterized result and only rebuilds it on a pan/zoom
change, and loads one block per update tick, so no single frame stalls on I/O.

### 7.3 Predicted performance

Both SD read and `tinfl` inflate run at roughly **1 MB/s** on this hardware, so
device time is dominated by *bytes touched*, which the host controls and `--stats`
measures. A worst-case view (~56 blocks) is predicted at ~89 ms at close zoom
(L0) up to ~257 ms at far zoom, amortized one block per update tick. The card
should be freshly formatted so the ~92 MB file lays contiguous for fast seeks
(`CONFIG_FATFS_USE_FASTSEEK`).

---

## 8. Why the pieces fit together

- **One file, seekable** → solves the SD-copy overhead (1 file vs 61,920) while
  keeping random access via the block directory.
- **Grid-registered `n·2^L+1` pyramid** → arbitrary zoom by stride, exact
  inter-level registration (no popping), decimation is free.
- **Shared-edge blocks** → no seams between the seek units.
- **Constant-block dedup + predictor/DEFLATE** → ~92 MB whole world, integer-only
  decode within the ESP32's ROM-DEFLATE budget.
- **Water code burned into L0 pre-decimation** → water extent at every zoom for
  the cost of one rasterization, always registered with the terrain.
- **VW importance-ordered vectors in super-cells** → progressive, constant-density
  line detail from one encoding, no per-tile seams.
- **Embedded provenance** → every card is traceable to exact source versions.

---

## 9. Legacy per-tile format (context)

The original format (`build` command, `pack.py`, `terrain_tile.hh`, still present
and passing its `tests/test_roundtrip.py`) wrote **61,920 files** at
`/sd/tiles/<RRR>/<CCC>.map`, one per 1°×1° tile, each a 74-byte header plus a
fixed 128×128 elevation grid, per-tile-clipped vector records, and a 1-bit water
mask. It has a single resolution and terrain only drew at the two closest zooms.
It is retained until the firmware moves to `world.map`; the new format supersedes
it on all three counts (file count, zoom range, compression).

---

## 10. Source map

| Concern | File |
|---|---|
| On-disk structs, block codec, predictor, CRC (source of truth) | `terrain_tiler/mapfmt.py` |
| L0 resample, water rasterize, decimation, block iteration | `terrain_tiler/pyramid.py` |
| Archive assembly (parallel encode, directories, finalize) | `terrain_tiler/archive.py` |
| VW effective-area importance | `terrain_tiler/vecsimplify.py` |
| Super-cell binning, vector records + index | `terrain_tiler/vecpack.py` |
| Provenance capture | `terrain_tiler/provenance.py` |
| CLI (`build-map`, `--stats`; legacy `build`) | `terrain_tiler/cli.py` |
| ETOPO reader / legacy quantize | `terrain_tiler/dem.py` |
| Natural Earth loader (reused) | `terrain_tiler/vectors.py` |
| Legacy per-tile packer | `terrain_tiler/pack.py` |
| Tests (format + VW + reference decoder) | `tests/test_mapfmt.py`, `tests/test_vectors_vw.py`, `tests/test_roundtrip.py` |
