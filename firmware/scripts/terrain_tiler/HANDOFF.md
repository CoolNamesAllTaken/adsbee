# Handoff — Terrain `world.map` format: device-side (ESP32) pass

You are picking up a multi-session effort to rearchitect the ADSBee terrain map.
The **host side is done** (this directory). The **next pass is the ESP32 firmware
reader**, which was deliberately deferred. This file is the self-contained
handoff — you should not need the prior chat.

## Start here (internal Claude resources for THIS project)

1. **The approved design + full decision log:**
   `/Users/nano/.claude/plans/i-would-like-to-eventual-hejlsberg.md`
   Read this first. It has the context, the frozen on-disk layout, the
   **"Device-side contract (NOT built this pass)"** section (your spec), the
   codec decision (and why the bake-off *overturned* the original LERC choice in
   favor of PNG-predictor+DEFLATE), and the ESP32 performance predictions.

2. **Firmware agent guide:** `/Users/nano/Documents/pfb/adsbee/firmware/AGENTS.md`
   Build system (`bash build.sh esp` from `firmware/adsbee_1090/`, Docker-based,
   ESP-IDF v5.5.2), the 3-processor architecture, conventions. Read before building.

3. **Other related plan files** in `/Users/nano/.claude/plans/` (same project):
   several `*fountain*`, `*ladybug*`, `*manatee*`, `ownship-altitude-fix.md`, etc.
   — prior features on this branch; consult only if you touch adjacent code.

4. **Persistent memory:** `/Users/nano/.claude/projects/-Users-nano-Documents-pfb-adsbee/memory/`
   Currently **empty** (no `MEMORY.md` yet). If you learn something non-obvious
   and durable during the firmware pass, write it there (one fact per file +
   a `MEMORY.md` index line), per the memory conventions in the system prompt.

5. **Scratchpad convention:** put throwaway build/test artifacts in the session
   scratchpad dir (see your environment's "Scratchpad Directory" note), **not**
   in the repo. The whole-world `world.map` (~92 MB) should be built to scratch,
   never committed. `data/` and `out_sd/` are already git-ignored here.

Note: there is **no `.claude/` config dir, no `CLAUDE.md`** in this repo — only
`firmware/AGENTS.md`. Don't go looking for project skills/agents; there are none.

## What "done" means (host side, this directory)

New single-file archive `world.map` replaces the 61,920-file `/sd/tiles/` set
(the file-count was what dominated SD copy time). Whole-world = **~92 MB, one
file**. Built + validated on real ETOPO. New modules:

| File | Role |
|---|---|
| `terrain_tiler/mapfmt.py` | **SINGLE SOURCE OF TRUTH** for the on-disk structs + block codec + Python reference decoder |
| `terrain_tiler/pyramid.py` | ETOPO → L0 lattice, 2:1 decimation to 8 levels, shared-edge 64×64 blocks |
| `terrain_tiler/archive.py` | Writes the archive (parallel block encode) |
| `terrain_tiler/vecsimplify.py` | Visvalingam–Whyatt importance ordering |
| `terrain_tiler/vecpack.py` | Super-cell vector binning + index |
| `terrain_tiler/provenance.py` | Embeds ETOPO + Natural Earth versions in the file |
| `tests/test_mapfmt.py`, `tests/test_vectors_vw.py` | Reference-decoder round-trip + VW property tests |

Build it yourself to inspect real output:
```bash
cd firmware/scripts/terrain_tiler && poetry install
poetry run terrain-tiler build-map -j 8 --stats \
  --dem data/ETOPO_2022_v1_30s_N90W180_surface.tif \
  --out <SCRATCH>/world.map           # ~92 MB; --stats prints device-perf prediction
python tests/test_mapfmt.py           # struct sizes + block codec (needs numpy)
python tests/test_vectors_vw.py       # VW importance / progressive vectors
```
The legacy per-tile `build` command + `pack.py` + `tests/test_roundtrip.py` are
left intact and still pass; the current firmware still reads that format until
your pass lands.

## Your task: the device-side reader

Implement the ESP32 reader for `world.map`, per the plan's device contract.
Files to change (all under `firmware/adsbee_1090/esp/main/peripherals/`):

- `terrain/terrain_tile.hh` — add `PyramidHeader`, `LevelDesc`, `BlockDirEntry`,
  `VecRecordHeaderV3`, `VecPointV3`; bump/redefine magic to `'TMAP'`; drop the
  `kTerrainMaxRangeNm = 40` hard gate (→ runtime level-select so zoom stays
  firmware-configurable). Add `static_assert(sizeof(...) == N)` — **N values are
  pinned in `mapfmt.py`** (see next section); they must match byte-for-byte.
- `terrain/terrain_loader.{hh,cpp}` — open the archive once, hold the `FILE*`
  open, cache the header + directory in PSRAM; `ComputeOverlap → ComputeViewBlocks`;
  `LoadTile → LoadBlock` (constant-fill synth, else `fseek`+read+decode).
- `terrain/terrain_types.hh` — `ParsedTile → ParsedBlock`.
- `epd/gui/terrain_render.cpp` — per-level block projection; importance-threshold
  vector streaming; remove the 40 NM gate.
- `esp/sdkconfig` — set `CONFIG_FATFS_USE_FASTSEEK=y`,
  `CONFIG_FATFS_FAST_SEEK_BUFFER_SIZE=256`.

### Decode is integer-only and (mostly) free on this chip
- **DEFLATE**: ESP32-S3 mask ROM has miniz `tinfl` — verified symbols in
  `~/.espressif/v5.5.2/esp-idf/components/esp_rom/esp32s3/ld/esp32s3.rom.ld`
  (`tinfl_decompress` @0x40000828, `..._mem_to_mem` @0x4000084c). Include the
  esp_rom `miniz.h`. **Zero flash cost.**
- **Block codec** (`BlockDirEntry.codec`): `0`=constant (fill byte in the entry,
  no payload), `1`=raw DEFLATE, `2`=PNG-row-predictor then DEFLATE. For codec 2,
  inflate then reverse the per-row predictor — the exact reference is
  `mapfmt.predictor_unfilter()` (integer adds, no float). Port that ~20-line loop.
- **Vectors**: read a super-cell's records, and per polyline take the prefix of
  importance-sorted points with `importance >= threshold`, re-sort that prefix by
  `seq`, draw. `threshold` from `px_per_nm`. Reference: `vecpack.py` +
  `test_vectors_vw.py::test_record_roundtrip_and_progressive`.

### The frozen sizes your `static_assert`s must match (from `mapfmt.py`)
```
PYR_HEADER_SIZE       == 52     # NOTE: use __attribute__((packed)); the u64
LEVEL_DESC_SIZE       == 32     #   vec_index_offset would else be 8-byte aligned
BLOCK_DIR_ENTRY_SIZE  == 12
VEC_RECORD_HDR_SIZE   ==  6
VEC_POINT_SIZE        ==  8
```
All fields little-endian. CRC-16/CCITT-FALSE + swap16 == the existing firmware
`CalculateCRC16` (`firmware/common/utils/buffer_utils.cpp`); `mapfmt.crc16`
already mirrors it, so header/dir CRCs will match.

### On-disk layout (see `mapfmt.py` docstrings for field-by-field)
```
[PyramidHeader 52B] [LevelDesc[num_levels]] [provenance JSON blob]
[per level: BlockDirEntry[blocks_x*blocks_y] then block payloads]
[vector index: VecIndexHeader + VecCellEntry[cols*rows] + records]
```
`PyramidHeader.vec_index_offset` points at the vector section;
`provenance_offset/len` at the JSON blob (has the ETOPO + NE versions).

### Perf you should expect (predicted from the built archive, ~1 MB/s SD + tinfl)
~89 ms per pan at close zoom (L0), up to ~257 ms at far zoom (L7), amortized one
block per `Update()` so no frame stalls. Regenerate exact numbers with
`build-map --stats`. Card must be freshly formatted so the 92 MB file lays
contiguous for fast-seek.

## Verification for your pass
1. Build ESP: `cd firmware/adsbee_1090 && bash build.sh esp`.
2. Confirm the `static_assert`s compile (proves struct parity with `mapfmt.py`).
3. Put a `world.map` on a card; verify a known location (e.g. Alps ~46N,10E)
   renders elevation, and step the zoom ladder to confirm all levels draw and
   coastlines progressively simplify.
4. Compare against a legacy-tileset screenshot at 20 NM for parity.
