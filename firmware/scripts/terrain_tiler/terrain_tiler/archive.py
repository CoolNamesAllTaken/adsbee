"""Assemble `world.map`: pyramid header + per-level block directories + block
payloads (+ provenance; vectors appended later).

File layout:
  [PyramidHeader]
  [LevelDesc[num_levels]]           fixed table, right after the header
  [provenance blob]
  [per-level: block directory then block payloads], level by level
  [vector index + vector payloads]  (integrated with vectors.py later)

Payloads stream to disk; the (small) per-level directories are held in memory and
the header + level table + directory CRC are patched at the end via a seek back
to the file start.

Block encoding (deflate/predictor, the CPU cost) is fanned across processes with
a ProcessPoolExecutor: L0 codes are shared to workers, each returns its block's
stored bytes; the writer appends them in row-major order.
"""
import os
from concurrent.futures import ProcessPoolExecutor
from multiprocessing import shared_memory

import numpy as np

from . import mapfmt
from . import pyramid

# Per-worker shared state: the level's code array mapped from shared memory (no
# per-worker copy — critical for L0, which is ~1 GB).
_WK = {}


def _wk_init(shm_name, codes_shape, codes_dtype):
    shm = shared_memory.SharedMemory(name=shm_name)
    _WK["shm"] = shm  # keep a ref so it isn't GC'd/closed
    _WK["codes"] = np.ndarray(codes_shape, dtype=np.dtype(codes_dtype), buffer=shm.buf)


def _wk_encode_row(by):
    """Encode all blocks in block-row `by`. Returns list of (bx, codec, stored, fill)."""
    codes = _WK["codes"]
    stride = mapfmt.BLOCK_STRIDE
    dim = mapfmt.BLOCK_DIM
    h, w = codes.shape
    blocks_x = mapfmt.blocks_across(w)
    y0 = by * stride
    rows = codes[y0:y0 + dim]
    if rows.shape[0] < dim:
        pad = np.empty((dim, w), np.uint8)
        pad[:rows.shape[0]] = rows
        pad[rows.shape[0]:] = rows[-1:]
        rows = pad
    out = []
    for bx in range(blocks_x):
        x0 = bx * stride
        blk = rows[:, x0:x0 + dim]
        if blk.shape[1] < dim:
            p = np.empty((dim, dim), np.uint8)
            p[:, :blk.shape[1]] = blk
            p[:, blk.shape[1]:] = blk[:, -1:]
            blk = p
        codec, stored, fill = mapfmt.encode_block(np.ascontiguousarray(blk))
        out.append((bx, codec, stored, fill))
    return by, out


class ArchiveWriter:
    def __init__(self, fileobj, num_levels, world_span_lat_e3=172_000,
                 world_span_lon_e3=360_000, jobs=0):
        self.f = fileobj
        self.num_levels = num_levels
        self.world_span_lat_e3 = world_span_lat_e3
        self.world_span_lon_e3 = world_span_lon_e3
        self.jobs = jobs if jobs and jobs > 0 else (os.cpu_count() or 1)
        self.levels = []
        self._all_dir_bytes = []

    def _reserve_front(self, provenance_blob):
        self.header_pos = 0
        self.level_table_pos = mapfmt.PYR_HEADER_SIZE
        self.provenance_pos = self.level_table_pos + self.num_levels * mapfmt.LEVEL_DESC_SIZE
        self.f.write(b"\x00" * mapfmt.PYR_HEADER_SIZE)
        self.f.write(b"\x00" * (self.num_levels * mapfmt.LEVEL_DESC_SIZE))
        self.f.write(provenance_blob)
        self.provenance_len = len(provenance_blob)
        return self.f.tell()

    def _write_level(self, level, codes, pool):
        w, h, blocks_x, blocks_y = pyramid.level_geometry(level, self.num_levels)
        n_blocks = blocks_x * blocks_y
        dir_entries = [None] * n_blocks

        dir_offset = self.f.tell()
        payload_offset = dir_offset + n_blocks * mapfmt.BLOCK_DIR_ENTRY_SIZE
        self.f.seek(payload_offset)
        written = payload_offset
        n_const = 0

        # Encode block-rows in parallel; results arrive in row order via map().
        for by, row in pool.map(_wk_encode_row, range(blocks_y), chunksize=4):
            for bx, codec, stored, fill in row:
                idx = by * blocks_x + bx
                if codec == mapfmt.BLOCK_CONSTANT:
                    n_const += 1
                    dir_entries[idx] = mapfmt.pack_block_dir_entry(
                        0, 0, mapfmt.BLOCK_DIM ** 2, codec, fill)
                else:
                    self.f.write(stored)
                    dir_entries[idx] = mapfmt.pack_block_dir_entry(
                        written, len(stored), mapfmt.BLOCK_DIM ** 2, codec, fill)
                    written += len(stored)

        end = self.f.tell()
        self.f.seek(dir_offset)
        dir_bytes = b"".join(dir_entries)
        self.f.write(dir_bytes)
        self._all_dir_bytes.append(dir_bytes)
        self.f.seek(end)

        self.levels.append(dict(
            samples_w=w, samples_h=h, blocks_x=blocks_x, blocks_y=blocks_y,
            dir_offset=dir_offset, nm_per_sample=mapfmt.nm_per_sample(level),
            elev_base_m=0, n_blocks=n_blocks, n_const=n_const,
            payload_bytes=written - payload_offset))

    def build_pyramid(self, l0_codes, provenance_blob, progress=None):
        """l0_codes: full (h,w) uint8 L0 lattice. Writes all levels."""
        self._reserve_front(provenance_blob)
        for level in range(self.num_levels):
            codes = l0_codes if level == 0 else pyramid.level_codes(
                l0_codes, level, self.num_levels)
            # Publish this level's codes into shared memory so workers map it
            # without copying (L0 is ~1 GB).
            shm = shared_memory.SharedMemory(create=True, size=codes.nbytes)
            try:
                buf = np.ndarray(codes.shape, dtype=codes.dtype, buffer=shm.buf)
                buf[:] = codes
                with ProcessPoolExecutor(
                        max_workers=self.jobs, initializer=_wk_init,
                        initargs=(shm.name, codes.shape, codes.dtype.str)) as pool:
                    self._write_level(level, codes, pool)
            finally:
                shm.close()
                shm.unlink()
            if progress:
                progress(level, self.levels[-1])
        self.vec_index_offset = self.f.tell()
        return self.vec_index_offset

    def finalize(self):
        self.f.seek(self.level_table_pos)
        for lv in self.levels:
            self.f.write(mapfmt.pack_level_desc(
                lv["samples_w"], lv["samples_h"], lv["blocks_x"], lv["blocks_y"],
                lv["dir_offset"], lv["nm_per_sample"], lv["elev_base_m"]))
        dir_crc = mapfmt.crc16(b"".join(self._all_dir_bytes))
        header = mapfmt.pack_pyramid_header(
            self.num_levels, self.world_span_lat_e3, self.world_span_lon_e3,
            vec_index_offset=self.vec_index_offset,
            provenance_offset=self.provenance_pos, provenance_len=self.provenance_len,
            dir_crc16=dir_crc)
        self.f.seek(self.header_pos)
        self.f.write(header)
        self.f.flush()

    def total_len(self):
        self.f.seek(0, 2)
        return self.f.tell()
