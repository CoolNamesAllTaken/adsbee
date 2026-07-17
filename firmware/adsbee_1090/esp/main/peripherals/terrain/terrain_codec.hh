#pragma once

#include <cstddef>
#include <cstdint>

#include "terrain_tile.hh"  // kBlockDim, BlockCodec

// Integer-only block decode for the world.map elevation pyramid. A block payload
// is one of three codecs (BlockDirEntry.codec):
//   0 constant       - no payload; the whole 64x64 is one fill code
//   1 raw DEFLATE    - inflate straight to 4096 codes
//   2 predictor+DEFLATE - inflate, then reverse the PNG-style per-row predictor
//
// DEFLATE inflate uses the ESP32-S3 ROM miniz (tinfl) — zero flash cost. The
// predictor reversal is a direct port of mapfmt.py::predictor_unfilter (adds and
// mod-256 only, no float). Reference: firmware/scripts/terrain_tiler/mapfmt.py.
//
// IMPORTANT: the `tinfl_decompressor` state struct is ~11 KB (three Huffman
// tables), so it must NOT live on the stack (the one-shot _mem_to_mem helper
// stack-allocates it and overflows the main task's 16 KB stack). The caller
// allocates it in PSRAM once and passes it in; kTinflDecompressorSize sizes that
// buffer without pulling miniz.h into this header.

namespace winglet_terrain {

// Byte size to allocate for the caller-owned tinfl_decompressor (a generous upper
// bound on sizeof(tinfl_decompressor); the real struct is ~11 KB — three Huffman
// tables). A static_assert in terrain_codec.cpp fails the build if this is ever
// too small. Allocate in PSRAM and pass the pointer to InflateRaw/DecodeBlock.
constexpr size_t kTinflDecompressorSize = 12288;  // 12 KB

// Inflate a RAW DEFLATE stream (no zlib header — the host uses wbits=-15) into
// out[0..out_len). `decompressor` is a PSRAM buffer >= kTinflDecompressorSize
// (holds the ~11 KB tinfl state off the stack). Returns true iff exactly out_len
// bytes were produced.
bool InflateRaw(const uint8_t* src, size_t src_len, uint8_t* out, size_t out_len,
                void* decompressor);

// Reverse the PNG-style per-row predictor. `filtered` layout is, per row,
// [filter_type u8][w residual bytes]; filtered_len must equal h*(w+1). Writes
// h*w decoded codes row-major into `out`. Integer/mod-256 only. Returns false on
// a size mismatch or an unknown filter type.
bool PredictorUnfilter(const uint8_t* filtered, size_t filtered_len, uint8_t* out,
                       int h, int w);

// Size of the scratch buffer DecodeBlock needs for codec 2: the predictor-
// filtered stream is one filter byte per row, so kBlockDim*(kBlockDim+1) = 4160
// bytes (larger than the 4096-byte decoded block).
constexpr size_t kBlockDecodeScratchLen = (size_t)kBlockDim * (kBlockDim + 1);

// Decode one block per its directory entry into `out` (sized raw_len == 4096):
//   codec 0: out is filled with `fill` (stored is ignored)
//   codec 1: InflateRaw(stored -> out)
//   codec 2: InflateRaw(stored -> scratch) then PredictorUnfilter(scratch -> out)
// `scratch` must be at least kBlockDecodeScratchLen bytes (only used by codec 2;
// may be null for codecs 0/1). `decompressor` is a PSRAM buffer >=
// kTinflDecompressorSize (used by codecs 1/2; may be null for codec 0). Returns
// false on any decode failure; the caller decides how to degrade.
bool DecodeBlock(uint8_t codec, uint8_t fill, const uint8_t* stored, size_t stored_len,
                 uint8_t* out, uint16_t raw_len, uint8_t* scratch, void* decompressor);

}  // namespace winglet_terrain
