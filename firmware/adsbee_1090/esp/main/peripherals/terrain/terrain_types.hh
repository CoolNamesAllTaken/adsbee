#pragma once

#include <cstdint>

#include "terrain_tile.hh"

// In-RAM representations produced by TerrainLoader and consumed by the Phase-3
// renderer. Large buffers live in PSRAM.
//
// ParsedBlock is one decoded 64x64 elevation block of a pyramid level, keyed by
// {level, bx, by}. Constant blocks are materialized to a full 64x64 (memset) so
// the render path is uniform. VecCellBlob is one super-cell's raw vector records,
// streamed by the renderer with a cursor (see terrain_tile.hh VecRecordHeaderV3).

namespace winglet_terrain {

struct ParsedBlock {
    bool in_use = false;
    int level = -1;
    int bx = -1;
    int by = -1;

    // Decoded 8-bit codes, exactly kBlockRawLen (4096) bytes, row-major
    // (row 0 = north). Held in PSRAM.
    uint8_t* codes = nullptr;

    int16_t elev_base_m = 0;
    uint8_t elev_step_m = 40;
    uint32_t lru_stamp = 0;

    // Raw code at local sample (lx, ly), lx/ly in [0, kBlockDim). No bounds check
    // (callers clamp); returns kElevVoidCode if the block has no codes.
    uint8_t SampleCode(int lx, int ly) const {
        if (!codes || lx < 0 || ly < 0 || lx >= kBlockDim || ly >= kBlockDim) {
            return kElevVoidCode;
        }
        return codes[ly * kBlockDim + lx];
    }

    bool SampleIsWater(int lx, int ly) const { return SampleCode(lx, ly) == kElevWaterCode; }

    // Decoded elevation in meters, or INT32_MIN for void/water (both are drawn
    // specially, not as terrain height).
    int32_t SampleMeters(int lx, int ly) const {
        uint8_t code = SampleCode(lx, ly);
        if (code == kElevVoidCode || code == kElevWaterCode) return INT32_MIN;
        return (int32_t)elev_base_m + (int32_t)code * (int32_t)elev_step_m;
    }
};

// One super-cell's vector records (raw bytes), streamed by the renderer.
struct VecCellBlob {
    bool in_use = false;
    int cell_index = -1;   // cell_row * kCellCols + cell_col
    int cell_row = -1;
    int cell_col = -1;
    uint8_t* data = nullptr;   // PSRAM
    uint32_t len = 0;
    uint16_t num_records = 0;
    uint32_t lru_stamp = 0;
};

}  // namespace winglet_terrain
