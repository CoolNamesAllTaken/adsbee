#pragma once

#include <cstdint>

#include "terrain_tile.hh"

// In-RAM representation of a loaded terrain tile, produced by TerrainLoader and
// consumed by the Phase-3 renderer. Large buffers live in PSRAM.
//
// The elevation grid is the raw decoded block (8-bit quantized codes, or int16 if
// the tile is flagged 16-bit). The vector layers are kept as raw byte blocks +
// counts; the renderer streams records with a cursor (see terrain_tile.hh
// VecRecordHeader), so no per-vertex allocation is needed.

namespace winglet_terrain {

struct ParsedTile {
    bool in_use = false;
    int row = -1;
    int col = -1;

    TileHeader hdr = {};

    // Elevation grid: elev_grid_w * elev_grid_h * elev_bytes_per_sample bytes.
    // For the 8-bit path, sample_m = hdr.elev_base_m + code * hdr.elev_step_m,
    // code == kElevVoidCode is no-data.
    uint8_t* elev = nullptr;
    uint32_t elev_len = 0;

    // Raw vector blocks (streamed by the renderer via a record cursor).
    uint8_t* vec_water = nullptr;
    uint32_t vec_water_len = 0;
    uint16_t water_count = 0;

    uint8_t* vec_road = nullptr;
    uint32_t vec_road_len = 0;
    uint16_t road_count = 0;

    // Water mask: 1 bit/pixel, 1 = water, at (mask_w x mask_h) = elevation-grid
    // resolution. Row-major north->south, ceil(w/8) bytes/row, MSB-first.
    uint8_t* water_mask = nullptr;
    uint32_t water_mask_len = 0;
    uint16_t mask_w = 0;
    uint16_t mask_h = 0;

    // True if grid cell (gx,gy) is water. Bounds-checked; false if no mask.
    bool IsWater(int gx, int gy) const {
        if (!water_mask || gx < 0 || gy < 0 || gx >= mask_w || gy >= mask_h) return false;
        uint32_t bytes_per_row = (mask_w + 7u) / 8u;
        uint32_t idx = (uint32_t)gy * bytes_per_row + (gx >> 3);
        if (idx >= water_mask_len) return false;
        return (water_mask[idx] & (0x80u >> (gx & 7))) != 0;
    }

    // Decode a quantized elevation sample at grid (gx, gy). Returns meters, or
    // INT32_MIN for void. Bounds-checked.
    int32_t SampleMeters(int gx, int gy) const {
        if (!elev || gx < 0 || gy < 0 || gx >= hdr.elev_grid_w || gy >= hdr.elev_grid_h) {
            return INT32_MIN;
        }
        uint32_t idx = (uint32_t)gy * hdr.elev_grid_w + gx;
        if (hdr.elev_bytes_per_sample == 2) {
            const int16_t* s = reinterpret_cast<const int16_t*>(elev);
            return s[idx];
        }
        uint8_t code = elev[idx];
        if (code == kElevVoidCode) return INT32_MIN;
        return (int32_t)hdr.elev_base_m + (int32_t)code * (int32_t)hdr.elev_step_m;
    }
};

}  // namespace winglet_terrain
