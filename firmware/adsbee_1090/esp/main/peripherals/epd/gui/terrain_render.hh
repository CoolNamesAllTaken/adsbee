#pragma once

#include "canvas.hh"
#include "peripherals/terrain/terrain_loader.hh"
#include "peripherals/terrain/terrain_types.hh"
#include "ui_data.hh"

// Renders microSD-loaded terrain (water fill, roads, cities) under the moving-map
// traffic/rings. Called first in DrawMapScreen so it draws beneath everything and
// is auto-clipped to the map window by the rail gutter mask. Expensive rasterization
// is cached (see TerrainCache) and only rebuilt when the ownship tile / zoom / pan
// changes; the common per-frame case is a single memcpy of the cached layer.

namespace winglet_ui {

// Equirectangular, ownship-centered geo->pixel transform (matches the traffic
// projection in map_screen.cpp so terrain and traffic register pixel-for-pixel).
struct MapProjection {
    float ownship_lat;
    float ownship_lon;
    float coslat;      // cosf(ownship_lat * pi/180)
    float px_per_nm;   // kOuterRingRadiusPx / range_nm
    bool valid;

    static MapProjection FromData(const MapScreenData& d);
    void GeoToPixel(float lat_deg, float lon_deg, int* px, int* py) const;
};

// Per-block affine: block-local sample (lx,ly) in [0,64) -> screen pixel,
// precomputed once per block from its {level,bx,by} key.
//   px = px_bias + lx*px_per_lx ; py = py_bias + ly*py_per_ly.
struct BlockProjection {
    float px_bias, px_per_lx;
    float py_bias, py_per_ly;
    static BlockProjection FromBlock(const winglet_terrain::ParsedBlock& b,
                                     const MapProjection& mp);
    void LocalToPixel(int lx, int ly, int* px, int* py) const;
};

// Per-super-cell affine: cell-local (u,v) in [0,65535] over the 8-degree cell
// -> screen pixel. v grows north.
struct CellProjection {
    float px_bias, px_per_u;
    float py_bias, py_per_v;
    static CellProjection FromCell(int cell_row, int cell_col, const MapProjection& mp);
    void UVToPixel(uint16_t u, uint16_t v, int* px, int* py) const;
};

// Draw all terrain layers (for the tiles overlapping the current window) onto
// `target`. Uses an off-screen PSRAM cache Canvas internally; cheap when nothing
// changed (just composites the cached layer).
void DrawTerrain(Canvas& target, const MapScreenData& data,
                 const winglet_terrain::TerrainLoader& loader);

}  // namespace winglet_ui
