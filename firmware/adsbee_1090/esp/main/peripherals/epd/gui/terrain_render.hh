#pragma once

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

// Per-tile affine u,v (tile-local [0,65535]) -> screen pixel, precomputed once
// per tile: px = px_bias + u*px_per_u ; py = py_bias + v*py_per_v.
struct TileProjection {
    float px_bias, px_per_u;
    float py_bias, py_per_v;
    static TileProjection FromTile(const winglet_terrain::ParsedTile& t, const MapProjection& mp);
    void UVToPixel(uint16_t u, uint16_t v, int* px, int* py) const;
    // Grid node (gx,gy) -> pixel (gx across = east, gy down = south per tiler layout).
    void GridToPixel(int gx, int gy, int grid_w, int grid_h, int* px, int* py) const;
};

// Draw all terrain layers for the tiles overlapping the current window. Uses the
// terrain cache internally; cheap when nothing changed.
void DrawTerrain(const MapScreenData& data, const winglet_terrain::TerrainLoader& loader);

}  // namespace winglet_ui
