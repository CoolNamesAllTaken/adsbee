"""Vector layers: Natural Earth water + roads/cities, clipped per tile.

Natural Earth (public domain, free for commercial use). We use only a few 10m
themes (coastline, lakes, rivers, roads, populated places) — a small slice of the
full dataset, matching the "aviation zooms, no street detail" budget.

Each feature is clipped to the tile box and encoded as tile-local uint16 records
(see terrain_tile.hh VecRecordHeader / VecPoint). Features straddling tile borders
are clipped into each tile, so edges meet with no on-device stitching.
"""
import glob
import os

import geopandas as gpd
import numpy as np
from rasterio.features import rasterize
from rasterio.transform import from_bounds
from shapely.geometry import box, LineString, MultiLineString, Polygon, MultiPolygon, Point

from . import pack

# Natural Earth is distributed as two separate downloads (physical + cultural).
# Each theme names its shapefile basename and which download it belongs to, so
# the loader can look in the matching directory.
NE_THEMES = {
    "ocean": ("ne_10m_ocean", "physical"),
    "coastline": ("ne_10m_coastline", "physical"),
    "lakes": ("ne_10m_lakes", "physical"),
    "rivers": ("ne_10m_rivers_lake_centerlines", "physical"),
    "roads": ("ne_10m_roads", "cultural"),
    "cities": ("ne_10m_populated_places", "cultural"),
}

# River centerlines are 0-width lines; buffer them (degrees) so they rasterize as
# a ~1-pixel-wide water strip at the tile grid resolution. ~half a grid cell of a
# 1-degree/128 tile = ~0.004 deg.
RIVER_BUFFER_DEG = 0.004

# Keep only major roads / notable cities to respect the budget.
ROAD_MAX_SCALERANK = 8      # NE roads scalerank: lower = more major
CITY_MAX_SCALERANK = 5      # NE populated places scalerank


class VectorSources:
    """Loads the NE themes once and holds spatial indexes for fast per-tile clip.

    Natural Earth ships physical and cultural vectors as two separate downloads,
    so we take one directory per download. Each is searched recursively for the
    theme's ``.shp``, which tolerates the extra nesting the NE zips unpack into
    (e.g. ``10m_cultural/10m_cultural/ne_10m_roads.shp``).
    """

    def __init__(self, physical_dir, cultural_dir):
        self.dirs = {"physical": physical_dir, "cultural": cultural_dir}
        self.layers = {}
        self._load()

    def _read(self, theme):
        basename, kind = NE_THEMES[theme]
        root = self.dirs[kind]
        matches = glob.glob(os.path.join(root, "**", f"{basename}.shp"), recursive=True)
        if not matches:
            raise FileNotFoundError(
                f"Natural Earth {kind} shapefile '{basename}.shp' not found under {root!r}"
            )
        return gpd.read_file(matches[0])

    def _load(self):
        self.layers["ocean"] = self._read("ocean")
        self.layers["coastline"] = self._read("coastline")
        self.layers["lakes"] = self._read("lakes")
        self.layers["rivers"] = self._read("rivers")
        roads = self._read("roads")
        if "scalerank" in roads.columns:
            roads = roads[roads["scalerank"] <= ROAD_MAX_SCALERANK]
        self.layers["roads"] = roads
        cities = self._read("cities")
        if "SCALERANK" in cities.columns:
            cities = cities[cities["SCALERANK"] <= CITY_MAX_SCALERANK]
        elif "scalerank" in cities.columns:
            cities = cities[cities["scalerank"] <= CITY_MAX_SCALERANK]
        self.layers["cities"] = cities

    # ---- tile-local coordinate encoding ----------------------------------
    @staticmethod
    def _to_uv(lon, lat, lon0, lat0, span):
        u = int(round((lon - lon0) / span * 65535))
        v = int(round((lat - lat0) / span * 65535))
        return (max(0, min(65535, u)), max(0, min(65535, v)))

    def _encode_lines(self, geom, lon0, lat0, span, feature_type, closed=False):
        """Yield packed records for a (Multi)LineString / polygon-ring geometry."""
        records = []

        def emit(coords):
            pts = [self._to_uv(x, y, lon0, lat0, span) for (x, y) in coords]
            if len(pts) >= 2:
                records.append(pack.pack_vec_record(feature_type, pts, closed=closed))

        if geom is None or geom.is_empty:
            return records
        gt = geom.geom_type
        if gt == "LineString":
            emit(list(geom.coords))
        elif gt == "MultiLineString":
            for part in geom.geoms:
                emit(list(part.coords))
        elif gt == "Polygon":
            emit(list(geom.exterior.coords))
            for ring in geom.interiors:
                emit(list(ring.coords))
        elif gt == "MultiPolygon":
            for poly in geom.geoms:
                emit(list(poly.exterior.coords))
                for ring in poly.interiors:
                    emit(list(ring.coords))
        return records

    def clip_tile(self, lat0, lon0, span):
        """Return (water_bytes, water_count, road_bytes, road_count) for the tile."""
        tile_box = box(lon0, lat0, lon0 + span, lat0 + span)

        water_recs = []
        # Coastline (open lines) + lakes (closed polygons) + rivers (open lines).
        for key, ftype, closed in (
            ("coastline", pack.VEC_COASTLINE, False),
            ("lakes", pack.VEC_LAKE, True),
            ("rivers", pack.VEC_RIVER, False),
        ):
            gdf = self.layers[key]
            hits = gdf.iloc[list(gdf.sindex.query(tile_box, predicate="intersects"))]
            for geom in hits.geometry:
                clipped = geom.intersection(tile_box)
                water_recs.extend(
                    self._encode_lines(clipped, lon0, lat0, span, ftype, closed=closed)
                )

        road_recs = []
        roads = self.layers["roads"]
        rhits = roads.iloc[list(roads.sindex.query(tile_box, predicate="intersects"))]
        for geom in rhits.geometry:
            clipped = geom.intersection(tile_box)
            road_recs.extend(
                self._encode_lines(clipped, lon0, lat0, span, pack.VEC_ROAD_MAJOR)
            )

        cities = self.layers["cities"]
        chits = cities.iloc[list(cities.sindex.query(tile_box, predicate="intersects"))]
        for _, row in chits.iterrows():
            pt = row.geometry
            if pt is None or pt.is_empty or pt.geom_type != "Point":
                continue
            uv = self._to_uv(pt.x, pt.y, lon0, lat0, span)
            name = str(row.get("NAME", row.get("name", "")))[:255]
            road_recs.append(
                pack.pack_vec_record(pack.VEC_CITY_POINT, [uv], name=name or None)
            )

        return (
            b"".join(water_recs), len(water_recs),
            b"".join(road_recs), len(road_recs),
        )

    def rasterize_water_mask(self, lat0, lon0, span, grid_dim):
        """Rasterize a 1-bit water mask for the tile (bit=1 where water).

        Union of ocean + lakes + buffered river centerlines, clipped to the tile.
        Output: grid_dim x grid_dim, row 0 = NORTH (matches the elevation grid),
        packed 1-bit MSB-first, ceil(grid_dim/8) bytes/row. Returns raw bytes.
        """
        tile_box = box(lon0, lat0, lon0 + span, lat0 + span)
        geoms = []

        for key in ("ocean", "lakes"):
            gdf = self.layers[key]
            for i in gdf.sindex.query(tile_box, predicate="intersects"):
                g = gdf.geometry.iloc[i].intersection(tile_box)
                if not g.is_empty:
                    geoms.append(g)

        rivers = self.layers["rivers"]
        for i in rivers.sindex.query(tile_box, predicate="intersects"):
            g = rivers.geometry.iloc[i].intersection(tile_box)
            if not g.is_empty:
                geoms.append(g.buffer(RIVER_BUFFER_DEG))

        # north-up transform: row 0 maps to the tile's north (lat0+span) edge.
        transform = from_bounds(lon0, lat0, lon0 + span, lat0 + span, grid_dim, grid_dim)
        if geoms:
            arr = rasterize(
                ((g, 1) for g in geoms),
                out_shape=(grid_dim, grid_dim),
                transform=transform,
                fill=0,
                all_touched=True,
                dtype=np.uint8,
            )
        else:
            arr = np.zeros((grid_dim, grid_dim), dtype=np.uint8)

        # Pack 1-bit MSB-first, ceil(w/8) bytes per row.
        packed = np.packbits(arr, axis=1)  # MSB-first per row, pads to byte
        return packed.tobytes()
