"""WGS84 conversions between geodetic (lat, lon, alt) and Earth-centered Earth-fixed (ECEF) coordinates."""

import numpy as np

WGS84_A = 6378137.0
WGS84_F = 1 / 298.257223563
WGS84_E2 = WGS84_F * (2 - WGS84_F)
WGS84_B = WGS84_A * (1 - WGS84_F)
WGS84_EP2 = (WGS84_A**2 - WGS84_B**2) / WGS84_B**2

C_M_PER_S = 299_792_458.0
FT_TO_M = 0.3048


def lla_to_ecef(lat_deg, lon_deg, alt_m):
    """Geodetic degrees and meters above the ellipsoid to ECEF meters. Accepts scalars or arrays, returns (..., 3)."""
    lat = np.radians(np.asarray(lat_deg, dtype=float))
    lon = np.radians(np.asarray(lon_deg, dtype=float))
    alt = np.asarray(alt_m, dtype=float)
    n = WGS84_A / np.sqrt(1 - WGS84_E2 * np.sin(lat) ** 2)
    x = (n + alt) * np.cos(lat) * np.cos(lon)
    y = (n + alt) * np.cos(lat) * np.sin(lon)
    z = (n * (1 - WGS84_E2) + alt) * np.sin(lat)
    return np.stack([x, y, z], axis=-1)


def ecef_to_lla(xyz):
    """ECEF meters (..., 3) to (lat_deg, lon_deg, alt_m) arrays (Bowring's method, sub-millimeter at aircraft heights)."""
    xyz = np.asarray(xyz, dtype=float)
    x, y, z = xyz[..., 0], xyz[..., 1], xyz[..., 2]
    p = np.hypot(x, y)
    th = np.arctan2(z * WGS84_A, p * WGS84_B)
    lat = np.arctan2(z + WGS84_EP2 * WGS84_B * np.sin(th) ** 3, p - WGS84_E2 * WGS84_A * np.cos(th) ** 3)
    lon = np.arctan2(y, x)
    n = WGS84_A / np.sqrt(1 - WGS84_E2 * np.sin(lat) ** 2)
    alt = p / np.cos(lat) - n
    return np.degrees(lat), np.degrees(lon), alt


def enu_basis(lat_deg, lon_deg):
    """Rows: east, north, up unit vectors (ECEF) at a geodetic point."""
    lat, lon = np.radians(lat_deg), np.radians(lon_deg)
    sl, cl, so, co = np.sin(lat), np.cos(lat), np.sin(lon), np.cos(lon)
    return np.array([[-so, co, 0.0], [-sl * co, -sl * so, cl], [cl * co, cl * so, sl]])


def enu_to_ecef(enu, lat0_deg, lon0_deg, alt0_m=0.0):
    """Local east/north/up meters (..., 3) around a reference point to ECEF meters."""
    origin = lla_to_ecef(lat0_deg, lon0_deg, alt0_m)
    return origin + np.asarray(enu, dtype=float) @ enu_basis(lat0_deg, lon0_deg)


def ecef_to_enu(xyz, lat0_deg, lon0_deg, alt0_m=0.0):
    """ECEF meters (..., 3) to local east/north/up meters around a reference point."""
    origin = lla_to_ecef(lat0_deg, lon0_deg, alt0_m)
    return (np.asarray(xyz, dtype=float) - origin) @ enu_basis(lat0_deg, lon0_deg).T


def destination(lat_deg, lon_deg, bearing_deg, distance_m):
    """Point at a distance and initial bearing on a sphere of the local mean radius (good to meters at 300 km)."""
    r = 6_371_008.8
    lat1, lon1, brg = np.radians(lat_deg), np.radians(lon_deg), np.radians(bearing_deg)
    d = np.asarray(distance_m, dtype=float) / r
    lat2 = np.arcsin(np.sin(lat1) * np.cos(d) + np.cos(lat1) * np.sin(d) * np.cos(brg))
    lon2 = lon1 + np.arctan2(np.sin(brg) * np.sin(d) * np.cos(lat1), np.cos(d) - np.sin(lat1) * np.sin(lat2))
    return np.degrees(lat2), (np.degrees(lon2) + 540) % 360 - 180
