"""WGS84 coordinate conversions."""

import math

import numpy as np

C = 299_792_458.0  # Speed of light in vacuum [m/s].
# Exponential refractivity profile of a standard atmosphere: surface refractivity and scale height.
REFRACTIVITY_N0 = 315e-6
REFRACTIVITY_SCALE_M = 7000.0
_GAUSS_X, _GAUSS_W = np.polynomial.legendre.leggauss(6)
WGS84_A = 6378137.0
WGS84_F = 1 / 298.257223563
WGS84_E2 = WGS84_F * (2 - WGS84_F)
WGS84_B = WGS84_A * (1 - WGS84_F)
WGS84_EP2 = (WGS84_A**2 - WGS84_B**2) / WGS84_B**2
FT = 0.3048
KT = 1852.0 / 3600.0


def llh_to_ecef(lat_deg, lon_deg, h_m):
    """Geodetic latitude, longitude [deg] and ellipsoidal height [m] to ECEF [m]. Accepts scalars or arrays."""
    lat = np.radians(lat_deg)
    lon = np.radians(lon_deg)
    slat = np.sin(lat)
    n = WGS84_A / np.sqrt(1 - WGS84_E2 * slat * slat)
    x = (n + h_m) * np.cos(lat) * np.cos(lon)
    y = (n + h_m) * np.cos(lat) * np.sin(lon)
    z = (n * (1 - WGS84_E2) + h_m) * slat
    return np.stack([x, y, z], axis=-1)


def ecef_to_llh(p):
    """ECEF [m] to (lat_deg, lon_deg, h_m), Bowring's method. Accepts shape (3,) or (N, 3)."""
    p = np.asarray(p, dtype=float)
    x, y, z = p[..., 0], p[..., 1], p[..., 2]
    r = np.hypot(x, y)
    theta = np.arctan2(z * WGS84_A, r * WGS84_B)
    st, ct = np.sin(theta), np.cos(theta)
    lat = np.arctan2(z + WGS84_EP2 * WGS84_B * st**3, r - WGS84_E2 * WGS84_A * ct**3)
    lon = np.arctan2(y, x)
    slat = np.sin(lat)
    n = WGS84_A / np.sqrt(1 - WGS84_E2 * slat * slat)
    h = r / np.cos(lat) - n
    return np.degrees(lat), np.degrees(lon), h


def enu_basis(lat_deg, lon_deg):
    """Rows: east, north, up unit vectors in ECEF at the given point."""
    lat, lon = math.radians(lat_deg), math.radians(lon_deg)
    sl, cl, so, co = math.sin(lat), math.cos(lat), math.sin(lon), math.cos(lon)
    return np.array([[-so, co, 0.0], [-sl * co, -sl * so, cl], [cl * co, cl * so, sl]])


def distance_m(lat1, lon1, lat2, lon2):
    """Great circle distance on a sphere [m]."""
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp, dl = p2 - p1, math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * 6371008.8 * math.asin(min(1.0, math.sqrt(a)))


def tropo_excess_m(rx_ecef, rx_radius_surface, p):
    """Extra path length [m] from the atmosphere along straight paths from receivers to point p.

    rx_ecef: (N, 3). rx_radius_surface: (N,) geocentric radius of the ground under each receiver.
    """
    rx_ecef = np.atleast_2d(rx_ecef)
    s = (_GAUSS_X + 1) / 2
    d = p - rx_ecef
    pts = rx_ecef[:, None, :] + s[None, :, None] * d[:, None, :]
    h = np.linalg.norm(pts, axis=2) - np.asarray(rx_radius_surface)[:, None]
    n = REFRACTIVITY_N0 * np.exp(-np.maximum(h, 0.0) / REFRACTIVITY_SCALE_M)
    return (n @ _GAUSS_W) / 2 * np.linalg.norm(d, axis=1)
