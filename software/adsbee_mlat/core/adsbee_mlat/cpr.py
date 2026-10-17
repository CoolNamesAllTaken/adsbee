"""Compact Position Reporting (CPR) for airborne positions: global and local decoding, and encoding for tests."""

import math

_NZ = 15
_D_LAT_EVEN = 360.0 / 60
_D_LAT_ODD = 360.0 / 59
_SCALE = 1 << 17


def _nl_table():
    table = []
    a = 1 - math.cos(math.pi / (2 * _NZ))
    for nl in range(59, 1, -1):
        lat = math.degrees(math.acos(math.sqrt(a / (1 - math.cos(2 * math.pi / nl)))))
        table.append((lat, nl))
    return table


_NL_TABLE = _nl_table()


def nl(lat: float) -> int:
    """Number of longitude zones at a latitude."""
    lat = abs(lat)
    if lat >= 87.0:
        return 1
    for limit, n in _NL_TABLE:
        if lat < limit:
            return n
    return 1


def global_airborne(lat_even: int, lon_even: int, lat_odd: int, lon_odd: int, odd_is_newest: bool):
    """Decodes an even/odd pair. Returns (lat, lon) of the newest message, or None if they straddle a zone boundary."""
    j = math.floor((59 * lat_even - 60 * lat_odd) / _SCALE + 0.5)
    rlat0 = _D_LAT_EVEN * ((j % 60) + lat_even / _SCALE)
    rlat1 = _D_LAT_ODD * ((j % 59) + lat_odd / _SCALE)
    if rlat0 >= 270:
        rlat0 -= 360
    if rlat1 >= 270:
        rlat1 -= 360
    if not (-90 <= rlat0 <= 90 and -90 <= rlat1 <= 90):
        return None
    if nl(rlat0) != nl(rlat1):
        return None
    if odd_is_newest:
        rlat = rlat1
        n = max(nl(rlat1) - 1, 1)
        m = math.floor((lon_even * (nl(rlat1) - 1) - lon_odd * nl(rlat1)) / _SCALE + 0.5)
        rlon = (360.0 / n) * ((m % n) + lon_odd / _SCALE)
    else:
        rlat = rlat0
        n = max(nl(rlat0), 1)
        m = math.floor((lon_even * (nl(rlat0) - 1) - lon_odd * nl(rlat0)) / _SCALE + 0.5)
        rlon = (360.0 / n) * ((m % n) + lon_even / _SCALE)
    if rlon >= 180:
        rlon -= 360
    return rlat, rlon


def local_airborne(cpr_lat: int, cpr_lon: int, odd: int, ref_lat: float, ref_lon: float):
    """Decodes one message relative to a reference position within about 180 nautical miles."""
    dlat = _D_LAT_ODD if odd else _D_LAT_EVEN
    j = math.floor(ref_lat / dlat) + math.floor(
        0.5 + ((ref_lat % dlat) / dlat) - cpr_lat / _SCALE
    )
    rlat = dlat * (j + cpr_lat / _SCALE)
    if not -90 <= rlat <= 90:
        return None
    n = nl(rlat) - odd
    dlon = 360.0 / n if n > 0 else 360.0
    m = math.floor(ref_lon / dlon) + math.floor(0.5 + ((ref_lon % dlon) / dlon) - cpr_lon / _SCALE)
    rlon = dlon * (m + cpr_lon / _SCALE)
    if rlon >= 180:
        rlon -= 360
    elif rlon < -180:
        rlon += 360
    return rlat, rlon


def encode_airborne(lat: float, lon: float, odd: int):
    """Encodes a position into 17-bit CPR latitude and longitude."""
    dlat = _D_LAT_ODD if odd else _D_LAT_EVEN
    yz = math.floor(_SCALE * ((lat % dlat) / dlat) + 0.5)
    rlat = dlat * (yz / _SCALE + math.floor(lat / dlat))
    n = nl(rlat) - odd
    dlon = 360.0 / n if n > 0 else 360.0
    xz = math.floor(_SCALE * ((lon % dlon) / dlon) + 0.5)
    return yz & (_SCALE - 1), xz & (_SCALE - 1)
