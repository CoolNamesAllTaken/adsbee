"""
Range maps: 12 height bands x 36 bearing sectors, one max distance per bin, one map per protocol.

On the wire (docs/swarm_api.md) a map is a 54-byte bitmap of present bins plus one byte per present
bin, in bin order, each `ceil(distance / unit_m)`. Stored the same way: `pack` writes the bitmap then
the values, so a sparse hour costs 54 bytes plus one per heard bin. Everything above this module
works with `Map`: {bin index: distance in meters}.
"""
from __future__ import annotations

import base64
import binascii
import math

SECTORS = 36
BANDS = 12
BINS = SECTORS * BANDS
BITMAP_BYTES = BINS // 8
SECTOR_DEG = 360 // SECTORS
#: Aircraft band floors in feet (baro, else geometric altitude); the last band has no ceiling.
BAND_FLOORS_FT = [0, 1000, 2000, 4000, 6000, 10000, 15000, 20000, 25000, 30000, 35000, 40000]
#: Remote ID band floors in feet above the receiver.
REMOTE_ID_FLOORS_FT = [0, 100, 200, 300, 400, 500, 700, 1000, 1500, 2000, 3000, 5000]
DEFAULT_UNIT_M = 2000

Map = dict[int, int]


class Protocol:
    def __init__(self, floors_ft: list[int], top_ft: int, unit_m: int | None, basis: str):
        self.floors_ft, self.top_ft, self.unit_m, self.basis = floors_ft, top_ft, unit_m, basis


#: What a report's `ranges` may hold, and `aircraft`: an old report's `range` (Mode S and UAT
#: mixed). `top_ft` is the top band's ceiling for the horizon limit; `unit_m` the one a report must
#: use (None: any); `basis` what the bands measure.
PROTOCOLS = {
    'mode_s': Protocol(BAND_FLOORS_FT, 60000, 2000, 'altitude'),
    'uat': Protocol(BAND_FLOORS_FT, 60000, 2000, 'altitude'),
    'remote_id': Protocol(REMOTE_ID_FLOORS_FT, 10000, 50, 'height_above_rx'),
    'aircraft': Protocol(BAND_FLOORS_FT, 60000, None, 'altitude'),
}
#: Reported in `ranges`.
REPORTED = ('mode_s', 'uat', 'remote_id')
#: Stored rows each user-facing protocol reads: `aircraft` is the max over every aircraft map.
SOURCES = {'mode_s': ('mode_s',), 'uat': ('uat',), 'remote_id': ('remote_id',),
           'aircraft': ('mode_s', 'uat', 'aircraft')}
LEGACY = 'aircraft'


class RangeError(ValueError):
    """A map that does not decode; the message says why."""


def bin_index(band: int, sector: int) -> int:
    return band * SECTORS + sector


FT_M = 0.3048


def horizon_limit_m(band: int, rx_alt_m: float | None, protocol: str = LEGACY) -> float:
    """The farthest a position in `band` can plausibly be (position guards):
    1.15 * 4.12 km * (sqrt(h_rx) + sqrt(h_band_top)) + 20 km, heights in meters, h_rx floored at 0."""
    table = PROTOCOLS[protocol]
    top_ft = table.floors_ft[band + 1] if band + 1 < BANDS else table.top_ft
    return (1.15 * 4.12 * (math.sqrt(max(rx_alt_m or 0.0, 0.0)) + math.sqrt(top_ft * FT_M)) + 20) * 1000


def within_horizon(values: Map, rx_alt_m: float | None, unit_m: int, protocol: str = LEGACY) -> tuple[Map, int]:
    """(the bins inside their band's horizon limit, how many were not). A value is rounded up to
    `unit_m` on the wire, so a bin up to one unit past the limit still counts."""
    kept = {i: m for i, m in values.items() if m <= horizon_limit_m(i // SECTORS, rx_alt_m, protocol) + unit_m}
    return kept, len(values) - len(kept)


def band_edges_ft(protocol: str = LEGACY) -> list[list[int | None]]:
    floors = PROTOCOLS[protocol].floors_ft
    return [[floor, floors[i + 1] if i + 1 < BANDS else None] for i, floor in enumerate(floors)]


def _bits(bitmap: bytes) -> list[int]:
    return [i for i in range(BINS) if bitmap[i >> 3] >> (i & 7) & 1]


def decode(changed_b64: str, max_b64: str, unit_m: int) -> Map:
    """The wire form to {bin: meters}. Bit i of the bitmap is byte i // 8, bit i % 8 (LSB first)."""
    try:
        bitmap = base64.b64decode(changed_b64, validate=True)
        values = base64.b64decode(max_b64, validate=True)
    except (binascii.Error, ValueError, TypeError) as exc:
        raise RangeError('changed and max must be base64') from exc
    if len(bitmap) != BITMAP_BYTES:
        raise RangeError(f'changed must be {BITMAP_BYTES} bytes')
    present = _bits(bitmap)
    if len(values) != len(present):
        raise RangeError(f'max has {len(values)} bytes for {len(present)} bins')
    if 0 in values:
        raise RangeError('max values are 1..255')
    return {index: value * unit_m for index, value in zip(present, values)}


def encode(ranges: Map, unit_m: int = DEFAULT_UNIT_M) -> tuple[str, str]:
    """{bin: meters} to the wire form (the simulator and tests)."""
    bitmap, values = _pack_parts(ranges, unit_m)
    return base64.b64encode(bitmap).decode(), base64.b64encode(values).decode()


def _pack_parts(ranges: Map, unit_m: int) -> tuple[bytes, bytes]:
    bitmap = bytearray(BITMAP_BYTES)
    values = bytearray()
    for index in sorted(ranges):
        if not 0 <= index < BINS:
            raise RangeError(f'bin {index} out of range')
        bitmap[index >> 3] |= 1 << (index & 7)
        values.append(min(255, max(1, math.ceil(ranges[index] / unit_m))))
    return bytes(bitmap), bytes(values)


def pack(ranges: Map, unit_m: int) -> bytes:
    """Stored form: bitmap then values, in `unit_m` steps (rounded up, as the device does)."""
    bitmap, values = _pack_parts(ranges, unit_m)
    return bitmap + values


def unpack(blob: bytes | memoryview | None, unit_m: int) -> Map:
    if not blob:
        return {}
    blob = bytes(blob)
    present = _bits(blob[:BITMAP_BYTES])
    return {index: value * unit_m for index, value in zip(present, blob[BITMAP_BYTES:])}


def merge(into: Map, other: Map) -> Map:
    """Max per bin, in place."""
    for index, meters in other.items():
        if meters > into.get(index, 0):
            into[index] = meters
    return into


def matrix(ranges: Map) -> list[list[int | None]]:
    """bands x sectors, meters or None: what a 3D view draws."""
    return [[ranges.get(bin_index(band, sector)) for sector in range(SECTORS)] for band in range(BANDS)]


def sector_max(ranges: Map) -> list[int | None]:
    """Per sector, the max over every band: the 2D outline."""
    out: list[int | None] = [None] * SECTORS
    for index, meters in ranges.items():
        sector = index % SECTORS
        if out[sector] is None or meters > out[sector]:
            out[sector] = meters
    return out
