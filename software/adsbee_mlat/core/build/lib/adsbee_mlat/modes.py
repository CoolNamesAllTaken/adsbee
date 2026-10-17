"""Mode S message decoding: parity, addresses, altitude, identity, velocity and CPR position fields."""

import math
from dataclasses import dataclass

_POLY = 0xFFF409
_CRC_TABLE = []
for _i in range(256):
    _c = _i << 16
    for _ in range(8):
        _c = ((_c << 1) ^ _POLY) if _c & 0x800000 else (_c << 1)
    _CRC_TABLE.append(_c & 0xFFFFFF)
_CRC_TABLE = tuple(_CRC_TABLE)


def parity(body: bytes) -> int:
    """Mode S CRC-24 of a message body (the message without its 3 parity bytes)."""
    crc = 0
    table = _CRC_TABLE
    for b in body:
        crc = ((crc << 8) & 0xFFFFFF) ^ table[((crc >> 16) ^ b) & 0xFF]
    return crc


def crc24(msg: bytes) -> int:
    """Syndrome of a whole message: 0 for a clean DF17/18, the aircraft address for address/parity formats."""
    return parity(msg[:-3]) ^ int.from_bytes(msg[-3:], "big")


# Formats whose parity field is the CRC xor the aircraft address.
AP_FORMATS = frozenset((0, 4, 5, 16, 20, 21))

_CALLSIGN_CHARS = "#ABCDEFGHIJKLMNOPQRSTUVWXYZ##### ###############0123456789######"


def _gillham_to_altitude(code: int):
    """Gillham (gray) coded altitude, bits C1 A1 C2 A2 C4 A4 X B1 D1 B2 D2 B4 D4 (X ignored), to feet or None."""

    def bit(i):
        return (code >> i) & 1

    if bit(4) or not (bit(12) or bit(10) or bit(8)):
        return None  # D1 set, or no C pulse: invalid.
    hundreds = 0
    for b, mask in ((12, 7), (10, 3), (8, 1)):  # C1 C2 C4
        if bit(b):
            hundreds ^= mask
    if hundreds & 5 == 5:
        hundreds ^= 2
    if hundreds > 5:
        return None
    five_hundreds = 0
    for b, mask in ((2, 0xFF), (0, 0x7F), (11, 0x3F), (9, 0x1F), (7, 0x0F), (5, 7), (3, 3), (1, 1)):
        if bit(b):  # D2 D4 A1 A2 A4 B1 B2 B4
            five_hundreds ^= mask
    if five_hundreds & 1:
        hundreds = 6 - hundreds
    return (five_hundreds * 5 + hundreds - 13) * 100


def decode_ac13(ac: int):
    """13-bit altitude code (DF0/4/16/20) to feet, or None."""
    if ac == 0:
        return None
    if (ac >> 6) & 1:
        return None  # Metric altitude, rare.
    if (ac >> 4) & 1:
        n = ((ac & 0x1F80) >> 2) | ((ac & 0x20) >> 1) | (ac & 0x0F)
        return n * 25 - 1000
    return _gillham_to_altitude(ac)


def decode_ac12(ac: int):
    """12-bit altitude code of an airborne position message to feet, or None."""
    if ac == 0:
        return None
    q = (ac >> 4) & 1
    if q:
        n = ((ac & 0x0FE0) >> 1) | (ac & 0x0F)
        return n * 25 - 1000
    ac13 = ((ac & 0x0FC0) << 1) | (ac & 0x3F)
    return _gillham_to_altitude(ac13)


def decode_squawk(id13: int) -> str:
    """13-bit identity code (C1 A1 C2 A2 C4 A4 X B1 D1 B2 D2 B4 D4) to a 4 digit squawk string."""
    a = ((id13 >> 7) & 1) << 2 | ((id13 >> 9) & 1) << 1 | ((id13 >> 11) & 1)
    b = ((id13 >> 1) & 1) << 2 | ((id13 >> 3) & 1) << 1 | ((id13 >> 5) & 1)
    c = ((id13 >> 8) & 1) << 2 | ((id13 >> 10) & 1) << 1 | ((id13 >> 12) & 1)
    d = (id13 & 1) << 2 | ((id13 >> 2) & 1) << 1 | ((id13 >> 4) & 1)
    return f"{a}{b}{c}{d}"


@dataclass(slots=True)
class Decoded:
    """Fields of one Mode S message. Only the fields its format carries are set."""

    df: int
    icao: int
    trusted: bool = False  # Address from a format with a parity check of its own (DF11 with IID 0, DF17, DF18).
    alt_ft: int | None = None
    squawk: str | None = None
    callsign: str | None = None
    tc: int | None = None
    cpr_odd: int | None = None
    cpr_lat: int | None = None
    cpr_lon: int | None = None
    nuc: int | None = None
    gs_kt: float | None = None
    track_deg: float | None = None
    vr_fpm: float | None = None
    geo_minus_baro_ft: int | None = None


def decode(msg: bytes):
    """Decodes a 7 or 14 byte message. Returns Decoded, or None if its parity fails or the format is unsupported."""
    df = msg[0] >> 3
    if len(msg) != (7 if df < 16 else 14):
        return None
    crc = crc24(msg)
    if df in (17, 18):
        if crc:
            return None
        icao = int.from_bytes(msg[1:4], "big")
        d = Decoded(df, icao, True)
        if df == 18 and (msg[0] & 7) not in (0, 1, 2, 6):
            return d  # Non-ICAO address or TIS-B management: identity only.
        _decode_es(msg, d)
        return d
    if df == 11:
        if crc & 0xFFFF80:
            return None
        icao = int.from_bytes(msg[1:4], "big")
        return Decoded(df, icao, crc == 0)
    if df in AP_FORMATS:
        d = Decoded(df, crc)
        if df in (0, 4, 16, 20):
            d.alt_ft = decode_ac13(((msg[2] << 8) | msg[3]) & 0x1FFF)
        else:
            d.squawk = decode_squawk(((msg[2] << 8) | msg[3]) & 0x1FFF)
        if df == 20 or df == 21:
            _decode_commb_identity(msg, d)
        return d
    return None


def _decode_commb_identity(msg: bytes, d: Decoded):
    """Comm-B register 2,0 (aircraft identification) carried by DF20/21."""
    if msg[4] != 0x20:
        return
    v = int.from_bytes(msg[5:11], "big")
    cs = "".join(_CALLSIGN_CHARS[(v >> (42 - 6 * i)) & 0x3F] for i in range(8))
    if "#" not in cs:
        d.callsign = cs.strip() or None


def _decode_es(msg: bytes, d: Decoded):
    me = msg[4:11]
    tc = me[0] >> 3
    d.tc = tc
    if 1 <= tc <= 4:
        v = int.from_bytes(me, "big")
        cs = "".join(_CALLSIGN_CHARS[(v >> (42 - 6 * i)) & 0x3F] for i in range(8))
        if "#" not in cs:
            d.callsign = cs.strip() or None
    elif 9 <= tc <= 18 or 20 <= tc <= 22:
        ac = (me[1] << 4) | (me[2] >> 4)
        if tc <= 18:
            d.alt_ft = decode_ac12(ac)
            d.nuc = 18 - tc
        d.cpr_odd = (me[2] >> 2) & 1
        d.cpr_lat = ((me[2] & 3) << 15) | (me[3] << 7) | (me[4] >> 1)
        d.cpr_lon = ((me[4] & 1) << 16) | (me[5] << 8) | me[6]
    elif tc == 19:
        _decode_velocity(me, d)


def _decode_velocity(me: bytes, d: Decoded):
    st = me[0] & 7
    v = int.from_bytes(me, "big")
    vr_sign = (v >> 19) & 1
    vr = (v >> 10) & 0x1FF
    if vr:
        d.vr_fpm = (-1 if vr_sign else 1) * (vr - 1) * 64.0
    gd = v & 0xFF
    if gd:
        d.geo_minus_baro_ft = (-1 if gd & 0x80 else 1) * ((gd & 0x7F) - 1) * 25
    if st in (1, 2):
        mult = 4 if st == 2 else 1
        ew_sign = (v >> 42) & 1
        ew = (v >> 32) & 0x3FF
        ns_sign = (v >> 31) & 1
        ns = (v >> 21) & 0x3FF
        if ew and ns:
            vx = (-1 if ew_sign else 1) * (ew - 1) * mult
            vy = (-1 if ns_sign else 1) * (ns - 1) * mult
            d.gs_kt = math.hypot(vx, vy)
            d.track_deg = math.degrees(math.atan2(vx, vy)) % 360.0
    elif st in (3, 4):
        if (v >> 42) & 1:
            d.track_deg = ((v >> 32) & 0x3FF) * 360.0 / 1024.0
        asp = (v >> 21) & 0x3FF
        if asp:
            d.gs_kt = (asp - 1) * (4 if st == 4 else 1)  # Airspeed: the best speed this message offers.
