"""Mode S frame encoder: DF4/5/11/17/20/21 with valid parity, CPR airborne positions, altitude and identity codes."""

import math

CRC24_GENERATOR = 0xFFF409
CPR_BITS = 17
CPR_SCALE = 1 << CPR_BITS
CALLSIGN_CHARS = "#ABCDEFGHIJKLMNOPQRSTUVWXYZ##### ###############0123456789######"


def _crc_table():
    table = []
    for byte in range(256):
        crc = byte << 16
        for _ in range(8):
            crc = (crc << 1) ^ CRC24_GENERATOR if crc & 0x800000 else crc << 1
        table.append(crc & 0xFFFFFF)
    return table


_CRC_TABLE = _crc_table()


def crc24(data: bytes) -> int:
    """Mode S parity (CRC-24, generator 0x1FFF409) over the message bits before the parity field."""
    crc = 0
    for byte in data:
        crc = ((crc << 8) & 0xFFFFFF) ^ _CRC_TABLE[(crc >> 16) ^ byte]
    return crc


def _frame(bits: int, num_bits: int, overlay: int = 0) -> bytes:
    """Append parity (XOR overlay, e.g. the address for AP fields) to num_bits - 24 bits of message."""
    body = (bits << 24).to_bytes(num_bits // 8, "big")[: num_bits // 8 - 3]
    return body + (crc24(body) ^ overlay).to_bytes(3, "big")


def altitude_ac13(alt_ft: float) -> int:
    """13-bit altitude code with Q bit set (25 ft steps), as in DF4/DF20. Valid from -1000 to 50175 ft."""
    n = max(0, min(0x7FF, int(round((alt_ft + 1000) / 25))))
    return ((n >> 5) << 7) | (((n >> 4) & 1) << 5) | (1 << 4) | (n & 0xF)


def altitude_ac12(alt_ft: float) -> int:
    """12-bit altitude code with Q bit set (25 ft steps), as in ADS-B airborne position messages."""
    n = max(0, min(0x7FF, int(round((alt_ft + 1000) / 25))))
    return ((n >> 4) << 5) | (1 << 4) | (n & 0xF)


def identity_code(squawk: str) -> int:
    """13-bit identity code for a four digit octal squawk (bit order C1 A1 C2 A2 C4 A4 X B1 D1 B2 D2 B4 D4)."""
    a, b, c, d = (int(ch, 8) for ch in squawk)
    bit = lambda digit, weight: (digit >> weight) & 1  # weight 0, 1, 2 for the 1, 2, 4 pulses
    order = [
        bit(c, 0), bit(a, 0), bit(c, 1), bit(a, 1), bit(c, 2), bit(a, 2), 0,
        bit(b, 0), bit(d, 0), bit(b, 1), bit(d, 1), bit(b, 2), bit(d, 2),
    ]  # fmt: skip
    code = 0
    for v in order:
        code = (code << 1) | v
    return code


def cpr_nl(lat_deg: float) -> int:
    """Number of longitude zones at a latitude."""
    lat = abs(lat_deg)
    if lat < 1e-9:
        return 59
    if lat > 87.0:
        return 1 if lat > 87.0 + 1e-9 else 2
    nz = 15
    a = 1 - math.cos(math.pi / (2 * nz))
    b = math.cos(math.pi / 180 * lat) ** 2
    return int(math.floor(2 * math.pi / math.acos(1 - a / b)))


def cpr_encode_airborne(lat_deg: float, lon_deg: float, odd: bool) -> tuple[int, int]:
    """17-bit airborne CPR encoding: returns (YZ, XZ)."""
    i = 1 if odd else 0
    dlat = 360.0 / (60 - i)
    yz = math.floor(CPR_SCALE * ((lat_deg % dlat) / dlat) + 0.5)
    rlat = dlat * (yz / CPR_SCALE + math.floor(lat_deg / dlat))
    dlon = 360.0 / max(cpr_nl(rlat) - i, 1)
    xz = math.floor(CPR_SCALE * ((lon_deg % dlon) / dlon) + 0.5)
    return yz % CPR_SCALE, xz % CPR_SCALE


def df17(icao: int, me: int, ca: int = 5, df: int = 17) -> bytes:
    """Extended squitter (112 bits) carrying a 56-bit ME field."""
    return _frame((df << 83) | (ca << 80) | (icao << 56) | me, 112)


def me_airborne_position(lat_deg, lon_deg, alt_baro_ft, odd: bool, type_code: int = 11, t_flag: int = 0) -> int:
    yz, xz = cpr_encode_airborne(lat_deg, lon_deg, odd)
    me = type_code << 51
    me |= altitude_ac12(alt_baro_ft) << 36
    me |= t_flag << 35
    me |= (1 if odd else 0) << 34
    me |= yz << 17
    me |= xz
    return me


def me_identification(callsign: str, category: int = 3, type_code: int = 4) -> int:
    chars = 0
    for ch in callsign.upper().ljust(8)[:8]:
        idx = CALLSIGN_CHARS.find(ch)
        chars = (chars << 6) | (idx if idx > 0 else 32)
    return (type_code << 51) | (category << 48) | chars


def me_airborne_velocity(v_east_kt: float, v_north_kt: float, vr_fpm: float, gnss_minus_baro_ft: float = 0.0) -> int:
    """Subtype 1 (subsonic ground speed) velocity message."""
    vew = min(1023, int(round(abs(v_east_kt))) + 1)
    vns = min(1023, int(round(abs(v_north_kt))) + 1)
    vr = min(511, int(round(abs(vr_fpm) / 64)) + 1)
    dalt = min(127, int(round(abs(gnss_minus_baro_ft) / 25)) + 1)
    me = (19 << 51) | (1 << 48)
    me |= (1 if v_east_kt < 0 else 0) << 42 | vew << 32
    me |= (1 if v_north_kt < 0 else 0) << 31 | vns << 21
    me |= 1 << 20  # vertical rate source: barometric
    me |= (1 if vr_fpm < 0 else 0) << 19 | vr << 10
    me |= (1 if gnss_minus_baro_ft < 0 else 0) << 7 | dalt
    return me


def df11(icao: int, ca: int = 5) -> bytes:
    """All-call reply / acquisition squitter (interrogator code 0)."""
    return _frame((11 << 27) | (ca << 24) | icao, 56)


def df4(icao: int, alt_baro_ft: float, fs: int = 0) -> bytes:
    """Surveillance altitude reply."""
    return _frame((4 << 27) | (fs << 24) | altitude_ac13(alt_baro_ft), 56, icao)


def df5(icao: int, squawk: str, fs: int = 0) -> bytes:
    """Surveillance identity reply."""
    return _frame((5 << 27) | (fs << 24) | identity_code(squawk), 56, icao)


def df20(icao: int, alt_baro_ft: float, mb: int = 0, fs: int = 0) -> bytes:
    """Comm-B altitude reply."""
    return _frame((((20 << 27) | (fs << 24) | altitude_ac13(alt_baro_ft)) << 56) | mb, 112, icao)


def df21(icao: int, squawk: str, mb: int = 0, fs: int = 0) -> bytes:
    """Comm-B identity reply."""
    return _frame((((21 << 27) | (fs << 24) | identity_code(squawk)) << 56) | mb, 112, icao)


def mb_bds20(callsign: str) -> int:
    """Comm-B aircraft identification (BDS 2,0) register."""
    mb = 0x20
    for ch in callsign.upper().ljust(8)[:8]:
        idx = CALLSIGN_CHARS.find(ch)
        mb = (mb << 6) | (idx if idx > 0 else 32)
    return mb
