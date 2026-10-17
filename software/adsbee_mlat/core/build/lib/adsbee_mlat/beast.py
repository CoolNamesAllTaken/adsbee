"""Beast stream parsing and building, including the receiver info frame (see PROTOCOL.md)."""

ESC = 0x1A
TYPE_MODE_AC = 0x31
TYPE_MODE_S_SHORT = 0x32
TYPE_MODE_S_LONG = 0x33
TYPE_STATUS = 0x34
TYPE_FEED_ID = 0xE4
TYPE_RECEIVER_INFO = 0xE9
INFO_MAX_LEN = 512
TIMESTAMP_MODULUS = 1 << 48

# Unescaped body length after the type byte: 6 timestamp + 1 signal + message.
_BODY_LEN = {TYPE_MODE_AC: 9, TYPE_MODE_S_SHORT: 14, TYPE_MODE_S_LONG: 21, TYPE_STATUS: 9}
_ESC_BYTE = b"\x1a"
_ESC_PAIR = b"\x1a\x1a"


class BeastParser:
    """Incremental Beast parser.

    feed() returns (frames, infos, feed_ids): frames are (timestamp, signal, message) tuples of Mode S frames, infos
    are receiver info dicts and feed_ids are UUID strings from 0xe4 frames.
    """

    __slots__ = ("buf", "bad_frames")

    def __init__(self):
        self.buf = b""
        self.bad_frames = 0

    def feed(self, data: bytes):
        buf = self.buf + data if self.buf else data
        frames = []
        infos = []
        feed_ids = []
        n = len(buf)
        i = 0
        find = buf.find
        keep = n
        while True:
            j = find(_ESC_BYTE, i)
            if j < 0 or j + 1 >= n:
                keep = j if j >= 0 else n
                break
            t = buf[j + 1]
            body_len = _BODY_LEN.get(t)
            if body_len is not None:
                end = j + 2 + body_len
                if end > n:
                    keep = j
                    break
                body = buf[j + 2 : end]
                if ESC in body:
                    body, end = _unescape(buf, j + 2, body_len)
                    if body is None:
                        if end < 0:
                            keep = j
                            break
                        self.bad_frames += 1
                        i = end
                        continue
                if t != TYPE_MODE_AC and t != TYPE_STATUS:
                    frames.append((int.from_bytes(body[:6], "big"), body[6], body[7:]))
                i = end
            elif t == TYPE_RECEIVER_INFO:
                e = find(b"\n", j + 2, j + 2 + INFO_MAX_LEN)
                if e < 0:
                    if n - j < INFO_MAX_LEN + 2:
                        keep = j
                        break
                    self.bad_frames += 1
                    i = j + 2
                    continue
                info = parse_info(buf[j + 2 : e])
                if info is not None:
                    infos.append(info)
                else:
                    self.bad_frames += 1
                i = e + 1
            elif t == TYPE_FEED_ID:
                if j + 38 > n:
                    keep = j
                    break
                feed_ids.append(buf[j + 2 : j + 38].decode("ascii", "replace"))
                i = j + 38
            else:
                # Unknown type, an escaped 0x1a seen out of sync, or a frame type we skip (UAT): resynchronize.
                i = j + 2
        self.buf = buf[keep:] if keep < n else b""
        if len(self.buf) > 4096:
            self.buf = b""
        return frames, infos, feed_ids


def _unescape(buf: bytes, start: int, length: int):
    """Unescapes length bytes from buf[start:]. Returns (body, end), (None, -1) if incomplete, (None, resync) if bad."""
    out = bytearray()
    i = start
    n = len(buf)
    while len(out) < length:
        if i >= n:
            return None, -1
        b = buf[i]
        if b == ESC:
            if i + 1 >= n:
                return None, -1
            if buf[i + 1] != ESC:
                return None, i  # A new frame starts here: this one is truncated.
            i += 2
        else:
            i += 1
        out.append(b)
    return bytes(out), i


def escape(data: bytes) -> bytes:
    return data.replace(_ESC_BYTE, _ESC_PAIR)


def build_mode_s(timestamp: int, msg: bytes, signal: int = 0x80) -> bytes:
    """One escaped Mode S frame."""
    t = TYPE_MODE_S_SHORT if len(msg) == 7 else TYPE_MODE_S_LONG
    body = (timestamp % TIMESTAMP_MODULUS).to_bytes(6, "big") + bytes((signal,)) + msg
    return bytes((ESC, t)) + escape(body)


_INFO_FLOAT_KEYS = ("lat", "lon", "alt", "hacc", "vacc")


def build_info(**fields) -> bytes:
    """Receiver info frame from keyword fields (see PROTOCOL.md). Floats keep enough digits for millimeters."""
    fields.setdefault("v", 1)
    parts = []
    for k, v in fields.items():
        if v is None:
            continue
        if isinstance(v, float):
            v = f"{v:.8f}".rstrip("0").rstrip(".") if k in ("lat", "lon") else f"{v:.3f}"
        s = str(v)
        if any(c in s for c in ";=\n") or not s.isprintable():
            raise ValueError(f"bad value for {k}")
        parts.append(f"{k}={s}")
    payload = ";".join(parts).encode("ascii")
    if len(payload) > INFO_MAX_LEN:
        raise ValueError("receiver info too long")
    return bytes((ESC, TYPE_RECEIVER_INFO)) + payload + b"\n"


def parse_info(payload: bytes):
    """Parses a receiver info payload into a dict with typed values, or None if malformed."""
    try:
        text = payload.decode("ascii")
    except UnicodeDecodeError:
        return None
    out = {}
    for part in text.split(";"):
        if not part:
            continue
        k, sep, v = part.partition("=")
        if not sep:
            return None
        out[k.strip()] = v.strip()
    if "id" not in out or not out["id"]:
        return None
    try:
        for k in _INFO_FLOAT_KEYS:
            if k in out:
                out[k] = float(out[k])
        if "clk" in out:
            out["clk"] = int(out["clk"])
        if "v" in out:
            out["v"] = int(out["v"])
        if "mov" in out:
            out["mov"] = out["mov"] == "1"
        if "pps" in out:
            ticks, _, sec = out["pps"].partition("@")
            out["pps"] = (int(ticks, 16), int(sec))
    except ValueError:
        return None
    return out
