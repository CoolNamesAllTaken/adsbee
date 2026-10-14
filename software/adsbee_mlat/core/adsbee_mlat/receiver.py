"""Per-receiver state: identity, position, timestamp unwrapping and the coarse map from receiver time to Unix time."""

from collections import deque

import numpy as np

from . import geo

TIMESTAMP_MODULUS = 1 << 48
_HALF_MODULUS = 1 << 47
# Default one sigma timestamp noise by clock rate [s]: quantization plus typical demodulator jitter.
DEFAULT_JITTER_S = {12_000_000: 70e-9, 48_000_000: 40e-9}
# Default position accuracy by source, (horizontal, vertical) one sigma [m].
DEFAULT_ACCURACY_M = {"gnss": (5.0, 10.0), "fixed": (1.0, 2.0), "config": (1.0, 2.0)}
RESET_TOLERANCE_S = 1.0  # A timestamp this far off the Unix time map means the counter restarted.


class Receiver:
    """A receiver feeding the server. Times are seconds of this receiver's clock since its current epoch began."""

    def __init__(self, rid: str, index: int, clock_hz: int = 12_000_000):
        self.id = rid
        self.index = index
        self.name = rid
        self.clock_hz = clock_hz
        self.epoch = None
        self.lat = self.lon = self.alt = None
        self.ecef = None
        self.pos_src = "config"
        self.hacc, self.vacc = DEFAULT_ACCURACY_M["config"]
        self.moving = False
        self.pps = None
        self.firmware = None
        self.connected = False
        self.peer = None
        self.jitter_s = DEFAULT_JITTER_S.get(clock_hz, 70e-9)
        self.jitter_estimated = False
        self.msg_count = 0
        self.msg_rate = 0.0
        self._rate_count = 0
        self._rate_t = None
        self.on_reset = None  # Callback(receiver) when the clock restarts.
        self.resets = 0
        self._reset_clock()

    def _reset_clock(self):
        self._last_raw = None
        self._wraps = 0
        self._base = None
        self._unix_offset = None
        self._offset_bins = deque(maxlen=10)
        self._bin_start = None
        self._bin_min = None

    def reset_clock(self):
        self._reset_clock()
        self.resets += 1
        if self.on_reset:
            self.on_reset(self)

    @property
    def has_position(self) -> bool:
        return self.ecef is not None

    def set_position(self, lat: float, lon: float, alt: float, src: str, hacc=None, vacc=None):
        self.lat, self.lon, self.alt = float(lat), float(lon), float(alt)
        self.ecef = geo.llh_to_ecef(self.lat, self.lon, self.alt)
        self.radius_surface = float(np.linalg.norm(self.ecef)) - self.alt
        self.pos_src = src
        dh, dv = DEFAULT_ACCURACY_M.get(src, (5.0, 10.0))
        self.hacc = float(hacc) if hacc is not None else dh
        self.vacc = float(vacc) if vacc is not None else dv

    def set_clock_hz(self, hz: int):
        if hz != self.clock_hz:
            self.clock_hz = int(hz)
            if not self.jitter_estimated:
                self.jitter_s = DEFAULT_JITTER_S.get(self.clock_hz, 70e-9)
            if self._base is not None:
                self.reset_clock()

    def apply_info(self, info: dict):
        """Applies a receiver info frame. Returns True if the clock was reset."""
        reset = False
        if "name" in info:
            self.name = info["name"]
        if "fw" in info:
            self.firmware = info["fw"]
        if "clk" in info and info["clk"] != self.clock_hz:
            self.set_clock_hz(info["clk"])
            reset = True
        if "ep" in info:
            if self.epoch is not None and info["ep"] != self.epoch and self._base is not None:
                self.reset_clock()
                reset = True
            self.epoch = info["ep"]
        if all(k in info for k in ("lat", "lon", "alt")):
            self.set_position(info["lat"], info["lon"], info["alt"], info.get("src", "gnss"), info.get("hacc"),
                              info.get("vacc"))
        if "mov" in info:
            self.moving = info["mov"]
        if "pps" in info:
            self.pps = info["pps"]
        return reset

    def to_seconds(self, raw: int) -> float:
        """Unwraps a 48 bit timestamp into seconds since this epoch began. Call in arrival order."""
        last = self._last_raw
        if last is None:
            self._base = raw
            self._wraps = 0
        elif raw < last - _HALF_MODULUS:
            self._wraps += TIMESTAMP_MODULUS
        elif raw > last + _HALF_MODULUS:
            self._wraps -= TIMESTAMP_MODULUS  # Slightly reordered frames across a wrap.
        self._last_raw = raw
        return (raw + self._wraps - self._base) / self.clock_hz

    def observe_wall(self, t_rx: float, wall: float) -> bool:
        """Feeds the receive time of the newest frame of a read. Returns False (after resetting) on a clock jump."""
        off = wall - t_rx
        if self._unix_offset is not None and abs(off - self._unix_offset) > RESET_TOLERANCE_S:
            self.reset_clock()
            return False
        if self._bin_start is None or wall - self._bin_start >= 1.0:
            if self._bin_min is not None:
                self._offset_bins.append(self._bin_min)
            self._bin_start = wall
            self._bin_min = off
        elif off < self._bin_min:
            self._bin_min = off
        mins = min(self._offset_bins) if self._offset_bins else self._bin_min
        self._unix_offset = min(mins, self._bin_min)
        return True

    def to_unix(self, t_rx: float):
        """Coarse Unix time of a receiver time (network delay removed by a sliding minimum), or None."""
        if self._unix_offset is None:
            return None
        return t_rx + self._unix_offset

    def update_rate(self, now: float):
        if self._rate_t is None:
            self._rate_t = now
            self._rate_count = self.msg_count
            return
        dt = now - self._rate_t
        if dt >= 1.0:
            self.msg_rate = (self.msg_count - self._rate_count) / dt
            self._rate_t = now
            self._rate_count = self.msg_count

    def position_array(self):
        return np.asarray(self.ecef)
