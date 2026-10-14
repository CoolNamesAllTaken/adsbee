"""Receiver model: position, clock and timestamp error model."""

from dataclasses import dataclass, field

from .clock import Clock
from .geodesy import enu_to_ecef, ecef_to_lla, lla_to_ecef


@dataclass
class TimingModel:
    """Errors added to the true arrival instant before the clock counts it.

    jitter_ns: white Gaussian demodulator jitter. grid_ns: the demodulator's own time grid (uniform error, 0 for
    none); the counter's own resolution comes from Clock.clock_hz. snr_jitter_ns: extra Gaussian jitter at 10 dB above
    the sensitivity, scaling with 1/amplitude. pair_bias_ns: constant error per receiver and aircraft (signal level
    dependence of the demodulator, short-delay multipath). fixed_delay_ns: constant receiver delay (filters, cable).
    multipath_prob / multipath_mean_ns: share of frames delayed by a long reflection, exponential delay.
    """

    jitter_ns: float = 14.5
    grid_ns: float = 0.0
    snr_jitter_ns: float = 0.0
    pair_bias_ns: float = 8.0
    fixed_delay_ns: float = 0.0
    multipath_prob: float = 0.002
    multipath_mean_ns: float = 300.0


@dataclass
class Receiver:
    id: str
    lat: float  # True position (WGS84, meters above the ellipsoid).
    lon: float
    alt_m: float
    clock: Clock = field(default_factory=Clock)
    timing: TimingModel = field(default_factory=TimingModel)
    name: str = ""
    pos_src: str = "fixed"  # "gnss" | "fixed" | "config"
    reported_lat: float | None = None  # Position the receiver reports; None: the true position.
    reported_lon: float | None = None
    reported_alt_m: float | None = None
    sensitivity_dbm: float = -83.0  # 50 % decode level.
    sensitivity_width_db: float = 1.0
    antenna_gain_dbi: float = 3.0
    cable_loss_db: float = 1.0
    min_elevation_deg: float = -1.0  # Terrain or horizon mask.

    def __post_init__(self):
        self.name = self.name or self.id
        self.reported_lat = self.lat if self.reported_lat is None else self.reported_lat
        self.reported_lon = self.lon if self.reported_lon is None else self.reported_lon
        self.reported_alt_m = self.alt_m if self.reported_alt_m is None else self.reported_alt_m

    @property
    def clock_hz(self) -> int:
        return int(self.clock.clock_hz)

    @property
    def ecef(self):
        return lla_to_ecef(self.lat, self.lon, self.alt_m)

    @property
    def reported_ecef(self):
        return lla_to_ecef(self.reported_lat, self.reported_lon, self.reported_alt_m)

    def add_position_noise(self, rng, horizontal_sigma_m=2.0, vertical_sigma_m=4.0):
        """Reported position = true position plus Gaussian noise per axis (horizontal sigma per axis)."""
        enu = rng.normal(0, [horizontal_sigma_m, horizontal_sigma_m, vertical_sigma_m])
        lat, lon, alt = ecef_to_lla(enu_to_ecef(enu, self.lat, self.lon, self.alt_m))
        self.reported_lat, self.reported_lon, self.reported_alt_m = float(lat), float(lon), float(alt)
        return self

    def info(self) -> dict:
        """Fields of a receiver entry on the mlat:receivers channel."""
        return {
            "id": self.id, "name": self.name, "lat": self.reported_lat, "lon": self.reported_lon,
            "alt_m": self.reported_alt_m, "pos_src": self.pos_src, "clock_hz": self.clock_hz,
        }  # fmt: skip


# Receiver types. Jitter values are per frame and exclude the counter resolution.
def adsbee_1090_timing() -> TimingModel:
    """ADSBee 1090: comparator sampled at 12 MHz, edge average over 24 bits; bench jitter about 15 ns RMS at 48 MHz."""
    return TimingModel(jitter_ns=14.5, grid_ns=0.0, pair_bias_ns=8.0)


def adsbee_1421_timing() -> TimingModel:
    """ADSBee m1421: sync word edge on a 125 ns grid (about 37 ns RMS)."""
    return TimingModel(jitter_ns=5.0, grid_ns=125.0, pair_bias_ns=8.0)


def rtlsdr_dump1090_timing() -> TimingModel:
    """RTL-SDR with dump1090 at 2.4 MS/s: about 50-60 ns per frame."""
    return TimingModel(jitter_ns=55.0, grid_ns=0.0, snr_jitter_ns=20.0, pair_bias_ns=15.0)


RECEIVER_TYPES = {
    "adsbee_1090": adsbee_1090_timing,
    "adsbee_1421": adsbee_1421_timing,
    "rtlsdr": rtlsdr_dump1090_timing,
}
