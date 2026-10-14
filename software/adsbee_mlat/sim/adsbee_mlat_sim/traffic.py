"""Aircraft model and transmit schedules."""

from dataclasses import dataclass

import numpy as np

from .geodesy import FT_TO_M, destination, lla_to_ecef

KT_TO_MPS = 1852 / 3600
# 95 % horizontal position error bound per ADS-B navigation accuracy category (NACp), meters.
NACP_EPU_M = {6: 555.6, 7: 185.2, 8: 92.6, 9: 30.0, 10: 10.0, 11: 3.0}

# Message kinds and their schedule: (mean interval s, half-width of the uniform jitter s).
SCHEDULE_ADSB = {"pos": (0.5, 0.1), "vel": (0.5, 0.1), "ident": (5.0, 0.2)}
SCHEDULE_ACQUISITION = (1.0, 0.2)  # DF11 squitter of every Mode S transponder.
REPLY_KINDS = ("df4", "df5", "df20", "df21")
REPLY_SHARES = (0.45, 0.25, 0.2, 0.1)


@dataclass
class Aircraft:
    icao: int
    lat: float  # Position at true time 0.
    lon: float
    alt_m: float  # Height above the ellipsoid.
    gs_mps: float = 230.0
    track_deg: float = 0.0
    vr_mps: float = 0.0
    callsign: str = ""
    squawk: str = "1000"
    adsb: bool = True  # Transmits DF17 extended squitters.
    reply_rate_hz: float = 2.0  # Mode S replies to ground interrogations (DF4/5/20/21).
    tx_power_dbm: float = 57.0  # Effective radiated power.
    fading_db: float = 3.0  # Per frame antenna pattern and fading spread.
    nacp: int = 9
    pos_latency_s: float = 0.05  # Age of the reported ADS-B position at transmission.
    error_tau_s: float = 60.0  # Correlation time of the GNSS position error.
    baro_bias_m: float = 0.0  # Height minus pressure altitude.

    def __post_init__(self):
        self.callsign = self.callsign or f"SIM{self.icao & 0xFFF:03X}"

    def position(self, t):
        """True (lat, lon, alt_m) at true times t, flying a great circle at constant ground speed."""
        t = np.asarray(t, dtype=float)
        lat, lon = destination(self.lat, self.lon, self.track_deg, self.gs_mps * t)
        return lat, lon, self.alt_m + self.vr_mps * t

    def ecef(self, t):
        return lla_to_ecef(*self.position(t))

    def baro_alt_ft(self, alt_m):
        return (np.asarray(alt_m) - self.baro_bias_m) / FT_TO_M

    def velocity_kt(self):
        v_east = self.gs_mps * np.sin(np.radians(self.track_deg)) / KT_TO_MPS
        v_north = self.gs_mps * np.cos(np.radians(self.track_deg)) / KT_TO_MPS
        return v_east, v_north, self.vr_mps / FT_TO_M * 60


def renewal_times(rng, duration_s, mean_s, half_width_s):
    """Transmit times with uniformly jittered intervals, random phase."""
    n = int(duration_s / max(mean_s - half_width_s, 1e-3)) + 2
    intervals = rng.uniform(mean_s - half_width_s, mean_s + half_width_s, n)
    t = rng.uniform(0, mean_s) + np.concatenate([[0], np.cumsum(intervals[:-1])])
    return t[t < duration_s]


def gauss_markov(rng, t, sigma, tau_s, dims=2):
    """First-order Gauss-Markov process sampled at sorted times t."""
    out = np.zeros((len(t), dims))
    if len(t) == 0:
        return out
    out[0] = rng.normal(0, sigma, dims)
    dt = np.diff(t)
    a = np.exp(-dt / tau_s)
    noise = rng.normal(0, 1, (len(t) - 1, dims)) * (sigma * np.sqrt(1 - a**2))[:, None]
    for i in range(1, len(t)):
        out[i] = a[i - 1] * out[i - 1] + noise[i - 1]
    return out


def random_traffic(rng, center_lat, center_lon, n, radius_m, adsb_share=0.8, alt_range_m=(3000, 12000),
                   icao_base=0xADF000):  # fmt: skip
    """Aircraft spread uniformly over a disk, random tracks; ICAO addresses from icao_base up."""
    aircraft = []
    for i in range(n):
        r = radius_m * np.sqrt(rng.uniform())
        lat, lon = destination(center_lat, center_lon, rng.uniform(0, 360), r)
        alt = rng.uniform(*alt_range_m)
        aircraft.append(
            Aircraft(
                icao=icao_base + i, lat=float(lat), lon=float(lon), alt_m=alt,
                gs_mps=rng.uniform(120, 260), track_deg=rng.uniform(0, 360), vr_mps=rng.choice([0, 0, 0, -6, 6]),
                squawk="".join(str(d) for d in rng.integers(0, 8, 4)), adsb=bool(rng.uniform() < adsb_share),
                reply_rate_hz=rng.uniform(0.5, 4), tx_power_dbm=rng.uniform(54, 58), nacp=int(rng.choice([8, 9, 9, 10])),
                pos_latency_s=rng.uniform(0, 0.15),
            )
        )  # fmt: skip
    return aircraft
