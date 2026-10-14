"""Synthetic Mode S traffic for multilateration (MLAT): per-receiver timestamped frames with a full error model."""

import numpy as np

from .clock import Clock
from .geodesy import destination, ecef_to_lla, lla_to_ecef
from .receiver import RECEIVER_TYPES, Receiver, TimingModel
from .scenario import Emissions, Frame, Receptions, Scenario, write_beast
from .traffic import Aircraft, random_traffic

__all__ = [
    "Aircraft", "Clock", "Emissions", "Frame", "Receiver", "Receptions", "Scenario", "TimingModel",
    "RECEIVER_TYPES", "destination", "ecef_to_lla", "lla_to_ecef", "make_array", "example_scenario",
    "random_traffic", "write_beast",
]  # fmt: skip


def make_array(center_lat, center_lon, n, baseline_m, clock_hz=48e6, receiver_type="adsbee_1090", seed=0,
               alt_m=50.0, gnss_sigma_m=None, ppm_sd=10.0, random_walk_ppm=0.002, center_receiver=None):  # fmt: skip
    """n receivers on a circle whose chords between neighbors equal baseline_m (n=2: a pair baseline_m apart).

    center_receiver: put one more receiver at the center (default: True for n >= 5, so 5 = 4 on a ring + 1).
    gnss_sigma_m: horizontal sigma per axis of the reported position (vertical twice that); None: surveyed.
    """
    rng = np.random.default_rng([seed, 10])
    if center_receiver is None:
        center_receiver = n >= 5
    n_ring = n - 1 if center_receiver else n
    radius = baseline_m / (2 * np.sin(np.pi / n_ring)) if n_ring > 1 else 0.0
    points = [(center_lat, center_lon)] if center_receiver else []
    for k in range(n_ring):
        lat, lon = destination(center_lat, center_lon, 360.0 * k / n_ring, radius)
        points.append((float(lat), float(lon)))
    receivers = []
    for k, (lat, lon) in enumerate(points):
        rx = Receiver(
            id=f"rx{k}", lat=lat, lon=lon, alt_m=alt_m, timing=RECEIVER_TYPES[receiver_type](),
            clock=Clock(clock_hz=clock_hz, offset_s=rng.uniform(0, 1000), ppm=rng.normal(0, ppm_sd),
                        random_walk_ppm=random_walk_ppm, seed=int(rng.integers(1 << 31))),
            pos_src="fixed" if gnss_sigma_m is None else "gnss",
        )  # fmt: skip
        if gnss_sigma_m is not None:
            rx.add_position_noise(rng, gnss_sigma_m, 2 * gnss_sigma_m)
        receivers.append(rx)
    return receivers


def example_scenario(n_receivers=4, baseline_m=20e3, n_aircraft=40, radius_m=150e3, clock_hz=48e6, seed=0,
                     center=(47.6, -122.3)):  # fmt: skip
    """Small ready-made scenario: a receiver ring and random traffic around it."""
    rng = np.random.default_rng([seed, 11])
    receivers = make_array(*center, n_receivers, baseline_m, clock_hz=clock_hz, seed=seed)
    aircraft = random_traffic(rng, *center, n_aircraft, radius_m)
    return Scenario(receivers=receivers, aircraft=aircraft, seed=seed)
