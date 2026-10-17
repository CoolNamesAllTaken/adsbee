"""Scenario: receivers plus aircraft, simulated into per-receiver timestamped Mode S frames."""

from dataclasses import dataclass, field

import numpy as np

from . import modes
from .geodesy import C_M_PER_S, enu_basis, lla_to_ecef
from .receiver import Receiver
from .traffic import (NACP_EPU_M, REPLY_KINDS, REPLY_SHARES, SCHEDULE_ACQUISITION, SCHEDULE_ADSB, Aircraft,
                      gauss_markov, renewal_times)  # fmt: skip

FREQ_HZ = 1090e6
EARTH_RADIUS_M = 6_371_008.8
REFRACTION_K = 4 / 3
# Beast timestamp convention: end of data bit 56, 64 us after the start of the first preamble pulse.
TIMESTAMP_AFTER_PREAMBLE_S = 64e-6
KINDS = ("pos", "vel", "ident", "df11") + REPLY_KINDS
KIND_DF = {"pos": 17, "vel": 17, "ident": 17, "df11": 11, "df4": 4, "df5": 5, "df20": 20, "df21": 21}
GAUSS_NODES, GAUSS_WEIGHTS = np.polynomial.legendre.leggauss(8)


@dataclass
class Emissions:
    """Every transmission, sorted by emit time. Positions are true; rep_* is what an ADS-B position message says."""

    aircraft: np.ndarray  # Index into Scenario.aircraft.
    kind: np.ndarray  # Index into KINDS.
    t_emit: np.ndarray  # Start of the first preamble pulse, true seconds since the scenario start.
    ecef: np.ndarray  # (n, 3)
    lat: np.ndarray
    lon: np.ndarray
    alt_m: np.ndarray
    odd: np.ndarray  # CPR format of position messages.
    rep_lat: np.ndarray  # NaN except for position messages.
    rep_lon: np.ndarray

    def __len__(self):
        return len(self.t_emit)

    def take(self, idx):
        return Emissions(**{k: v[idx] for k, v in self.__dict__.items()})


@dataclass
class Receptions:
    """Every decoded frame: one row per (receiver, emission)."""

    rx: np.ndarray  # Index into Scenario.receivers.
    emission: np.ndarray  # Index into the Emissions the run made.
    t_arrival: np.ndarray  # True arrival of the timestamped instant (Beast convention).
    t_measured: np.ndarray  # t_arrival plus all timing errors, before the receiver clock.
    ticks: np.ndarray  # Receiver counter value (int64, unwrapped).
    signal_dbm: np.ndarray
    tropo_s: np.ndarray  # Excess delay of the troposphere (included in t_arrival).
    err_jitter_s: np.ndarray  # White jitter plus demodulator grid.
    err_bias_s: np.ndarray  # Fixed receiver delay plus receiver/aircraft bias.
    err_multipath_s: np.ndarray

    @staticmethod
    def concat(parts):
        return Receptions(**{k: np.concatenate([getattr(p, k) for p in parts]) for k in Receptions.__dataclass_fields__})

    def __len__(self):
        return len(self.rx)


@dataclass
class Frame:
    """One timestamped Mode S frame as a receiver reports it, plus the truth behind it."""

    rx_id: str
    ticks: int  # Receiver counter, unwrapped; Beast output wraps it to 48 bits.
    clock_hz: int
    msg: bytes  # 7 or 14 bytes with valid parity.
    signal_dbm: float
    # Truth.
    icao: int
    df: int
    t_emit: float  # Start of preamble, true seconds since the scenario start.
    t_arrival: float  # True time of the timestamped instant at the receiver.
    t_unix: float  # t_arrival on the wall clock.
    lat: float  # Aircraft at t_emit.
    lon: float
    alt_m: float
    ecef: tuple
    err_ns: float  # Timestamp error before clock effects (jitter, bias, multipath).

    def beast(self, wrap_bits: int = 48) -> bytes:
        """Beast binary frame (0x1a, type 0x32/0x33, escaped 6-byte timestamp, signal byte, message)."""
        frame_type = b"\x32" if len(self.msg) == 7 else b"\x33"
        ts = (self.ticks & ((1 << wrap_bits) - 1)).to_bytes(6, "big")
        signal = int(min(255, max(1, round(255 * 10 ** ((self.signal_dbm + 40) / 20)))))
        body = ts + bytes([signal]) + self.msg
        return b"\x1a" + frame_type + body.replace(b"\x1a", b"\x1a\x1a")

    def as_dict(self) -> dict:
        d = dict(self.__dict__)
        d["msg"] = self.msg.hex()
        d["icao"] = f"{self.icao:06x}"
        return d


@dataclass
class Scenario:
    receivers: list[Receiver]
    aircraft: list[Aircraft]
    seed: int = 0
    t0_unix: float = 1_760_000_000.0  # Wall clock at true time 0.
    tropo: bool = True
    tropo_n0: float = 315.0  # Surface refractivity (N units).
    tropo_scale_height_m: float = 7000.0
    chunk_s: float = 5.0
    _pair_bias: np.ndarray = field(init=False, repr=False)

    def __post_init__(self):
        rng = np.random.default_rng([self.seed, 1])
        sd = np.array([r.timing.pair_bias_ns for r in self.receivers]) * 1e-9
        self._pair_bias = rng.normal(0, 1, (len(self.receivers), len(self.aircraft))) * sd[:, None]

    def receiver_index(self, rx_id):
        return next(i for i, r in enumerate(self.receivers) if r.id == rx_id)

    # Emissions.
    def emissions(self, duration_s: float) -> Emissions:
        rng = np.random.default_rng([self.seed, 2])
        rows = []
        for ai, ac in enumerate(self.aircraft):
            parts = []
            if ac.adsb:
                for kind, (mean, half) in SCHEDULE_ADSB.items():
                    parts.append((renewal_times(rng, duration_s, mean, half), KINDS.index(kind)))
            parts.append((renewal_times(rng, duration_s, *SCHEDULE_ACQUISITION), KINDS.index("df11")))
            if ac.reply_rate_hz > 0:
                n = rng.poisson(ac.reply_rate_hz * duration_s)
                t = np.sort(rng.uniform(0, duration_s, n))
                kinds = rng.choice([KINDS.index(k) for k in REPLY_KINDS], n, p=REPLY_SHARES)
                parts.append((t, kinds))
            t = np.concatenate([p[0] for p in parts])
            kind = np.concatenate([np.broadcast_to(p[1], p[0].shape) for p in parts])
            order = np.argsort(t)
            t, kind = t[order], kind[order]
            lat, lon, alt = ac.position(t)
            is_pos = kind == KINDS.index("pos")
            odd = np.zeros(len(t), bool)
            odd[is_pos] = (np.arange(is_pos.sum()) + rng.integers(2)) % 2 == 1
            rep_lat = np.full(len(t), np.nan)
            rep_lon = np.full(len(t), np.nan)
            if is_pos.any():
                tp = t[is_pos]
                lat_l, lon_l, _ = ac.position(tp - ac.pos_latency_s)
                err = gauss_markov(rng, tp, NACP_EPU_M.get(ac.nacp, 30.0) / 2.45, ac.error_tau_s)
                rep_lat[is_pos] = lat_l + np.degrees(err[:, 1] / EARTH_RADIUS_M)
                rep_lon[is_pos] = lon_l + np.degrees(err[:, 0] / (EARTH_RADIUS_M * np.cos(np.radians(lat_l))))
            rows.append((np.full(len(t), ai), kind, t, lat, lon, alt, odd, rep_lat, rep_lon))
        cols = [np.concatenate(c) for c in zip(*rows)] if rows else [np.zeros(0)] * 9
        order = np.argsort(cols[2], kind="stable")
        ac_idx, kind, t, lat, lon, alt, odd, rep_lat, rep_lon = (c[order] for c in cols)
        return Emissions(
            aircraft=ac_idx.astype(int), kind=kind.astype(int), t_emit=t, ecef=lla_to_ecef(lat, lon, alt),
            lat=lat, lon=lon, alt_m=alt, odd=odd.astype(bool), rep_lat=rep_lat, rep_lon=rep_lon,
        )  # fmt: skip

    # Propagation and reception.
    def tropo_delay_s(self, rx_ecef, rx_alt_m, target_ecef):
        """Excess delay of an exponential refractivity profile, integrated along the straight path."""
        if not self.tropo:
            return np.zeros(len(target_ecef))
        r_surface = np.linalg.norm(rx_ecef) - rx_alt_m
        s = (GAUSS_NODES + 1) / 2
        pts = rx_ecef + s[None, :, None] * (target_ecef - rx_ecef)[:, None, :]
        h = np.linalg.norm(pts, axis=2) - r_surface
        n = self.tropo_n0 * 1e-6 * np.exp(-np.maximum(h, 0) / self.tropo_scale_height_m)
        length = np.linalg.norm(target_ecef - rx_ecef, axis=1)
        return (n @ GAUSS_WEIGHTS) / 2 * length / C_M_PER_S

    def _receive(self, em: Emissions, em_offset: int, rng) -> Receptions:
        parts = []
        for ri, rx in enumerate(self.receivers):
            rx_ecef = rx.ecef
            vec = em.ecef - rx_ecef
            dist = np.linalg.norm(vec, axis=1)
            up = enu_basis(rx.lat, rx.lon)[2]
            # Refraction raises the apparent elevation (4/3 Earth radius model).
            elev = np.degrees(np.arcsin(vec @ up / dist) + dist / (2 * EARTH_RADIUS_M) * (1 - 1 / REFRACTION_K))
            fspl = 20 * np.log10(dist) + 20 * np.log10(FREQ_HZ) - 147.55
            tx = np.array([a.tx_power_dbm for a in self.aircraft])[em.aircraft]
            fade = np.array([a.fading_db for a in self.aircraft])[em.aircraft]
            power = tx - fspl + rx.antenna_gain_dbi - rx.cable_loss_db + rng.normal(0, 1, len(dist)) * fade
            p_decode = 1 / (1 + np.exp(-(power - rx.sensitivity_dbm) / max(rx.sensitivity_width_db, 1e-3)))
            got = (elev >= rx.min_elevation_deg) & (rng.uniform(size=len(dist)) < p_decode)
            idx = np.nonzero(got)[0]
            n = len(idx)
            tropo = self.tropo_delay_s(rx_ecef, rx.alt_m, em.ecef[idx])
            t_arr = em.t_emit[idx] + TIMESTAMP_AFTER_PREAMBLE_S + dist[idx] / C_M_PER_S + tropo
            tm = rx.timing
            snr_db = power[idx] - rx.sensitivity_dbm
            jitter_sd = np.sqrt(tm.jitter_ns**2 + (tm.snr_jitter_ns * 10 ** ((10 - snr_db) / 20)) ** 2) * 1e-9
            jitter = rng.normal(0, 1, n) * jitter_sd + rng.uniform(-0.5, 0.5, n) * tm.grid_ns * 1e-9
            bias = tm.fixed_delay_ns * 1e-9 + self._pair_bias[ri, em.aircraft[idx]]
            mp = np.where(rng.uniform(size=n) < tm.multipath_prob, rng.exponential(tm.multipath_mean_ns * 1e-9, n), 0.0)
            t_meas = t_arr + jitter + bias + mp
            parts.append(
                Receptions(
                    rx=np.full(n, ri), emission=idx + em_offset, t_arrival=t_arr, t_measured=t_meas,
                    ticks=rx.clock.ticks(t_meas), signal_dbm=power[idx], tropo_s=tropo, err_jitter_s=jitter,
                    err_bias_s=bias, err_multipath_s=mp,
                )
            )  # fmt: skip
        return Receptions.concat(parts)

    def _chunks(self, duration_s):
        em = self.emissions(duration_s)
        edges = np.arange(0, duration_s + self.chunk_s, self.chunk_s)
        bounds = np.searchsorted(em.t_emit, edges)
        for ci in range(len(edges) - 1):
            lo, hi = bounds[ci], bounds[ci + 1]
            rng = np.random.default_rng([self.seed, 3, ci])
            yield em, lo, hi, self._receive(em.take(slice(lo, hi)), lo, rng), edges[ci + 1]

    def simulate(self, duration_s: float):
        """All emissions and receptions of a run as arrays (fast path for studies). Receptions sorted by arrival."""
        em, parts = None, []
        for em, _, _, rec, _ in self._chunks(duration_s):
            parts.append(rec)
        rec = Receptions.concat(parts)
        order = np.argsort(rec.t_arrival, kind="stable")
        return em, Receptions(**{k: getattr(rec, k)[order] for k in Receptions.__dataclass_fields__})

    # Frames.
    def encode(self, em: Emissions, i: int) -> bytes:
        ac = self.aircraft[em.aircraft[i]]
        kind = KINDS[em.kind[i]]
        alt_ft = float(ac.baro_alt_ft(em.alt_m[i]))
        if kind == "pos":
            return modes.df17(ac.icao, modes.me_airborne_position(em.rep_lat[i], em.rep_lon[i], alt_ft, bool(em.odd[i])))
        if kind == "vel":
            return modes.df17(ac.icao, modes.me_airborne_velocity(*ac.velocity_kt(), ac.baro_bias_m / 0.3048))
        if kind == "ident":
            return modes.df17(ac.icao, modes.me_identification(ac.callsign))
        if kind == "df11":
            return modes.df11(ac.icao)
        if kind == "df4":
            return modes.df4(ac.icao, alt_ft)
        if kind == "df5":
            return modes.df5(ac.icao, ac.squawk)
        if kind == "df20":
            return modes.df20(ac.icao, alt_ft, modes.mb_bds20(ac.callsign))
        return modes.df21(ac.icao, ac.squawk, modes.mb_bds20(ac.callsign))

    def frames(self, duration_s: float):
        """Yield Frame records of every receiver, sorted by true arrival time."""
        pending = None
        for em, _, _, rec, chunk_end in self._chunks(duration_s):
            if pending is not None:
                rec = Receptions.concat([pending, rec])
            order = np.argsort(rec.t_arrival, kind="stable")
            ready = order[rec.t_arrival[order] < chunk_end]
            later = order[rec.t_arrival[order] >= chunk_end]
            for j in ready:
                yield self._frame(em, rec, j)
            pending = Receptions(**{k: getattr(rec, k)[later] for k in Receptions.__dataclass_fields__})
        if pending is not None:
            for j in np.argsort(pending.t_arrival, kind="stable"):
                yield self._frame(em, pending, j)

    def _frame(self, em, rec, j) -> Frame:
        i = rec.emission[j]
        rx = self.receivers[rec.rx[j]]
        ac = self.aircraft[em.aircraft[i]]
        return Frame(
            rx_id=rx.id, ticks=int(rec.ticks[j]), clock_hz=rx.clock_hz, msg=self.encode(em, i),
            signal_dbm=float(rec.signal_dbm[j]), icao=ac.icao, df=KIND_DF[KINDS[em.kind[i]]],
            t_emit=float(em.t_emit[i]), t_arrival=float(rec.t_arrival[j]), t_unix=self.t0_unix + float(rec.t_arrival[j]),
            lat=float(em.lat[i]), lon=float(em.lon[i]), alt_m=float(em.alt_m[i]), ecef=tuple(float(v) for v in em.ecef[i]),
            err_ns=float((rec.err_jitter_s[j] + rec.err_bias_s[j] + rec.err_multipath_s[j]) * 1e9),
        )  # fmt: skip


def write_beast(frames, directory):
    """Write one <rx_id>.beast file per receiver; returns {rx_id: path}."""
    import os

    os.makedirs(directory, exist_ok=True)
    files, paths = {}, {}
    try:
        for f in frames:
            if f.rx_id not in files:
                paths[f.rx_id] = os.path.join(directory, f"{f.rx_id}.beast")
                files[f.rx_id] = open(paths[f.rx_id], "wb")
            files[f.rx_id].write(f.beast())
    finally:
        for fh in files.values():
            fh.close()
    return paths
