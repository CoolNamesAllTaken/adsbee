"""Per-aircraft state: decoded identity and ADS-B data, and an extended Kalman filter (EKF) MLAT track.

The track state is ECEF position and velocity with a constant velocity model. Every message heard by two or more
synchronized receivers updates it with its time differences of arrival, so fixes come at the aircraft's own message
rate. A track starts from a least squares fix.
"""

import math

import numpy as np

from . import cpr, geo, solver

C = geo.C
ACCEL_NOISE = 1.0  # White acceleration spectral density [m^2/s^3].
# The filter treats timing errors as independent between messages. Per receiver and aircraft biases (multipath,
# signal level) and clock sync errors are not, so the reported error is the filter's estimate scaled by this factor,
# calibrated in simulation so that about 65 % of fixes fall within it.
ERROR_SCALE = 2.0
INIT_VEL_SIGMA = 150.0  # [m/s]
GATE_PER_DOF = 9.0
GATE_OFFSET = 16.0
MAX_REJECTS = 5
TRACK_TIMEOUT_S = 30.0
CONFIRM_UPDATES = 3
MAX_PUBLISH_ERR_M = 5000.0
ALT_SIGMA_BARO_M = 60.0  # Barometric altitude as a height above the ellipsoid, unknown local pressure and geoid.
ALT_SIGMA_GEO_M = 20.0  # Barometric altitude corrected with the ADS-B GNSS height difference.
ALT_MAX_AGE_S = 15.0
CPR_PAIR_MAX_S = 10.0
CPR_LOCAL_MAX_S = 60.0


class Track:
    __slots__ = ("x", "p", "t", "updates", "rejects", "confirmed", "last_nrecv", "last_gdop")

    def __init__(self, ecef, cov, t):
        self.x = np.concatenate([ecef, np.zeros(3)])
        self.p = np.zeros((6, 6))
        self.p[:3, :3] = cov + np.eye(3) * 1.0
        self.p[3:, 3:] = np.eye(3) * INIT_VEL_SIGMA**2
        self.t = t
        self.updates = 0
        self.rejects = 0
        self.confirmed = False
        self.last_nrecv = None
        self.last_gdop = None

    def predict(self, t):
        dt = t - self.t
        if dt <= 0:
            return
        f = np.eye(6)
        f[0, 3] = f[1, 4] = f[2, 5] = dt
        q = ACCEL_NOISE
        q11 = q * dt**3 / 3
        q12 = q * dt**2 / 2
        q22 = q * dt
        qm = np.zeros((6, 6))
        for k in range(3):
            qm[k, k] = q11
            qm[k, k + 3] = qm[k + 3, k] = q12
            qm[k + 3, k + 3] = q22
        self.x = f @ self.x
        self.p = f @ self.p @ f.T + qm
        self.t = t

    def update_tdoa(self, rx_ecef, times, sigmas, alt=None):
        """TDOA update against the first receiver (lowest variance first). Returns True if accepted."""
        p = self.x[:3]
        d = p - rx_ecef
        r = np.sqrt(np.einsum("ij,ij->i", d, d))
        u = d / r[:, None]
        m = len(times) - 1
        z = (times[1:] - times[0]) * C
        hx = r[1:] - r[0]
        hm = np.zeros((m + (alt is not None), 6))
        hm[:m, :3] = u[1:] - u[0]
        s0 = (sigmas[0] * C) ** 2
        rm = np.full((m, m), s0)
        rm[np.diag_indices(m)] += (sigmas[1:] * C) ** 2
        nu = z - hx
        if alt is not None:
            lat, lon, h = geo.ecef_to_llh(p)
            up = geo.enu_basis(lat, lon)[2]
            hm[m, :3] = up
            nu = np.append(nu, alt[0] - h)
            rm2 = np.zeros((m + 1, m + 1))
            rm2[:m, :m] = rm
            rm2[m, m] = alt[1] ** 2
            rm = rm2
        s = hm @ self.p @ hm.T + rm
        try:
            si = np.linalg.inv(s)
        except np.linalg.LinAlgError:
            return False
        d2 = float(nu @ si @ nu)
        if self.updates >= 2 and d2 > GATE_PER_DOF * len(nu) + GATE_OFFSET:
            self.rejects += 1
            return False
        k = self.p @ hm.T @ si
        self.x = self.x + k @ nu
        ikh = np.eye(6) - k @ hm
        self.p = ikh @ self.p @ ikh.T + k @ rm @ k.T
        self.updates += 1
        self.rejects = 0
        if self.updates >= CONFIRM_UPDATES:
            self.confirmed = True
        return True

    def llh(self):
        return geo.ecef_to_llh(self.x[:3])

    def horizontal_error_m(self):
        """Estimated one sigma horizontal error (root of the summed east and north variances) [m]."""
        lat, lon, _ = self.llh()
        e = geo.enu_basis(lat, lon)
        c = e @ self.p[:3, :3] @ e.T
        return ERROR_SCALE * math.sqrt(max(c[0, 0] + c[1, 1], 0.0))

    def velocity_enu(self):
        lat, lon, _ = self.llh()
        return geo.enu_basis(lat, lon) @ self.x[3:]


class Aircraft:
    __slots__ = ("icao", "callsign", "squawk", "alt_ft", "alt_t", "geo_minus_baro_ft", "gmb_t", "gs_kt", "track_deg",
                 "vr_fpm", "vel_t", "cpr", "adsb_lat", "adsb_lon", "adsb_t", "adsb_nuc", "track", "last_seen",
                 "trusted_t", "messages", "mlat_fixes", "adsb_fixes", "init_blocked_until")

    def __init__(self, icao):
        self.icao = icao
        self.callsign = self.squawk = None
        self.alt_ft = self.alt_t = None
        self.geo_minus_baro_ft = self.gmb_t = None
        self.gs_kt = self.track_deg = self.vr_fpm = self.vel_t = None
        self.cpr = [None, None]  # Even, odd: (cpr_lat, cpr_lon, t)
        self.adsb_lat = self.adsb_lon = self.adsb_t = None
        self.adsb_nuc = None
        self.track = None
        self.last_seen = None
        self.trusted_t = None
        self.messages = 0
        self.mlat_fixes = 0
        self.adsb_fixes = 0
        self.init_blocked_until = 0.0

    def apply(self, d, t):
        """Applies decoded fields at Unix time t. Returns (lat, lon) if this message gave a new ADS-B position."""
        self.messages += 1
        self.last_seen = t
        if d.trusted:
            self.trusted_t = t
        if d.alt_ft is not None:
            self.alt_ft = d.alt_ft
            self.alt_t = t
        if d.squawk is not None:
            self.squawk = d.squawk
        if d.callsign is not None:
            self.callsign = d.callsign
        if d.gs_kt is not None or d.vr_fpm is not None:
            self.gs_kt, self.track_deg, self.vr_fpm, self.vel_t = d.gs_kt, d.track_deg, d.vr_fpm, t
        if d.geo_minus_baro_ft is not None:
            self.geo_minus_baro_ft = d.geo_minus_baro_ft
            self.gmb_t = t
        if d.cpr_lat is None or d.tc is None or not (9 <= d.tc <= 18):
            return None
        self.cpr[d.cpr_odd] = (d.cpr_lat, d.cpr_lon, t)
        pos = None
        if self.adsb_t is not None and t - self.adsb_t < CPR_LOCAL_MAX_S:
            pos = cpr.local_airborne(d.cpr_lat, d.cpr_lon, d.cpr_odd, self.adsb_lat, self.adsb_lon)
            if pos is not None and geo.distance_m(pos[0], pos[1], self.adsb_lat, self.adsb_lon) > 1000.0 + 400.0 * (
                    t - self.adsb_t):
                pos = None
                self.adsb_t = None  # Implausible jump: decode the next pair globally.
        if pos is None:
            other = self.cpr[1 - d.cpr_odd]
            if other is not None and abs(t - other[2]) < CPR_PAIR_MAX_S:
                if d.cpr_odd:
                    pos = cpr.global_airborne(other[0], other[1], d.cpr_lat, d.cpr_lon, True)
                else:
                    pos = cpr.global_airborne(d.cpr_lat, d.cpr_lon, other[0], other[1], False)
        if pos is None:
            return None
        self.adsb_lat, self.adsb_lon, self.adsb_t = pos[0], pos[1], t
        self.adsb_nuc = d.nuc
        self.adsb_fixes += 1
        return pos

    def geometric_alt(self, t, alt_ft=None):
        """(height above ellipsoid [m], sigma [m]) from barometric altitude, or None."""
        if alt_ft is None:
            if self.alt_ft is None or t - self.alt_t > ALT_MAX_AGE_S:
                return None
            alt_ft = self.alt_ft
            age = max(t - self.alt_t, 0.0)
        else:
            age = 0.0
        h = alt_ft * geo.FT
        sigma = ALT_SIGMA_BARO_M
        if self.geo_minus_baro_ft is not None and t - self.gmb_t < 120.0:
            h += self.geo_minus_baro_ft * geo.FT
            sigma = ALT_SIGMA_GEO_M
        if age:
            vr = abs(self.vr_fpm or 0.0) * geo.FT / 60.0
            sigma = math.hypot(sigma, age * max(vr, 5.0))
        return h, sigma


AMBIGUITY_STARTS_KM = (30.0, 80.0, 150.0, 250.0)
AMBIGUITY_SEPARATION_M = 2000.0


def _unique_exact_fix(rx_ecef, times, sigmas, alt, fix):
    """An exactly determined fix (three receivers and altitude) often has a mirror solution. Solves again from
    starting points around the receivers and returns False if another solution fits as well."""
    lat, lon, _ = geo.ecef_to_llh(rx_ecef.mean(axis=0))
    for r_km in AMBIGUITY_STARTS_KM:
        for k in range(12):
            brg = math.radians(30.0 * k)
            dlat = r_km * 1e3 * math.cos(brg) / 111_320.0
            dlon = r_km * 1e3 * math.sin(brg) / (111_320.0 * math.cos(math.radians(lat)))
            g = geo.llh_to_ecef(lat + dlat, lon + dlon, alt[0] if alt is not None else 9000.0)
            other = solver.solve(rx_ecef, times, sigmas, alt, g)
            if other is None or other.chi2 > 1.0:
                continue
            if np.linalg.norm(other.ecef - fix.ecef) > AMBIGUITY_SEPARATION_M:
                return False
    return True


def init_track(rx_ecef, times, sigmas, alt, t_unix, guess=None):
    """Least squares fix to start a track. Returns (Track, Fix), (None, None) or (None, "ambiguous")."""
    fix = solver.solve(rx_ecef, times, sigmas, alt, guess)
    if fix is None:
        return None, None
    if fix.dof > 0 and fix.chi2 / fix.dof > 25.0:
        return None, None
    if fix.horizontal_error_m() > 20e3:
        return None, None
    if fix.dof == 0 and guess is None and not _unique_exact_fix(rx_ecef, times, sigmas, alt, fix):
        return None, "ambiguous"
    return Track(fix.ecef, fix.cov, t_unix), fix
