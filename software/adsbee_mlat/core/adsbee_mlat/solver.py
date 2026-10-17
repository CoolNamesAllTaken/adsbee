"""Time difference of arrival (TDOA) position solver: Levenberg-Marquardt least squares with an optional altitude
constraint, plus covariance and geometric dilution of precision (GDOP)."""

import math
from dataclasses import dataclass

import numpy as np
from scipy.optimize import least_squares

from . import geo

C = geo.C
MAX_RANGE_M = 500e3
MIN_ALT_M = -1500.0
MAX_ALT_M = 25000.0


@dataclass
class Fix:
    ecef: np.ndarray
    cov: np.ndarray  # 3x3 ECEF position covariance [m^2].
    t_emit: float  # Emission time on the base clock [s].
    chi2: float  # Sum of squared normalized residuals.
    dof: int
    gdop: float | None
    residuals_s: np.ndarray

    @property
    def llh(self):
        return geo.ecef_to_llh(self.ecef)

    def horizontal_error_m(self):
        lat, lon, _ = self.llh
        e = geo.enu_basis(lat, lon)
        enu_cov = e @ self.cov @ e.T
        return math.sqrt(max(enu_cov[0, 0] + enu_cov[1, 1], 0.0))


def _height(p):
    return geo.ecef_to_llh(p)[2]


def gdop(rx_ecef, pos):
    """GDOP of a geometry, or None with fewer than 4 receivers or a singular geometry."""
    if len(rx_ecef) < 4:
        return None
    d = pos - rx_ecef
    u = d / np.linalg.norm(d, axis=1)[:, None]
    h = np.hstack([u, np.ones((len(u), 1))])
    try:
        q = np.linalg.inv(h.T @ h)
    except np.linalg.LinAlgError:
        return None
    tr = np.trace(q)
    return float(math.sqrt(tr)) if tr > 0 else None


def solve(rx_ecef, times, sigmas, altitude=None, guess=None):
    """Solves for the emitter position.

    rx_ecef: (N, 3) receiver positions. times: (N,) arrival times on one clock [s]. sigmas: (N,) one sigma timing
    noise [s]. altitude: optional (height_m, sigma_m) above the ellipsoid. guess: optional initial ECEF.
    Returns a Fix or None if the problem is underdetermined or the solution is implausible.
    """
    rx_ecef = np.asarray(rx_ecef, dtype=float)
    times = np.asarray(times, dtype=float)
    sigmas = np.asarray(sigmas, dtype=float)
    n = len(times)
    n_meas = n + (1 if altitude is not None else 0)
    if n_meas < 4 + 0 or n < 3:
        return None
    t_ref = times.min()
    pr = (times - t_ref) * C  # Pseudoranges relative to the earliest arrival [m].
    w = 1.0 / (sigmas * C)
    if guess is None:
        c = rx_ecef.mean(axis=0)
        lat, lon, _ = geo.ecef_to_llh(c)
        guess = geo.llh_to_ecef(lat, lon, altitude[0] if altitude is not None else 9000.0)
    guess = np.asarray(guess, dtype=float)
    x0 = np.concatenate([guess, [np.linalg.norm(guess - rx_ecef[np.argmin(times)])]])

    if altitude is not None:
        alt_m, alt_sigma = altitude

    def resid(x):
        p = x[:3]
        r = np.linalg.norm(rx_ecef - p, axis=1)
        out = (pr + x[3] - r) * w
        if altitude is not None:
            out = np.append(out, (_height(p) - alt_m) / alt_sigma)
        return out

    def jac(x):
        p = x[:3]
        d = p - rx_ecef
        r = np.linalg.norm(d, axis=1)
        j = np.empty((n_meas, 4))
        j[:n, :3] = -(d / r[:, None]) * w[:, None]
        j[:n, 3] = w
        if altitude is not None:
            lat, lon, _ = geo.ecef_to_llh(p)
            j[n, :3] = geo.enu_basis(lat, lon)[2] / alt_sigma
            j[n, 3] = 0.0
        return j

    try:
        res = least_squares(resid, x0, jac=jac, method="lm", x_scale=[1e4, 1e4, 1e4, 1e4], max_nfev=100)
    except (ValueError, np.linalg.LinAlgError):
        return None
    if not res.success and res.status <= 0:
        return None
    p = res.x[:3]
    _, _, h = geo.ecef_to_llh(p)
    if not (MIN_ALT_M <= h <= MAX_ALT_M):
        return None
    if np.min(np.linalg.norm(rx_ecef - p, axis=1)) > MAX_RANGE_M:
        return None
    jm = res.jac
    try:
        cov = np.linalg.inv(jm.T @ jm)
    except np.linalg.LinAlgError:
        return None
    chi2 = float(np.sum(res.fun**2))
    t_emit = t_ref - res.x[3] / C
    resid_s = res.fun[:n] / w / C
    return Fix(p, cov[:3, :3], t_emit, chi2, n_meas - 4, gdop(rx_ecef, p), resid_s)
