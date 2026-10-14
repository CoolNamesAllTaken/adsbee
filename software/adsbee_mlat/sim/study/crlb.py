"""Cramer-Rao lower bound of time-of-arrival multilateration, with an optional altitude measurement."""

import numpy as np

from adsbee_mlat_sim.geodesy import C_M_PER_S, enu_basis, enu_to_ecef, lla_to_ecef


def horizontal_sigma(targets_ecef, receivers_ecef, toa_sigma_s, alt_sigma_m=None, up=None, return_cov=False):
    """RMS horizontal error (meters, 1 sigma per axis combined) of an efficient estimator, per target.

    Unknowns: target position and emission time. Measurements: arrival time at each receiver with independent
    Gaussian errors toa_sigma_s (scalar or per receiver), plus the target height with alt_sigma_m if given.
    targets_ecef: (n, 3). up: (n, 3) local up unit vectors (default: geocentric direction).
    """
    t = np.atleast_2d(targets_ecef)
    r = np.atleast_2d(receivers_ecef)
    sig = np.broadcast_to(np.asarray(toa_sigma_s, float), (len(r),))
    if up is None:
        up = t / np.linalg.norm(t, axis=1, keepdims=True)
    d = t[:, None, :] - r[None, :, :]
    u = d / np.linalg.norm(d, axis=2, keepdims=True)  # (n, m, 3)
    # Work in meters: range measurements c * toa, unknown emission time as c * t0.
    w = 1 / (C_M_PER_S * sig) ** 2
    # Fisher information of the position after eliminating the emission time (Schur complement).
    ux = u
    a = np.einsum("nmi,m,nmj->nij", ux, w, ux)
    b = np.einsum("nmi,m->ni", ux, w)
    fim = a - np.einsum("ni,nj->nij", b, b) / w.sum()
    if alt_sigma_m is not None:
        fim = fim + np.einsum("ni,nj->nij", up, up) / alt_sigma_m**2
    # Horizontal plane basis per target.
    east = np.cross(np.array([0.0, 0.0, 1.0]), up)
    east /= np.linalg.norm(east, axis=1, keepdims=True)
    north = np.cross(up, east)
    basis = np.stack([east, north, up], axis=1)  # (n, 3, 3) rows e, n, u
    fim_enu = np.einsum("nai,nij,nbj->nab", basis, fim, basis)
    out = np.full(len(t), np.nan)
    covs = np.full((len(t), 2, 2), np.nan)
    for k in range(len(t)):
        try:
            cov = np.linalg.inv(fim_enu[k])
        except np.linalg.LinAlgError:
            continue
        if np.all(np.isfinite(cov)) and cov[0, 0] >= 0 and cov[1, 1] >= 0:
            out[k] = np.sqrt(cov[0, 0] + cov[1, 1])
            covs[k] = cov[:2, :2]
    return (out, covs) if return_cov else out


def median_radius(cov2, n=4000, seed=0):
    """Median horizontal error of a zero-mean Gaussian with 2x2 covariance (elongated ellipses have a smaller
    median relative to the RMS)."""
    w, v = np.linalg.eigh(cov2)
    z = np.random.default_rng(seed).normal(size=(n, 2)) * np.sqrt(np.maximum(w, 0))
    return float(np.median(np.linalg.norm(z, axis=1)))


def grid_targets(center_lat, center_lon, half_width_m, n, alt_m):
    """Square grid of targets around a point: returns (east, north) axes and ECEF (n*n, 3), up vectors."""
    ax = np.linspace(-half_width_m, half_width_m, n)
    e, nn = np.meshgrid(ax, ax)
    enu = np.stack([e.ravel(), nn.ravel(), np.zeros(e.size)], axis=1)
    # Put targets on the curved Earth: offset straight-line ENU down by the drop d^2/2R, then up by alt.
    drop = (e.ravel() ** 2 + nn.ravel() ** 2) / (2 * 6_371_000.0)
    enu[:, 2] = alt_m - drop
    ecef = enu_to_ecef(enu, center_lat, center_lon)
    up = ecef / np.linalg.norm(ecef, axis=1, keepdims=True)
    return ax, ecef, up


def ring_targets(center_lat, center_lon, range_m, alt_m, n_az=72):
    from adsbee_mlat_sim.geodesy import destination

    az = np.arange(n_az) * 360.0 / n_az
    lat, lon = destination(center_lat, center_lon, az, range_m)
    ecef = lla_to_ecef(lat, lon, np.full(n_az, alt_m))
    up = np.stack([enu_basis(a, b)[2] for a, b in zip(lat, lon)])
    return az, ecef, up
