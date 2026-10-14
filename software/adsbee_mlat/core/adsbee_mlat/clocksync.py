"""Pairwise clock synchronization from reference aircraft with known positions.

For a message from an aircraft at a known position, each receiver's emission time estimate is its receive time minus
the propagation delay. For a receiver pair (i, j) the difference of those estimates follows the relative clock offset,
which a two state Kalman filter tracks per pair: offset a at a reference time and rate difference b. Receivers without
a direct pair are connected through the sync graph (shortest path by variance).
"""

import heapq
import math

import numpy as np

# Clock process noise: white frequency noise [s^2/s] and frequency random walk [1/s].
Q_PHASE = 1e-19
Q_RATE = 4e-18
INITIAL_RATE_VAR = (100e-6) ** 2  # Unknown crystals: +-100 ppm between two receivers.
GATE_SIGMA = 5.0
GATE_FLOOR_S = 200e-9  # Never reject innovations below this.
MAX_OUTLIERS_IN_ROW = 6
STALE_S = 60.0  # A pair not updated for this long (receiver time) is dropped.
VALID_MIN_UPDATES = 4
VALID_MAX_STD_S = 1e-6
MIN_UPDATE_INTERVAL_S = 0.1  # Per pair, to bound the work for large groups.
RESID_EWMA = 0.05


class PairSync:
    """Relation between receivers i (lower index) and j: e_j - e_i = a + b * (e_i - t_ref)."""

    __slots__ = ("i", "j", "a", "b", "p00", "p01", "p11", "t_ref", "n", "outliers", "resid_var", "last_wall",
                 "total_outliers")

    def __init__(self, i, j):
        self.i = i
        self.j = j
        self.n = 0
        self.outliers = 0
        self.total_outliers = 0
        self.resid_var = None
        self.last_wall = None
        self.t_ref = None

    def _init(self, ei, z, r):
        self.a = z
        self.b = 0.0
        self.p00 = r
        self.p01 = 0.0
        self.p11 = INITIAL_RATE_VAR
        self.t_ref = ei
        self.n = 1
        self.outliers = 0

    def predict(self, ei):
        """Predicted (offset, variance) of e_j - e_i at receiver i time ei."""
        dt = ei - self.t_ref
        a = self.a + self.b * dt
        adt = abs(dt)
        var = self.p00 + 2 * dt * self.p01 + dt * dt * self.p11 + Q_PHASE * adt + Q_RATE * adt**3 / 3
        return a, var

    def update(self, ei, ej, r, wall=None) -> bool:
        """Adds one measurement. Returns False if rejected as an outlier."""
        z = ej - ei
        if self.n == 0 or (self.t_ref is not None and abs(ei - self.t_ref) > STALE_S):
            self._init(ei, z, r)
            self.last_wall = wall
            return True
        dt = ei - self.t_ref
        adt = abs(dt)
        # Predict.
        a = self.a + self.b * dt
        p00 = self.p00 + 2 * dt * self.p01 + dt * dt * self.p11 + Q_PHASE * adt + Q_RATE * adt**3 / 3
        p01 = self.p01 + dt * self.p11 + Q_RATE * dt * adt / 2
        p11 = self.p11 + Q_RATE * adt
        nu = z - a
        s = p00 + r
        if self.n >= 3 and nu * nu > GATE_SIGMA * GATE_SIGMA * s and abs(nu) > GATE_FLOOR_S:
            self.outliers += 1
            self.total_outliers += 1
            if self.outliers >= MAX_OUTLIERS_IN_ROW:
                self._init(ei, z, r)  # Persistent disagreement: a clock step. Start over.
                self.last_wall = wall
            return False
        k0 = p00 / s
        k1 = p01 / s
        self.a = a + k0 * nu
        self.b = self.b + k1 * nu
        self.p00 = (1 - k0) * p00
        self.p01 = (1 - k0) * p01
        self.p11 = p11 - k1 * p01
        self.t_ref = ei
        self.n += 1
        self.outliers = 0
        self.last_wall = wall
        if self.n > 3:
            e2 = nu * nu
            self.resid_var = e2 if self.resid_var is None else self.resid_var + RESID_EWMA * (e2 - self.resid_var)
        return True

    @property
    def valid(self):
        return self.n >= VALID_MIN_UPDATES and self.p00 < VALID_MAX_STD_S**2


class ClockSync:
    """All receiver pairs plus the graph used to bring timestamps onto one receiver's clock."""

    def __init__(self):
        self.pairs = {}  # (i, j) with i < j -> PairSync
        self.adj = {}  # receiver index -> set of peer indexes with a pair
        self._paths = {}
        self._paths_wall = None
        self.updates = 0
        self.rejects = 0
        self.excluded = set()  # Receivers whose clocks are too noisy to use.

    def reset_receiver(self, idx):
        for peer in list(self.adj.get(idx, ())):
            key = (idx, peer) if idx < peer else (peer, idx)
            self.pairs.pop(key, None)
            self.adj.get(peer, set()).discard(idx)
        self.adj.pop(idx, None)
        self._paths.clear()

    def pair(self, i, j):
        key = (i, j) if i < j else (j, i)
        p = self.pairs.get(key)
        if p is None:
            p = self.pairs[key] = PairSync(*key)
            self.adj.setdefault(key[0], set()).add(key[1])
            self.adj.setdefault(key[1], set()).add(key[0])
        return p

    def add_event(self, idxs, emit_times, var_each, wall, pos_var_fn=None):
        """One reference message: receiver indexes, emission time estimates (each on its own clock) and their noise.

        pos_var_fn(a, b) optionally returns the extra variance of e_b - e_a from the reference position error.
        """
        n = len(idxs)
        for x in range(n):
            ix = idxs[x]
            for y in range(x + 1, n):
                iy = idxs[y]
                if ix < iy:
                    i, j, ei, ej, a, b = ix, iy, emit_times[x], emit_times[y], x, y
                else:
                    i, j, ei, ej, a, b = iy, ix, emit_times[y], emit_times[x], y, x
                p = self.pairs.get((i, j))
                if p is None:
                    p = self.pair(i, j)
                elif p.valid and p.last_wall is not None and wall - p.last_wall < MIN_UPDATE_INTERVAL_S:
                    continue
                r = var_each[a] + var_each[b]
                if pos_var_fn is not None:
                    r += pos_var_fn(a, b)
                if p.update(ei, ej, r, wall):
                    self.updates += 1
                else:
                    self.rejects += 1

    def expire(self, wall, max_age=STALE_S):
        dead = [k for k, p in self.pairs.items() if p.last_wall is not None and wall - p.last_wall > max_age]
        for i, j in dead:
            del self.pairs[(i, j)]
            self.adj.get(i, set()).discard(j)
            self.adj.get(j, set()).discard(i)
        if dead:
            self._paths.clear()

    def convert(self, i, j, tj):
        """Time tj on receiver j's clock expressed on receiver i's clock, through a direct pair. (t, var) or None."""
        if i == j:
            return tj, 0.0
        if i < j:
            p = self.pairs.get((i, j))
            if p is None or not p.valid:
                return None
            # e_j = e_i + a + b (e_i - t_ref)  =>  e_i = (e_j - a + b t_ref) / (1 + b)
            ti = (tj - p.a + p.b * p.t_ref) / (1 + p.b)
            _, var = p.predict(ti)
        else:
            p = self.pairs.get((j, i))
            if p is None or not p.valid:
                return None
            off, var = p.predict(tj)
            ti = tj + off
        if p.resid_var is not None:
            var = max(var, 0.0)
        return ti, var

    def paths_from(self, base, wall):
        """Shortest variance paths from base over valid pairs: dict target -> list of hops [base, ..., target]."""
        if self._paths_wall is None or wall - self._paths_wall > 1.0:
            self._paths.clear()
            self._paths_wall = wall
        cached = self._paths.get(base)
        if cached is not None:
            return cached
        dist = {base: 0.0}
        prev = {}
        heap = [(0.0, base)]
        while heap:
            d, u = heapq.heappop(heap)
            if d > dist.get(u, math.inf):
                continue
            for v in self.adj.get(u, ()):
                if v in self.excluded:
                    continue
                p = self.pairs.get((u, v) if u < v else (v, u))
                if p is None or not p.valid:
                    continue
                w = p.p00 + (p.resid_var or 0.0) + 1e-18
                nd = d + w
                if nd < dist.get(v, math.inf):
                    dist[v] = nd
                    prev[v] = u
                    heapq.heappush(heap, (nd, v))
        paths = {base: [base]}
        for v in dist:
            if v == base:
                continue
            path = [v]
            while path[-1] != base:
                path.append(prev[path[-1]])
            path.reverse()
            if len(path) <= 4:
                paths[v] = path
        self._paths[base] = paths
        return paths

    def to_base(self, base, idx, t, wall):
        """Converts receiver idx's time t onto base's clock along the sync graph. (t, var) or None."""
        if idx == base:
            return t, 0.0
        path = self.paths_from(base, wall).get(idx)
        if path is None:
            return None
        var = 0.0
        # Walk from idx back to base.
        for k in range(len(path) - 1, 0, -1):
            r = self.convert(path[k - 1], path[k], t)
            if r is None:
                return None
            t, v = r
            var += v
        return t, var

    def degree(self, idx):
        n = 0
        for v in self.adj.get(idx, ()):
            p = self.pairs.get((idx, v) if idx < v else (v, idx))
            if p is not None and p.valid:
                n += 1
        return n

    def estimate_jitter(self, receivers):
        """Least squares split of pair residual variances into per receiver timestamp variances.

        Returns {index: sigma_s} for receivers in at least two estimated pairs, using pairs with residual history.
        """
        rows = []
        vals = []
        for (i, j), p in self.pairs.items():
            if p.resid_var is None or p.n < 10:
                continue
            rows.append((i, j))
            vals.append(max(p.resid_var - p.p00, 0.0))
        if len(rows) < 3:
            return {}
        idxs = sorted({k for r in rows for k in r})
        pos = {k: n for n, k in enumerate(idxs)}
        a = np.zeros((len(rows), len(idxs)))
        for r, (i, j) in enumerate(rows):
            a[r, pos[i]] = 1.0
            a[r, pos[j]] = 1.0
        counts = a.sum(axis=0)
        sol, *_ = np.linalg.lstsq(a, np.asarray(vals), rcond=None)
        out = {}
        for k, n in pos.items():
            if counts[n] >= 2:
                out[k] = math.sqrt(max(sol[n], (5e-9) ** 2))
        return out
