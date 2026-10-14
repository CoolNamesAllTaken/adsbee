"""The MLAT pipeline: receptions in, aircraft fixes out. Independent of networking so it can be driven directly."""

import math
import random
import time
from collections import deque

import numpy as np

from . import geo, modes, tracker
from .clocksync import ClockSync
from .receiver import Receiver

C = geo.C
GROUP_WINDOW_S = 0.3  # Wait this long (wall time) for copies of a message from other receivers.
SAME_EMISSION_S = 2e-3  # Copies of identical bytes farther apart than this (Unix time map) are separate emissions.
AIRCRAFT_TIMEOUT_S = 300.0
ADSB_SUPPRESSES_MLAT_S = 5.0
SYNC_POS_SIGMA_M = {None: 50.0}  # Reference aircraft position error by NUC, default.
UNTRUSTED_MIN_RECEIVERS = 3
MAX_RECEIVERS = 12  # Per MLAT update.
MAX_SYNC_RECEIVERS = 12  # Per reference message; a random subset of larger groups.
# Share of messages of aircraft with a live ADS-B position that update their MLAT track (keeps it ready for gaps).
ADSB_MLAT_FRACTION = 0.1


def _sync_pos_sigma(nuc):
    if nuc is None:
        return 50.0
    return {9: 5.0, 8: 10.0, 7: 20.0, 6: 50.0, 5: 100.0}.get(nuc, 500.0)


class Engine:
    """Groups receptions of the same message, synchronizes clocks, solves and tracks.

    Call add_frames() with each read from a receiver and tick() regularly (every 10 to 50 ms). Fixes go to
    on_fix(dict) in the shape of an entry of the mlat:aircraft channel.
    """

    def __init__(self, group_window_s=GROUP_WINDOW_S, publish_mlat_for_adsb=False, on_fix=None, on_mlat=None,
                 clock=time.time, max_receivers=MAX_RECEIVERS, adsb_mlat_fraction=ADSB_MLAT_FRACTION):
        self.receivers = {}
        self.by_index = []
        self.sync = ClockSync()
        self.aircraft = {}
        self.groups = {}
        self.group_window_s = group_window_s
        self.publish_mlat_for_adsb = publish_mlat_for_adsb
        self.max_receivers = max_receivers
        self.on_fix = on_fix
        self.on_mlat = on_mlat  # Optional on_mlat(aircraft, track, extra) for every accepted MLAT update.
        self.clock = clock
        self.stats = dict(frames=0, unstamped=0, groups=0, bad_parity=0, sync_events=0, solves=0, solve_ok=0,
                          tdoa_updates=0, tdoa_rejects=0, mlat_fixes=0, adsb_fixes=0, no_sync=0)
        self.latencies = deque(maxlen=5000)
        self.residuals = deque(maxlen=5000)
        self._last_housekeeping = None
        self._dist_key = None
        self._rng = random.Random(1)
        self.adsb_mlat_fraction = adsb_mlat_fraction

    # Receivers.

    def receiver(self, rid, clock_hz=None):
        rx = self.receivers.get(rid)
        if rx is None:
            rx = Receiver(rid, len(self.by_index), clock_hz or 12_000_000)
            rx.on_reset = self._on_reset
            self.receivers[rid] = rx
            self.by_index.append(rx)
        elif clock_hz is not None:
            rx.set_clock_hz(clock_hz)
        return rx

    def _on_reset(self, rx):
        self.sync.reset_receiver(rx.index)
        # Drop pending receptions stamped with the old clock.
        for g in self.groups.values():
            g[1][:] = [r for r in g[1] if r[0] is not rx]

    def apply_info(self, info):
        rx = self.receiver(info["id"], info.get("clk"))
        rx.apply_info(info)
        return rx

    # Ingest.

    def add_frames(self, rx, frames, wall=None):
        """frames: (timestamp, signal, message) tuples from one read, in order."""
        if wall is None:
            wall = self.clock()
        n = len(frames)
        if not n:
            return
        rx.msg_count += n
        self.stats["frames"] += n
        groups = self.groups
        for attempt in (0, 1):
            stamped = []
            to_seconds = rx.to_seconds
            last_t = None
            for ts, _sig, msg in frames:
                if ts:
                    last_t = to_seconds(ts)
                    stamped.append((msg, last_t))
                else:
                    stamped.append((msg, None))
            if last_t is None or rx.observe_wall(last_t, wall):
                break
            # The clock restarted: unwrap this read again from the new base.
        for msg, t in stamped:
            g = groups.get(msg)
            if g is None:
                groups[msg] = [wall, [(rx, t)]]
            else:
                g[1].append((rx, t))

    def tick(self, now=None):
        if now is None:
            now = self.clock()
        cutoff = now - self.group_window_s
        groups = self.groups
        while groups:
            msg = next(iter(groups))
            g = groups[msg]
            if g[0] > cutoff:
                break
            del groups[msg]
            self._process_group(msg, g[1], now)
        if self._last_housekeeping is None or now - self._last_housekeeping >= 1.0:
            self._housekeeping(now)
            self._last_housekeeping = now

    def _housekeeping(self, now):
        for rx in self.by_index:
            rx.update_rate(now)
        self.sync.expire(now)
        for idx, sigma in self.sync.estimate_jitter().items():
            rx = self.by_index[idx]
            rx.jitter_s = sigma
            rx.jitter_estimated = True
        excluded = set()
        for rx in self.by_index:
            if rx.jitter_estimated and rx.jitter_s > 1e-6:
                excluded.add(rx.index)
        self.sync.excluded = excluded
        for rx in self.by_index:
            rx.sync_degree = self.sync.degree(rx.index)
        dead = [k for k, a in self.aircraft.items() if now - (a.last_seen or 0) > AIRCRAFT_TIMEOUT_S]
        for k in dead:
            del self.aircraft[k]

    # Processing.

    def _process_group(self, msg, receptions, now):
        self.stats["groups"] += 1
        d = modes.decode(msg)
        if d is None:
            self.stats["bad_parity"] += 1
            return
        ac = self.aircraft.get(d.icao)
        if not d.trusted and (ac is None or ac.trusted_t is None):
            if len({r[0] for r in receptions}) < UNTRUSTED_MIN_RECEIVERS:
                return  # Address/parity formats only count for aircraft known from a self-checking format.
        if ac is None:
            ac = self.aircraft[d.icao] = tracker.Aircraft(d.icao)

        stamped = [r for r in receptions if r[1] is not None and r[0].has_position]
        self.stats["unstamped"] += len(receptions) - len(stamped)
        clusters = self._split_emissions(stamped) if len(stamped) > 1 else [stamped]
        for k, cluster in enumerate(clusters):
            t_unix = None
            if cluster:
                rx0, t0 = cluster[0]
                t_unix = rx0.to_unix(t0)
            if t_unix is None:
                t_unix = now - self.group_window_s
            if k == 0:
                pos = ac.apply(d, t_unix)
                if pos is not None:
                    self.stats["adsb_fixes"] += 1
                    self._emit_adsb(ac, t_unix)
                    if len(cluster) >= 2:
                        self._sync_event(ac, d, pos, cluster, t_unix, now)
            if len(cluster) >= 2:
                if (self.adsb_mlat_fraction < 1.0 and ac.adsb_t is not None
                        and t_unix - ac.adsb_t < ADSB_SUPPRESSES_MLAT_S
                        and self._rng.random() >= self.adsb_mlat_fraction):
                    continue
                self._mlat(ac, d, cluster, t_unix, now)

    def _split_emissions(self, stamped):
        """Separates repeated identical messages; keeps one reception per receiver per emission."""
        seen = set()
        dup = False
        for rx, _ in stamped:
            if rx in seen:
                dup = True
                break
            seen.add(rx)
        if not dup:
            return [stamped]
        tagged = sorted(((rx.to_unix(t) or 0.0, rx, t) for rx, t in stamped), key=lambda x: x[0])
        clusters = []
        cur = []
        cur_rx = set()
        last = None
        for tu, rx, t in tagged:
            if last is not None and (tu - last > SAME_EMISSION_S or rx in cur_rx):
                clusters.append(cur)
                cur, cur_rx = [], set()
            cur.append((rx, t))
            cur_rx.add(rx)
            last = tu
        clusters.append(cur)
        return clusters

    def _sync_event(self, ac, d, pos, cluster, t_unix, now):
        alt = ac.geometric_alt(t_unix, d.alt_ft)
        if alt is None:
            return
        p = geo.llh_to_ecef(pos[0], pos[1], alt[0])
        if len(cluster) > MAX_SYNC_RECEIVERS:
            cluster = self._rng.sample(cluster, MAX_SYNC_RECEIVERS)
        idxs = []
        emits = []
        var_each = []
        units = []
        excess = geo.tropo_excess_m(np.array([rx.ecef for rx, _ in cluster]),
                                    np.array([rx.radius_surface for rx, _ in cluster]), p)
        for k, (rx, t) in enumerate(cluster):
            dv = p - rx.ecef
            r = math.sqrt(dv[0] * dv[0] + dv[1] * dv[1] + dv[2] * dv[2])
            idxs.append(rx.index)
            emits.append(t - (r + excess[k]) / C)
            var_each.append(rx.jitter_s**2 + (rx.hacc / C) ** 2)
            units.append(dv / r)
        sigma_p = math.hypot(_sync_pos_sigma(d.nuc), alt[1] * 0.3)

        def pos_var(a, b):
            du = units[a] - units[b]
            return float(du @ du) * (sigma_p / C) ** 2

        self.sync.add_event(idxs, emits, var_each, now, pos_var)
        self.stats["sync_events"] += 1

    def _rx_distances(self):
        """Distances between receivers [m], cached until a receiver is added or moves."""
        key = (len(self.by_index), Receiver.position_changes)
        if self._dist_key != key:
            pts = np.array([rx.ecef if rx.has_position else np.full(3, np.nan) for rx in self.by_index])
            d = np.linalg.norm(pts[:, None, :] - pts[None, :, :], axis=2)
            self._dist = np.nan_to_num(d, nan=0.0)
            self._dist_key = key
        return self._dist

    def _to_common_clock(self, cluster, now):
        """Brings a cluster onto one receiver's clock. Returns (rx list, times, sigmas) sorted by sigma, or None.

        Large clusters are cut to max_receivers, chosen for the widest spread (farthest point sampling).
        """
        sync = self.sync
        excluded = sync.excluded
        cl = [c for c in cluster if c[0].sync_degree > 0 and c[0].index not in excluded]
        if len(cl) < 2:
            return None
        base = max(cl, key=lambda c: c[0].sync_degree)[0]
        if len(cl) > self.max_receivers:
            dist = self._rx_distances()[np.ix_([c[0].index for c in cl], [c[0].index for c in cl])]
            k = next(k for k, c in enumerate(cl) if c[0] is base)
            chosen = [k]
            dmin = dist[k].copy()
            for _ in range(self.max_receivers - 1):
                k = int(np.argmax(dmin))
                chosen.append(k)
                np.minimum(dmin, dist[k], out=dmin)
            cl = [cl[k] for k in chosen]
        out_rx = []
        times = []
        sig = []
        for rx, t in cl:
            r = sync.to_base(base.index, rx.index, t, now)
            if r is None:
                continue
            tb, var = r
            out_rx.append(rx)
            times.append(tb)
            sig.append(math.sqrt(var + rx.jitter_s**2 + (rx.hacc / C) ** 2))
        if len(out_rx) < 2:
            return None
        order = np.argsort(sig)
        return [out_rx[k] for k in order], np.asarray(times)[order], np.asarray(sig)[order]

    def _mlat(self, ac, d, cluster, t_unix, now):
        conv = self._to_common_clock(cluster, now)
        if conv is None:
            self.stats["no_sync"] += 1
            return
        rxs, times, sigmas = conv
        rx_ecef = np.array([rx.ecef for rx in rxs])
        rx_surface = np.array([rx.radius_surface for rx in rxs])
        alt = ac.geometric_alt(t_unix, d.alt_ft)
        tr = ac.track
        if tr is not None and (t_unix - tr.t > tracker.TRACK_TIMEOUT_S or tr.rejects >= tracker.MAX_REJECTS):
            tr = ac.track = None
        if tr is None:
            n_meas = len(rxs) + (alt is not None)
            if n_meas < 4 or len(rxs) < 3:
                return
            self.stats["solves"] += 1
            tr, fix = tracker.init_track(rx_ecef, times, sigmas, alt, t_unix)
            if tr is None:
                return
            # Again with the atmosphere's delay for the first solution.
            times_c = times - geo.tropo_excess_m(rx_ecef, rx_surface, fix.ecef) / C
            tr2, fix2 = tracker.init_track(rx_ecef, times_c, sigmas, alt, t_unix, fix.ecef)
            if tr2 is not None:
                tr, fix = tr2, fix2
            self.stats["solve_ok"] += 1
            ac.track = tr
            tr.updates = 1
            tr.last_nrecv = len(rxs)
            tr.last_gdop = fix.gdop
            return
        tr.predict(t_unix)
        times = times - geo.tropo_excess_m(rx_ecef, rx_surface, tr.x[:3]) / C
        if not tr.update_tdoa(rx_ecef, times, sigmas, alt):
            self.stats["tdoa_rejects"] += 1
            return
        self.stats["tdoa_updates"] += 1
        tr.last_nrecv = len(rxs)
        tr.last_gdop = tracker.solver.gdop(rx_ecef, tr.x[:3]) if len(rxs) >= 4 else None
        # Post-fit residuals, for statistics.
        r = np.linalg.norm(rx_ecef - tr.x[:3], axis=1) / C
        res = (times - times[0]) - (r - r[0])
        if len(res) > 1:
            self.residuals.append(float(np.sqrt(np.mean(res[1:] ** 2))))
        if not tr.confirmed:
            return
        self.latencies.append(now - t_unix)
        if self.on_mlat is not None:
            self.on_mlat(ac, tr, dict(t=t_unix, nrecv=len(rxs), df=d.df))
        if not self.publish_mlat_for_adsb and ac.adsb_t is not None and t_unix - ac.adsb_t < ADSB_SUPPRESSES_MLAT_S:
            return
        err = tr.horizontal_error_m()
        if err > tracker.MAX_PUBLISH_ERR_M:
            return
        self.stats["mlat_fixes"] += 1
        ac.mlat_fixes += 1
        self._emit_mlat(ac, tr, t_unix, err)

    # Output.

    def _common(self, ac):
        return {"icao": f"{ac.icao:06x}", "callsign": ac.callsign, "squawk": ac.squawk}

    def _emit_adsb(self, ac, t):
        if self.on_fix is None:
            return
        e = self._common(ac)
        e.update(src="adsb", lat=round(ac.adsb_lat, 6), lon=round(ac.adsb_lon, 6), alt_ft=ac.alt_ft,
                 gs_kt=_r(ac.gs_kt, 1), track_deg=_r(ac.track_deg, 1), vr_fpm=_r(ac.vr_fpm, 0), t=round(t, 3),
                 err_m=None, nrecv=None, gdop=None)
        self.on_fix(e)

    def _emit_mlat(self, ac, tr, t, err):
        if self.on_fix is None:
            return
        lat, lon, h = tr.llh()
        ve, vn, vu = tr.velocity_enu()
        e = self._common(ac)
        alt_ft = ac.alt_ft if ac.alt_ft is not None and t - (ac.alt_t or 0) < 30 else round(float(h) / geo.FT)
        e.update(src="mlat", lat=round(float(lat), 6), lon=round(float(lon), 6), alt_ft=alt_ft,
                 gs_kt=round(math.hypot(ve, vn) / geo.KT, 1), track_deg=round(math.degrees(math.atan2(ve, vn)) % 360, 1),
                 vr_fpm=round(vu / geo.FT * 60), t=round(t, 3), err_m=round(err, 1), nrecv=tr.last_nrecv,
                 gdop=_r(tr.last_gdop, 2))
        self.on_fix(e)

    def receivers_status(self):
        out = []
        for rx in self.by_index:
            if not rx.has_position:
                continue
            peers = []
            for v in self.sync.adj.get(rx.index, ()):
                p = self.sync.pairs.get((rx.index, v) if rx.index < v else (v, rx.index))
                if p is not None and p.valid:
                    peers.append(self.by_index[v].id)
            out.append({"id": rx.id, "name": rx.name, "lat": round(rx.lat, 7), "lon": round(rx.lon, 7),
                        "alt_m": round(rx.alt, 2), "pos_src": rx.pos_src, "clock_hz": rx.clock_hz,
                        "msg_rate": round(rx.msg_rate, 1),
                        "sync_ok": bool(peers) and rx.index not in self.sync.excluded,
                        "clock_err_ns": round(rx.jitter_s * 1e9, 1) if rx.jitter_estimated else None,
                        "peers": sorted(peers)})
        return out


def _r(v, nd):
    return None if v is None else round(v, nd)
