"""Optional multi-process engine: the front process parses and groups, worker processes each own a share of the
aircraft (by address) with their own clock synchronization and tracks."""

import multiprocessing as mp
import queue
import threading
import time
from collections import deque

from . import modes
from .engine import Engine
from .receiver import Receiver

STATUS_INTERVAL_S = 1.0


def _receiver_table(by_index):
    return [(rx.index, rx.id, rx.name, rx.lat, rx.lon, rx.alt, rx.pos_src, rx.hacc, rx.vacc, rx.clock_hz)
            for rx in by_index if rx.has_position]


def _worker(conn, engine_kwargs):
    fixes = []
    eng = Engine(on_fix=fixes.append, **engine_kwargs)
    mirrors = {}
    last_status = 0.0
    while True:
        msg = conn.recv()
        kind = msg[0]
        if kind == "groups":
            _, now, offsets, groups = msg
            for idx, off in offsets:
                rx = mirrors.get(idx)
                if rx is not None:
                    rx._unix_offset = off
            for m, recs in groups:
                eng._process_group(m, [(mirrors[i], t) for i, t in recs if i in mirrors], now)
            eng.tick(now)
            if fixes:
                conn.send(("fixes", fixes[:]))
                fixes.clear()
            if now - last_status >= STATUS_INTERVAL_S:
                last_status = now
                status = {r["id"]: (r["sync_ok"], r["clock_err_ns"], r["peers"]) for r in eng.receivers_status()}
                conn.send(("status", dict(eng.stats), status, list(eng.latencies), list(eng.residuals),
                           eng.aircraft_count(), eng.valid_pair_count()))
                eng.latencies.clear()
                eng.residuals.clear()
        elif kind == "rx":
            for idx, rid, name, lat, lon, alt, src, hacc, vacc, hz in msg[1]:
                while len(eng.by_index) <= idx:
                    eng.receiver(f"__placeholder{len(eng.by_index)}")
                rx = eng.by_index[idx]
                if rx.id != rid:
                    del eng.receivers[rx.id]
                    rx.id = rid
                    eng.receivers[rid] = rx
                rx.name = name
                rx.clock_hz = hz
                if (rx.lat, rx.lon, rx.alt, rx.pos_src) != (lat, lon, alt, src):
                    rx.set_position(lat, lon, alt, src, hacc, vacc)
                mirrors[idx] = rx
        elif kind == "reset":
            eng.sync.reset_receiver(msg[1])
        elif kind == "stop":
            return


class ShardedEngine:
    """Same interface as Engine (as the server uses it), spread over worker processes."""

    def __init__(self, workers, group_window_s=0.3, publish_mlat_for_adsb=False, on_fix=None, clock=time.time,
                 **kw):
        self.front = Engine(group_window_s=group_window_s, clock=clock)
        self.front.dispatch = self._dispatch
        self.on_fix = on_fix
        self.clock = clock
        kwargs = dict(group_window_s=group_window_s, publish_mlat_for_adsb=publish_mlat_for_adsb, **kw)
        ctx = mp.get_context("spawn")
        self.conns = []
        self.procs = []
        for _ in range(workers):
            a, b = ctx.Pipe()
            p = ctx.Process(target=_worker, args=(b, kwargs), daemon=True)
            p.start()
            self.conns.append(a)
            self.procs.append(p)
        self._rx_version = None
        self._worker_stats = [dict() for _ in range(workers)]
        self._worker_status = [dict() for _ in range(workers)]
        self._worker_counts = [(0, 0)] * workers
        self.latencies = deque(maxlen=5000)
        self.residuals = deque(maxlen=5000)
        # Results are drained by threads so a worker never blocks on a full pipe while the front sends to it.
        self._inbox = queue.SimpleQueue()
        self._readers = [threading.Thread(target=self._reader, args=(k, c), daemon=True)
                         for k, c in enumerate(self.conns)]
        for t in self._readers:
            t.start()

    def _reader(self, k, conn):
        while True:
            try:
                self._inbox.put((k, conn.recv()))
            except (EOFError, OSError):
                return

    # Engine interface.

    @property
    def receivers(self):
        return self.front.receivers

    @property
    def by_index(self):
        return self.front.by_index

    def receiver(self, rid, clock_hz=None):
        rx = self.front.receiver(rid, clock_hz)
        rx.on_reset = self._on_reset
        return rx

    def apply_info(self, info):
        rx = self.receiver(info["id"], info.get("clk"))
        rx.apply_info(info)
        return rx

    def add_frames(self, rx, frames, wall=None):
        rx.on_reset = self._on_reset
        self.front.add_frames(rx, frames, wall)

    def tick(self, now=None):
        if now is None:
            now = self.clock()
        self._sync_receivers()
        self.front.tick(now)
        self._poll()

    @property
    def stats(self):
        out = dict(self.front.stats)
        for k in out:
            if k != "frames":
                out[k] = sum(ws.get(k, 0) for ws in self._worker_stats)
        out["groups"] = self.front.stats["groups"]
        return out

    def aircraft_count(self):
        return sum(c[0] for c in self._worker_counts)

    def valid_pair_count(self):
        return max((c[1] for c in self._worker_counts), default=0)

    def receivers_status(self):
        out = []
        for r in self.front.receivers_status():
            ok, errs, peers = False, [], set()
            for st in self._worker_status:
                s = st.get(r["id"])
                if s is None:
                    continue
                ok |= s[0]
                if s[1] is not None:
                    errs.append(s[1])
                peers.update(s[2])
            r["sync_ok"] = ok
            r["clock_err_ns"] = sorted(errs)[len(errs) // 2] if errs else None
            r["peers"] = sorted(peers)
            out.append(r)
        return out

    def close(self):
        for c in self.conns:
            try:
                c.send(("stop",))
            except (BrokenPipeError, OSError):
                pass
        for p in self.procs:
            p.join(timeout=30)
        for t in self._readers:
            t.join(timeout=2)

    # Internals.

    def _on_reset(self, rx):
        self.front._on_reset(rx)
        for c in self.conns:
            c.send(("reset", rx.index))

    def _sync_receivers(self):
        v = (len(self.front.by_index), Receiver.position_changes)
        if v != self._rx_version:
            self._rx_version = v
            table = _receiver_table(self.front.by_index)
            for c in self.conns:
                c.send(("rx", table))

    def _dispatch(self, groups, now):
        self.front.stats["groups"] += len(groups)
        n = len(self.conns)
        shards = [[] for _ in range(n)]
        for msg, recs in groups:
            d = modes.decode(msg)
            if d is None:
                continue
            shards[d.icao % n].append((msg, [(rx.index, t) for rx, t in recs]))
        offsets = [(rx.index, rx._unix_offset) for rx in self.front.by_index if rx._unix_offset is not None]
        for c, sh in zip(self.conns, shards):
            c.send(("groups", now, offsets, sh))

    def _poll(self):
        while True:
            try:
                k, msg = self._inbox.get_nowait()
            except queue.Empty:
                return
            if True:
                if msg[0] == "fixes":
                    if self.on_fix is not None:
                        for e in msg[1]:
                            self.on_fix(e)
                elif msg[0] == "status":
                    _, stats, status, lat, res, n_ac, n_pairs = msg
                    self._worker_stats[k] = stats
                    self._worker_status[k] = status
                    self._worker_counts[k] = (n_ac, n_pairs)
                    self.latencies.extend(lat)
                    self.residuals.extend(res)
