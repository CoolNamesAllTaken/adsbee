"""Networked server: receiver feeds over TCP and UDP, results to Redis and an SBS (BaseStation) port."""

import asyncio
import json
import logging
import time

import numpy as np

from . import beast
from .config import Config
from .engine import Engine

log = logging.getLogger("adsbee_mlat")

TICK_S = 0.02
SNAPSHOT_TTL_S = 60.0  # Aircraft older than this leave the snapshot.
SNAPSHOT_KEY_TTL_S = 30  # The snapshot key expires if the server stops updating it.
READ_SIZE = 65536


class Publisher:
    """Collects fixes and publishes them on the Redis channels of the web interface."""

    def __init__(self, redis_url=None, redis_client=None):
        self.redis_url = redis_url
        self.redis = redis_client
        self.batch = []
        self.snapshot = {}
        self.sent = []  # Optional copy of every published message (channel, payload) for tests.
        self.keep_sent = False
        self._warned = False

    async def connect(self):
        if self.redis is None and self.redis_url:
            import redis.asyncio as aioredis

            self.redis = aioredis.from_url(self.redis_url)

    def add_fix(self, entry):
        self.batch.append(entry)
        self.snapshot[entry["icao"]] = entry

    async def _publish(self, channel, payload):
        data = json.dumps(payload, separators=(",", ":"))
        if self.keep_sent:
            self.sent.append((channel, payload))
        if self.redis is None:
            return
        try:
            await self.redis.publish(channel, data)
            self._warned = False
        except Exception as e:  # Keep running while Redis is away.
            if not self._warned:
                log.warning("redis publish failed: %s", e)
                self._warned = True

    async def flush_aircraft(self, now):
        if not self.batch:
            return
        batch, self.batch = self.batch, []
        await self._publish("mlat:aircraft", {"t": round(now, 3), "aircraft": batch})

    async def flush_status(self, now, receivers, stats):
        await self._publish("mlat:receivers", {"t": round(now, 3), "receivers": receivers})
        await self._publish("mlat:stats", dict(stats, t=round(now, 3)))
        for k in [k for k, e in self.snapshot.items() if now - e["t"] > SNAPSHOT_TTL_S]:
            del self.snapshot[k]
        snap = {"t": round(now, 3), "aircraft": list(self.snapshot.values())}
        if self.keep_sent:
            self.sent.append(("mlat:snapshot", snap))
        if self.redis is not None:
            try:
                await self.redis.set("mlat:snapshot", json.dumps(snap, separators=(",", ":")), ex=SNAPSHOT_KEY_TTL_S)
            except Exception:
                pass


class SBSOutput:
    """BaseStation port 30003 style output of MLAT fixes, for readsb, tar1090 and similar."""

    def __init__(self):
        self.writers = set()

    async def handle(self, reader, writer):
        self.writers.add(writer)
        try:
            await reader.read()
        finally:
            self.writers.discard(writer)
            writer.close()

    def send(self, e):
        if not self.writers or e["src"] != "mlat":
            return
        t = time.gmtime(e["t"])
        ms = int((e["t"] % 1) * 1000)
        d = time.strftime("%Y/%m/%d", t)
        hms = time.strftime("%H:%M:%S", t) + f".{ms:03d}"
        alt = "" if e["alt_ft"] is None else str(int(e["alt_ft"]))
        gs = "" if e["gs_kt"] is None else f"{e['gs_kt']:.0f}"
        trk = "" if e["track_deg"] is None else f"{e['track_deg']:.0f}"
        vr = "" if e["vr_fpm"] is None else f"{e['vr_fpm']:.0f}"
        cs = e["callsign"] or ""
        sq = e["squawk"] or ""
        line = (f"MSG,3,1,1,{e['icao'].upper()},1,{d},{hms},{d},{hms},{cs},{alt},{gs},{trk},{e['lat']:.6f},"
                f"{e['lon']:.6f},{vr},{sq},,,,0\r\n").encode()
        for w in list(self.writers):
            if w.transport.get_write_buffer_size() < 1 << 20:
                w.write(line)


class Server:
    def __init__(self, cfg: Config, publisher: Publisher | None = None, clock=time.time):
        self.cfg = cfg
        self.clock = clock
        self.publisher = publisher or Publisher(cfg.redis_url)
        self.sbs = SBSOutput()
        self.engine = Engine(group_window_s=cfg.group_window_s, publish_mlat_for_adsb=cfg.publish_mlat_for_adsb,
                             on_fix=self._on_fix, clock=clock)
        self._by_uuid = {}
        self._by_peer = {}
        for rc in cfg.receivers:
            rx = self.engine.receiver(rc.id, rc.clock_hz)
            rx.name = rc.name or rc.id
            rx.set_position(rc.lat, rc.lon, rc.alt, "config")
            if rc.uuid:
                self._by_uuid[rc.uuid.lower()] = rx
            if rc.peer:
                self._by_peer[rc.peer] = rx
        self._servers = []
        self._tasks = []
        self.connections = {}  # receiver id -> writer
        self._stat_prev = None
        self.process_time = 0.0

    def apply_receiver_config(self, doc):
        """Applies the web admin's receiver settings: {"receivers": {id: {"enabled": bool, "fixed": {...}|null}}}."""
        for rid, rc in (doc.get("receivers") or {}).items():
            rx = self.engine.receiver(rid)
            rx.enabled = rc.get("enabled", True) is not False
            if rc.get("name"):
                rx.name = rc["name"]
            fixed = rc.get("fixed")
            if fixed:
                rx.fixed_override = (float(fixed["lat"]), float(fixed["lon"]), float(fixed.get("alt_m", 0.0)))
                rx.set_position(*rx.fixed_override, "fixed")
            else:
                rx.fixed_override = None

    async def _watch_receiver_config(self):
        redis = self.publisher.redis
        try:
            raw = await redis.get("mlat:receiver_config")
            if raw:
                self.apply_receiver_config(json.loads(raw))
            pubsub = redis.pubsub()
            await pubsub.subscribe("mlat:config")
            async for m in pubsub.listen():
                if m.get("type") == "message":
                    try:
                        self.apply_receiver_config(json.loads(m["data"]))
                    except (ValueError, KeyError, TypeError) as e:
                        log.warning("bad receiver config: %s", e)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            log.warning("receiver config watch stopped: %s", e)

    def _on_fix(self, e):
        self.publisher.add_fix(e)
        self.sbs.send(e)

    # Feeds.

    def _ingest(self, state, data, peer):
        """Feeds bytes of one connection or datagram. state: dict with parser and receiver."""
        t0 = time.perf_counter()
        frames, infos, feed_ids = state["parser"].feed(data)
        wall = self.clock()
        for info in infos:
            rx = self.engine.apply_info(info)
            state["rx"] = rx
        for uuid in feed_ids:
            rx = self._by_uuid.get(uuid.lower())
            if rx is not None:
                state["rx"] = rx
        rx = state.get("rx")
        if rx is None:
            rx = self._by_peer.get(peer)
            state["rx"] = rx
        if rx is not None and frames and rx.enabled:
            self.engine.add_frames(rx, frames, wall)
        self.process_time += time.perf_counter() - t0
        return rx

    async def _handle_tcp(self, reader, writer, preset=None):
        peer = writer.get_extra_info("peername")
        host = peer[0] if peer else None
        state = {"parser": beast.BeastParser(), "rx": preset}
        rx = None
        try:
            while True:
                data = await reader.read(READ_SIZE)
                if not data:
                    break
                rx = self._ingest(state, data, host)
                if rx is not None and not rx.connected:
                    rx.connected = True
                    log.info("receiver %s connected from %s", rx.id, host)
        except (ConnectionError, asyncio.IncompleteReadError):
            pass
        finally:
            if rx is not None:
                rx.connected = False
                log.info("receiver %s disconnected", rx.id)
            writer.close()

    class _UDP(asyncio.DatagramProtocol):
        def __init__(self, server):
            self.server = server

        def datagram_received(self, data, addr):
            self.server._ingest({"parser": beast.BeastParser(), "rx": None}, data, addr[0])

    async def _connector(self, rc):
        host, _, port = rc.connect.rpartition(":")
        rx = self.engine.receivers[rc.id]
        while True:
            try:
                reader, writer = await asyncio.open_connection(host, int(port))
                log.info("connected to %s for %s", rc.connect, rc.id)
                await self._handle_tcp(reader, writer, preset=rx)
            except OSError as e:
                log.warning("connect %s: %s", rc.connect, e)
            await asyncio.sleep(5.0)

    # Periodic work.

    async def _ticker(self):
        next_aircraft = next_status = self.clock()
        while True:
            await asyncio.sleep(TICK_S)
            now = self.clock()
            t0 = time.perf_counter()
            self.engine.tick(now)
            self.process_time += time.perf_counter() - t0
            if now >= next_aircraft:
                next_aircraft = now + self.cfg.aircraft_interval_s
                await self.publisher.flush_aircraft(now)
            if now >= next_status:
                next_status = now + self.cfg.status_interval_s
                await self.publisher.flush_status(now, self.engine.receivers_status(), self.stats(now))

    def stats(self, now):
        s = self.engine.stats
        prev = self._stat_prev
        self._stat_prev = (now, dict(s), self.process_time)
        out = {"receivers": sum(1 for r in self.engine.by_index if r.connected),
               "aircraft": len(self.engine.aircraft),
               "sync_pairs": sum(1 for p in self.engine.sync.pairs.values() if p.valid)}
        if prev is not None and now > prev[0]:
            dt = now - prev[0]
            for k, name in (("frames", "msgs_per_s"), ("groups", "groups_per_s"),
                            ("tdoa_updates", "tdoa_updates_per_s"), ("mlat_fixes", "mlat_fixes_per_s"),
                            ("adsb_fixes", "adsb_fixes_per_s"), ("sync_events", "sync_events_per_s")):
                out[name] = round((s[k] - prev[1][k]) / dt, 1)
            out["cpu_load"] = round((self.process_time - prev[2]) / dt, 3)
            out["solves_per_s"] = round((s["tdoa_updates"] + s["solve_ok"] - prev[1]["tdoa_updates"]
                                         - prev[1]["solve_ok"]) / dt, 1)
            out["init_solves_per_s"] = round((s["solves"] - prev[1]["solves"]) / dt, 1)
        lat = self.engine.latencies
        if lat:
            a = np.fromiter(lat, float)
            out["latency_ms"] = out["latency_ms_p50"] = round(float(np.percentile(a, 50)) * 1e3, 1)
            out["latency_ms_p95"] = round(float(np.percentile(a, 95)) * 1e3, 1)
            lat.clear()
        res = self.engine.residuals
        if res:
            rms = float(np.sqrt(np.mean(np.square(np.fromiter(res, float)))))
            out["residual_ns_rms"] = round(rms * 1e9, 1)
            out["residual_m"] = round(rms * 299_792_458.0, 1)
            res.clear()
        return out

    async def start(self):
        await self.publisher.connect()
        srv = await asyncio.start_server(self._handle_tcp, self.cfg.listen_host, self.cfg.listen_port)
        self._servers.append(srv)
        self.port = srv.sockets[0].getsockname()[1]
        if self.cfg.udp:
            loop = asyncio.get_running_loop()
            transport, _ = await loop.create_datagram_endpoint(lambda: self._UDP(self),
                                                               local_addr=(self.cfg.listen_host, self.port))
            self._udp = transport
        if self.cfg.sbs_port is not None:
            sbs = await asyncio.start_server(self.sbs.handle, self.cfg.listen_host, self.cfg.sbs_port)
            self._servers.append(sbs)
            self.sbs_port = sbs.sockets[0].getsockname()[1]
        for rc in self.cfg.receivers:
            if rc.connect:
                self._tasks.append(asyncio.create_task(self._connector(rc)))
        self._tasks.append(asyncio.create_task(self._ticker()))
        if self.publisher.redis is not None:
            self._tasks.append(asyncio.create_task(self._watch_receiver_config()))
        log.info("listening on %s:%d (TCP%s)", self.cfg.listen_host, self.port, "+UDP" if self.cfg.udp else "")

    async def stop(self):
        for t in self._tasks:
            t.cancel()
        for s in self._servers:
            s.close()
        if getattr(self, "_udp", None):
            self._udp.close()

    async def run_forever(self):
        await self.start()
        await asyncio.Event().wait()
