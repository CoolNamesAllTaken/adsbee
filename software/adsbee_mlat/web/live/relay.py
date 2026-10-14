"""Relays the MLAT core's Redis channels to browser WebSockets.

One Redis subscription per process fans out to every connected client. Each message is
converted once to the browser format and the same text is queued for every client; a client
whose queue is full loses its oldest messages rather than slowing the others down.

Browser messages (JSON text):
  {"type": "ac", "t": T, "snap": bool, "a": [[icao, src, lat, lon, alt_ft, gs_kt, track_deg,
      vr_fpm, fix_dt_s, err_m, nrecv, gdop, callsign, squawk], ...]}
      src is 0 for ADS-B and 1 for MLAT; the fix time is T + fix_dt_s.
  {"type": "rx", "t": T, "receivers": [...]}  receivers from the core plus "owner" and
      "enabled" from the admin; disabled receivers are dropped.
  {"type": "stats", ...}  the core's stats message unchanged.
"""

import asyncio
import json
import logging
import time

import redis.asyncio as aioredis
from asgiref.sync import sync_to_async
from django.conf import settings

from receivers.config import CONFIG_CHANNEL, CONFIG_KEY

AIRCRAFT_CHANNEL = "mlat:aircraft"
RECEIVERS_CHANNEL = "mlat:receivers"
STATS_CHANNEL = "mlat:stats"
SNAPSHOT_KEY = "mlat:snapshot"

# Messages buffered per client before the oldest is dropped (about 6 s of aircraft batches).
CLIENT_QUEUE_LEN = 64

log = logging.getLogger(__name__)


def _num(v, digits):
    return None if v is None else round(float(v), digits)


def compact_aircraft(batch, snap=False):
    """Converts an aircraft batch from the core into the browser format (a JSON string)."""
    t = float(batch.get("t") or time.time())
    rows = []
    for a in batch.get("aircraft") or ():
        try:
            lat, lon = float(a["lat"]), float(a["lon"])
            rows.append(
                [
                    str(a["icao"]).lower(),
                    1 if a.get("src") == "mlat" else 0,
                    round(lat, 5),
                    round(lon, 5),
                    _num(a.get("alt_ft"), 0),
                    _num(a.get("gs_kt"), 1),
                    _num(a.get("track_deg"), 1),
                    _num(a.get("vr_fpm"), 0),
                    round(float(a.get("t", t)) - t, 3),
                    _num(a.get("err_m"), 0),
                    a.get("nrecv"),
                    _num(a.get("gdop"), 1),
                    a.get("callsign"),
                    a.get("squawk"),
                ]
            )
        except (KeyError, TypeError, ValueError):
            continue
    return json.dumps({"type": "ac", "t": round(t, 3), "snap": snap, "a": rows}, separators=(",", ":"))


def enrich_receivers(msg, config):
    """Adds admin metadata to a receivers message and drops disabled receivers."""
    out = []
    for r in msg.get("receivers") or ():
        cfg = config.get(str(r.get("id")))
        if cfg is not None:
            if not cfg.get("enabled", True):
                continue
            r = dict(r)
            if cfg.get("name"):
                r["name"] = cfg["name"]
            r["owner"] = cfg.get("owner", "")
        out.append(r)
    return json.dumps({"type": "rx", "t": msg.get("t"), "receivers": out}, separators=(",", ":"))


@sync_to_async
def _register_receivers(names):
    """Adds receivers the core reports to the admin, named as the core names them."""
    from receivers.models import Receiver

    for rid, name in names.items():
        Receiver.objects.get_or_create(receiver_id=rid, defaults={"name": str(name or "")[:100]})


class Client:
    def __init__(self, send):
        self.send = send
        self.queue = asyncio.Queue(CLIENT_QUEUE_LEN)
        self.dropped = 0

    def put(self, text):
        if self.queue.full():
            self.queue.get_nowait()
            self.dropped += 1
        self.queue.put_nowait(text)

    async def run(self):
        while True:
            await self.send(await self.queue.get())


class Relay:
    def __init__(self, redis_url=None, client_factory=None):
        self.redis_url = redis_url or settings.REDIS_URL
        self._client_factory = client_factory or (lambda: aioredis.Redis.from_url(self.redis_url))
        self.clients = set()
        self.config = {}
        self.known_ids = set()
        self.last_rx = None
        self.last_stats = None
        self.last_message_time = None
        self._task = None
        self._redis = None

    def ensure_running(self):
        if self._task is None or self._task.done():
            self._task = asyncio.get_running_loop().create_task(self._run())

    async def stop(self):
        if self._task:
            self._task.cancel()
            try:
                await self._task
            except asyncio.CancelledError:
                pass
            self._task = None

    async def add(self, send):
        """Registers a client and queues the snapshot. Returns the Client; await client.run() to send."""
        self.ensure_running()
        client = Client(send)
        self.clients.add(client)
        try:
            raw = await self._get_redis().get(SNAPSHOT_KEY)
            if raw:
                client.put(compact_aircraft(json.loads(raw), snap=True))
        except Exception as e:  # A missing snapshot only delays the first aircraft by one batch.
            log.warning("Snapshot unavailable: %s", e)
        for text in (self.last_rx, self.last_stats):
            if text:
                client.put(text)
        return client

    def remove(self, client):
        self.clients.discard(client)

    def broadcast(self, text):
        for c in self.clients:
            c.put(text)

    def _get_redis(self):
        if self._redis is None:
            self._redis = self._client_factory()
        return self._redis

    async def _load_config(self, r):
        raw = await r.get(CONFIG_KEY)
        if raw:
            self._apply_config(raw)
        else:
            from receivers.config import publish_config

            await sync_to_async(publish_config)()

    def _apply_config(self, raw):
        self.config = json.loads(raw).get("receivers", {})
        self.known_ids |= set(self.config)

    async def handle(self, channel, data):
        if isinstance(channel, bytes):
            channel = channel.decode()
        self.last_message_time = time.time()
        if channel == AIRCRAFT_CHANNEL:
            self.broadcast(compact_aircraft(json.loads(data)))
        elif channel == RECEIVERS_CHANNEL:
            msg = json.loads(data)
            names = {str(r["id"]): r.get("name") for r in msg.get("receivers") or () if r.get("id") is not None}
            new = {rid: name for rid, name in names.items() if rid not in self.known_ids}
            if new:
                self.known_ids |= set(new)
                await _register_receivers(new)
            self.last_rx = enrich_receivers(msg, self.config)
            self.broadcast(self.last_rx)
        elif channel == STATS_CHANNEL:
            msg = json.loads(data)
            msg["type"] = "stats"
            self.last_stats = json.dumps(msg, separators=(",", ":"))
            self.broadcast(self.last_stats)
        elif channel == CONFIG_CHANNEL:
            self._apply_config(data)

    async def _run(self):
        backoff = 0.5
        while True:
            pubsub = None
            try:
                r = self._get_redis()
                pubsub = r.pubsub()
                await pubsub.subscribe(AIRCRAFT_CHANNEL, RECEIVERS_CHANNEL, STATS_CHANNEL, CONFIG_CHANNEL)
                await self._load_config(r)
                backoff = 0.5
                async for msg in pubsub.listen():
                    if msg["type"] != "message":
                        continue
                    try:
                        await self.handle(msg["channel"], msg["data"])
                    except (ValueError, TypeError, AttributeError) as e:
                        log.warning("Bad message on %s: %s", msg["channel"], e)
            except asyncio.CancelledError:
                raise
            except Exception as e:
                log.warning("Redis relay error, retrying in %.1f s: %s", backoff, e)
                if pubsub is not None:
                    try:
                        await pubsub.aclose()
                    except Exception:
                        pass
                self._redis = None
                await asyncio.sleep(backoff)
                backoff = min(backoff * 2, 10)


_relay = None


def get_relay():
    global _relay
    if _relay is None:
        _relay = Relay()
    return _relay


def set_relay(relay):
    """Replaces the process relay (tests)."""
    global _relay
    _relay = relay
