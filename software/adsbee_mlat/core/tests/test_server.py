"""Server pieces that need no simulator: Redis publishing, receiver config from the web admin, config file."""

import asyncio
import json
import time

import fakeredis.aioredis
import pytest

from adsbee_mlat import beast, config
from adsbee_mlat.server import Publisher, Server


def _cfg(**kw):
    c = config.Config(listen_host="127.0.0.1", listen_port=0, sbs_port=None, redis_url=None)
    for k, v in kw.items():
        setattr(c, k, v)
    return c


def test_config_file(tmp_path):
    p = tmp_path / "mlat.toml"
    p.write_text('''
[server]
listen = "0.0.0.0:4000"
group_window_s = 0.5

[[receiver]]
id = "garage"
match = { uuid = "38366a5c-c54f-4256-bd0a-1557961f5ad0" }
lat = 37.42
lon = -122.08
alt = 30.0
''')
    cfg = config.load(str(p), env={"REDIS_URL": "redis://r:6379/1", "MLAT_FEED_PORT": "4100"})
    assert cfg.listen_port == 4100 and cfg.group_window_s == 0.5 and cfg.redis_url == "redis://r:6379/1"
    assert cfg.receivers[0].uuid.startswith("38366a5c") and cfg.receivers[0].clock_hz == 12_000_000


def test_publish_and_receiver_config():
    async def run():
        redis = fakeredis.aioredis.FakeRedis()
        pub = Publisher(redis_client=redis)
        server = Server(_cfg(), publisher=pub)
        await redis.set("mlat:receiver_config", json.dumps(
            {"t": 0, "receivers": {"b": {"enabled": False}, "a": {"fixed": {"lat": 1.0, "lon": 2.0, "alt_m": 3.0}}}}))
        ps = redis.pubsub()
        await ps.subscribe("mlat:aircraft", "mlat:receivers", "mlat:stats")
        await server.start()
        await asyncio.sleep(0.1)
        # Receiver a reports a position, which the fixed override wins over.
        _, w = await asyncio.open_connection("127.0.0.1", server.port)
        w.write(beast.build_info(id="a", ep="1", clk=48_000_000, lat=10.0, lon=20.0, alt=5.0, src="gnss"))
        w.write(beast.build_mode_s(48_000_000, bytes.fromhex("8D40621D58C382D690C8AC2863A7")))
        _, w2 = await asyncio.open_connection("127.0.0.1", server.port)
        w2.write(beast.build_info(id="b", ep="1", clk=48_000_000, lat=10.0, lon=20.0, alt=5.0, src="gnss"))
        w2.write(beast.build_mode_s(48_000_000, bytes.fromhex("8D40621D58C382D690C8AC2863A7")))
        await w.drain()
        await w2.drain()
        pub.add_fix({"icao": "40621d", "src": "adsb", "lat": 52.2, "lon": 3.9, "alt_ft": 38000, "gs_kt": None,
                     "track_deg": None, "vr_fpm": None, "callsign": None, "squawk": None, "t": time.time(), "err_m": None,
                     "nrecv": None, "gdop": None})
        await asyncio.sleep(1.3)
        msgs = {}
        for _ in range(50):
            m = await ps.get_message(ignore_subscribe_messages=True, timeout=0.05)
            if m is not None:
                msgs.setdefault(m["channel"].decode(), []).append(json.loads(m["data"]))
        snap = json.loads(await redis.get("mlat:snapshot"))
        ttl = await redis.ttl("mlat:snapshot")
        a, b = server.engine.receivers["a"], server.engine.receivers["b"]
        w.close()
        w2.close()
        await server.stop()
        return msgs, snap, ttl, a, b

    msgs, snap, ttl, a, b = asyncio.run(run())
    assert (a.lat, a.lon, a.alt, a.pos_src) == (1.0, 2.0, 3.0, "fixed")
    assert a.msg_count == 1 and b.msg_count == 0  # b is disabled.
    assert msgs["mlat:aircraft"][0]["aircraft"][0]["icao"] == "40621d"
    rx = {r["id"]: r for r in msgs["mlat:receivers"][-1]["receivers"]}
    assert rx["a"]["pos_src"] == "fixed" and rx["a"]["clock_hz"] == 48_000_000
    assert "aircraft" in msgs["mlat:stats"][-1]
    assert snap["aircraft"][0]["icao"] == "40621d" and 0 < ttl <= 30
