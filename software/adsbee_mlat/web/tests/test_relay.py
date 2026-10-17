import asyncio
import json

import fakeredis
import pytest
from channels.testing import WebsocketCommunicator

from live.relay import (
    AIRCRAFT_CHANNEL, CLIENT_QUEUE_LEN, RECEIVERS_CHANNEL, SNAPSHOT_KEY, STATS_CHANNEL, Client, Relay,
    compact_aircraft, enrich_receivers, set_relay,
)
from mlat_web.asgi import application
from receivers.config import CONFIG_CHANNEL, CONFIG_KEY
from receivers.models import Receiver

FIX = {"icao": "A1B2C3", "src": "mlat", "lat": 37.123456789, "lon": -122.5, "alt_ft": 12000.4, "gs_kt": 250.06,
       "track_deg": 90.04, "vr_fpm": -640, "callsign": "UAL1", "squawk": "1200", "t": 99.9, "err_m": 35.2,
       "nrecv": 5, "gdop": 1.83}
RX = {"t": 100.0, "receivers": [
    {"id": "bee-1", "name": "core name", "lat": 37, "lon": -122, "alt_m": 10, "pos_src": "gnss", "clock_hz": 48000000,
     "msg_rate": 100.0, "sync_ok": True, "clock_err_ns": 12.0, "peers": ["bee-2"]},
    {"id": "bee-2", "name": "two", "lat": 37.1, "lon": -122.1, "alt_m": 10, "pos_src": "fixed", "clock_hz": 12000000,
     "msg_rate": 50.0, "sync_ok": False, "clock_err_ns": None, "peers": []},
]}


def test_compact_aircraft_format():
    msg = json.loads(compact_aircraft({"t": 100.0, "aircraft": [FIX, dict(FIX, icao="ffffff", src="adsb", err_m=None)]}))
    assert msg["type"] == "ac" and msg["t"] == 100.0 and msg["snap"] is False
    assert msg["a"][0] == ["a1b2c3", 1, 37.12346, -122.5, 12000, 250.1, 90.0, -640, -0.1, 35, 5, 1.8, "UAL1", "1200"]
    assert msg["a"][1][1] == 0 and msg["a"][1][9] is None


def test_compact_aircraft_skips_bad_rows():
    rows = [{"icao": "a"}, {"icao": "b", "lat": "x", "lon": 1}, {"icao": "c", "lat": 1, "lon": 2, "t": 5}]
    msg = json.loads(compact_aircraft({"t": 5, "aircraft": rows}, snap=True))
    assert [r[0] for r in msg["a"]] == ["c"] and msg["snap"] is True


def test_enrich_receivers_applies_admin_config():
    cfg = {"bee-1": {"name": "Roof", "owner": "Ana", "enabled": True}, "bee-2": {"name": "", "enabled": False}}
    msg = json.loads(enrich_receivers(RX, cfg))
    assert msg["type"] == "rx"
    assert [r["id"] for r in msg["receivers"]] == ["bee-1"]
    assert msg["receivers"][0]["name"] == "Roof" and msg["receivers"][0]["owner"] == "Ana"
    assert json.loads(enrich_receivers(RX, {}))["receivers"][1]["name"] == "two"


async def test_client_queue_drops_oldest():
    sent = []
    c = Client(lambda t: sent.append(t))
    for i in range(CLIENT_QUEUE_LEN + 5):
        c.put(str(i))
    assert c.dropped == 5
    assert c.queue.get_nowait() == "5"


@pytest.fixture
def fake_server():
    return fakeredis.FakeServer()


@pytest.fixture
def relay(fake_server):
    r = Relay(redis_url="redis://fake", client_factory=lambda: fakeredis.aioredis.FakeRedis(server=fake_server))
    set_relay(r)
    yield r
    set_relay(None)


async def recv_json(comm, timeout=2):
    return json.loads(await comm.receive_from(timeout=timeout))


async def wait_subscribed(relay):
    for _ in range(100):
        numsub = await relay._get_redis().pubsub_numsub(AIRCRAFT_CHANNEL)
        if numsub and numsub[0][1] > 0:
            return
        await asyncio.sleep(0.02)
    raise AssertionError("relay never subscribed")


@pytest.mark.django_db(transaction=True)
async def test_websocket_snapshot_then_live(relay, fake_server):
    pub = fakeredis.aioredis.FakeRedis(server=fake_server)
    await pub.set(SNAPSHOT_KEY, json.dumps({"t": 100.0, "aircraft": [FIX]}))
    await pub.set(CONFIG_KEY, json.dumps({"receivers": {"bee-1": {"name": "Roof", "owner": "Ana", "enabled": True}}}))

    comm = WebsocketCommunicator(application, "/ws/live")
    connected, _ = await comm.connect()
    assert connected
    snap = await recv_json(comm)
    assert snap["type"] == "ac" and snap["snap"] is True and snap["a"][0][0] == "a1b2c3"

    await wait_subscribed(relay)
    await pub.publish(AIRCRAFT_CHANNEL, json.dumps({"t": 101.0, "aircraft": [dict(FIX, t=100.95, lat=37.2)]}))
    live = await recv_json(comm)
    assert live["snap"] is False and live["a"][0][2] == 37.2 and live["a"][0][8] == -0.05

    await pub.publish(RECEIVERS_CHANNEL, json.dumps(RX))
    rx = await recv_json(comm)
    assert rx["type"] == "rx" and rx["receivers"][0]["name"] == "Roof"
    # Unknown receivers are added to the admin.
    rows = await asyncio.to_thread(lambda: list(Receiver.objects.values_list("receiver_id", "name")))
    assert rows == [("bee-2", "two")]

    await pub.publish(STATS_CHANNEL, json.dumps({"t": 101.0, "solves_per_s": 12}))
    stats = await recv_json(comm)
    assert stats == {"type": "stats", "t": 101.0, "solves_per_s": 12}

    # A config change from the admin takes effect on the next receivers message.
    await pub.publish(CONFIG_CHANNEL, json.dumps({"receivers": {"bee-1": {"enabled": False}}}))
    await pub.publish(RECEIVERS_CHANNEL, json.dumps(RX))
    rx = await recv_json(comm)
    assert [r["id"] for r in rx["receivers"]] == ["bee-2"]

    # Late joiners get the last receivers and stats messages with the snapshot.
    comm2 = WebsocketCommunicator(application, "/ws/live")
    await comm2.connect()
    types = [(await recv_json(comm2))["type"] for _ in range(3)]
    assert types == ["ac", "rx", "stats"]

    await comm.disconnect()
    await comm2.disconnect()
    assert not relay.clients
    await relay.stop()


@pytest.mark.django_db(transaction=True)
async def test_bad_messages_are_ignored(relay, fake_server):
    pub = fakeredis.aioredis.FakeRedis(server=fake_server)
    comm = WebsocketCommunicator(application, "/ws/live")
    await comm.connect()
    await wait_subscribed(relay)
    await pub.publish(AIRCRAFT_CHANNEL, b"not json")
    await pub.publish(STATS_CHANNEL, json.dumps({"t": 1, "solves_per_s": 3}))
    assert (await recv_json(comm))["solves_per_s"] == 3
    await comm.disconnect()
    await relay.stop()


@pytest.mark.django_db(transaction=True)
async def test_relay_reconnects_after_redis_error(fake_server):
    fake_server.connected = False
    relay = Relay(redis_url="redis://fake", client_factory=lambda: fakeredis.aioredis.FakeRedis(server=fake_server))
    relay.ensure_running()
    await asyncio.sleep(0.3)
    fake_server.connected = True
    await wait_subscribed(relay)
    await relay.stop()
