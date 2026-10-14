"""End to end: simulated receivers stream Beast over TCP and UDP sockets to the server; fixes are compared with truth."""

import asyncio
import time

import pytest

sim = pytest.importorskip("adsbee_mlat_sim")

from adsbee_mlat import validation  # noqa: E402
from adsbee_mlat.config import Config  # noqa: E402
from adsbee_mlat.server import Publisher, Server  # noqa: E402

DURATION_S = 25.0


async def _run(udp):
    sc = sim.example_scenario(n_receivers=5, baseline_m=30e3, n_aircraft=25, radius_m=100e3, clock_hz=48e6, seed=3)
    cfg = Config(listen_host="127.0.0.1", listen_port=0, sbs_port=0, redis_url=None, group_window_s=0.2)
    pub = Publisher()
    pub.keep_sent = True
    server = Server(cfg, publisher=pub)
    col = validation.TruthCollector(sc)
    server.engine.on_mlat = col.on_mlat
    await server.start()
    sbs_reader, sbs_writer = await asyncio.open_connection("127.0.0.1", server.sbs_port)
    sc.t0_unix = time.time() + 1.0
    frames = list(sc.frames(DURATION_S))
    await validation.stream(sc, frames, "127.0.0.1", server.port, udp=udp)
    await asyncio.sleep(1.0)
    col.time_shift = [validation.mapping_shift(server.engine, frames[-2000:])]
    sbs = await asyncio.wait_for(sbs_reader.read(1 << 20), 1.0)
    sbs_writer.close()
    await server.stop()
    return sc, server, pub, col, sbs


@pytest.mark.parametrize("udp", [False, True], ids=["tcp", "udp"])
def test_end_to_end(udp):
    sc, server, pub, col, sbs = asyncio.run(_run(udp))
    eng = server.engine
    assert set(eng.receivers) == {rx.id for rx in sc.receivers}
    assert all(r["sync_ok"] for r in eng.receivers_status())
    rows = col.errors(settle_s=10.0)
    s = validation.summarize(rows)
    assert s["n"] > 500
    assert s["h_p50"] < 150.0, s
    assert s["rate_hz_median"] > 2.0, s

    channels = {c for c, _ in pub.sent}
    assert {"mlat:aircraft", "mlat:receivers", "mlat:stats", "mlat:snapshot"} <= channels
    fixes = [a for c, p in pub.sent if c == "mlat:aircraft" for a in p["aircraft"]]
    srcs = {f["src"] for f in fixes}
    assert srcs == {"adsb", "mlat"}
    # MLAT is published for aircraft without ADS-B positions (and only fills gaps for the others).
    modes_only = {f"{a.icao:06x}" for a in sc.aircraft if not a.adsb}
    mlat = [f for f in fixes if f["src"] == "mlat"]
    assert {f["icao"] for f in mlat} >= modes_only
    assert sum(f["icao"] in modes_only for f in mlat) > 0.9 * len(mlat)
    for f in fixes:
        assert set(f) == {"icao", "src", "lat", "lon", "alt_ft", "gs_kt", "track_deg", "vr_fpm", "callsign", "squawk",
                          "t", "err_m", "nrecv", "gdop"}
    stats = [p for c, p in pub.sent if c == "mlat:stats"]
    assert any("latency_ms_p50" in p for p in stats)
    assert sbs.startswith(b"MSG,3,")
