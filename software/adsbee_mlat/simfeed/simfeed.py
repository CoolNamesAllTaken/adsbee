"""Simulated receivers feeding an MLAT server over real sockets, in real time.

ADSBee receivers send Beast with receiver info frames and 48 MHz timestamps. Plain Beast receivers send 12 MHz
timestamps and only a feed ID frame; the server knows them from its configuration file (--write-config).

python simfeed.py --host core --port 31090 [--adsbee 8 --beast 2 --aircraft 80]
python simfeed.py --write-config ../config/sim.toml
"""

import argparse
import asyncio
import logging
import time
import uuid
from collections import defaultdict

import adsbee_mlat_sim as sim
import numpy as np

from adsbee_mlat import beast

log = logging.getLogger("simfeed")
CENTER = (47.6, -122.3)
INFO_INTERVAL_S = 10.0
BATCH_S = 0.02


def build(args):
    rng = np.random.default_rng([args.seed, 1])
    rxs = sim.make_array(*CENTER, args.adsbee, args.baseline_km * 1e3, clock_hz=48e6, receiver_type="adsbee_1090",
                         seed=args.seed)
    for k in range(args.beast):
        lat, lon = sim.destination(*CENTER, 45.0 + 180.0 * k, args.baseline_km * 1e3 * 0.6)
        rxs.append(sim.Receiver(id=f"beast-{k + 1}", lat=float(lat), lon=float(lon), alt_m=30.0, pos_src="config",
                                timing=sim.RECEIVER_TYPES["rtlsdr"](),
                                clock=sim.Clock(clock_hz=12e6, offset_s=float(rng.uniform(0, 1000)),
                                                ppm=float(rng.normal(0, 20)), seed=100 + k)))
    for rx in rxs[:args.adsbee]:
        rx.id = f"adsbee-{rx.id[2:]}"
        rx.name = f"ADSBee {rx.id[7:]}"
    acs = sim.random_traffic(rng, *CENTER, args.aircraft, args.radius_km * 1e3, adsb_share=args.adsb_share)
    return sim.Scenario(receivers=rxs, aircraft=acs, seed=args.seed)


def feed_uuid(rid):
    return str(uuid.uuid5(uuid.NAMESPACE_URL, f"adsbee-mlat-simfeed/{rid}"))


def write_config(sc, path):
    lines = ["# Plain Beast receivers of simfeed/simfeed.py (generated with --write-config).", ""]
    for rx in sc.receivers:
        if rx.clock_hz != 12_000_000:
            continue
        lines += ["[[receiver]]", f'id = "{rx.id}"', f'name = "Beast {rx.id[6:]}"',
                  f'match = {{ uuid = "{feed_uuid(rx.id)}" }}', f"lat = {rx.lat:.7f}", f"lon = {rx.lon:.7f}",
                  f"alt = {rx.alt_m:.1f}", "clock_hz = 12000000", ""]
    with open(path, "w") as f:
        f.write("\n".join(lines))


def info_frame(rx):
    return beast.build_info(id=rx.id, name=rx.name, ep="1", clk=rx.clock_hz, lat=rx.reported_lat,
                            lon=rx.reported_lon, alt=rx.reported_alt_m, src="fixed", fw="simfeed")


async def connect(host, port):
    for _ in range(120):
        try:
            return await asyncio.open_connection(host, port)
        except OSError:
            await asyncio.sleep(1.0)
    raise SystemExit(f"cannot connect to {host}:{port}")


async def run(args):
    sc = build(args)
    writers = {}
    adsbee = {rx.id: rx for rx in sc.receivers if rx.clock_hz == 48_000_000}
    for rx in sc.receivers:
        _, w = await connect(args.host, args.port)
        if rx.id in adsbee:
            w.write(info_frame(rx))
        else:
            w.write(b"\x1a\xe4" + feed_uuid(rx.id).encode())
        writers[rx.id] = w
    log.info("%d receivers connected, %d aircraft (%d without ADS-B)", len(writers), len(sc.aircraft),
             sum(not a.adsb for a in sc.aircraft))
    sc.t0_unix = time.time() + 1.0
    pending = defaultdict(list)
    t_batch = None
    next_info = time.time() + INFO_INTERVAL_S
    n = 0
    for f in sc.frames(args.duration):
        if t_batch is None:
            t_batch = f.t_unix + BATCH_S
        if f.t_unix > t_batch:
            delay = t_batch - time.time()
            if delay > 0:
                await asyncio.sleep(delay)
            for rid, chunks in pending.items():
                writers[rid].write(b"".join(chunks))
            pending.clear()
            await asyncio.gather(*(w.drain() for w in writers.values()))
            t_batch = f.t_unix + BATCH_S
            if time.time() > next_info:
                next_info += INFO_INTERVAL_S
                for rid, rx in adsbee.items():
                    writers[rid].write(info_frame(rx))
                log.info("%d frames sent", n)
        pending[f.rx_id].append(beast.build_mode_s(f.ticks, f.msg))
        n += 1


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=31090)
    ap.add_argument("--adsbee", type=int, default=8, help="ADSBee receivers (48 MHz)")
    ap.add_argument("--beast", type=int, default=2, help="Plain Beast receivers (12 MHz, from the config file)")
    ap.add_argument("--aircraft", type=int, default=80)
    ap.add_argument("--adsb-share", type=float, default=0.6)
    ap.add_argument("--radius-km", type=float, default=150.0)
    ap.add_argument("--baseline-km", type=float, default=30.0)
    ap.add_argument("--duration", type=float, default=6 * 3600.0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--write-config", metavar="PATH")
    args = ap.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(name)s: %(message)s")
    if args.write_config:
        write_config(build(args), args.write_config)
        return
    asyncio.run(run(args))


if __name__ == "__main__":
    main()
