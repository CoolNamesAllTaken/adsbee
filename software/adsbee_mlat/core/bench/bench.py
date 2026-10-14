"""Throughput benchmark: Beast parsing and the engine on a large simulated network.

python bench/bench.py --receivers 50 --aircraft 400 --duration 10 [--cache FILE]
"""

import argparse
import json
import os
import pickle
import time
from collections import defaultdict

import adsbee_mlat_sim as sim

from adsbee_mlat import beast, validation
from adsbee_mlat.engine import Engine


def frames_for(args):
    if args.cache and os.path.exists(args.cache):
        with open(args.cache, "rb") as f:
            return pickle.load(f)
    rng = sim.np.random.default_rng([args.seed, 1])
    rxs = validation.random_array(sim, 47.6, -122.3, args.receivers, args.radius_km * 1e3, seed=args.seed)
    acs = sim.random_traffic(rng, 47.6, -122.3, args.aircraft, args.traffic_radius_km * 1e3)
    sc = sim.Scenario(receivers=rxs, aircraft=acs, seed=args.seed)
    t = time.time()
    frames = [(f.rx_id, f.ticks, f.msg, f.t_arrival) for f in sc.frames(args.duration)]
    infos = [validation.receiver_info(r) for r in rxs]
    print(f"generated {len(frames)} frames in {time.time() - t:.0f} s")
    data = (infos, frames, sc.t0_unix)
    if args.cache:
        with open(args.cache, "wb") as f:
            pickle.dump(data, f)
    return data


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--receivers", type=int, default=50)
    ap.add_argument("--aircraft", type=int, default=400)
    ap.add_argument("--radius-km", type=float, default=100)
    ap.add_argument("--traffic-radius-km", type=float, default=250)
    ap.add_argument("--duration", type=float, default=10)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--cache")
    ap.add_argument("--json")
    ap.add_argument("--workers", type=int, default=1, help="Worker processes (sharded engine)")
    ap.add_argument("--adsb-mlat-fraction", type=float, default=0.1,
                    help="1.0: MLAT every message of every aircraft (worst case)")
    args = ap.parse_args()
    infos, frames, t0 = frames_for(args)
    duration = float(frames[-1][3] - frames[0][3])
    out = {"receivers": len(infos), "frames": len(frames), "sim_s": round(duration, 2),
           "offered_msgs_per_s": round(len(frames) / duration)}

    # Beast parsing: one byte stream per receiver, read in 64 KiB chunks.
    streams = defaultdict(list)
    for rid, ticks, msg, _ in frames:
        streams[rid].append(beast.build_mode_s(ticks, msg))
    blobs = [b"".join(v) for v in streams.values()]
    t = time.perf_counter()
    n = 0
    for blob in blobs:
        p = beast.BeastParser()
        for i in range(0, len(blob), 65536):
            n += len(p.feed(blob[i:i + 65536])[0])
    dt = time.perf_counter() - t
    out["parse_msgs_per_s"] = round(n / dt)

    # Engine: reads of 20 ms per receiver, ticks every 20 ms, simulated wall clock.
    if args.workers > 1:
        from adsbee_mlat.parallel import ShardedEngine

        eng = ShardedEngine(args.workers, group_window_s=0.3, adsb_mlat_fraction=args.adsb_mlat_fraction)
    else:
        eng = Engine(group_window_s=0.3, adsb_mlat_fraction=args.adsb_mlat_fraction)
    wall_start = time.perf_counter()
    for info in infos:
        eng.apply_info(info)
    chunk = 0.02
    pending = defaultdict(list)
    t_engine = 0.0
    t_ingest = 0.0
    next_flush = frames[0][3] + chunk
    for rid, ticks, msg, ta in frames:
        while ta >= next_flush:
            wall = t0 + next_flush + 0.05
            a = time.perf_counter()
            for r, fr in pending.items():
                eng.add_frames(eng.receivers[r], fr, wall)
            b = time.perf_counter()
            eng.tick(wall)
            t_engine += time.perf_counter() - a
            t_ingest += b - a
            pending.clear()
            next_flush += chunk
        pending[rid].append((ticks % (1 << 48), 0x80, msg))
    if args.workers > 1:
        for k in range(40):
            eng.tick(t0 + next_flush + 0.05 + k * chunk)
        eng.close()
        eng._poll()
        wall = time.perf_counter() - wall_start
        out.update(workers=args.workers, front_cpu_s=round(t_engine, 2), wall_s=round(wall, 2),
                   realtime_factor=round(duration / wall, 2), worker_stats=eng.stats)
        print(json.dumps(out, indent=1))
        return
    s = eng.stats
    out.update(engine_cpu_s=round(t_engine, 2), engine_realtime_load=round(t_engine / duration, 3),
               ingest_cpu_s=round(t_ingest, 2), engine_msgs_per_s=round(len(frames) / t_engine),
               groups_per_s=round(s["groups"] / duration), mean_group_size=round(s["frames"] / max(s["groups"], 1), 1),
               sync_events_per_s=round(s["sync_events"] / duration), pair_updates_per_s=round(eng.sync.updates / duration),
               solves_per_s=round(s["solves"] / duration), tdoa_updates_per_s=round(s["tdoa_updates"] / duration),
               tdoa_updates_per_cpu_s=round(s["tdoa_updates"] / t_engine), valid_pairs=int(sum(p.valid for p in eng.sync.pairs.values())))
    print(json.dumps(out, indent=1))
    if args.json:
        with open(args.json, "w") as f:
            json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
