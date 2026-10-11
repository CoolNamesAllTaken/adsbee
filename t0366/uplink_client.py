#!/usr/bin/env python3
"""Connects to an ADSBee 1090 /uplink WebSocket and prints the frame count and rate.

  uplink_client.py <host> [--clients N] [--seconds S] [--stall-client-s S] [--expect tables.json] [--json out]

Message: 432 byte payload, int8 RSSI (dBm, -128 unknown), 3 reserved bytes, uint32 LE ms since boot.
Also reads /metrics for the ESP32 heap. --stall-client-s makes the last client stop reading for S seconds."""
import argparse, asyncio, json, struct, time
import websockets


def deinterleave(enc: bytes) -> bytes:
    return b"".join(bytes(enc[j * 6 + b] for j in range(72)) for b in range(6))


async def uplink(host, idx, a, stats, expect):
    st = stats[idx]
    async with websockets.connect(f"ws://{host}/uplink", max_size=None, ping_interval=None) as ws:
        st["connected"] = time.time()
        end = time.time() + a.seconds
        stalled = False
        while time.time() < end:
            if a.stall_client_s and idx == a.clients - 1 and not stalled and time.time() - st["connected"] > 5:
                stalled = True
                st["stall_start_frames"] = st["frames"]
                # Stop reading and shrink nothing: the TCP window fills and the device must skip old frames.
                ws.transport.pause_reading()
                await asyncio.sleep(a.stall_client_s)
                ws.transport.resume_reading()
                continue
            try:
                m = await asyncio.wait_for(ws.recv(), timeout=0.5)
            except asyncio.TimeoutError:
                continue
            now = time.time()
            if not isinstance(m, bytes) or len(m) != 440:
                st["bad_len"] += 1
                continue
            rssi, r0, r1, r2, t_ms = struct.unpack_from("<bBBBI", m, 432)
            st["frames"] += 1
            st["rssi"].append(rssi)
            st["t_ms"].append(t_ms)
            st["rx"].append(now)
            if (r0, r1, r2) != (0, 0, 0):
                st["bad_reserved"] += 1
            if expect is not None:
                st["match" if m[:432] in expect else "mismatch"] += 1


async def metrics(host, a, heap):
    try:
        async with websockets.connect(f"ws://{host}/metrics", max_size=None, ping_interval=None) as ws:
            end = time.time() + a.seconds + 1
            while time.time() < end:
                try:
                    m = await asyncio.wait_for(ws.recv(), timeout=2)
                except asyncio.TimeoutError:
                    continue
                try:
                    e = json.loads(m)["device_status"]["esp32"]
                    heap.append((time.time(), e["heap_free_bytes"], e["heap_largest_free_block_bytes"],
                                 e.get("core_0_usage_percent"), e.get("core_1_usage_percent")))
                except Exception:
                    pass
    except Exception as ex:
        print("metrics socket:", ex)


async def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("host"); ap.add_argument("--clients", type=int, default=1)
    ap.add_argument("--seconds", type=float, default=30); ap.add_argument("--stall-client-s", type=float, default=0)
    ap.add_argument("--expect"); ap.add_argument("--json"); ap.add_argument("--no-metrics", action="store_true")
    a = ap.parse_args()
    expect = None
    if a.expect:
        expect = {deinterleave(bytes.fromhex(h)) for h in json.load(open(a.expect))["uat_uplink"]}
    stats = [dict(frames=0, bad_len=0, bad_reserved=0, match=0, mismatch=0, rssi=[], t_ms=[], rx=[]) for _ in range(a.clients)]
    heap = []
    tasks = [uplink(a.host, i, a, stats, expect) for i in range(a.clients)]
    if not a.no_metrics:
        tasks.append(metrics(a.host, a, heap))
    res = await asyncio.gather(*tasks, return_exceptions=True)
    out = {"host": a.host, "clients": [], "errors": [repr(r) for r in res if isinstance(r, Exception)]}
    for i, st in enumerate(stats):
        rx = st["rx"]
        span = (rx[-1] - rx[0]) if len(rx) > 1 else 0
        per_s = {}
        for t in rx:
            per_s[int(t)] = per_s.get(int(t), 0) + 1
        c = {"client": i, "frames": st["frames"], "rate_hz": round((len(rx) - 1) / span, 2) if span else 0,
             "peak_per_s": max(per_s.values()) if per_s else 0, "bad_len": st["bad_len"],
             "bad_reserved": st["bad_reserved"], "match": st["match"], "mismatch": st["mismatch"],
             "rssi_min_max": [min(st["rssi"]), max(st["rssi"])] if st["rssi"] else None,
             "t_ms_first_last": [st["t_ms"][0], st["t_ms"][-1]] if st["t_ms"] else None,
             "t_ms_monotonic": all(b >= a_ for a_, b in zip(st["t_ms"], st["t_ms"][1:]))}
        if "stall_start_frames" in st:
            c["frames_before_stall"] = st["stall_start_frames"]
        out["clients"].append(c)
        print(f"client {i}: {c['frames']} frames, {c['rate_hz']} /s (peak {c['peak_per_s']} /s), match {c['match']}, "
              f"mismatch {c['mismatch']}, bad {c['bad_len'] + c['bad_reserved']}, rssi {c['rssi_min_max']}")
    if heap:
        out["heap_free_min_max"] = [min(h[1] for h in heap), max(h[1] for h in heap)]
        out["heap_largest_block_min_max"] = [min(h[2] for h in heap), max(h[2] for h in heap)]
        out["cpu0_max"] = max(h[3] or 0 for h in heap); out["cpu1_max"] = max(h[4] or 0 for h in heap)
        out["heap_samples"] = heap
        print(f"heap free {out['heap_free_min_max']} B, largest block {out['heap_largest_block_min_max']} B, "
              f"cpu max {out['cpu0_max']}% / {out['cpu1_max']}%")
    if a.json:
        json.dump(out, open(a.json, "w"))

asyncio.run(main())
