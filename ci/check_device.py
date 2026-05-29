#!/usr/bin/env python3
"""Verify ADSBee device health via the /metrics WebSocket."""

import asyncio
import json
import sys
import argparse
import time
import websockets
import websockets.exceptions


async def check_health(host: str, timeout: float = 30.0) -> bool:
    url = f"ws://{host}/metrics"
    deadline = time.monotonic() + timeout

    print(f"  Connecting to {url} (timeout {timeout:.0f}s)...")

    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        try:
            async with websockets.connect(url, open_timeout=min(5.0, remaining)) as ws:
                while time.monotonic() < deadline:
                    inner_remaining = deadline - time.monotonic()
                    try:
                        raw = await asyncio.wait_for(ws.recv(), timeout=min(5.0, inner_remaining))
                    except asyncio.TimeoutError:
                        print("  Waiting for metrics...")
                        continue

                    try:
                        data = json.loads(raw)
                    except json.JSONDecodeError:
                        continue

                    esp32 = data.get("device_status", {}).get("esp32", {})
                    uptime = esp32.get("uptime_ms", 0)
                    heap   = esp32.get("heap_free_bytes", 0)

                    if uptime > 0 and heap > 0:
                        print(f"  esp32 uptime={uptime} ms  heap_free={heap} bytes")
                        print("  Device is healthy.")
                        return True

        except (OSError, websockets.exceptions.WebSocketException) as exc:
            print(f"  Connection error: {exc}")
            await asyncio.sleep(2.0)

    print(f"  Device did not respond within {timeout:.0f}s.")
    return False


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("host", help="Device hostname or IP (e.g. adsbee1090.local)")
    parser.add_argument("--timeout", type=float, default=30.0,
                        help="Total wait time in seconds (default: 30)")
    args = parser.parse_args()

    ok = asyncio.run(check_health(args.host, args.timeout))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
