#!/usr/bin/env python3
"""Verify ADSBee device health via the /metrics WebSocket."""

import asyncio
import json
import re
import sys
import argparse
import time
import websockets
import websockets.exceptions


async def check_firmware_version(host: str, expected: str, timeout: float = 10.0) -> bool:
    """Query AT+DEVICE_INFO? and verify RP2040 Firmware Version matches expected."""
    url = f"ws://{host}/console"
    try:
        async with websockets.connect(url, open_timeout=timeout) as ws:
            await ws.send("AT+DEVICE_INFO?\r\n")
            deadline = time.monotonic() + timeout
            while time.monotonic() < deadline:
                remaining = deadline - time.monotonic()
                try:
                    raw = await asyncio.wait_for(ws.recv(), timeout=min(3.0, remaining))
                except asyncio.TimeoutError:
                    break
                text = raw if isinstance(raw, str) else raw.decode("utf-8", errors="replace")
                m = re.search(r"RP2040 Firmware Version:\s*(\S+)", text)
                if m:
                    actual = m.group(1).strip()
                    if actual == expected:
                        print(f"  Firmware version: {actual} ✓")
                        return True
                    else:
                        print(f"  Firmware version mismatch: got {actual!r}, expected {expected!r}")
                        return False
    except Exception as exc:
        print(f"  Version check error: {exc}")
    print(f"  Could not read firmware version from {host}")
    return False


async def check_health(host: str, timeout: float = 30.0, expected_version: str | None = None) -> bool:
    url = f"ws://{host}/metrics"
    deadline = time.monotonic() + timeout

    print(f"  Connecting to {url} (timeout {timeout:.0f}s)...")

    # Require evidence that BOTH processors are alive: the ESP32 (which serves
    # /metrics) and the RP2040 (the OTA target). The ESP32 keeps running across
    # an RP2040 reboot and caches the RP2040's last-reported status, so its own
    # uptime/heap can't prove the RP2040 came back. We additionally require the
    # RP2040's reported uptime to *advance* between two samples — that only
    # happens while it is actively heartbeating over SPI, so a hung or
    # never-rebooted RP2040 (frozen, stale uptime) fails the check.
    rp2040_uptime_baseline: int | None = None

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

                    device_status = data.get("device_status", {})
                    esp32  = device_status.get("esp32", {})
                    rp2040 = device_status.get("rp2040", {})
                    uptime = esp32.get("uptime_ms", 0)
                    heap   = esp32.get("heap_free_bytes", 0)
                    rp2040_uptime = rp2040.get("uptime_ms", 0)

                    if not (uptime > 0 and heap > 0):
                        continue  # ESP32 not healthy yet.

                    if rp2040_uptime <= 0:
                        print("  esp32 up; waiting for RP2040 to report in...")
                        continue

                    # First RP2040 sample: record a baseline, then wait for it to advance.
                    if rp2040_uptime_baseline is None:
                        rp2040_uptime_baseline = rp2040_uptime
                        print(f"  esp32 uptime={uptime} ms  heap_free={heap} bytes  "
                              f"rp2040 uptime={rp2040_uptime} ms (confirming liveness...)")
                        continue
                    if rp2040_uptime <= rp2040_uptime_baseline:
                        continue  # RP2040 uptime not advancing yet — could be stale.

                    print(f"  esp32 uptime={uptime} ms  heap_free={heap} bytes  "
                          f"rp2040 uptime advancing ({rp2040_uptime_baseline}→{rp2040_uptime} ms)")
                    if expected_version is not None:
                        if not await check_firmware_version(host, expected_version):
                            return False
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
    parser.add_argument("--expected-version", metavar="VER",
                        help="Expected RP2040 firmware version (e.g. 0.9.0-rc19)")
    args = parser.parse_args()

    ok = asyncio.run(check_health(args.host, args.timeout, args.expected_version))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
