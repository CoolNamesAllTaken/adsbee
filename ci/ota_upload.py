#!/usr/bin/env python3
"""
OTA firmware uploader for ADSBee.

Mirrors the FirmwareUploader / ADSBeeAT logic in adsbee.js, but runs from the
command line so a CI script can drive it without a browser.

Protocol summary (all over ws://<host>/console):
  AT+LOG_LEVEL=ERRORS         silence verbose log output
  AT+PROTOCOL_OUT=CONSOLE,NONE  stop aircraft data on this socket
  AT+RX_ENABLE=0              stop the 1090 receiver
  AT+OTA=GET_PARTITION        device replies with "Partition: N"
  AT+OTA=ERASE,<off_hex>,<len_dec>  erase N bytes from offset (hex)
  AT+OTA=WRITE,<off_hex>,<len_dec>,<crc32_hex>  prepare chunk write
    → device replies READY, then we push raw bytes, device replies OK
  AT+OTA=VERIFY               verify written data
  AT+OTA=BOOT                 reboot into new partition (no response awaited)
"""

import asyncio
import struct
import sys
import zlib
import argparse
import time
import re
from typing import Optional
import websockets
import websockets.exceptions

# .ota file layout constants (must match the firmware / adsbee.js)
HEADER_SIZE   = 5 * 4        # 20 bytes
APP_OFFSET    = 4 * 1024     # flash offset where app binary begins
CHUNK_SIZE    = 0x1000 * 3   # matches adsbee.js WRITE_CHUNK_BYTES
MAX_RETRIES   = 3
CHUNK_DELAY_S = 0.05         # Required inter-chunk pause: without this delay Python's faster
                             # cadence overruns the RP2040 AT parse buffer and OTA stalls at
                             # ~88% (the 0xFF padding region). Do not set to 0.

# Timeouts (seconds)
CMD_TIMEOUT    = 6.0
ERASE_TIMEOUT  = 20.0
WRITE_TIMEOUT  = 5.0
VERIFY_TIMEOUT = 20.0   # VERIFY CRC32s the whole partition; can exceed CMD_TIMEOUT on large images.


def crc32(data: bytes) -> int:
    """Standard CRC-32 (same polynomial as the JS implementation)."""
    return zlib.crc32(data) & 0xFFFF_FFFF


class ADSBeeAT:
    def __init__(self, host: str) -> None:
        self.url = f"ws://{host}/console"
        self.ws: Optional[websockets.WebSocketClientProtocol] = None
        self._queue: asyncio.Queue[str] = asyncio.Queue()
        self._recv_task: Optional[asyncio.Task] = None

    async def connect(self) -> None:
        self.ws = await websockets.connect(self.url)
        self._queue = asyncio.Queue()
        self._recv_task = asyncio.create_task(self._recv_loop())

    async def _recv_loop(self) -> None:
        try:
            assert self.ws is not None
            async for msg in self.ws:
                text = msg if isinstance(msg, str) else msg.decode("utf-8", errors="replace")
                await self._queue.put(text)
        except Exception:
            pass

    async def disconnect(self) -> None:
        if self._recv_task:
            self._recv_task.cancel()
            try:
                await self._recv_task
            except (asyncio.CancelledError, Exception):
                pass
        if self.ws:
            try:
                await self.ws.close()
            except Exception:
                pass
            self.ws = None

    async def flush(self, delay: float = 0.05) -> None:
        await asyncio.sleep(delay)
        while not self._queue.empty():
            self._queue.get_nowait()

    async def recv_until(self, sentinel: str, timeout: float = CMD_TIMEOUT,
                         ignore_cppat_errors: bool = False) -> list[str]:
        """Collect WebSocket messages until one contains *sentinel*. Return all collected."""
        accumulated: list[str] = []
        deadline = time.monotonic() + timeout

        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError(f"Timed out ({timeout:.0f}s) waiting for '{sentinel}'. "
                                   f"Got: {accumulated}")
            try:
                msg = await asyncio.wait_for(self._queue.get(), timeout=remaining)
            except asyncio.TimeoutError:
                raise TimeoutError(f"Timed out ({timeout:.0f}s) waiting for '{sentinel}'. "
                                   f"Got: {accumulated}")

            accumulated.append(msg)

            # sentinel check (substring match, same as JS)
            if sentinel in msg:
                return accumulated

            if any(line.strip().startswith("ERROR") for line in msg.splitlines()):
                raise RuntimeError(f"Device returned ERROR. Context: {msg!r}")

            # "Unable to find AT prefix" is spurious noise from binary data — always ignore.
            # Binary sends may also trigger other CppAT errors; ignore those too.
            if "CppAT::" in msg and "Unable to find AT prefix" not in msg:
                if not ignore_cppat_errors:
                    raise RuntimeError(f"CppAT parse error from device: {msg!r}")

    async def send_cmd(self, cmd: str, sentinel: str = "OK",
                       timeout: float = CMD_TIMEOUT) -> list[str]:
        print(f"    CMD  {cmd.rstrip()}")
        assert self.ws is not None
        await self.ws.send(cmd)  # text frame, same as browser
        return await self.recv_until(sentinel, timeout)

    async def send_bytes(self, data: bytes, timeout: float = WRITE_TIMEOUT) -> list[str]:
        assert self.ws is not None
        await self.ws.send(data)
        return await self.recv_until("OK", timeout, ignore_cppat_errors=True)

    # ── OTA helpers ─────────────────────────────────────────────────────────

    async def ota_get_partition(self) -> int:
        lines = await self.send_cmd("AT+OTA=GET_PARTITION\r\n")
        for line in lines:
            m = re.search(r"Partition:\s*(\d+)", line)
            if m:
                return int(m.group(1))
        raise RuntimeError(f"Could not parse partition number. Response: {lines}")

    async def ota_erase(self, offset: int, length: int) -> None:
        # offset in hex, length in decimal – matches firmware parser
        await self.send_cmd(f"AT+OTA=ERASE,{offset:x},{length}\r\n", timeout=ERASE_TIMEOUT)

    async def ota_write_bytes(self, offset: int, data: bytes) -> None:
        ck = crc32(data)
        cmd = f"AT+OTA=WRITE,{offset:x},{len(data)},{ck:x}\r\n"
        await self.send_cmd(cmd, sentinel="READY")
        await self.send_bytes(data)

    async def ota_write_file(self, ota_path: str) -> int:
        """Write the OTA image and boot it. Returns the partition index written to."""
        with open(ota_path, "rb") as f:
            raw = f.read()

        num_partitions = struct.unpack_from("<I", raw, 0)[0]
        partition = await self.ota_get_partition()
        print(f"    OTA partition index: {partition} (of {num_partitions})")

        if partition >= num_partitions:
            raise RuntimeError(
                f"Partition {partition} out of range ({num_partitions} available in file)"
            )

        part_offset = struct.unpack_from("<I", raw, 4 + 4 * partition)[0]
        contents = raw[part_offset:]

        header  = contents[:HEADER_SIZE]
        app_len = struct.unpack_from("<I", contents, 8)[0]

        print(f"    Firmware app size: {app_len:,} bytes")
        print(f"    Erasing {HEADER_SIZE + app_len:,} bytes from flash offset 0...")
        erase_t0 = time.monotonic()
        await self.ota_erase(0, HEADER_SIZE + app_len)
        erase_elapsed = time.monotonic() - erase_t0
        print(f"    Erase done in {erase_elapsed:.1f}s")

        print(f"    Writing header ({HEADER_SIZE} bytes) at flash offset 0...")
        await self.ota_write_bytes(0, header)

        total_written = 0
        retries = 0
        app_end = HEADER_SIZE + app_len
        write_t0 = time.monotonic()
        for i in range(HEADER_SIZE, app_end, CHUNK_SIZE):
            flash_offset = (i - HEADER_SIZE) + APP_OFFSET
            chunk = contents[i : min(i + CHUNK_SIZE, app_end)]

            for attempt in range(MAX_RETRIES):
                try:
                    if attempt > 0:
                        retries += 1
                        print(f"    Retry {attempt}/{MAX_RETRIES} at flash+{flash_offset:#x}...")
                        # Reconnect: a failed binary send leaves garbage in the ESP32 console buffer.
                        await self.disconnect()
                        await asyncio.sleep(1.0)
                        await self.connect()
                        await self.ota_erase(flash_offset, CHUNK_SIZE)
                    await self.ota_write_bytes(flash_offset, chunk)
                    break
                except Exception as exc:
                    if attempt == MAX_RETRIES - 1:
                        raise
                    print(f"    Chunk at {flash_offset:#x} failed ({exc}), retrying...")

            total_written += len(chunk)
            elapsed = time.monotonic() - write_t0
            rate = total_written / elapsed if elapsed > 0 else 0
            pct = int(total_written * 100 / app_len)
            print(f"    Progress: {pct:3d}%  ({total_written:,}/{app_len:,} bytes)  {rate/1024:.1f} KiB/s")

            if CHUNK_DELAY_S > 0:
                await asyncio.sleep(CHUNK_DELAY_S)

        write_elapsed = time.monotonic() - write_t0
        avg_rate = total_written / write_elapsed if write_elapsed > 0 else 0
        print(f"    Write done in {write_elapsed:.1f}s  avg {avg_rate/1024:.1f} KiB/s  retries: {retries}")

        print("    Verifying partition...")
        await self.send_cmd("AT+OTA=VERIFY\r\n", timeout=VERIFY_TIMEOUT)

        print("    Booting new partition...")
        # Fire-and-forget: device reboots immediately, may not send OK
        try:
            assert self.ws is not None
            await self.ws.send("AT+OTA=BOOT\r\n")
        except Exception:
            pass

        return partition


async def upload(host: str, ota_path: str) -> int:
    """Upload and boot the OTA image. Returns the partition index written to."""
    at = ADSBeeAT(host)
    print(f"  Connecting to ws://{host}/console ...")
    upload_t0 = time.monotonic()
    await at.connect()

    try:
        await at.flush()
        await at.send_cmd("AT+LOG_LEVEL=ERRORS\r\n")
        await at.send_cmd("AT+PROTOCOL_OUT=CONSOLE,NONE\r\n")
        await at.flush()
        await at.send_cmd("AT+RX_ENABLE=0\r\n")

        return await at.ota_write_file(ota_path)

    finally:
        await at.disconnect()
        print(f"  OTA upload total (connect + erase + write + verify + boot): "
              f"{time.monotonic() - upload_t0:.1f}s")


async def get_partition(host: str) -> int:
    """Return the current complementary (inactive) partition index.

    Used after an OTA reboot to confirm the active partition flipped: the value
    reported here must differ from the partition the image was written to.
    """
    at = ADSBeeAT(host)
    await at.connect()
    try:
        await at.flush()
        await at.send_cmd("AT+PROTOCOL_OUT=CONSOLE,NONE\r\n")
        await at.flush()
        return await at.ota_get_partition()
    finally:
        await at.disconnect()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("host", help="Device hostname or IP (e.g. cibee.local)")
    parser.add_argument("ota_file", help="Path to .ota firmware file")
    args = parser.parse_args()

    asyncio.run(upload(args.host, args.ota_file))


if __name__ == "__main__":
    main()
