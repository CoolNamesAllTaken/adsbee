"""Remote ID release test: two ADSBee 1090s transmit and receive Broadcast Remote ID over Bluetooth.

The units hear each other, so no host Bluetooth adapter is needed. Each unit's side (``run_unit``)
holds the unit's lock, sets Remote ID up for its role without saving, watches the console (and
``/metrics`` when the unit's host is known) for the run, then restores what it found. ``run_case``
starts both sides, locally or over ssh, and judges the case. See ci/hil/README.md.
"""

import json
import os
import re
import shlex
import signal
import statistics
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple

from .console import AtConsole

BLE = "BT4+BT5_LR"


@dataclass
class Role:
    rx: Optional[str] = None  # Receive transports, None = receive off.
    tx: Optional[str] = None  # Transmit transports, None = transmit off.

    def __str__(self) -> str:
        parts = ([f"RX {self.rx}"] if self.rx else []) + ([f"TX {self.tx}"] if self.tx else [])
        return " + ".join(parts) or "Remote ID off"


# Case -> (unit A's role, unit B's role). Every receiver counts the other unit's frames.
CASES: Dict[str, Tuple[Role, Role]] = {
    "rxtx": (Role(rx=BLE, tx=BLE), Role(rx=BLE, tx=BLE)),
    "tx-bt4": (Role(tx="BT4"), Role(rx=BLE)),
    "tx-bt5lr": (Role(tx="BT5_LR"), Role(rx=BLE)),
    "tx-both": (Role(tx=BLE), Role(rx=BLE)),
    "rx-only": (Role(rx=BLE, tx=BLE), Role(rx=BLE)),
    "off": (Role(), Role()),
}
CASE_HELP = {
    "rxtx": "both units receive and transmit BT4+BT5_LR; each must hear the other",
    "tx-bt4": "A transmits BT4 only (receive off); B receives",
    "tx-bt5lr": "A transmits BT5_LR only (receive off); B receives",
    "tx-both": "A transmits BT4+BT5_LR (receive off); B receives",
    "rx-only": "A receives and transmits; B receives only",
    "off": "Remote ID off on both: decode and heap baseline",
}
DEFAULT_UAS_IDS = ("ADSBEEBENCHA", "ADSBEEBENCHB")  # Bench UAS IDs, sent with no position.

ANSI = re.compile(r"\x1b\[[0-9;]*m")
SECRET = re.compile(r"WIFI_AP=|WIFI_STA=|OTA Key|PASSW|SSID", re.IGNORECASE)
HEARTBEAT = re.compile(r"\[ADSBeeServer::Update\].*heap: (\d+)K free")
WD_SCAN = re.compile(r"Bluetooth scan stalled")
WD_ADV = re.compile(r"Bluetooth advertising stalled \(set (\d+)\)")
HOST_RESET = re.compile(r"Bluetooth host reset, reason=(-?\d+)")
BLE_ERROR = re.compile(r"remote_id_ble.*failed", re.IGNORECASE)
HEAP_PAUSE = re.compile(r"ServiceHeapWatch")
SPI_ERROR = re.compile(r"SPICoprocessor.*\[ESP32\].*(Timed out|Failed)|Unable to read ESP32 status")
NOTABLE = re.compile(r"rror|ERROR|arning|WARN|[Rr]eset|[Bb]oot|stalled|anic|abort|Guru")
QUIET_NOTE = re.compile(r"IPWANTask|Corrected .* error|Reset Reason")  # Routine lines.
RID_JSON = re.compile(r"\{[^{}]*\"type\":\"remote_id\"[^{}]*\}")
HEARTBEAT_GAP_S = 10.0  # The ESP32 logs a heartbeat every second at LOG_LEVEL=INFO.


def parse_rid_query(text: str, key: str) -> Optional[Dict[str, str]]:
    """AT+REMOTE_ID? or AT+REMOTE_ID_TX? reply to {field: value}, fields named by their (LABEL) suffixes."""
    m = re.search(rf"^\+?{key}=(.*)$", text, re.MULTILINE)
    if not m:
        return None
    first, _, rest = m.group(1).partition(",")
    out = {"ENABLED": first.strip()}
    for value, label in re.findall(r"(?:^|,)(.*?)\(([A-Z_0-9]+)\)(?=,|$)", rest.strip()):
        out[label] = value
    return out


def transports_arg(value: str) -> str:
    """A transports field as an AT argument: names pass through, rc8-style masks become names."""
    if re.fullmatch(r"0x[0-9A-Fa-f]+|\d+", value or ""):
        mask = int(value, 0)
        names = [n for bit, n in ((1, "BT4"), (2, "BT5_LR"), (4, "WIFI_BEACON")) if mask & bit]
        return "+".join(names) or "NONE"
    return value or "NONE"


def status_words(fields: Optional[Dict[str, str]]) -> List[str]:
    return [w for w in (fields or {}).get("ESP32_STATUS", "").split("+") if w and w != "NONE"]


def expected_status(role: Role) -> List[str]:
    want = []
    if role.rx:
        want += ["BT_SCANNING"] + (["BT5_LR_SCANNING"] if "BT5_LR" in role.rx else [])
    if role.tx:
        want += [w for t, w in (("BT4", "TX_BT4"), ("BT5_LR", "TX_BT5_LR")) if t in role.tx.split("+")]
        want += ["TX_NO_POSITION"]
    return want


def _noise(line: str) -> bool:
    """Console lines that are not AT replies: coprocessor logs and aircraft JSON."""
    return line.startswith("CoProcessor:") or line.startswith("{")


class UnitSession:
    """An open console: a reader thread keeps every line (secrets dropped) and classifies events."""

    def __init__(self, console: AtConsole, peer_uas_id: Optional[str] = None):
        self.c = console
        self.peer = peer_uas_id
        self.lines: List[Tuple[float, str]] = []
        self.events: List[Tuple[float, str, object]] = []
        self.error: Optional[str] = None
        self._mutex = threading.Lock()
        self._stop = threading.Event()
        self._raw: List[Tuple[float, str]] = []  # Unredacted lines, only for AT replies.
        self._t = threading.Thread(target=self._run, daemon=True)
        self._t.start()

    def _run(self) -> None:
        buf = b""
        while not self._stop.is_set():
            try:
                d = self.c.read(65536)
            except Exception as e:  # noqa: BLE001 - USB re-enumeration, unplug
                self.error = f"console read failed: {e}"
                return
            if not d:
                continue
            now = time.time()
            buf += d
            *done, buf = buf.split(b"\n")
            for raw in done:
                line = ANSI.sub("", raw.decode(errors="replace")).strip()
                if line:
                    self._add(now, line)

    def _add(self, t: float, line: str) -> None:
        ev = []
        m = HEARTBEAT.search(line)
        if m:
            ev.append(("heap_kb", int(m.group(1))))
        if WD_SCAN.search(line):
            ev.append(("wd_scan", 1))
        m = WD_ADV.search(line)
        if m:
            ev.append(("wd_adv", int(m.group(1))))
        m = HOST_RESET.search(line)
        if m:
            ev.append(("host_reset", int(m.group(1))))
        if BLE_ERROR.search(line):
            ev.append(("ble_error", line[:200]))
        if HEAP_PAUSE.search(line):
            ev.append(("heap_pause", line[:200]))
        if SPI_ERROR.search(line):
            ev.append(("spi_error", line[:200]))
        if NOTABLE.search(line) and not QUIET_NOTE.search(line) and not SECRET.search(line):
            ev.append(("note", line[:240]))
        for o in RID_JSON.findall(line):
            try:
                rid = json.loads(o)
            except ValueError:
                continue
            if self.peer and rid.get("rid_uas_id", rid.get("flight")) == self.peer:
                ev.append(("rid_report", rid.get("rssi")))
        with self._mutex:
            self._raw.append((t, line))
            self.lines.append((t, "<redacted>" if SECRET.search(line) else line))
            self.events.extend((t, k, v) for k, v in ev)

    def mark(self) -> int:
        with self._mutex:
            return len(self._raw)

    def at(self, cmd: str, timeout: float = 4.0, quiet: float = 0.4) -> str:
        """Sends one command; returns its reply lines (raw: don't log them).

        Ends at OK/ERROR, or ``quiet`` seconds after the last reply line (queries print no OK).
        """
        k = self.mark()
        self.c.write((cmd + "\r\n").encode())
        deadline = time.time() + timeout
        while time.time() < deadline:
            time.sleep(0.03)
            with self._mutex:
                got = [(t, l) for t, l in self._raw[k:] if not _noise(l)]
            if any(re.match(r"^(OK|ERROR)", l) for _, l in got):
                break
            if got and time.time() - got[-1][0] > quiet:
                break
        with self._mutex:
            return "\n".join(l for _, l in self._raw[k:] if not _noise(l))

    def events_between(self, t0: float, t1: float) -> List[Tuple[float, str, object]]:
        with self._mutex:
            return [e for e in self.events if t0 <= e[0] < t1]

    def heartbeat_gaps(self, t0: float, t1: float) -> List[float]:
        """Gaps of HEARTBEAT_GAP_S or more between ESP32 heartbeats in [t0, t1): an ESP32 reboot or hang."""
        ts = [t for t, k, _ in self.events_between(t0 - HEARTBEAT_GAP_S, t1) if k == "heap_kb"]
        ts = [t0] + ts + [t1] if ts else []
        return [round(b - a, 1) for a, b in zip(ts, ts[1:]) if b - a >= HEARTBEAT_GAP_S]

    def close(self) -> None:
        self._stop.set()
        self._t.join(timeout=2)


class MetricsSampler:
    """Reads ws://<host>/metrics on a thread: per-second dictionary counters and ESP32 status."""

    KEYS = ("valid_remote_id_frames", "valid_squitter_frames", "valid_extended_squitter_frames",
            "valid_uat_adsb_frames", "valid_uat_uplink_frames", "num_mode_s_aircraft", "num_remote_id_aircraft")

    def __init__(self, host: str):
        self.host = host
        self.samples: List[Dict] = []  # {"t", KEYS...}
        self.status: List[Dict] = []  # {"t", "heap", "esp_up"}
        self.errors: List[str] = []
        self._stop = threading.Event()
        self._t = threading.Thread(target=self._thread, daemon=True)

    def start(self) -> "MetricsSampler":
        self._t.start()
        return self

    def _thread(self) -> None:
        import asyncio

        asyncio.run(self._run())

    async def _run(self) -> None:
        import asyncio

        import websockets  # pip install 'adsbee-hil[ota]'

        while not self._stop.is_set():
            try:
                async with websockets.connect(f"ws://{self.host}/metrics", open_timeout=10,
                                              ping_interval=None) as ws:
                    last_ping = time.time()
                    while not self._stop.is_set():
                        if time.time() - last_ping > 30:  # The server drops clients silent for 90 s.
                            await ws.send("ping")
                            last_ping = time.time()
                        try:
                            msg = json.loads(await asyncio.wait_for(ws.recv(), 2))
                        except asyncio.TimeoutError:
                            continue
                        now = time.time()
                        a = msg.get("aircraft_dictionary_metrics")
                        if a:
                            self.samples.append({"t": now, **{k: a.get(k, 0) for k in self.KEYS}})
                        e = (msg.get("device_status") or {}).get("esp32")
                        if e:
                            self.status.append({"t": now, "heap": e.get("heap_free_bytes"),
                                                "esp_up": e.get("uptime_ms")})
            except Exception as e:  # noqa: BLE001 - keep sampling through network hiccups
                self.errors.append(f"{time.strftime('%H:%M:%S')} {str(e)[:120]}")
                await asyncio.sleep(3)

    def stop(self) -> None:
        self._stop.set()
        self._t.join(timeout=5)

    def window(self, t0: float, t1: float) -> Dict:
        s = [x for x in self.samples if t0 <= x["t"] < t1]
        st = [x for x in self.status if t0 <= x["t"] < t1]
        n = len(s)
        out = {"metrics_s": n}
        if n:
            rid = sum(x["valid_remote_id_frames"] for x in s)
            out.update(rid_frames=rid, rid_per_s=round(rid / n, 2),
                       modes_per_s=round(sum(x["valid_squitter_frames"] + x["valid_extended_squitter_frames"]
                                             for x in s) / n, 1),
                       uat_per_s=round(sum(x["valid_uat_adsb_frames"] + x["valid_uat_uplink_frames"]
                                           for x in s) / n, 2),
                       aircraft=round(statistics.mean(x["num_mode_s_aircraft"] for x in s), 1))
        heaps = [x["heap"] for x in st if x["heap"]]
        if heaps:
            out.update(heap_min_kb=round(min(heaps) / 1024, 1), heap_med_kb=round(statistics.median(heaps) / 1024, 1))
        return out

    def esp32_reboots(self, t0: float, t1: float) -> int:
        ups = [x["esp_up"] for x in self.status if t0 <= x["t"] < t1 and x["esp_up"] is not None]
        return sum(1 for a, b in zip(ups, ups[1:]) if b < a)


class UnitError(RuntimeError):
    pass


def _found_state(s: UnitSession) -> Dict:
    info = s.at("AT+DEVICE_INFO?", 6)
    state = {
        "versions": dict(re.findall(r"^(\w+) Firmware Version: (\S+)", info, re.MULTILINE)),
        "psram": (re.search(r"ESP32 PSRAM: (.*)", info) or [None, "?"])[1].strip(),
        "rx": parse_rid_query(s.at("AT+REMOTE_ID?"), "REMOTE_ID"),
        "tx": parse_rid_query(s.at("AT+REMOTE_ID_TX?"), "REMOTE_ID_TX"),
        "log_level": (re.search(r"LOG_LEVEL=(\w+)", s.at("AT+LOG_LEVEL?")) or [None, None])[1],
        "console_protocol": (re.search(r"PROTOCOL_OUT=CONSOLE,(\w+)", s.at("AT+PROTOCOL_OUT?")) or [None, None])[1],
        "position_source": (re.search(r"Source: (\w+)", s.at("AT+RX_POSITION?")) or [None, None])[1],
        "feed_enable": (re.search(r"FEED_ENABLE=(\d)", s.at("AT+FEED_ENABLE?")) or [None, None])[1],
        "uptime_s": _uptime(s),
        "esp32_reset_reason": _reset_reason(s),
        "config_hash": _config_hash(s),
    }
    m = re.search(r"^\+?WIFI_AP=(\d)", s.at("AT+WIFI_AP?"), re.MULTILINE)  # Rest of the line is secret.
    state["wifi_ap"] = m.group(1) if m else None
    if not state["rx"] or not state["tx"]:
        raise UnitError("no AT+REMOTE_ID? / AT+REMOTE_ID_TX? reply: not an ADSBee 1090 with Remote ID")
    return state


def _uptime(s: UnitSession) -> Optional[int]:
    m = re.search(r"UPTIME=(\d+)", s.at("AT+UPTIME?"))
    return int(m.group(1)) if m else None


def _reset_reason(s: UnitSession) -> Optional[str]:
    m = re.search(r"ESP32 Reset Reason: (.*)", s.at("AT+ESP32_REBOOT_INFO?"))
    return m.group(1).strip() if m else None


def _config_hash(s: UnitSession) -> str:
    return " ".join(re.findall(r"\w+=0x[0-9A-Fa-f]+", s.at("AT+CONFIG_HASH?", 6)))


def _ok(reply: str) -> bool:
    return bool(re.search(r"^OK", reply, re.MULTILINE)) and "ERROR" not in reply


def _apply(s: UnitSession, role: Role, uas_id: str, log: Callable[[str], None]) -> List[str]:
    """Sets the role (never saved). Returns the commands that failed."""
    failed = []
    cmds = [f"AT+REMOTE_ID_TX=1,{role.tx},{uas_id},1,0" if role.tx else "AT+REMOTE_ID_TX=0",
            f"AT+REMOTE_ID=1,{role.rx}" if role.rx else "AT+REMOTE_ID=0"]
    for cmd in cmds:
        reply = s.at(cmd, 5)
        log(f"{cmd} -> {'OK' if _ok(reply) else reply.strip()[-200:]}")
        if not _ok(reply):
            failed.append(cmd)
    return failed


def _wait_status(s: UnitSession, role: Role, timeout: float) -> Tuple[Optional[float], List[str], List[str]]:
    """Polls until the ESP32 reports the role's status words: (seconds taken or None, rx words, tx words)."""
    want = expected_status(role)
    t0 = time.time()
    rx = tx = []
    while time.time() - t0 < timeout:
        # AT+REMOTE_ID_TX? reports the receive and transmit status words together.
        words = status_words(parse_rid_query(s.at("AT+REMOTE_ID_TX?"), "REMOTE_ID_TX"))
        rx = [w for w in words if not w.startswith("TX_")]
        tx = [w for w in words if w.startswith("TX_")]
        have = set(words)
        unwanted = set(tx) if not role.tx else set()
        if all(w in have for w in want) and not unwanted and "TX_BLOCKED" not in have:
            return round(time.time() - t0, 1), rx, tx
        time.sleep(1)
    return None, rx, tx


def _restore(s: UnitSession, found: Dict, changed: Dict, log: Callable[[str], None]) -> List[str]:
    """Puts back what run_unit changed (never saved, so a reboot restores it too). Returns failures."""
    failed = []
    tx, rx = found["tx"], found["rx"]
    cmds = ["AT+REMOTE_ID_TX=0"]
    uas = tx.get("UAS_ID", "")
    op = tx.get("OPERATOR_ID", "")
    cmds.append(f"AT+REMOTE_ID_TX={tx['ENABLED']},{transports_arg(tx.get('TRANSPORTS'))},"
                f"{'-' if uas in ('', '(device serial)') else uas},{tx.get('ID_TYPE', 1)},{tx.get('UA_TYPE', 0)},"
                f"{'-' if op in ('', '(none)') else op}")
    cmds.append(f"AT+REMOTE_ID={rx['ENABLED']},{transports_arg(rx.get('TRANSPORTS'))}")
    if changed.get("console_protocol"):
        cmds.append(f"AT+PROTOCOL_OUT=CONSOLE,{found['console_protocol']}")
    if changed.get("wifi_ap"):
        cmds.append("AT+WIFI_AP=1")
    if found.get("log_level"):
        cmds.append(f"AT+LOG_LEVEL={found['log_level']}")
    for cmd in cmds:
        reply = s.at(cmd, 5)
        if not _ok(reply):
            failed.append(f"{cmd}: {reply.strip()[-160:]}")
    log(f"restored ({len(cmds)} commands, {len(failed)} failed)")
    return failed


def run_unit(receiver, role: Role, uas_id: str, peer_uas_id: Optional[str], start_at: float, duration_s: float,
             window_s: float = 60.0, metrics_host: Optional[str] = None, wifi_ap_off: bool = False,
             emit: Callable[[Dict], None] = print, log: Callable[[str], None] = print) -> Dict:
    """One unit's side of a case. Holds the unit's lock from setup to restore; returns the summary record."""
    with receiver.console() as console:
        s = UnitSession(console, peer_uas_id if role.rx else None)
        sampler = None
        found: Optional[Dict] = None
        changed: Dict[str, bool] = {}
        summary: Dict = {"ev": "end", "unit": receiver.id, "role": str(role), "errors": []}
        try:
            s.at("AT+UPTIME?")  # Flushes a partial line left by an earlier client.
            found = _found_state(s)
            emit({"ev": "start", "unit": receiver.id, "role": str(role), "uas_id": uas_id if role.tx else None,
                  "peer_uas_id": peer_uas_id, "metrics_host": metrics_host, "start_at": start_at,
                  "found": {k: v for k, v in found.items() if k not in ("rx", "tx")},
                  "found_rx": found["rx"], "found_tx": found["tx"]})
            log(f"found: {found['versions']}, PSRAM {found['psram']}, RX {found['rx'].get('ENABLED')} "
                f"{found['rx'].get('TRANSPORTS')}, TX {found['tx'].get('ENABLED')}, log {found['log_level']}, "
                f"position source {found['position_source']}, WiFi AP {found['wifi_ap']}")
            if role.tx and found["position_source"] in ("FIXED", "GNSS"):
                raise UnitError(f"AT+RX_POSITION source is {found['position_source']}: transmitting would "
                                "broadcast this unit's position. Use a unit whose source is NONE, LOWEST or ICAO.")
            if (role.rx or role.tx) and found["wifi_ap"] == "1" and found["psram"] == "NONE":
                if not wifi_ap_off:
                    raise UnitError("no PSRAM and WiFi AP on: Remote ID can't run (pass --wifi-ap-off to turn the "
                                    "AP off for the run; it is turned back on afterwards)")
                s.at("AT+WIFI_AP=0", 5)
                changed["wifi_ap"] = True
                time.sleep(4)
            s.at("AT+LOG_LEVEL=INFO")  # Heartbeat (heap) and watchdog lines are INFO.
            if role.rx and peer_uas_id and not metrics_host:
                s.at("AT+PROTOCOL_OUT=CONSOLE,AIRCRAFT_JSON")
                changed["console_protocol"] = True
            t_cmd = time.time()
            failed = _apply(s, role, uas_id, log)
            applied_s, rx_words, tx_words = _wait_status(s, role, 20)
            emit({"ev": "status", "unit": receiver.id, "failed_commands": failed, "applied_s": applied_s,
                  "rx_status": rx_words, "tx_status": tx_words, "want": expected_status(role)})
            if failed:
                raise UnitError(f"refused: {failed}")
            if role.tx and "TX_NO_POSITION" not in tx_words:
                raise UnitError(f"transmit status {tx_words} lacks TX_NO_POSITION: stopped to avoid sending a position")
            log(f"status after {applied_s if applied_s is not None else '>20'} s: RX {'+'.join(rx_words) or '-'}, "
                f"TX {'+'.join(tx_words) or '-'} (not saved)")
            summary.update(applied_s=applied_s, setup_s=round(time.time() - t_cmd, 1))
            if metrics_host:
                sampler = MetricsSampler(metrics_host).start()
            while time.time() < start_at - 3:
                time.sleep(0.2)
            uptime0, t_up0 = _uptime(s), time.time()
            reason0 = _reset_reason(s)
            n_windows = max(1, int(round(duration_s / window_s)))
            for i in range(n_windows):
                t0 = start_at + i * window_s
                t1 = t0 + window_s
                while time.time() < t1:
                    if s.error:
                        raise UnitError(s.error)
                    time.sleep(0.2)
                emit(_window_record(s, sampler, receiver.id, role, peer_uas_id, i, t0, t1))
            uptime1 = _uptime(s)
            elapsed = time.time() - t_up0
            summary["rp2040_uptime_s"] = [uptime0, uptime1, round(elapsed)]
            summary["rp2040_reboots"] = int(uptime0 is not None and uptime1 is not None and
                                            uptime1 + 5 < uptime0 + elapsed)
            summary["esp32_reset_reason"] = [reason0, _reset_reason(s)]
            summary["status_end"] = status_words(parse_rid_query(s.at("AT+REMOTE_ID_TX?"), "REMOTE_ID_TX"))
        except UnitError as e:
            summary["errors"].append(str(e))
            log(f"ERROR: {e}")
        finally:
            if sampler:
                sampler.stop()
                summary["metrics_errors"] = sampler.errors[-5:]
            try:
                if found:
                    summary["restore_failed"] = _restore(s, found, changed, log)
                    summary["config_hash_restored"] = _config_hash(s) == found["config_hash"]
            except Exception as e:  # noqa: BLE001
                summary["errors"].append(f"restore: {e}")
            s.close()
        emit(summary)
        return summary


def _window_record(s: UnitSession, sampler: Optional[MetricsSampler], unit: str, role: Role,
                   peer: Optional[str], i: int, t0: float, t1: float) -> Dict:
    ev = s.events_between(t0, t1)
    heaps = [v for _, k, v in ev if k == "heap_kb"]
    rid = [v for _, k, v in ev if k == "rid_report"]
    rec = {"ev": "window", "unit": unit, "i": i, "t0": round(t0, 1), "s": round(t1 - t0, 1),
           "wd_scan": sum(1 for _, k, _ in ev if k == "wd_scan"),
           "wd_adv": sum(1 for _, k, _ in ev if k == "wd_adv"),
           "host_resets": sum(1 for _, k, _ in ev if k == "host_reset"),
           "ble_errors": sum(1 for _, k, _ in ev if k == "ble_error"),
           "heap_pauses": sum(1 for _, k, _ in ev if k == "heap_pause"),
           "spi_errors": sum(1 for _, k, _ in ev if k == "spi_error"),
           "heartbeat_gaps_s": s.heartbeat_gaps(t0, t1),
           "notes": [f"{time.strftime('%H:%M:%S', time.gmtime(t))} {v}" for t, k, v in ev if k == "note"][:30]}
    if heaps:
        rec.update(heap_min_kb=min(heaps), heap_med_kb=statistics.median(heaps))
    if sampler:
        rec.update(sampler.window(t0, t1))
        rec["esp32_reboots"] = sampler.esp32_reboots(t0 - 5, t1)
    else:
        rec["esp32_reboots"] = len(rec["heartbeat_gaps_s"])
    if role.rx and peer and not sampler:
        # Console only: the peer's aircraft JSON contact. Its RSSI changes when new frames arrive; the
        # contact itself stays for 60 s after the last frame.
        rec["rid_reports"] = len(rid)
        rec["rid_rssi_changes"] = sum(1 for a, b in zip(rid, rid[1:]) if a != b)
    return rec


# -- the two-unit case ----------------------------------------------------------------------------


@dataclass
class UnitSpec:
    """'[SSH_HOST:]DEVICE': a bench id or USB serial, on this host or on SSH_HOST."""

    ssh: Optional[str]
    device: str
    metrics_host: Optional[str] = None

    @classmethod
    def parse(cls, text: str, metrics_host: Optional[str] = None) -> "UnitSpec":
        ssh, _, dev = text.rpartition(":")
        return cls(ssh or None, dev, metrics_host)

    def __str__(self) -> str:
        return f"{self.ssh}:{self.device}" if self.ssh else self.device


def unit_command(spec: UnitSpec, role: Role, uas_id: str, peer: Optional[str], start_at: float, minutes: float,
                 window_s: float, wifi_ap_off: bool, config: Optional[str], remote_hil: str,
                 remote_config: Optional[str], lock_timeout: float) -> List[str]:
    args = ["remote-id-unit", spec.device, "--uas-id", uas_id, "--start-at", f"{start_at:.1f}",
            "--minutes", str(minutes), "--window", str(window_s)]
    if role.rx:
        args += ["--rx", role.rx]
    if role.tx:
        args += ["--tx", role.tx]
    if peer:
        args += ["--peer-uas-id", peer]
    if spec.metrics_host:
        args += ["--host", spec.metrics_host]
    if wifi_ap_off:
        args += ["--wifi-ap-off"]
    common = ["--lock-timeout", str(lock_timeout)]
    if spec.ssh:
        def q(a: str) -> str:  # Quoted for the remote shell; a leading ~/ still expands there.
            return "~/" + shlex.quote(a[2:]) if a.startswith("~/") else shlex.quote(a)
        cfg = ["-c", remote_config] if remote_config else []
        remote = " ".join([q(a) for a in shlex.split(remote_hil)] + [q(a) for a in cfg + common + args])
        return ["ssh", "-o", "BatchMode=yes", "-o", "ServerAliveInterval=30", spec.ssh, remote]
    cfg = ["-c", config] if config else []
    return [sys.executable, "-m", "adsbee_hil"] + cfg + common + args


def run_case(case: str, a: UnitSpec, b: UnitSpec, minutes: float, window_s: float = 60.0, setup_s: float = 45.0,
             uas_ids: Tuple[str, str] = DEFAULT_UAS_IDS, wifi_ap_off: bool = False, config: Optional[str] = None,
             remote_hil: str = "adsbee-hil", remote_config: Optional[str] = None, lock_timeout: float = 600.0,
             json_path: Optional[str] = None, out: Callable[[str], None] = print) -> int:
    """Runs one case on units A and B at the same time; prints per-minute lines and a verdict. 0 = pass."""
    roles = CASES[case]
    specs = (a, b)
    names = ("A", "B")
    start_at = time.time() + setup_s
    records: Dict[str, List[Dict]] = {"A": [], "B": []}
    procs = []
    jf = open(json_path, "a", buffering=1) if json_path else None
    out(f"remote-id {case}: {CASE_HELP[case]}")
    for n, spec, role, uas, peer_i in zip(names, specs, roles, uas_ids, (1, 0)):
        peer_role = roles[peer_i]
        peer = uas_ids[peer_i] if (role.rx and peer_role.tx) else None
        out(f"  {n} = {spec}: {role}" + (f", UAS ID {uas}" if role.tx else "") +
            (f", counts {peer}" if peer else "") + (f", /metrics {spec.metrics_host}" if spec.metrics_host else ""))
        cmd = unit_command(spec, role, uas, peer, start_at, minutes, window_s, wifi_ap_off, config, remote_hil,
                           remote_config, lock_timeout)
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, bufsize=1,
                             start_new_session=True)
        procs.append(p)
    out(f"  measuring {minutes:g} min from {time.strftime('%H:%M:%S', time.localtime(start_at))}, "
        f"{window_s:g} s windows; settings are never saved")

    def pump(n: str, p: subprocess.Popen) -> None:
        for line in p.stdout:
            line = line.strip()
            if not line.startswith("{"):
                continue
            try:
                r = json.loads(line)
            except ValueError:
                continue
            records[n].append(r)
            if jf:
                jf.write(json.dumps({"case": case, "unit": n, **r}) + "\n")
            if r.get("ev") == "window":
                out(f"  {n} {format_window(r)}")

    def errs(n: str, p: subprocess.Popen) -> None:
        for line in p.stderr:
            if line.strip() and "setlocale" not in line:
                out(f"  {n}: {line.rstrip()}")

    threads = [threading.Thread(target=f, args=(n, p), daemon=True)
               for n, p in zip(names, procs) for f in (pump, errs)]
    for t in threads:
        t.start()
    try:
        for p in procs:
            p.wait()
    except KeyboardInterrupt:
        for p in procs:
            os.killpg(p.pid, signal.SIGTERM)  # The unit side restores on SIGTERM.
        for p in procs:
            p.wait()
        raise
    for t in threads:
        t.join(timeout=5)
    verdict, lines = judge(case, records, minutes, window_s)
    for line in lines:
        out(line)
    if jf:
        jf.write(json.dumps({"case": case, "verdict": verdict, "summary": lines}) + "\n")
        jf.close()
    return 0 if verdict == "PASS" else 1


def format_window(r: Dict) -> str:
    parts = [f"min {r['i'] + 1:>3}"]
    if "rid_per_s" in r:
        parts.append(f"rid {r['rid_per_s']:5.2f}/s")
    elif "rid_reports" in r:
        parts.append(f"rid contact {r['rid_reports']:3d} reports, {r['rid_rssi_changes']:3d} RSSI changes")
    if "modes_per_s" in r:
        parts.append(f"Mode S {r['modes_per_s']:6.1f}/s, UAT {r['uat_per_s']:5.2f}/s, {r['aircraft']:4.1f} ac")
    if "heap_min_kb" in r:
        parts.append(f"heap {r['heap_min_kb']}/{r['heap_med_kb']} kB")
    parts.append(f"wd scan {r['wd_scan']} adv {r['wd_adv']}, host resets {r['host_resets']}")
    if r.get("esp32_reboots"):
        parts.append(f"ESP32 REBOOT x{r['esp32_reboots']}")
    if r.get("heap_pauses"):
        parts.append(f"heap pauses {r['heap_pauses']}")
    return ", ".join(parts)


def _heard(r: Dict) -> Optional[bool]:
    if "rid_frames" in r:
        return r["rid_frames"] > 0
    if "rid_reports" in r:
        return r["rid_rssi_changes"] > 0
    return None


def judge(case: str, records: Dict[str, List[Dict]], minutes: float, window_s: float) -> Tuple[str, List[str]]:
    """Pass: every receiver heard its peer in every window, no ESP32 or RP2040 reboot, status as asked,
    settings restored."""
    lines, fail = [], []
    roles = dict(zip("AB", CASES[case]))
    want_windows = max(1, int(round(minutes * 60 / window_s)))
    for n in "AB":
        recs = records[n]
        start = next((r for r in recs if r.get("ev") == "start"), {})
        status = next((r for r in recs if r.get("ev") == "status"), {})
        end = next((r for r in recs if r.get("ev") == "end"), {})
        wins = [r for r in recs if r.get("ev") == "window"]
        unit = start.get("unit", n)
        role = roles[n]
        s = [f"{n} {unit} ({role})"]
        if start.get("found", {}).get("versions"):
            s.append("fw " + "/".join(sorted(set(start["found"]["versions"].values()))))
        if end.get("errors"):
            fail.append(f"{n}: {'; '.join(end['errors'])}")
        if not end:
            fail.append(f"{n}: no result (unit side failed)")
        if len(wins) < want_windows:
            fail.append(f"{n}: {len(wins)} of {want_windows} windows")
        if status:
            missing = [w for w in status.get("want", []) if w not in status.get("rx_status", []) +
                       status.get("tx_status", [])]
            s.append(f"status in {status.get('applied_s')} s without save" if not missing else
                     f"status missing {missing}")
            if missing:
                fail.append(f"{n}: status missing {missing}")
        heard = [_heard(r) for r in wins]
        if role.rx and roles["B" if n == "A" else "A"].tx and wins:
            empty = sum(1 for h in heard if h is False)
            if "rid_frames" in wins[0]:
                frames = sum(r.get("rid_frames", 0) for r in wins)
                secs = sum(r.get("metrics_s", 0) for r in wins)
                s.append(f"RX {frames / max(secs, 1):.2f} frames/s, empty windows {empty}/{len(wins)}")
            else:
                s.append(f"RX (console, RSSI changes) quiet windows {empty}/{len(wins)}")
            if empty:
                fail.append(f"{n}: {empty} window(s) without Remote ID from the peer")
        reboots = sum(r.get("esp32_reboots", 0) for r in wins)
        rp = end.get("rp2040_reboots", 0)
        reasons = end.get("esp32_reset_reason") or [None, None]
        if reasons[0] != reasons[1] and not reboots:
            reboots = 1  # Missed by the counters, but the ESP32's last reset reason changed.
        s.append(f"ESP32 reboots {reboots}" + (f", RP2040 reboots {rp}" if rp else ""))
        if reboots or rp:
            fail.append(f"{n}: {reboots} ESP32 / {rp} RP2040 reboot(s)")
        heaps = [r["heap_min_kb"] for r in wins if "heap_min_kb" in r]
        meds = [r["heap_med_kb"] for r in wins if "heap_med_kb" in r]
        if heaps:
            s.append(f"heap min {min(heaps)} kB, median {statistics.median(meds)} kB")
        ms = [r["modes_per_s"] for r in wins if "modes_per_s" in r]
        if ms:
            s.append(f"Mode S {statistics.mean(ms):.1f}/s, UAT "
                     f"{statistics.mean(r['uat_per_s'] for r in wins if 'uat_per_s' in r):.2f}/s, "
                     f"{statistics.mean(r['aircraft'] for r in wins if 'aircraft' in r):.1f} aircraft")
        s.append(f"watchdog resets scan {sum(r['wd_scan'] for r in wins)} adv {sum(r['wd_adv'] for r in wins)}, "
                 f"host resets {sum(r['host_resets'] for r in wins)}, BLE errors {sum(r['ble_errors'] for r in wins)}"
                 + (f", heap pauses {sum(r['heap_pauses'] for r in wins)}" if any(r['heap_pauses'] for r in wins)
                    else ""))
        if end and (end.get("restore_failed") or end.get("config_hash_restored") is False):
            fail.append(f"{n}: settings not restored ({end.get('restore_failed') or 'CONFIG_HASH differs'})")
        elif end:
            s.append("restored")
        lines.append("  " + "; ".join(s))
    verdict = "FAIL" if fail else "PASS"
    lines.append(f"RESULT {case}: {verdict}" + (" - " + "; ".join(fail) if fail else ""))
    return verdict, lines


# -- guards ---------------------------------------------------------------------------------------


def check_guards(receiver, log: Callable[[str], None] = print) -> bool:
    """Checks that the unit refuses Remote ID transports its RAM can't run next to its network.

    Read-only: refused commands change nothing, and nothing is sent that would be accepted.
    """
    with receiver.console() as console:
        s = UnitSession(console)
        try:
            s.at("AT+UPTIME?")
            found = _found_state(s)
            eth = (re.search(r"ETHERNET=(\d)", s.at("AT+ETHERNET?")) or [None, "0"])[1] == "1"
            sta = (re.search(r"^\+?WIFI_STA=(\d)", s.at("AT+WIFI_STA?"), re.MULTILINE) or [None, "0"])[1] == "1"
            ap = found["wifi_ap"] == "1"
            psram = found["psram"] not in ("NONE", "UNKNOWN", "?")
            allowed = found["rx"].get("ALLOWED_TRANSPORTS", "")
            want = ("BT4+BT5_LR+WIFI_BEACON" if psram or not (ap or sta or eth)
                    else "NONE" if (ap or sta) else "BT4+BT5_LR")
            ok = allowed == want
            log(f"PSRAM {found['psram']}, WiFi AP {int(ap)}, WiFi STA {int(sta)}, Ethernet {int(eth)}: allowed "
                f"{allowed} (expected {want}) {'OK' if ok else 'WRONG'}")
            refused = [t for t in ("BT4", "BT5_LR", "WIFI_BEACON") if t not in want.split("+")]
            for t in refused:
                for cmd in (f"AT+REMOTE_ID=1,{t}", f"AT+REMOTE_ID_TX=1,{t}"):
                    reply = s.at(cmd, 5)
                    good = "ERROR" in reply and "PSRAM" in reply
                    ok &= good
                    log(f"{cmd} -> {'refused (PSRAM message) OK' if good else 'NOT REFUSED: ' + reply.strip()[-160:]}")
                    if not good and "ERROR" not in reply:
                        _restore(s, found, {}, log)
            if not refused:
                log("every transport allowed here: no refusal to check")
            same = _config_hash(s) == found["config_hash"]
            ok &= same
            log(f"settings unchanged: {'yes' if same else 'NO'}")
            return ok
        finally:
            s.close()
