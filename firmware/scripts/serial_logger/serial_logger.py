#!/usr/bin/env python3
"""
serial_logger.py — Generic multi-serial-port timestamped logger

Usage:
  python serial_logger.py --port DEV:BAUD[:LABEL] [--port ...] [--output FILE] [--gui]

Examples:
  python serial_logger.py \\
      --port /dev/tty.usbmodem1234:115200:RP2040 \\
      --port /dev/tty.usbmodem5678:115200:ESP32 \\
      --output session.log

  python serial_logger.py \\
      --port /dev/tty.usbmodem1234:115200:RP2040 \\
      --port /dev/tty.usbmodem5678:115200:ESP32 \\
      --gui
"""

from __future__ import annotations

import argparse
import queue
import signal
import sys
import threading
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional

import serial
import serial.serialutil


# ─── Colors ───────────────────────────────────────────────────────────────────

ANSI_COLORS = ["\033[36m", "\033[33m", "\033[32m", "\033[35m", "\033[34m", "\033[31m"]
ANSI_RESET = "\033[0m"

# Rich/Textual color names (same hue order as ANSI_COLORS)
RICH_COLORS = ["cyan", "yellow", "green", "magenta", "blue", "red"]


# ─── Data model ───────────────────────────────────────────────────────────────

@dataclass
class PortConfig:
    device: str
    baud: int
    label: str
    color_idx: int


@dataclass
class LogEntry:
    port: PortConfig
    line: str
    timestamp: datetime


# ─── Reader thread ────────────────────────────────────────────────────────────

class ReaderThread(threading.Thread):
    def __init__(
        self,
        port: PortConfig,
        log_queue: "queue.Queue[LogEntry]",
        stop_event: threading.Event,
    ):
        super().__init__(daemon=True, name=f"reader-{port.label}")
        self.port = port
        self.queue = log_queue
        self.stop = stop_event
        self.connected = False

    def run(self) -> None:
        while not self.stop.is_set():
            try:
                with serial.Serial(self.port.device, self.port.baud, timeout=0.1) as ser:
                    self.connected = True
                    while not self.stop.is_set():
                        raw = ser.readline()
                        if raw:
                            ts = datetime.now()
                            text = raw.decode("utf-8", errors="replace").rstrip("\r\n")
                            self.queue.put(LogEntry(self.port, text, ts))
            except (serial.SerialException, OSError):
                self.connected = False
                if not self.stop.is_set():
                    time.sleep(2.0)


# ─── Shared helpers ───────────────────────────────────────────────────────────

def _fmt_ts(ts: datetime) -> str:
    return ts.strftime("%H:%M:%S.") + f"{ts.microsecond // 1000:03d}"


# ─── CLI mode ─────────────────────────────────────────────────────────────────

def run_cli(
    ports: list[PortConfig],
    log_queue: "queue.Queue[LogEntry]",
    stop_event: threading.Event,
    output: Optional[Path],
) -> None:
    label_width = max(len(p.label) for p in ports)
    file = open(output, "a", encoding="utf-8") if output else None

    try:
        while not stop_event.is_set():
            try:
                entry = log_queue.get(timeout=0.1)
            except queue.Empty:
                continue
            _write_entry(entry, label_width, file)
        # drain on exit
        while True:
            try:
                entry = log_queue.get_nowait()
                _write_entry(entry, label_width, file)
            except queue.Empty:
                break
    finally:
        if file:
            file.close()


def _write_entry(entry: LogEntry, label_width: int, file) -> None:
    ts = _fmt_ts(entry.timestamp)
    label = entry.port.label.ljust(label_width)
    color = ANSI_COLORS[entry.port.color_idx % len(ANSI_COLORS)]
    print(f"{color}[{ts}] [{label}]{ANSI_RESET} {entry.line}")
    if file:
        file.write(f"[{ts}] [{label}] {entry.line}\n")
        file.flush()


# ─── GUI mode (Textual TUI) ───────────────────────────────────────────────────

def run_gui(
    ports: list[PortConfig],
    threads: list[ReaderThread],
    log_queue: "queue.Queue[LogEntry]",
    stop_event: threading.Event,
    output: Optional[Path],
) -> None:
    try:
        from textual.app import App, ComposeResult
        from textual.binding import Binding
        from textual.widget import Widget
        from textual.widgets import Footer, Header, RichLog, Static
        from rich.markup import escape as rich_escape
    except ImportError:
        print("error: textual is required for --gui mode.", file=sys.stderr)
        print("Install with:  pip install textual  or  poetry install", file=sys.stderr)
        sys.exit(1)

    label_width = max(len(p.label) for p in ports)
    thread_map = {t.port.label: t for t in threads}

    class PortPanel(Widget):
        DEFAULT_CSS = """
        PortPanel {
            height: 1fr;
            border: solid $panel-lighten-2;
            margin: 0 0 1 0;
        }
        PortPanel > .port-header {
            height: 1;
            background: $panel;
            padding: 0 1;
        }
        PortPanel > RichLog {
            height: 1fr;
        }
        """

        def __init__(self, port: PortConfig, **kwargs):
            super().__init__(id=f"panel-{port.label}", **kwargs)
            self._port = port

        def header_markup(self, connected: bool) -> str:
            c = RICH_COLORS[self._port.color_idx % len(RICH_COLORS)]
            dot = f"[bold {c}]●[/]" if connected else "[bold red]●[/]"
            status = "[dim]connected[/]" if connected else "[dim yellow]reconnecting…[/]"
            return (
                f"{dot} [bold {c}]{rich_escape(self._port.label)}[/]  "
                f"[dim]{rich_escape(self._port.device)}  {self._port.baud} baud[/]  "
                f"{status}"
            )

        def compose(self) -> ComposeResult:
            yield Static(
                self.header_markup(False),
                id=f"header-{self._port.label}",
                classes="port-header",
            )
            yield RichLog(
                id=f"log-{self._port.label}",
                markup=True,
                auto_scroll=True,
                highlight=False,
            )

    class SerialLoggerApp(App):
        CSS = """
        Screen {
            layout: vertical;
        }
        """
        TITLE = "Serial Logger"
        BINDINGS = [
            Binding("q", "quit", "Quit"),
            Binding("s", "save", "Save"),
            Binding("a", "toggle_scroll", "Auto-scroll"),
            Binding("c", "clear_all", "Clear"),
        ]

        def __init__(self) -> None:
            super().__init__()
            self._total = 0
            self._auto_scroll = True
            self._buffer: list[str] = []
            self._file = open(output, "a", encoding="utf-8") if output else None
            self._conn_state: dict[str, bool] = {p.label: False for p in ports}

        def compose(self) -> ComposeResult:
            yield Header(show_clock=True)
            for port in ports:
                yield PortPanel(port)
            yield Footer()

        def on_mount(self) -> None:
            self.sub_title = "Lines: 0"
            self.set_interval(0.05, self._poll)

        def _poll(self) -> None:
            # Update connection status dots
            for port in ports:
                t = thread_map[port.label]
                if t.connected != self._conn_state[port.label]:
                    self._conn_state[port.label] = t.connected
                    panel = self.query_one(f"#panel-{port.label}", PortPanel)
                    header = panel.query_one(f"#header-{port.label}", Static)
                    header.update(panel.header_markup(t.connected))

            # Drain log queue (cap per tick to stay responsive)
            count = 0
            try:
                while count < 200:
                    entry = log_queue.get_nowait()
                    c = RICH_COLORS[entry.port.color_idx % len(RICH_COLORS)]
                    ts = _fmt_ts(entry.timestamp)

                    panel = self.query_one(f"#panel-{entry.port.label}", PortPanel)
                    log_widget = panel.query_one(f"#log-{entry.port.label}", RichLog)
                    log_widget.write(
                        f"[dim]{ts}[/dim]  [{c}]{rich_escape(entry.line)}[/{c}]"
                    )

                    plain = f"[{ts}] [{entry.port.label.ljust(label_width)}] {entry.line}\n"
                    self._buffer.append(plain)
                    if self._file:
                        self._file.write(plain)
                        self._file.flush()

                    self._total += 1
                    count += 1
            except queue.Empty:
                pass

            if count:
                self.sub_title = f"Lines: {self._total:,}"

        def action_save(self) -> None:
            path = (
                output
                or Path(f"serial_log_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log")
            )
            with open(path, "w", encoding="utf-8") as f:
                f.writelines(self._buffer)
            self.notify(f"Saved {len(self._buffer):,} lines → {path}")

        def action_toggle_scroll(self) -> None:
            self._auto_scroll = not self._auto_scroll
            for port in ports:
                panel = self.query_one(f"#panel-{port.label}", PortPanel)
                log_widget = panel.query_one(f"#log-{port.label}", RichLog)
                log_widget.auto_scroll = self._auto_scroll
            self.notify(f"Auto-scroll {'on' if self._auto_scroll else 'off'}")

        def action_clear_all(self) -> None:
            for port in ports:
                panel = self.query_one(f"#panel-{port.label}", PortPanel)
                log_widget = panel.query_one(f"#log-{port.label}", RichLog)
                log_widget.clear()
            self._buffer.clear()
            self._total = 0
            self.sub_title = "Lines: 0"

        def on_unmount(self) -> None:
            stop_event.set()
            if self._file:
                self._file.close()

    SerialLoggerApp().run()


# ─── Argument parsing ─────────────────────────────────────────────────────────

def _parse_port_spec(spec: str, idx: int) -> PortConfig:
    parts = spec.split(":")
    if len(parts) < 2:
        raise argparse.ArgumentTypeError(
            f"Port spec must be DEVICE:BAUD[:LABEL], got: {spec!r}"
        )
    device = parts[0]
    try:
        baud = int(parts[1])
    except ValueError:
        raise argparse.ArgumentTypeError(f"Invalid baud rate in: {spec!r}")
    label = parts[2] if len(parts) >= 3 else Path(device).name
    return PortConfig(device=device, baud=baud, label=label, color_idx=idx)


# ─── Entry point ──────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generic multi-serial-port timestamped logger",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Examples:\n"
            "  %(prog)s --port /dev/tty.usbmodem1234:115200:RP2040"
            " --port /dev/tty.usbmodem5678:115200:ESP32\n"
            "  %(prog)s --port /dev/ttyUSB0:115200 --port /dev/ttyUSB1:115200"
            " --output session.log --gui\n"
        ),
    )
    parser.add_argument(
        "--port", "-p",
        action="append",
        required=True,
        metavar="DEV:BAUD[:LABEL]",
        help="Serial port spec (may be repeated)",
    )
    parser.add_argument(
        "--output", "-o",
        type=Path,
        metavar="FILE",
        help="Tee all output to this file (appended)",
    )
    parser.add_argument(
        "--gui",
        action="store_true",
        help="Launch Textual TUI instead of plain terminal output",
    )
    args = parser.parse_args()

    ports = [_parse_port_spec(spec, i) for i, spec in enumerate(args.port)]

    log_queue: queue.Queue[LogEntry] = queue.Queue()
    stop_event = threading.Event()

    reader_threads = [ReaderThread(p, log_queue, stop_event) for p in ports]
    for t in reader_threads:
        t.start()

    if not args.gui:
        def _sigint(sig, frame):
            stop_event.set()
        signal.signal(signal.SIGINT, _sigint)

    try:
        if args.gui:
            run_gui(ports, reader_threads, log_queue, stop_event, args.output)
        else:
            run_cli(ports, log_queue, stop_event, args.output)
    finally:
        stop_event.set()
        for t in reader_threads:
            t.join(timeout=2.0)


if __name__ == "__main__":
    main()
