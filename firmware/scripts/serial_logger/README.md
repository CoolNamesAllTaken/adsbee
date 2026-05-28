# Serial Logger

A generic multi-serial-port timestamped logger. Captures output from multiple serial ports simultaneously, prefixes each line with a wall-clock timestamp and port label, and tees everything to a log file. Includes an optional Textual TUI for split-pane monitoring.

## Requirements

- Python 3.9+
- `pyserial` and `textual` (installed via Poetry)

## Installation

```bash
cd firmware/scripts/serial_logger
poetry install
```

## Usage

### CLI mode (default)

Timestamped, color-coded output in the terminal:

```bash
poetry run serial-logger \
  --port /dev/tty.usbmodemXXXX:115200:RP2040 \
  --port /dev/tty.usbmodemYYYY:115200:ESP32 \
  --output session.log
```

### TUI mode (`--gui`)

Split-pane Textual interface, one scrollable panel per port:

```bash
poetry run serial-logger \
  --port /dev/tty.usbmodemXXXX:115200:RP2040 \
  --port /dev/tty.usbmodemYYYY:115200:ESP32 \
  --output session.log \
  --gui
```

| Key | Action |
|-----|--------|
| `q` | Quit |
| `s` | Save buffer to file |
| `a` | Toggle auto-scroll |
| `c` | Clear all panels |

## Port spec format

```
DEVICE:BAUD[:LABEL]
```

`LABEL` is optional — defaults to the device basename (e.g. `tty.usbmodem1234`).

## Options

| Flag | Description |
|------|-------------|
| `--port`, `-p` | Serial port spec (repeatable) |
| `--output`, `-o` | Log file path (appended to if it exists) |
| `--gui` | Launch Textual TUI |

## Notes

- Both modes reconnect automatically if a port disconnects (2 s retry).
- The status dot in TUI mode turns red while reconnecting.
- Log files are written in plain text (no ANSI codes).
- Timestamps are captured the moment a line arrives from the serial port.
