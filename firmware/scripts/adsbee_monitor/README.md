# ADSBee Multi-Receiver Monitor

A GUI application for monitoring multiple ADSBee ADS-B receivers simultaneously, comparing performance metrics across devices in real time.

## Requirements

- Python 3.11+
- `websockets` library (only external dependency)
- `tkinter` (included in most Python distributions; on Ubuntu/Debian: `sudo apt install python3-tk`)

## Installation

```bash
# Using pip
pip install websockets

# Or using the pyproject.toml
pip install .
```

## Running

```bash
python adsbee_monitor.py
```

## Usage

1. Click **+ Add Receiver** to add an ADSBee device by IP address (e.g. `192.168.1.50`).
   - Optionally give it a friendly name like "Roof Antenna" or "Unit A".
   - The app connects to `ws://<ip>/metrics` automatically.
2. Add as many receivers as needed — cards appear in a responsive grid.
3. **Metrics displayed per receiver:**
   - Raw squitter frames (since last reset)
   - Valid squitter frames + **valid %**
   - Raw extended squitter frames (since last reset)
   - Valid extended squitter frames + **valid %**
   - Demods 1090 count
   - Number of Mode S and UAT aircraft tracked
4. **Aggregate bar** at the top sums all receivers for easy comparison.
5. **Reset:**
   - Click **⟳ Reset All** to zero all receivers simultaneously.
   - Click a card to select it (highlighted in blue), then click **⟳ Reset Selected** to reset only chosen receivers.
   - Use **Select All / None** for bulk selection.
6. Click ✕ on a card to disconnect and remove a receiver.

## Valid % Color Coding

| Color  | Range     |
|--------|-----------|
| 🟢 Green  | ≥ 90%  |
| 🟡 Yellow | 70–89% |
| 🟠 Orange | 50–69% |
| 🔴 Red    | < 50%  |

## Notes

- The app reconnects automatically if a receiver drops offline.
- Metrics are *cumulative since last reset* — the device's own counters are used as a baseline, so resetting the GUI does not affect the device itself.
- The connection indicator (●) shows green when connected, red when disconnected/reconnecting.
