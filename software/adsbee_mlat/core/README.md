# ADSBee MLAT server core

Receives Mode S frames with timestamps from ADSBee and other Beast receivers, synchronizes their clocks with ADS-B
reference aircraft and locates aircraft by multilateration (MLAT). Results go to Redis for the web map and to an SBS
(BaseStation) port.

- Receiver feed protocol: [../PROTOCOL.md](../PROTOCOL.md)
- Redis channels: `mlat:aircraft` (fixes, every 100 ms), `mlat:receivers` and `mlat:stats` (every second), key
  `mlat:snapshot` (all live aircraft). Receiver settings from the web admin are read from `mlat:receiver_config` and
  channel `mlat:config`.

## Run

```bash
pip install -e '.[test]'
adsbee-mlat --config mlat.toml        # or: python -m adsbee_mlat
```

| Environment variable | Default | Meaning |
|---|---|---|
| `REDIS_URL` | `redis://localhost:6379/0` | Redis to publish to; empty to disable |
| `MLAT_FEED_PORT` | `31090` | TCP and UDP port for receiver feeds |
| `MLAT_SBS_PORT` | `31003` | SBS output of MLAT fixes; `0` to disable |
| `MLAT_CONFIG` | none | TOML file: server options and plain Beast receivers (see PROTOCOL.md) |

Example `mlat.toml`:

```toml
[server]
group_window_s = 0.3          # Wait for copies of a message from other receivers.
publish_mlat_for_adsb = false # MLAT fixes of aircraft with a live ADS-B position are not published.

[[receiver]]
id = "readsb-box"
connect = "192.0.2.20:30005"  # Pull Beast from an existing receiver.
lat = 37.50
lon = -122.10
alt = 12.0
clock_hz = 12000000
```

## How it works

- **Ingest**: Beast frames are grouped by message bytes. A group is closed 0.3 s after its first copy arrived.
- **Clock sync**: every DF17 airborne position heard by two or more receivers gives each receiver pair a measurement
  of their clock offset (arrival time minus the propagation delay from the decoded position, including an exponential
  atmosphere model). A two state Kalman filter per pair tracks offset and rate; its process noise adapts to the
  oscillators. Receivers without a direct pair are joined through the sync graph. The timestamp noise of each
  receiver is split out of the pair residuals; receivers above 500 ns are left out.
- **Solver and tracking**: a new aircraft is located with a Levenberg-Marquardt least squares fix (at least 4
  measurements: receivers plus barometric altitude). After that, every message heard by two or more synchronized
  receivers updates an extended Kalman filter (position and velocity), so fixes come at the aircraft's message rate.
  Large groups use at most 12 receivers, chosen for the widest spread.
- **ADS-B**: positions (CPR), identity, squawk and velocity are decoded and published as they arrive.

## Test and benchmark

```bash
pip install -e ../sim          # Simulator for the end-to-end tests.
pytest -q
python bench/bench.py --receivers 50 --aircraft 400 --duration 10   # Throughput (--workers N to shard).
python bench/validate.py out/ --socket 120                          # Accuracy scenarios on simulated traffic.
python bench/report.py out/ --bench b.json --out report.html        # HTML report (needs matplotlib).
```

For large networks set `workers` (or `MLAT_WORKERS`) above 1: aircraft are then shared out by address over worker
processes, each with its own clock synchronization.
