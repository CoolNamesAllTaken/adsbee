# adsbee_mlat_sim

Synthetic Mode S traffic for testing multilateration (MLAT). It simulates aircraft, a set of receivers and every
error between them, and yields what each receiver would report: timestamped Mode S frames with valid parity, plus the
truth behind each one.

## Install

```bash
pip install -e software/adsbee_mlat/sim[test]
pytest software/adsbee_mlat/sim/tests
```

## Use

```python
import adsbee_mlat_sim as sim

sc = sim.example_scenario(n_receivers=4, baseline_m=20e3, n_aircraft=40, clock_hz=48e6, seed=1)
for frame in sc.frames(duration_s=60):
    frame.rx_id, frame.ticks, frame.clock_hz, frame.msg   # what the receiver reports
    frame.beast()                                         # the same as a Beast binary frame
    frame.icao, frame.t_emit, frame.lat, frame.ecef       # truth
```

- `frames()` yields records of all receivers in order of true arrival time. `simulate()` returns the same run as
  numpy arrays (`Emissions`, `Receptions`), which is much faster for statistics.
- `ticks` is the receiver's free-running counter at the Beast timestamp instant: the end of data bit 56, 64 us after
  the start of the preamble, for short and long frames. It is unwrapped; `beast()` wraps it to 48 bits.
- `t_emit`, `t_arrival` are true seconds since the scenario start; `t_unix = Scenario.t0_unix + t_arrival`.
- `write_beast(frames, directory)` writes one `<rx_id>.beast` file per receiver.
- The same seed gives the same run.

## Model

- Aircraft (`Aircraft`): great-circle tracks at constant speed and vertical rate. With `adsb=True` they send DF17
  airborne position (CPR, barometric altitude) and velocity at 2/s and identification every 5 s. Every aircraft sends
  DF11 squitters at 1/s and DF4/5/20/21 replies at `reply_rate_hz`. Set `adsb=False` for Mode S only targets.
  Reported ADS-B positions are the true position `pos_latency_s` earlier plus a slowly varying error sized by `nacp`.
  `baro_bias_m` offsets the barometric altitude from the true height.
- Receivers (`Receiver`): true and reported position (`add_position_noise()` for GNSS error), sensitivity, antenna
  gain, elevation mask. `RECEIVER_TYPES` holds timing models for the ADSBee 1090, the ADSBee m1421 and an RTL-SDR
  running dump1090.
- Timing (`TimingModel`): Gaussian jitter, demodulator time grid, signal-to-noise jitter, a constant error per
  receiver and aircraft, a fixed receiver delay and occasional long multipath delays.
- Clock (`Clock`): counter rate (`clock_hz`), offset, frequency error, frequency random walk, sinusoidal wander,
  phase steps and counter resets.
- Propagation: straight-line delay plus the excess delay of an exponential troposphere; free-space path loss with
  per-frame fading decides which receivers decode a frame.

## Timestamp study

`study/` compares receiver clock rates (12 vs 48 MHz) for MLAT accuracy.

- `crlb.py`: Cramer-Rao bound of a time-of-arrival fix, with an optional altitude measurement.
- `mc.py`: Monte Carlo of the full chain: clock sync from ADS-B reference aircraft, then a batched solver.
- `run_study.py [results.json]`: runs every scenario and the bound maps (about 2 minutes on 6 cores).

```bash
pip install -e 'software/adsbee_mlat/sim[study]'
cd software/adsbee_mlat/sim/study && python run_study.py results.json
```
