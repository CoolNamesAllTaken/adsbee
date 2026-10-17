# ADSBee MLAT receiver feed protocol

Version 1. This is the stream a receiver sends to the ADSBee multilateration (MLAT) server.

The feed is a Mode S Beast stream with one extra frame type, the **receiver info frame**. Mode S frames are
unchanged, so the same stream also works for any Beast consumer (readsb, dump1090, tar1090). The receiver info frame
tells the server who the receiver is, what its timestamps count and where its antenna is.

## Why Beast with an extra frame

- Firmware already builds Beast frames (`firmware/common/comms/beast/`), and every existing feeder speaks it, so the
  server needs one parser for ADSBee and third-party receivers.
- Beast has no field for clock rate, position or receiver identity. A new frame type carries them without touching the
  Mode S frames.
- The receiver info frame payload is printable ASCII, so it never contains the Beast escape byte `0x1a`. A Beast parser
  that does not know the type skips to the next `0x1a`, which is the start of the next real frame. The same trick is
  used by the `0xe4` feed ID frame that readsb accepts.

## Transport

| | TCP (default) | UDP |
|---|---|---|
| Server port | 31090 | 31090 |
| Direction | Receiver connects to the server and only sends | Receiver sends datagrams |
| Framing | Continuous Beast byte stream | Each datagram holds whole Beast frames only |
| Receiver info | First frame after connecting, then periodically | First frame of **every** datagram (at least `id`, `clk` and `ep`) |

A receiver may also send the stream as MQTT messages (ADSBee feeds with the MQTT transport): each message holds whole
Beast frames, and the receiver info follows the TCP rules, since the broker connection is a TCP connection. Send `clk`
in every info frame: a server that first hears of a receiver from a frame without it can only assume a clock rate.

TCP is preferred: frames arrive in order and a lost connection is visible to both sides. UDP suits links where a TCP
connection cannot be kept up; a lost datagram costs only the frames in it. Keep datagrams under 1400 bytes.

The server also accepts plain Beast (see [Plain Beast receivers](#plain-beast-receivers)).

## Mode S frames

Standard Beast Mode S frames, escaped as usual (`0x1a` in the body is sent as `0x1a 0x1a`):

```
0x1a | 0x32 (56 bit) or 0x33 (112 bit) | 6 byte timestamp, big-endian | 1 byte signal level | 7 or 14 byte message
```

- **Timestamp**: the receiver's free-running counter at the frame's reception, in ticks of the clock rate declared by
  `clk` (12 MHz if no receiver info frame was received), taken modulo 2^48.
- **Reference instant**: the end of message bit 56 (64 microseconds after the start of the first preamble pulse) for
  56 and 112 bit messages alike. This is what dump1090, readsb and the ADSBee 1090 send. Any other point at a fixed
  delay from the preamble works too: a constant per-receiver offset is absorbed by clock synchronization. A delay that
  differs between 56 and 112 bit messages, or with signal level, is an error.
- **Timestamp 0** means "no timestamp" (dump1090 convention, used by the ADSBee m1421 for frames it could not stamp).
  The server decodes such frames (identity, positions) and leaves them out of MLAT.
- **Wraparound**: the server unwraps the 48 bit value. At 48 MHz it wraps every 67.9 days, at 12 MHz every 271 days.
- Other Beast frame types (Mode A/C `0x31`, status `0x34`, UAT `0xec`, `0xe3`, `0xe4`) may be present and are ignored
  or used for identification only.

## Receiver info frame

```
0x1a | 0xe9 | ASCII payload | 0x0a (newline)
```

The payload is `key=value` fields separated by `;`. Characters are printable ASCII (`0x20` to `0x7e`) except `;` and
`=` inside values. The whole frame is at most 512 bytes. Unknown keys are ignored, so later versions can add fields.

Example (GNSS receiver, 48 MHz clock):

```
v=1;id=0bee00038172d18c;name=Hilltop;clk=48000000;ep=3fa2;lat=37.4219983;lon=-122.0840575;alt=31.42;src=gnss;hacc=2.5;vacc=4.0;pps=2f1c0a39b100@1791936000;fw=adsbee_1090-0.9.1
```

| Key | Required | Value |
|---|---|---|
| `v` | yes | Protocol version, `1`. |
| `id` | yes | Receiver ID, 1 to 32 characters of `[0-9A-Za-z_.-]`. ADSBee devices use their 64 bit device ID in hex (16 characters). Stable across reboots. |
| `ep` | yes | Clock epoch: 1 to 8 hex digits that change whenever the timestamp counter restarts or jumps (boot, sleep, clock source change). The server drops this receiver's clock synchronization when it changes. A random value at boot is enough. |
| `clk` | yes in the first frame | Timestamp clock rate in Hz (integer), the nominal rate of the counter in the 6 byte field. `48000000` for ADSBee, `12000000` for classic Beast. |
| `lat`, `lon` | yes in the first frame | Antenna position, WGS84 degrees, at least 7 decimals. |
| `alt` | yes in the first frame | Antenna height above the WGS84 ellipsoid, meters. |
| `src` | yes in the first frame | Position source: `gnss` (live receiver fix) or `fixed` (entered by the operator or surveyed). |
| `hacc`, `vacc` | no | One sigma horizontal and vertical position accuracy, meters. The server weights the receiver by them. |
| `mov` | no | `1` if the receiver may move (vehicle). The server then expects a position at least once per second. |
| `pps` | no | `<ticks>@<unix_s>`: the counter value (hex, same units and wrap as the 6 byte field) at the latest GNSS pulse per second (PPS) edge, and the UTC second (integer Unix time) that edge marks. |
| `name` | no | Display name, up to 32 characters. |
| `fw` | no | Firmware or software version. |

Fields not present keep their previous value, so a periodic frame may carry only what changed (plus `v`, `id`, `ep`).

### When to send it

- First frame of every TCP connection and of every UDP datagram. In a UDP datagram that comes between full frames,
  `v`, `id`, `clk` and `ep` are enough (ADSBee sends that short frame).
- Every 10 seconds, with `lat`, `lon`, `alt`, `src` and `pps` if available.
- At least once per second (with position) while `mov=1`.
- Immediately when `ep` changes, before any frame stamped with the new epoch.

## Server behavior

- A receiver is identified by `id`. A new connection with the same `id` replaces the old one.
- Before the first receiver info frame of a TCP connection, frames are attributed to a configured receiver if one
  matches (see below); otherwise they are dropped.
- Clock synchronization is reset when `ep` changes, when `clk` changes, or when timestamps go backwards or jump by more
  than one second against the server's wall clock.
- With `src=gnss` and no `hacc`, the server assumes 5 m horizontal and 10 m vertical accuracy; with `src=fixed`, 1 m
  and 2 m.

## Plain Beast receivers

Existing feeders send plain Beast without receiver info frames. The server's configuration file lists them:

```toml
[[receiver]]
id = "garage-pi"
match = { uuid = "38366a5c-c54f-4256-bd0a-1557961f5ad0" }   # From a 0xe4 feed ID frame, or:
# match = { peer = "192.0.2.10" }                           # Source address of the TCP connection.
lat = 37.42
lon = -122.08
alt = 30.0
clock_hz = 12000000

[[receiver]]
id = "readsb-box"
connect = "192.0.2.20:30005"   # The server connects out to a Beast output instead.
lat = 37.50
lon = -122.10
alt = 12.0
clock_hz = 12000000
```

These receivers report `pos_src = "config"`. A receiver info frame, if one arrives later, overrides the file.

## Firmware notes

- ADSBee 1090: the counter is the 48 MHz MLAT count (`RawModeSPacket::mlat_48mhz_64bit_counts`), already at the end of
  bit 56. The MLAT feed sends it at 48 MHz with `clk=48000000`. The existing Beast feeds keep sending 12 MHz (the 48 MHz
  count divided by 4), so mlat-client and other consumers are unaffected.
- ADSBee m1421: same 48 MHz count, taken at the LR2021 sync event, and 0 for frames it could not stamp.
- The MLAT feed is a new `ReportingProtocol` value appended at the end of the enum (values are stored in flash).
