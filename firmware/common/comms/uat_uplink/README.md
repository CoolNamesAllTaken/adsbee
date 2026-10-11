# UAT uplink stream

ADSBee 1090 and ADSBee 1421 pass received UAT ground uplinks (FIS-B weather and other broadcast data) to map
clients. Each uplink is the de-interleaved, error-corrected 432 byte payload: an 8 byte UAT header followed by
424 bytes of application data. Uplinks that fail error correction are never sent.

Both formats carry:

- **RSSI**: signal strength in dBm.
- **Timestamp**: receive time in milliseconds since the receiver booted, as an unsigned 32 bit number (wraps
  after 49.7 days).

## WebSocket `/uplink` (ADSBee 1090)

`ws://<device>/uplink` sends one binary message per uplink. Clients send nothing.

| Offset | Size | Field |
|---|---|---|
| 0 | 432 | Payload |
| 432 | 1 | RSSI, signed. `-128` means unknown. |
| 433 | 3 | Reserved, zero |
| 436 | 4 | Timestamp, unsigned, little endian |

- A message is 440 bytes. Later firmware may append fields: read by offset and ignore extra bytes.
- Up to 4 clients. The device keeps the 8 newest uplinks; a client that reads too slowly skips the oldest ones.
- New clients get uplinks received after they connect.

## Serial line (ADSBee 1090 and ADSBee 1421)

`AT+PROTOCOL_OUT=<interface>,AIRCRAFT_JSON_UAT_UPLINK` sends the `AIRCRAFT_JSON` aircraft lines plus one line
per uplink:

```
{"uat_uplink":"<576 Base64 characters>","rssi":-80,"t":123456}
```

- `uat_uplink`: payload in padded Base64 (RFC 4648).
- `rssi`: left out when unknown.
- `t`: timestamp.
- Lines end with `\n` and are at most 621 bytes. Aircraft lines have a `hex` key and no `uat_uplink` key.
- Plain `AIRCRAFT_JSON` never sends uplink lines.

Bit rate needed:

- One UAT frame has 32 uplink slots per second, so a receiver in range of many ground stations can produce
  32 lines (20 kB) per second: 198720 bit/s. Use 230400 baud or more for the full stream. The ADSBee 1421
  console default of 1000000 baud leaves room for aircraft lines as well.
- 115200 baud carries 18 uplink lines per second with nothing else on the line.
- ADSBee 1421: uplink lines are sent only while half of the transmit buffer is free, so aircraft lines go
  first. Uplinks that don't fit are dropped and counted as `uat_report_q_ovf` in `AT+RX_STATS?`.
- ADSBee 1090: `COMMS_UART` writes wait for the UART, so a bit rate that is too low for the uplink rate slows
  the receiver. The USB console has no such limit.
