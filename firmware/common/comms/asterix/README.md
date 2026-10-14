# ASTERIX output

ADSBee 1090 and ADSBee 1421 can report traffic as EUROCONTROL ASTERIX, the surveillance data format used by air
navigation service providers:

- **CAT021** (ADS-B target reports), [Edition 2.6](https://www.eurocontrol.int/publication/cat021-eurocontrol-specification-surveillance-data-exchange-asterix-part-12-category-21).
  The records are also valid Edition 2.7: 2.7 only adds I021/090 extensions that ADSBee doesn't send.
- **CAT023** (ground station and service status), [Edition 1.3](https://www.eurocontrol.int/publication/cat023-eurocontrol-specification-surveillance-data-exchange-part-16-category-23).

## Turning it on

- Serial: `AT+PROTOCOL_OUT=<interface>,ASTERIX` (ADSBee 1090 `CONSOLE` or `COMMS_UART`, ADSBee 1421 `CONSOLE`).
- Network feed (ADSBee 1090): `AT+FEED=<index>,<uri>,<port>,1,ASTERIX`, or pick ASTERIX in the web UI feed editor.
- Data source: `AT+ASTERIX_SAC_SIC=<sac>,<sic>` sets the System Area Code and System Identification Code (0-255
  each, default 0,0) carried by every record. Use the codes your ASTERIX consumer assigned to this receiver; SACs
  are allocated per country by EUROCONTROL. Save with `AT+SETTINGS=SAVE`.

## What is sent

Once per second:

1. One CAT023 data block: a ground station status report, then a service status report for the 1090 MHz
   receiver (service ID 1, 1090 ES) and one for the UAT receiver (service ID 2), each normal or disabled.
2. CAT021 data blocks with one record per aircraft. Blocks are at most 1024 bytes, so each fits in one UDP
   datagram.

The stream is data blocks back to back with no extra framing. Each block starts with its category and length.

CAT021 records carry, when known: I021/010 data source, 040 target report descriptor, 161 track number, 015
service ID, 131 position, 080 address, 073 and 075 times of reception of position and velocity, 140 geometric
height, 090 quality indicators (NACv, NIC, NICbaro, SIL, NACp, SDA, GVA, PIC), 210 ADS-B version and link
technology, 070 Mode 3/A, 145 flight level, 152 magnetic heading, 200 emergency and alert status, 155 and 157
vertical rates, 160 ground speed and track, 150 and 151 airspeed, 077 report time, 170 callsign, 020 emitter
category, 008 TCAS RA and single antenna, 132 signal strength.

Not reported:

- Aircraft without a position.
- 1090 MHz DF18 targets and UAT TIS-B or ADS-R targets: CAT021 has no way to mark a rebroadcast, and on 1090 MHz
  the firmware doesn't keep the field that separates rebroadcasts from other DF18 transmitters.
- Mode S aircraft that don't send ADS-B, and Remote ID drones. CAT021 is ADS-B only. Monoradar categories
  (CAT048, CAT010) need a measured range and bearing and multilateration (CAT020) needs several receivers.
- Ground speed and heading of aircraft on the ground (CAT021 puts these in its Reserved Expansion Field).

Track numbers stay with an aircraft while it is reported and are reused 60 s after it was last reported. The
first ground station status report after boot sets RN (track numbering restarted).

## Time

ASTERIX times are seconds since midnight UTC. ADSBee takes UTC from a GNSS receiver (`AT+GNSS`), with the
accuracy of its NMEA time messages. Without GNSS time:

- Times count from boot, modulo 24 h.
- CAT023 reports TSV (time source invalid) and NOGO (data must not be used operationally), and leaves out
  I023/070.
- Every CAT021 record sets the I021/040 NOGO bit.

The ADSBee 1421 has no GNSS input, so its output always carries NOGO.

## Decoding

- Wireshark and tshark decode ASTERIX on UDP and TCP port 8600. For another port use
  `tshark -d tcp.port==<port>,asterix`.
- Python: [asterix_decoder](https://pypi.org/project/asterix_decoder/) or
  [libasterix](https://pypi.org/project/libasterix/).
