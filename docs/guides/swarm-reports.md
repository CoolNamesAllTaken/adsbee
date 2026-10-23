# Swarm Reports

An ADSBee 1090 can report to a swarm server once an hour: range per direction and altitude for Mode S, UAT and Remote ID, message and aircraft counts, and its firmware versions. The server shows range maps and status for all your receivers. Off by default.

## Turn on

1. Copy the token from your account page on the swarm server.
2. Send on the [CLI](../getting-started/quick-start.md#connect-to-cli):

```
AT+SWARM=1,https://adsbee.aero,<token>
AT+SETTINGS=SAVE
```

Or use **Settings → System → Swarm Reports** on the device's webpage.

| Command | Does |
|---|---|
| `AT+SWARM=<enabled>,<server>,<token>` | `enabled` 0 or 1; `server` a base URL (`https://` or `http://`); empty arguments keep their value |
| `AT+SWARM?` | Shows the setting, token masked |

A self-hosted server works the same: give its URL as `server`.

## What is sent

* Unique ID, ESP32 MAC address, firmware versions, the Automatic Updates setting, uptime.
* Receiver position, only when its source is `FIXED` (not 0, 0) or `GNSS` with a fix.
* Per period: valid Mode S, extended squitter and UAT messages, most and distinct aircraft.
* Range per protocol: the farthest position per 10° sector and height band. Only with that position, only for positions heard directly (no TIS-B or ADS-R), each after 2 position decodes.

  | Map | From | Bands | Step |
  |---|---|---|---|
  | `mode_s` | 1090 MHz ADS-B | Altitude (baro, else GNSS): 0, 1k, 2k, 4k, 6k, 10k, 15k, 20k, 25k, 30k, 35k, 40k+ ft | 2 km |
  | `uat` | 978 MHz UAT ADS-B | Same as `mode_s` | 2 km |
  | `remote_id` | Remote ID drones | Height above the receiver (GNSS): 0, 100, 200, 300, 400, 500, 700, 1k, 1.5k, 2k, 3k, 5k+ ft | 50 m, up to 12.75 km |

  A protocol with nothing heard in the period is left out.
  Positions beyond the radio horizon of their band are dropped and counted. If 10% or more of an hour's positions, from 5 or more aircraft or drones, are dropped, that hour's range is withheld and the server shows "check position". This catches gross errors of about 200 km or more (a sign flip, a wrong country), not a position that is only somewhat off.
* OTA keys, to adsbee.aero only (to verify the unit is genuine).

Needs WiFi station or Ethernet. The first report goes 2-5 minutes after power-up, turning it on, or changing the server or token. A failed report is retried after 1, 2, 4, ... minutes (up to the report period, longer if the server asks) and merged into the next one, so no period is lost.

## Firmware from the swarm

If the swarm account stages a firmware version for this ADSBee, it installs that version instead of the one adsbee.aero recommends, but only with `AT+AUTO_UPDATE=1` (see [Automatic updates](update-firmware.md#automatic-updates)).

## Status

The device status the webpage reads has a `swarm` block: result of the last report (`ok`, `no answer`, `rejected`, `removed`, ...), HTTP status, seconds since the last report and until the next. `removed` means the unit was taken off the account; it stops reporting until it gets a new token or reboots.
