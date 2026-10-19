# Swarm Reports

An ADSBee 1090 can report to a swarm server once an hour: range per direction and altitude, message and aircraft counts, and its firmware versions. The server shows range maps and status for all your receivers. Off by default.

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
* Range: farthest aircraft per 10° sector and altitude band, in 2 km steps. Only with that position, and only for aircraft heard directly (no TIS-B or ADS-R) with 2 consistent position decodes.
  Positions beyond the radio horizon of their altitude band are dropped and counted. If 10% or more of an hour's positions, from 5 or more aircraft, are dropped, that hour's range is withheld and the server shows "check position". This catches gross errors of about 200 km or more (a sign flip, a wrong country), not a position that is only somewhat off.
* OTA keys, to adsbee.aero only (to verify the unit is genuine).

Needs WiFi station or Ethernet. The first report goes 2-5 minutes after power-up. A failed report is merged into the next one, so no period is lost.

## Firmware from the swarm

If the swarm account stages a firmware version for this ADSBee, it installs that version instead of the one adsbee.aero recommends, but only with `AT+AUTO_UPDATE=1` (see [Automatic updates](update-firmware.md#automatic-updates)).

## Status

The device status the webpage reads has a `swarm` block: result of the last report (`ok`, `no answer`, `rejected`, `removed`, ...), HTTP status, seconds since the last report and until the next. `removed` means the unit was taken off the account; it stops reporting until it gets a new token or reboots.
