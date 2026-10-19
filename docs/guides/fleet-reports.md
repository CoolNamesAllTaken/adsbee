# Fleet Reports

An ADSBee 1090 can report to a fleet server once an hour: range per direction and altitude, message and aircraft counts, and its firmware versions. The server shows range maps and status for all your receivers. Off by default.

## Turn on

1. Copy the token from your account page on the fleet server.
2. Send on the [CLI](../getting-started/quick-start.md#connect-to-cli):

```
AT+FLEET=1,https://adsbee.aero,<token>
AT+SETTINGS=SAVE
```

Or use **Settings → System → Fleet Reports** on the device's webpage.

| Command | Does |
|---|---|
| `AT+FLEET=<enabled>,<server>,<token>` | `enabled` 0 or 1; `server` a base URL (`https://` or `http://`); empty arguments keep their value |
| `AT+FLEET?` | Shows the setting, token masked |

A self-hosted server works the same: give its URL as `server`.

## What is sent

* Unique ID, ESP32 MAC address, firmware versions, the Automatic Updates setting, uptime.
* Receiver position and its source (`AT+RX_POSITION`).
* Per period: valid Mode S, extended squitter and UAT messages, most and distinct aircraft.
* Range: farthest aircraft per 10° sector and altitude band, in 2 km steps. Only with a `FIXED` or `GNSS` receiver position, and only for aircraft with 2 consistent position decodes.
* OTA keys, to adsbee.aero only (to verify the unit is genuine).

Needs WiFi station or Ethernet. The first report goes 2-5 minutes after power-up. A failed report is merged into the next one, so no period is lost.

## Firmware from the fleet

If the fleet account stages a firmware version for this ADSBee, it installs that version instead of the one adsbee.aero recommends, but only with `AT+AUTO_UPDATE=1` (see [Automatic updates](update-firmware.md#automatic-updates)).

## Status

The device status the webpage reads has a `fleet` block: result of the last report (`ok`, `no answer`, `rejected`, `removed`, ...), HTTP status, seconds since the last report and until the next. `removed` means the unit was taken off the account; it stops reporting until it gets a new token or reboots.
