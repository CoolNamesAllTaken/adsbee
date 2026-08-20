# ADSBee m1421 Web Console

A single-file, self-contained web console for the ADSBee m1421 (TI CC1314R10) that
mimics the ADSBee 1090 ESP32 web interface, but talks to the device over the
**Web Serial API** instead of WebSockets. Open `adsbee_1421_console.html` directly in
Chrome or Edge (works from `file://`, no server needed) and click **Connect**
(the page probes the firmware's baud whitelist to find the device — see below).

## Features

- **Baud auto-detection** — the device boots at its saved console baud
  (`AT+BAUD_RATE` + `AT+SETTINGS=SAVE`; factory default 1,000,000), so it may be
  at any of {115200, 230400, 460800, 921600, 1000000}. On connect the page
  sweeps that list — trying last session's rate first — and locks onto whatever
  rate answers. Each probe is `AT+BAUD_RATE?`, repeated for ~2.7 s per rate
  before moving on (opening the port asserts DTR, which resets the device, so it
  is usually still booting when the first probe goes out), and the rate shown is
  the one the device itself reports. Behind the programmer jig
  (`firmware/adsbee_1421/programmer/`) the host baud is virtual and the jig
  retunes the device to it after each host-driven reset; the page waits that
  out and, if the device's rate ever differs from the host port's, says so
  rather than guessing. After `AT+REBOOT`,
  `AT+SETTINGS=RESET`, or a firmware flash the page re-sweeps automatically, and
  a hand-typed `AT+BAUD_RATE=CONSOLE,<n>` is followed to the new rate instead of
  desyncing the link. Disconnecting leaves the device at its current rate.
- **Console tab** — interactive AT command terminal (line editing, history, ANSI
  colors), a Receiver Statistics panel, a Device Status card, and firmware upload.
  - Statistics update whenever an `RX_STATS=` response appears — type
    `AT+RX_STATS?` yourself or click **Refresh**. There is no background polling,
    so the console stream stays clean.
  - An **uptime** card sits alongside the statistics, fed by `AT+UPTIME?`. It is read
    quietly on connect and after anything that reboots the device (`AT+REBOOT`,
    `AT+SETTINGS=RESET`, a firmware flash), and refreshed by the same **Refresh**
    button — or by typing `AT+UPTIME?` yourself.
  - Device info (`AT+DEVICE_INFO?`) is queried once per connect.
  - All protocol output (CSBee, raw aircraft JSON, etc.) prints in the terminal.
    Aircraft JSON is hidden from the terminal only while the Map tab itself is
    driving the stream; JSON lines always feed the map's aircraft store either way.
- **Map tab** — Leaflet map + sortable aircraft table + detail sidebar. Entering the
  tab saves the current `AT+LOG_LEVEL` / `AT+PROTOCOL_OUT` settings, then sets
  `AT+LOG_LEVEL=SILENT` and `AT+PROTOCOL_OUT=CONSOLE,AIRCRAFT_JSON` and renders the
  newline-delimited aircraft JSON stream. Switching back to the Console tab restores
  the saved settings.
  - Aircraft on the ground (`on_ground`) render gray on both the map and the table
    (`grnd` in the altitude column). Icon rotation and the Hdg column use the ground
    track when reported, falling back to true/magnetic heading (surface traffic).
    Because surface reception is bursty (poor line-of-sight), ground aircraft are
    retained at their last known state for 10 minutes without an update (airborne:
    1 minute). The sidebar always shows a Status row (Airborne / On ground) and a
    "Last seen" age.
  - Each moving aircraft gets a **velocity vector**: a screen-space line along its
    direction whose length scales with speed (about one icon width at 250 kt,
    clamped) — zooming the map never changes its on-screen size.
  - These changes are RAM-only (`AT+SETTINGS=SAVE` is never issued), so a device
    power cycle always returns to the persisted configuration — including if the
    page is closed while on the Map tab (a best-effort restore is attempted on
    close, but cannot be guaranteed).
- **Upload Firmware** — flashes a `.hex` image (from
  `firmware/adsbee_1421/ti/build/<Config>/adsbee_1421-<ver>.hex`) via the
  CC13x4 factory ROM serial bootloader, a direct port of
  `software/adsbee_1421_flasher/adsbee_1421_flasher.py`. Runs at the detected
  baud (the ROM auto-bauds up to ~1.2 M): ~15 s for a ~600 KB image at 1 M
  instead of ~2 min at 115200. After the post-flash reboot the page re-detects
  the link automatically.

## Firmware upload wiring

Bootloader entry uses hardware control lines (same as the Python flasher's `auto`
mode): the adapter's **RTS must be wired to SYNC (DIO_5)** and **DTR to RESET_N**,
with TX → DIO_2 and RX → DIO_3. The page holds SYNC high through a reset pulse so
the boot ROM enters the serial bootloader; if that fails it falls back to
`AT+REBOOT`-with-SYNC entry, then to a manual power-cycle prompt. The firmware's
CCFG must enable the bootloader backdoor (see the flasher README).

Entry never erases anything by itself; erase begins only after the bootloader ACKs.
Only the 2 KB flash sectors covered by the image are erased (`SECTOR_ERASE`, never a
bank erase), so the module's Settings (`0x000FC000`) and Device Info / OTA keys
(`0x000FE000`) survive a reflash; an image that reaches into those sectors is refused
before anything is erased.
If a flash fails partway, the device stays in the ROM bootloader — reopen the dialog
and **Retry**. The board cannot be bricked (an interrupted flash leaves the
factory-default CCFG, which keeps the bootloader enabled).

## Notes

- Requires Chrome or Edge (Web Serial). Firefox/Safari show an unsupported banner.
- Map tiles load from openstreetmap.org and need internet; everything else works
  offline. Leaflet 1.9.4 is vendored inline (BSD-2-Clause, license header kept).
- Connecting may briefly reset the device: Chromium asserts DTR when opening a
  port, and DTR is wired to RESET_N. The page parks the lines in the normal-run
  state immediately after opening.
- The page is assembled by hand — Leaflet's JS/CSS are pasted between
  `BEGIN/END VENDORED` markers with the sourcemap comment and `url(images/...)`
  rules stripped. To upgrade Leaflet, replace those two blocks.
