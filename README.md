# ADSBee 1090

ADSBee 1090 is an open-source multi band radio receiver and decoder for ADS-B packets transmitted by aircraft and ground stations. ADSBee 1090 is based on an RP2040 microcontroller, and utilizes two independent PIO blocks to find and decode ADS-B messages without the need for an FPGA. ADSBee 1090 includes a radio receiver frontend with filtering and amplification, as well as a software defined comparator circuit with an adjustable trigger threshold for customizable receive sensitivity in a diverse range of RF environments.

![ADSBee 1090 Logo](images/adsbee_logo.png)

## This Fork: GDL90 over Bluetooth LE (`ble-gdl90` branch)

This fork adds a **BLE ADS-B Receiver Service** to the ESP32-S3 firmware, so
EFBs connect over Bluetooth LE instead of WiFi. Proven on ADSBee 1090U
hardware end to end (AvareX on Android, Python on macOS, and Chrome via Web
Bluetooth as clients).

**Why:** a tablet joined to the receiver's WiFi loses its internet
connection. Over BLE, traffic streams in while the tablet stays on a phone
hotspot for weather and NOTAMs — and BLE works on iOS/iPadOS, which
Bluetooth SPP never did. A traffic-first GDL90 stream is only a few kB/s,
comfortably inside BLE bandwidth; FIS-B uplink is handled too (see below),
which matters now that [CIFIB](https://cifib.ca) is building independent
978 MHz FIS-B ground stations in Canada.

**What's here:**

- **ADS-B Receiver GATT service** (`0BEE0001-1090-46F0-A9AC-52D6BE4C29CC`):
  typed notify characteristics for Traffic, Ownship, and Status, each
  notification exactly one framed GDL90 message — atomic, no byte-stream
  reassembly, payloads any GDL90 decoder already understands. An Uplink
  characteristic carries FIS-B frames (too big for one notification) with a
  1-byte first/last/sequence fragmentation header. Up to 3 concurrent
  clients, preferred MTU 517. Full spec:
  [BLE_ADSB_SERVICE.md](https://github.com/perryc/avarex/blob/canadian-data/docs/BLE_ADSB_SERVICE.md).
- **AT command console over BLE**: the standard Nordic UART Service is wired
  to the same console queue as the WiFi websocket console, so any generic
  BLE serial terminal app can configure the device wirelessly — including
  switching WiFi/BLE modes without a USB cable.
- **[BLE Panel](software/ble_panel/index.html)**: a single-file Web
  Bluetooth app (Chrome/Edge) with a live decoded traffic table, status,
  and the AT console — the functional equivalent of the embedded web UI,
  usable when the receiver's WiFi is off.
- **Client implementation** in the
  [perryc/avarex fork](https://github.com/perryc/avarex/tree/ble-adsb)
  (`ble-adsb` branch), including multi-receiver merge (e.g. ADSBee for
  1090ES plus a [SoftRF](https://github.com/lyusupov/SoftRF/wiki/Card-Edition-MkIII)
  unit for FANET) and a receiver simulator for development without hardware.

**Constraints and findings** (relevant upstream even without this feature):

- On the 1090U's ESP32-S3 (no PSRAM), **BLE mode and WiFi mode are mutually
  exclusive** — the BT controller needs ~55 KB of internal RAM that WiFi
  AP+STA otherwise consume. Toggle with `AT+WIFI_AP` / `AT+WIFI_STA` (over
  USB or the BLE console). A PSRAM-equipped module would lift this.
- The stock sdkconfig builds the BLE controller **scan-only**:
  `BT_CTRL_BLE_ADV`, `BT_CTRL_BLE_MASTER` (the connection engine), and
  `BT_CTRL_BLE_SECURITY_ENABLE` are disabled. Advertising of any kind —
  including the existing **Broadcast Remote ID transmit feature — cannot
  work on the stock config**; this fork enables them.
- NimBLE host bring-up during early boot destabilizes the RP2040↔ESP32 SPI
  link; this fork defers it ~45 s and adds a periodic BLE status heartbeat
  to the console, since boot-time logs predate the console bridge.

## Features
* Decoding of 1090MHz transponder signals (ADS-B and Mode S).
* Decoding of 978MHz UAT transponder signals (ADS-B) and uplink data (FIS-B/TIS-B).
* 1x USB console input / output for changing parameters and transmitting data.
* 1x UARTs for reporting data or ingesting GNSS information.
* Built-in EEPROM for storing nonvolatile settings.
* Feature-rich AT command set for customizing baud rates, output data protocols, signal conditioning values, etc.
* Multiple supported output protocols:
    * Raw packets
    * MAVLINK1
    * MAVLINK2
    * GDL90
    * Mode S Beast
    * CSBee (custom information rich ASCII protocol)
* 2.4GHz 802.11 radio for automatic streaming of decoded values to custom endpoints on the internet. No external compute required, just add WiFi and power!
* Ethernet interface (requires external PoE pant or W5500 IC).
* GNSS module connector for MLAT and ground station location information.
* Low(ish) power draw.

## Purchasing and Support
ADSBee 1090 is a product of Pants for Birds LLC. To learn more about the project or purchase a device, please visit [pantsforbirds.com/adsbee-1090](https://pantsforbirds.com/adsbee-1090).

## General Architecture
ADSBee 1090 utilizes some basic RF hardware (SAW filters, LNA, logarithmic power detector) to amplify the received pulse-position-modulated ADS-B waveform into a pulse train that is conditioned by a comparator and fed to a PIO input pin on the RP2040. The RP2040 utilizes two PIO state machines, one for preamble detection and one for manchester decoding of the message body, to decode the ADS-Bee message. This offers significant cost and power savings over FPGA-based solutions that solve the same problem.

A filtered PWM output from the RP2040 can be used to adjust the bias of the data slicer comparator circuit on the output of the receive signal chain, allowing logarithmic adjustments in receiver sensitivity which can be used to filter out weaker ADS-B signals in congested environments or maximize sensitivity for increased receive range.

There are two devices connected to the RP2040 via a common SPI bus: a CC1312 for secondary band receive and an ESP32 S3 for networking functions.

The CC1312 can be tuned to a variety of sub-GHz frequencies to decode UAT mesages (and potentially more protocols in the future). These messages are forwarded to the RP2040 over SPI and reported through a unified interface along with the Mode S packets received by the RP2040.

The ESP32 S3 ingests raw packets from the RP2040 and maintains a separate, identical, aircraft dictionary for use in reporting over network interfaces (WiFi, Ethernet).

All three microcontrollers utilize code stored on the RP2040's external flash chip, so firmware updates are conducted by flashing a single firmware image to the RP2040, which in turn flashes updated firmware images to the CC1312 and ESP32 S3.

## Devices

The ADSBee 1090U from Pants for Birds LLC includes an RP2040, ESP32, CC1312, and custom 1090MHz RF frontend on a single PCBA, enabling all multi-band receive and networking functions (except for Ethernet, which requires an external pant).

[![ADSBee 1090U Picture](images/adsbee_1090u_pic.png)](https://pantsforbirds.com/product/adsbee-1090u/)


The ADSBee m1090 is a solder-down module containing only the 1090MHz frontend and RP2040, and can be extended to have the same features by populating a CC1312 and ESP32 on its carrier board. This enables custom devices to easily integrate a subset or complete clone of the ADSBee 1090U's functions, while running the same open source firmware image. The ADSBee m1090 removes one of the two LNA stages on the ADSBee 1090U, reducing power draw and improving ultra close range performance. For equivalent maximum reception range, an external LNA can be populated on the carrier PCB.

[![ADSBee m1090 Picture](images/adsbee_m1090_pic.png)](https://pantsforbirds.com/product/adsbee-m1090/)

For industrial and outdoor applications, the ADSBee 1090U is available as the GS3M PoE, a ruggedized weatherproof device connected and powered by 802.3af Power over Ethernet.

[![ADSBee GS3M PoE Picture](images/adsbee_gs3m_poe_pic.png)](https://pantsforbirds.com/product/adsbee-gs3m-poe/)
