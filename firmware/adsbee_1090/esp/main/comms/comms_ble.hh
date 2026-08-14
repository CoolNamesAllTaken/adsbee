#pragma once

#include <cstdint>

// BLE GATT transport for GDL90 (traffic/ownship/status) - the "BLE ADS-B Receiver Service".
//
// Proper typed GATT characteristics rather than a serial-port emulation: each notification carries exactly one
// complete framed GDL90 message, so clients never reassemble a byte stream, and the payloads remain standard GDL90
// that any EFB decoder understands. Leaves the client's WiFi free for internet (e.g. a phone hotspot), and works on
// iOS/iPadOS where Bluetooth SPP does not.
//
// Service layout (UUID base 0BEExxxx-1090-46F0-A9AC-52D6BE4C29CC, "0BEE 1090" = ADSBee 1090):
//   0BEE0001 ADS-B Receiver Service
//   0BEE0010 Traffic  (notify) - GDL90 Traffic Report (0x14) and UAT basic/long reports (30/31)
//   0BEE0011 Ownship  (notify) - GDL90 Ownship Report (0x0A) / Ownship Geometric Altitude (0x0B)
//   0BEE0012 Status   (notify) - GDL90 Heartbeat (0x00) / Initialization (0x02)
//   0BEE0013 Uplink   (notify) - GDL90 Uplink Data (0x07, FIS-B weather), fragmented with a 1-byte header
//   0BEE0020 Control  (write)  - reserved for configuration commands
//
// Uplink frames (~450 bytes framed) exceed one notification, so the Uplink characteristic fragments them: header
// bit7 = first, bit6 = last, bits 0-5 = sequence mod 64. All other characteristics are one complete message per
// notification. FIS-B applies wherever a 978 MHz uplink network exists (US FAA; Canadian CIFIB stations, cifib.ca).
// The interface spec lives in the AvareX repo at docs/BLE_ADSB_SERVICE.md.
namespace ble_gdl90 {

// Registers the GATT services with the NimBLE host. Must be called after nimble_port_init() and before the host task
// starts; BleHostEnsureInitialized() in remote_id_ble.cpp does this at the single shared host bring-up point.
bool RegisterServices();

// Starts (or re-starts) the connectable advertising instance. Called from the shared host sync callback, and again
// internally after connect/disconnect events.
void OnHostSync();

// Brings the shared BLE host up (if not already up for Remote ID) so the GDL90 service is connectable. Call once
// during application init. Returns false if Bluetooth is not in the build or host init failed.
bool Start();

// Routes one complete framed GDL90 message (0x7E ... 0x7E) to the matching characteristic and notifies all subscribed
// clients. Uplink messages (0x07) are fragmented onto the Uplink characteristic; everything else is one message per
// notification. Cheap no-op with no subscribers.
bool SendGDL90Message(const uint8_t* buf, uint16_t len_bytes);

// True if any connected client is subscribed to at least one characteristic (callers can skip building messages).
bool HasSubscribers();

}  // namespace ble_gdl90
