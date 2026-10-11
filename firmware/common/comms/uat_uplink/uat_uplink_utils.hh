#pragma once

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "buffer_utils.hh"

// Framing of UAT ground uplinks (FIS-B) for map clients. Both formats are documented in README.md in this folder.

// De-interleaved uplink: 8 Byte UAT header, then 424 Bytes of application data.
static constexpr uint16_t kUATUplinkPayloadNumBytes = 432;
static constexpr int8_t kUATUplinkRSSIUnknown = INT8_MIN;

// WebSocket message: payload, then an 8 Byte trailer.
static constexpr uint16_t kUATUplinkMessageRSSIOffset = kUATUplinkPayloadNumBytes;           // int8_t, dBm.
static constexpr uint16_t kUATUplinkMessageReservedOffset = kUATUplinkPayloadNumBytes + 1;   // 3 Bytes, zero.
static constexpr uint16_t kUATUplinkMessageTimestampOffset = kUATUplinkPayloadNumBytes + 4;  // uint32_t, little endian.
static constexpr uint16_t kUATUplinkMessageNumBytes = kUATUplinkPayloadNumBytes + 8;

// {"uat_uplink":"<576 chars>","rssi":-127,"t":4294967295}\n plus the null terminator.
static constexpr uint16_t kUATUplinkBase64NumChars = (kUATUplinkPayloadNumBytes + 2) / 3 * 4;
static constexpr uint16_t kUATUplinkJSONLineMaxNumChars = kUATUplinkBase64NumChars + 48;

// RSSI as sent to clients. Raw packets use INT16_MIN for an unknown RSSI.
inline int8_t UATUplinkRSSIToInt8(int16_t rssi_dbm) {
    if (rssi_dbm == INT16_MIN) return kUATUplinkRSSIUnknown;
    if (rssi_dbm < -127) return -127;
    return rssi_dbm > INT8_MAX ? INT8_MAX : static_cast<int8_t>(rssi_dbm);
}

/**
 * Builds the binary message sent on the /uplink WebSocket.
 * @param[out] buf Buffer of at least kUATUplinkMessageNumBytes.
 * @param[in] payload De-interleaved uplink, kUATUplinkPayloadNumBytes long.
 * @param[in] rssi_dbm Signal strength, or INT16_MIN if unknown.
 * @param[in] timestamp_ms Receive time, in milliseconds since the receiver booted.
 * @retval Number of bytes written.
 */
inline uint16_t BuildUATUplinkMessage(uint8_t* buf, const uint8_t* payload, int16_t rssi_dbm, uint32_t timestamp_ms) {
    memcpy(buf, payload, kUATUplinkPayloadNumBytes);
    buf[kUATUplinkMessageRSSIOffset] = static_cast<uint8_t>(UATUplinkRSSIToInt8(rssi_dbm));
    memset(buf + kUATUplinkMessageReservedOffset, 0, 3);
    for (uint16_t i = 0; i < sizeof(timestamp_ms); i++) {
        buf[kUATUplinkMessageTimestampOffset + i] = (timestamp_ms >> (8 * i)) & 0xFF;
    }
    return kUATUplinkMessageNumBytes;
}

/**
 * Writes the JSON line sent on serial interfaces: {"uat_uplink":"<Base64 payload>","rssi":-80,"t":123456}\n. "rssi"
 * is left out when unknown.
 * @param[out] buf Buffer of at least kUATUplinkJSONLineMaxNumChars.
 * @param[in] payload De-interleaved uplink, kUATUplinkPayloadNumBytes long.
 * @param[in] rssi_dbm Signal strength, or INT16_MIN if unknown.
 * @param[in] timestamp_ms Receive time, in milliseconds since the receiver booted.
 * @retval Number of characters written, not counting the null terminator.
 */
inline uint16_t WriteUATUplinkJSONLine(char* buf, const uint8_t* payload, int16_t rssi_dbm, uint32_t timestamp_ms) {
    static const char kPrefix[] = "{\"uat_uplink\":\"";
    uint16_t n = sizeof(kPrefix) - 1;
    memcpy(buf, kPrefix, n);
    n += ByteBufferToBase64String(buf + n, payload, kUATUplinkPayloadNumBytes);
    int8_t rssi = UATUplinkRSSIToInt8(rssi_dbm);
    if (rssi != kUATUplinkRSSIUnknown) {
        n += snprintf(buf + n, kUATUplinkJSONLineMaxNumChars - n, "\",\"rssi\":%d", rssi);
    } else {
        buf[n++] = '"';
    }
    n += snprintf(buf + n, kUATUplinkJSONLineMaxNumChars - n, ",\"t\":%lu}\n", static_cast<unsigned long>(timestamp_ms));
    return n;
}
