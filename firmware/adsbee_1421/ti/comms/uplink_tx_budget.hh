#pragma once

#include <stdint.h>

#include "uat_uplink_utils.hh"

// Console UART budget for UAT uplink JSON lines (AIRCRAFT_JSON_UAT_UPLINK), shared with the host tests.
namespace UplinkTxBudget {

// Longest line: {"uat_uplink":"<576 chars>","rssi":-127,"t":4294967295}\n
static constexpr uint16_t kLineMaxNumBytes = kUATUplinkJSONLineMaxNumChars - 3;
// One UAT frame has 32 ground uplink slots per second.
static constexpr uint16_t kMaxLinesPerSecond = 32;
static constexpr uint16_t kUartBitsPerByte = 10;

// Uplink lines are only queued while the TX ring is nearly empty, so a burst of aircraft lines always finds room.
constexpr uint16_t MaxUsedBytes(uint16_t tx_ring_num_bytes) { return tx_ring_num_bytes / 8; }

// True if an uplink line may be queued with free_bytes of the TX ring free. One slot of the ring is never used.
constexpr bool HasRoomForLine(uint16_t free_bytes, uint16_t tx_ring_num_bytes) {
    return free_bytes + MaxUsedBytes(tx_ring_num_bytes) + 1 >= tx_ring_num_bytes;
}

// Uplink lines per second the console carries at baud with nothing else on the line.
constexpr uint32_t LinesPerSecond(uint32_t baud) { return baud / (kUartBitsPerByte * kLineMaxNumBytes); }

// Lowest bit rate that carries every uplink slot. The next standard rate up is 230400 baud.
static constexpr uint32_t kFullStreamMinBaud = kMaxLinesPerSecond * kLineMaxNumBytes * kUartBitsPerByte;

}  // namespace UplinkTxBudget
