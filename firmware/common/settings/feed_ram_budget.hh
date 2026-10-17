#pragma once

#include "settings.hh"

// ESP32 internal RAM taken by the active network feeds. AT+FEED and AT+MQTT refuse settings that would take more than
// the unit's budget. Costs are the drop in free internal heap (lowest value over a minute under traffic) per feed, measured
// on an ADSBee 1090U without PSRAM. With PSRAM, feed backlogs, lwIP and WiFi buffers move to PSRAM, so the same costs
// are an upper bound there.
namespace FeedRAMBudget {

static constexpr uint32_t kTCPFeedBytes = 8 * 1024;          // Socket, lwIP send buffer, 4 kB backlog.
static constexpr uint32_t kUDPFeedBytes = 2 * 1024;          // Socket and datagrams in flight.
static constexpr uint32_t kMQTTFeedBytes = 1 * 1024;         // Messages in the shared client's outbox.
static constexpr uint32_t kMQTTClientBytes = 12 * 1024;      // Shared client: task, buffers, socket, outbox.
static constexpr uint32_t kMQTTTLSBytes = 36 * 1024;         // TLS session of the shared client.
static constexpr uint32_t kBudgetBytes = 48 * 1024;          // Leaves room for the web server and firmware updates.
static constexpr uint32_t kBudgetBytesPSRAM = 96 * 1024;

inline uint32_t BudgetBytes(bool has_psram) { return has_psram ? kBudgetBytesPSRAM : kBudgetBytes; }

/**
 * Internal RAM the active feeds of these settings take, including the shared MQTT client once.
 */
inline uint32_t UsedBytes(const SettingsManager::Settings& settings) {
    if (!settings.feeds_enabled) {
        return 0;
    }
    uint32_t used = 0;
    bool mqtt = false;
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        if (!settings.feed_is_active[i]) {
            continue;
        }
        switch (settings.feed_transports[i]) {
            case SettingsManager::kFeedTransportUDP:
                used += kUDPFeedBytes;
                break;
            case SettingsManager::kFeedTransportMQTT:
                used += kMQTTFeedBytes;
                mqtt = true;
                break;
            default:
                used += kTCPFeedBytes;
                break;
        }
    }
    if (mqtt) {
        used += kMQTTClientBytes + (settings.mqtt_broker.tls ? kMQTTTLSBytes : 0);
    }
    return used;
}

}  // namespace FeedRAMBudget
