#pragma once

#include "settings.hh"

// ESP32 internal RAM taken by the active network feeds. AT+FEED and AT+MQTT refuse settings that would take more than
// the unit's budget.
//
// Costs are the drop of the lowest free internal heap (10th percentile of 2 s minimums, Beast at 200 msg/s per feed),
// measured on 1090U units without PSRAM; the larger of WiFi and Ethernet:
//   feed        WiFi    Ethernet
//   TCP         4-5 kB  2-3 kB   (8 TCP feeds connecting dipped to 7.7 kB free on WiFi)
//   UDP         1 kB    0.5 kB
//   MQTT        15 kB   12-13 kB once for any number of MQTT feeds (one client)
//   + TLS       6-8 kB  10-11 kB
//   + WebSocket 0-2 kB  2-5 kB
// Budgets keep the lowest free heap at or above 16 kB (where feeds start dropping data) from the idle level: 47 kB with
// WiFi access point and station, 100 kB on Ethernet alone. PSRAM units keep WiFi and lwIP buffers in PSRAM; their
// budgets are an estimate.
namespace FeedRAMBudget {

static constexpr uint32_t kTCPFeedBytes = 5 * 1024;
static constexpr uint32_t kUDPFeedBytes = 1 * 1024;
static constexpr uint32_t kMQTTClientBytes = 15 * 1024;
static constexpr uint32_t kMQTTTLSBytes = 10 * 1024;
static constexpr uint32_t kMQTTWebSocketBytes = 2 * 1024;

static constexpr uint32_t kBudgetBytesWiFi = 32 * 1024;
static constexpr uint32_t kBudgetBytesEthernet = 80 * 1024;
static constexpr uint32_t kBudgetBytesPSRAMExtra = 24 * 1024;

/**
 * Feed RAM budget of a unit: smaller while WiFi (access point or station) is on, larger with PSRAM.
 */
inline uint32_t BudgetBytes(const SettingsManager::Settings& settings, bool has_psram) {
    const SettingsManager::Settings::CoreNetworkSettings& net = settings.core_network_settings;
    uint32_t budget = (net.wifi_ap_enabled || net.wifi_sta_enabled) ? kBudgetBytesWiFi : kBudgetBytesEthernet;
    return budget + (has_psram ? kBudgetBytesPSRAMExtra : 0);
}

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
                mqtt = true;
                break;
            default:
                used += kTCPFeedBytes;
                break;
        }
    }
    if (mqtt) {
        const SettingsManager::Settings::MQTTBroker& broker = settings.mqtt_broker;
        used += kMQTTClientBytes + (broker.tls ? kMQTTTLSBytes : 0) +
                (broker.transport == SettingsManager::kMQTTTransportWebSocket ? kMQTTWebSocketBytes : 0);
    }
    return used;
}

}  // namespace FeedRAMBudget
