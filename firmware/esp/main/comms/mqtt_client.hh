#pragma once

#include <cstdint>
#include <string>
#include <unordered_map>
#include <chrono>
#include <functional>
#include "mqtt_client.h"  // ESP-IDF MQTT client
#include "transponder_packet.hh"
#include "settings.hh"
#include "console.hh"

namespace MQTT {

// Message types matching the protobuf definitions
struct AircraftStatus {
    std::string icao;
    uint8_t band;  // 1=1090MHz, 2=UAT
    std::string callsign;
    std::string category;
    double lat;
    double lon;
    int32_t alt_ft;
    float hdg_deg;
    float spd_kts;
    int32_t vr_fpm;
    std::string squawk;
    bool on_ground;
    uint64_t t_ms;
};

struct Telemetry {
    uint32_t uptime_sec;
    uint32_t msgs_rx;
    uint32_t msgs_tx;
    int32_t cpu_temp_c;
    uint32_t mem_free_kb;
    int32_t noise_floor_dbm;
    bool rx_1090;
    bool rx_978;
    bool wifi;
    bool mqtt;
    std::string fw_version;
    uint32_t mps_total;
    std::vector<uint32_t> mps_feeds;
};

struct GPS {
    double lat;
    double lon;
    float alt_m;
    uint8_t fix;  // 0=none, 1=2D, 2=3D
    uint32_t sats;
    float hdop;
    uint64_t ts;
};

// Rate limiter for 1Hz per aircraft
class AircraftRateLimiter {
public:
    bool ShouldPublish(const std::string& icao);
    void Reset();

private:
    struct AircraftState {
        std::chrono::steady_clock::time_point last_published;
        AircraftStatus last_status;
    };

    std::unordered_map<std::string, AircraftState> aircraft_states_;
    static constexpr auto kMinPublishInterval = std::chrono::milliseconds(1000);  // 1Hz
};

class MQTTClient {
public:
    struct Config {
        std::string broker_uri;
        uint16_t port;
        std::string username;
        std::string password;
        std::string client_id;
        std::string device_id;
        bool use_tls;
        SettingsManager::MQTTFormat format;
        SettingsManager::MQTTReportMode report_mode;
        uint16_t telemetry_interval_sec;
        uint16_t gps_interval_sec;
        uint8_t status_rate_hz;
    };

    MQTTClient(const Config& config, uint16_t feed_index);
    ~MQTTClient();

    // Connection management
    bool Connect();
    void Disconnect();
    bool IsConnected() const;

    // Publishing functions
    bool PublishAircraftStatus(const TransponderPacket& packet, uint8_t band);
    bool PublishTelemetry(const Telemetry& telemetry);
    bool PublishGPS(const GPS& gps);
    bool PublishRaw(const TransponderPacket& packet, uint8_t band);

    // Statistics
    struct Stats {
        uint32_t messages_published;
        uint32_t messages_dropped;
        uint32_t bytes_sent;
        uint32_t reconnect_count;
        std::string last_error;
    };
    Stats GetStats() const { return stats_; }

private:
    // ESP-IDF MQTT event handler
    static void MQTTEventHandler(void* handler_args, esp_event_base_t base,
                                  int32_t event_id, void* event_data);

    // Connection management with exponential backoff
    void HandleConnect();
    void HandleDisconnect();
    void ScheduleReconnect();

    // Topic generation
    std::string GetStatusTopic(const std::string& icao, uint8_t band) const;
    std::string GetRawTopic(const std::string& icao, uint8_t band) const;
    std::string GetTelemetryTopic() const;
    std::string GetGPSTopic() const;
    std::string GetOnlineTopic() const;

    // Serialization
    std::string SerializeStatusJSON(const AircraftStatus& status) const;
    std::string SerializeTelemetryJSON(const Telemetry& telemetry) const;
    std::string SerializeGPSJSON(const GPS& gps) const;
    std::vector<uint8_t> SerializeStatusBinary(const AircraftStatus& status) const;
    std::vector<uint8_t> SerializeTelemetryBinary(const Telemetry& telemetry) const;
    std::vector<uint8_t> SerializeGPSBinary(const GPS& gps) const;

    // Convert TransponderPacket to AircraftStatus
    AircraftStatus PacketToStatus(const TransponderPacket& packet, uint8_t band) const;

    // Configuration
    Config config_;
    uint16_t feed_index_;

    // MQTT client handle
    esp_mqtt_client_handle_t client_;

    // Connection state
    bool connected_;
    std::chrono::steady_clock::time_point last_connect_attempt_;
    uint32_t reconnect_delay_ms_;
    static constexpr uint32_t kInitialReconnectDelayMs = 1000;
    static constexpr uint32_t kMaxReconnectDelayMs = 60000;
    static constexpr float kReconnectBackoffFactor = 2.0f;
    static constexpr float kReconnectJitterFactor = 0.2f;

    // Rate limiting
    AircraftRateLimiter rate_limiter_;

    // Telemetry/GPS publishing timers
    std::chrono::steady_clock::time_point last_telemetry_publish_;
    std::chrono::steady_clock::time_point last_gps_publish_;

    // Statistics
    mutable Stats stats_;
};

}  // namespace MQTT