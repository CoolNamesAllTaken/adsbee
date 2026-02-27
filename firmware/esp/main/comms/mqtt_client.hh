#pragma once

#include "esp_log.h"
#include "mqtt_client.h"  // ESP-IDF MQTT client
#include "mqtt_config.h"
#include "data_structures.hh"
#include "mqtt/mqtt_protocol.hh"
#include "settings.hh"

#if CONFIG_MQTT_OTA_ENABLED
#include <memory>
class MQTTOTAHandler;
#endif

/**
 * MQTT client for real-time ADS-B data streaming.
 * Supports both JSON and binary formats with immediate delivery.
 * Optionally supports OTA firmware updates via MQTT when CONFIG_MQTT_OTA_ENABLED.
 */
class ADSBeeMQTTClient {
public:
    struct Config {
        uint8_t feed_index;           // Which feed (0-3) this client is for
        const char* broker_uri;       // From settings feed_uris
        uint16_t broker_port;         // From settings feed_ports
        const char* client_id;        // Unique client ID
        const char* device_id;        // Device identifier for topic hierarchy
        MQTTProtocol::Format format;  // kFormatJSON or kFormatBinary
        uint8_t mqtt_content = 0;     // 0=ALL, 1=RAW, 2=STATUS
        bool ota_enabled = false;     // Enable OTA via MQTT
    };

    ADSBeeMQTTClient();
    ~ADSBeeMQTTClient();

    /**
     * Initialize MQTT client for a specific feed
     * @param[in] config Configuration from settings
     * @return true on success
     */
    bool Init(const Config& config);

    /**
     * Start connection to broker
     * @return true if connection initiated
     */
    bool Connect();

    /**
     * Disconnect from broker
     */
    void Disconnect();

    /**
     * Check connection status
     * @return true if connected
     */
    bool IsConnected() const { return connected_; }

    /**
     * Publish decoded packet immediately (no buffering)
     */
    bool PublishPacket(const DecodedModeSPacket& packet,
                      MQTTProtocol::TransponderProtocol protocol = MQTTProtocol::kModeS);

    /**
     * Publish decoded UAT ADS-B packet immediately (no buffering)
     */
    bool PublishUATPacket(const DecodedUATADSBPacket& packet);

    /**
     * Publish aircraft status immediately
     */
    bool PublishAircraft(const ModeSAircraft& aircraft,
                        MQTTProtocol::TransponderProtocol protocol = MQTTProtocol::kModeS);

    /**
     * Publish device telemetry
     */
    bool PublishTelemetry(const MQTTProtocol::TelemetryData& telemetry);

    /**
     * Publish GNSS position
     */
    bool PublishGNSS(const MQTTProtocol::GNSSData& gnss);

    /**
     * Generic publish method for arbitrary topic/payload (used by OTA handler)
     * @param[in] topic MQTT topic string
     * @param[in] data Payload data
     * @param[in] len Payload length
     * @param[in] qos Quality of service (0, 1, or 2)
     * @param[in] retain Whether to set retain flag
     * @return true on success
     */
    bool Publish(const char* topic, const uint8_t* data, size_t len, int qos = 0, bool retain = false);

    /**
     * Subscribe to an MQTT topic
     * @param[in] topic Topic filter string
     * @param[in] qos Quality of service
     * @return true on success
     */
    bool Subscribe(const char* topic, int qos = 1);

    /**
     * Get device ID string
     */
    const char* GetDeviceId() const { return device_id_; }

    const Config& GetConfig() const { return config_; }
    MQTTProtocol::Format GetFormat() const { return config_.format; }

    uint32_t GetBandwidthPerHour(uint16_t messages_per_hour) const {
        return MQTTProtocol::EstimateBandwidth(config_.format, messages_per_hour);
    }

    uint32_t GetMessagesSent() const { return messages_sent_; }
    uint32_t GetBytesSent() const { return bytes_sent_; }

private:
    esp_mqtt_client_handle_t client_;
    Config config_;
    bool connected_;
    bool initialized_;
    bool started_;  // Track whether esp_mqtt_client_start() has been called

    // Store strings persistently
    char client_id_[64];
    char device_id_[32];
    char broker_uri_[256];

    // Statistics
    uint32_t messages_sent_;
    uint32_t bytes_sent_;

#if CONFIG_MQTT_OTA_ENABLED
    // OTA handler (created if ota_enabled in config)
    std::unique_ptr<MQTTOTAHandler> ota_handler_;

    // Subscribe to OTA topics on connect
    void SubscribeOTATopics();

    // Route incoming MQTT data messages to OTA handler
    void HandleOTAMessage(const char* topic, const uint8_t* data, size_t data_len);

    // Buffer for reassembling fragmented MQTT messages
    uint8_t* mqtt_data_buffer_ = nullptr;
    size_t mqtt_data_buffer_len_ = 0;
    size_t mqtt_data_total_len_ = 0;
#endif

    // MQTT event handler
    static void mqtt_event_handler(void* handler_args, esp_event_base_t base,
                                   int32_t event_id, void* event_data);
    void HandleEvent(esp_mqtt_event_handle_t event);
};

