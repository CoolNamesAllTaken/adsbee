#include "mqtt_client.hh"
#include "hal.hh"
#include "comms.hh"  // For CONSOLE_* macros
#include <string.h>  // For strncpy

#if CONFIG_MQTT_OTA_ENABLED
#include "mqtt_ota.hh"
#include <cstdlib>  // For strtoul
#include <cstring>  // For strstr, strrchr
#endif

// Compile-time check that Settings::MQTTFormat and MQTTProtocol::Format enum values match.
static_assert(static_cast<uint8_t>(SettingsManager::Settings::kMQTTFormatJSON) ==
              static_cast<uint8_t>(MQTTProtocol::kFormatJSON),
              "Settings::kMQTTFormatJSON must match MQTTProtocol::kFormatJSON");
static_assert(static_cast<uint8_t>(SettingsManager::Settings::kMQTTFormatBinary) ==
              static_cast<uint8_t>(MQTTProtocol::kFormatBinary),
              "Settings::kMQTTFormatBinary must match MQTTProtocol::kFormatBinary");

static const char* TAG = "MQTT";

ADSBeeMQTTClient::ADSBeeMQTTClient()
    : client_(nullptr), connected_(false), initialized_(false), started_(false),
      messages_sent_(0), bytes_sent_(0) {
}

ADSBeeMQTTClient::~ADSBeeMQTTClient() {
#if CONFIG_MQTT_OTA_ENABLED
    if (mqtt_data_buffer_) {
        free(mqtt_data_buffer_);
        mqtt_data_buffer_ = nullptr;
    }
#endif
    if (client_) {
        Disconnect();
        esp_mqtt_client_destroy(client_);
    }
}

void ADSBeeMQTTClient::mqtt_event_handler(void* handler_args, esp_event_base_t base,
                                           int32_t event_id, void* event_data) {
    ADSBeeMQTTClient* client = static_cast<ADSBeeMQTTClient*>(handler_args);
    esp_mqtt_event_handle_t event = static_cast<esp_mqtt_event_handle_t>(event_data);
    client->HandleEvent(event);
}

void ADSBeeMQTTClient::HandleEvent(esp_mqtt_event_handle_t event) {
    switch (event->event_id) {
        case MQTT_EVENT_CONNECTED:
            CONSOLE_INFO(TAG, "Connected to MQTT broker (feed %d)", config_.feed_index);
            connected_ = true;
#if CONFIG_MQTT_OTA_ENABLED
            if (ota_handler_) {
                SubscribeOTATopics();
                ota_handler_->Initialize(this);
            }
#endif
            break;

        case MQTT_EVENT_DISCONNECTED:
            CONSOLE_WARNING(TAG, "Disconnected from MQTT broker (feed %d)", config_.feed_index);
            connected_ = false;
            break;

        case MQTT_EVENT_ERROR:
            CONSOLE_ERROR(TAG, "MQTT error on feed %d", config_.feed_index);
            break;

#if CONFIG_MQTT_OTA_ENABLED
        case MQTT_EVENT_DATA: {
            if (!ota_handler_) break;

            // Handle fragmented MQTT messages
            if (event->current_data_offset == 0) {
                // First fragment or complete message
                mqtt_data_total_len_ = event->total_data_len;
                mqtt_data_buffer_len_ = 0;

                if (mqtt_data_total_len_ > (size_t)event->data_len) {
                    // Fragmented message - allocate buffer
                    if (mqtt_data_buffer_) {
                        free(mqtt_data_buffer_);
                    }
                    mqtt_data_buffer_ = (uint8_t*)malloc(mqtt_data_total_len_);
                    if (!mqtt_data_buffer_) {
                        CONSOLE_ERROR(TAG, "Failed to allocate buffer for fragmented MQTT message (%zu bytes)",
                                     mqtt_data_total_len_);
                        break;
                    }
                }
            }

            if (mqtt_data_buffer_ && mqtt_data_total_len_ > (size_t)event->data_len) {
                // Accumulate fragment
                if (mqtt_data_buffer_len_ + event->data_len <= mqtt_data_total_len_) {
                    memcpy(mqtt_data_buffer_ + mqtt_data_buffer_len_, event->data, event->data_len);
                    mqtt_data_buffer_len_ += event->data_len;
                }

                // Check if all fragments received
                if (mqtt_data_buffer_len_ >= mqtt_data_total_len_) {
                    // Complete message assembled
                    // Null-terminate the topic
                    char topic[MQTT_MAX_TOPIC_LEN];
                    size_t topic_len = event->topic_len < (int)(sizeof(topic) - 1) ? event->topic_len : sizeof(topic) - 1;
                    memcpy(topic, event->topic, topic_len);
                    topic[topic_len] = '\0';

                    HandleOTAMessage(topic, mqtt_data_buffer_, mqtt_data_buffer_len_);

                    free(mqtt_data_buffer_);
                    mqtt_data_buffer_ = nullptr;
                    mqtt_data_buffer_len_ = 0;
                    mqtt_data_total_len_ = 0;
                }
            } else {
                // Complete (non-fragmented) message
                char topic[MQTT_MAX_TOPIC_LEN];
                size_t topic_len = event->topic_len < (int)(sizeof(topic) - 1) ? event->topic_len : sizeof(topic) - 1;
                memcpy(topic, event->topic, topic_len);
                topic[topic_len] = '\0';

                HandleOTAMessage(topic, (const uint8_t*)event->data, event->data_len);
            }
            break;
        }
#endif

        default:
            break;
    }
}

bool ADSBeeMQTTClient::Init(const Config& config) {
    if (initialized_) {
        return true;
    }

    config_ = config;

    // Copy strings to persistent storage
    if (config.client_id) {
        strncpy(client_id_, config.client_id, sizeof(client_id_) - 1);
        client_id_[sizeof(client_id_) - 1] = '\0';
        config_.client_id = client_id_;
    }

    if (config.device_id) {
        strncpy(device_id_, config.device_id, sizeof(device_id_) - 1);
        device_id_[sizeof(device_id_) - 1] = '\0';
        config_.device_id = device_id_;
    }

    // Build and store broker URI with port
    snprintf(broker_uri_, sizeof(broker_uri_), "mqtt://%s:%d",
             config.broker_uri, config.broker_port);

    esp_mqtt_client_config_t mqtt_cfg = {};
    mqtt_cfg.broker.address.uri = broker_uri_;
    mqtt_cfg.credentials.client_id = client_id_;
    mqtt_cfg.session.keepalive = 60;
    mqtt_cfg.network.disable_auto_reconnect = false;
    mqtt_cfg.network.reconnect_timeout_ms = 5000;
    // Buffer for MQTT send/receive. OTA chunks larger than this arrive as
    // fragmented MQTT_EVENT_DATA events and are reassembled in HandleEvent().
    mqtt_cfg.buffer.size = MQTT_MAX_PAYLOAD_LEN;

    client_ = esp_mqtt_client_init(&mqtt_cfg);
    if (!client_) {
        CONSOLE_ERROR(TAG, "Failed to initialize MQTT client for feed %d", config.feed_index);
        return false;
    }

    esp_err_t err = esp_mqtt_client_register_event(client_, static_cast<esp_mqtt_event_id_t>(ESP_EVENT_ANY_ID),
                                                    mqtt_event_handler, this);
    if (err != ESP_OK) {
        CONSOLE_ERROR(TAG, "Failed to register MQTT event handler: %s", esp_err_to_name(err));
        esp_mqtt_client_destroy(client_);
        client_ = nullptr;
        return false;
    }

#if CONFIG_MQTT_OTA_ENABLED
    // Create OTA handler if enabled
    if (config.ota_enabled) {
        ota_handler_ = std::make_unique<MQTTOTAHandler>(device_id_, config.feed_index);
        CONSOLE_INFO(TAG, "OTA handler created for feed %d", config.feed_index);
    }
#endif

    initialized_ = true;
    CONSOLE_INFO(TAG, "MQTT client initialized for %s:%d (format=%s, ota=%s)",
                 config.broker_uri, config.broker_port,
                 MQTTProtocol::FormatToString(config.format),
                 config.ota_enabled ? "enabled" : "disabled");
    return true;
}

bool ADSBeeMQTTClient::Connect() {
    if (!initialized_ || !client_) {
        return false;
    }

    if (connected_) {
        return true;
    }

    // Only call esp_mqtt_client_start() once. After that, the ESP-IDF MQTT
    // library handles reconnection internally via its own task.
    if (started_) {
        return true;  // Already started, waiting for connection/reconnection
    }

    esp_err_t err = esp_mqtt_client_start(client_);
    if (err != ESP_OK) {
        CONSOLE_ERROR(TAG, "Failed to start MQTT client: %s", esp_err_to_name(err));
        return false;
    }

    started_ = true;
    return true;
}

void ADSBeeMQTTClient::Disconnect() {
    if (initialized_ && client_) {
        esp_mqtt_client_stop(client_);
        connected_ = false;
        started_ = false;
    }
}

bool ADSBeeMQTTClient::Publish(const char* topic, const uint8_t* data, size_t len, int qos, bool retain) {
    if (!initialized_ || !client_ || !connected_) {
        return false;
    }

    int msg_id = esp_mqtt_client_publish(client_, topic, (const char*)data, len, qos, retain);

    if (msg_id >= 0) {
        messages_sent_++;
        bytes_sent_ += len;
        return true;
    }

    return false;
}

bool ADSBeeMQTTClient::Subscribe(const char* topic, int qos) {
    if (!initialized_ || !client_ || !connected_) {
        return false;
    }

    int msg_id = esp_mqtt_client_subscribe(client_, topic, qos);
    if (msg_id >= 0) {
        CONSOLE_INFO(TAG, "Subscribed to %s (qos=%d)", topic, qos);
        return true;
    }

    CONSOLE_ERROR(TAG, "Failed to subscribe to %s", topic);
    return false;
}

#if CONFIG_MQTT_OTA_ENABLED
void ADSBeeMQTTClient::SubscribeOTATopics() {
    if (!connected_ || !ota_handler_) return;

    char topic[MQTT_MAX_TOPIC_LEN];

    // Subscribe to OTA control manifest
    snprintf(topic, sizeof(topic), "%s/ota/control/manifest", device_id_);
    Subscribe(topic, 1);

    // Subscribe to OTA control commands
    snprintf(topic, sizeof(topic), "%s/ota/control/command", device_id_);
    Subscribe(topic, 1);

    // Subscribe to OTA data chunks (wildcard)
    snprintf(topic, sizeof(topic), "%s/ota/data/chunk/+", device_id_);
    Subscribe(topic, 1);

    CONSOLE_INFO(TAG, "Subscribed to OTA topics for device %s", device_id_);
}

void ADSBeeMQTTClient::HandleOTAMessage(const char* topic, const uint8_t* data, size_t data_len) {
    if (!ota_handler_) return;

    if (strstr(topic, "/ota/control/manifest")) {
        CONSOLE_INFO(TAG, "Received OTA manifest (%zu bytes)", data_len);
        ota_handler_->HandleManifest(data, data_len);

    } else if (strstr(topic, "/ota/control/command")) {
        CONSOLE_INFO(TAG, "Received OTA command");
        ota_handler_->HandleCommand(data, data_len);

    } else if (strstr(topic, "/ota/data/chunk/")) {
        const char* chunk_str = strrchr(topic, '/');
        if (!chunk_str) return;
        chunk_str++;
        uint32_t chunk_index = strtoul(chunk_str, nullptr, 10);
        ota_handler_->HandleChunk(chunk_index, data, data_len);
    }
}
#endif

bool ADSBeeMQTTClient::PublishPacket(const DecodedModeSPacket& packet,
                                     MQTTProtocol::TransponderProtocol protocol) {
    if (!initialized_ || !client_ || !connected_) {
        return false;
    }

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatPacket(packet, buffer, sizeof(buffer), config_.format, protocol);

    if (len == 0) {
        return false;
    }

    uint32_t icao24 = packet.icao_address;
    char topic[MQTTProtocol::kMaxTopicSize];
    bool use_short = (config_.format == MQTTProtocol::kFormatBinary);

    if (!MQTTProtocol::GetTopic(icao24, "raw", topic, sizeof(topic), protocol, use_short, config_.device_id)) {
        return false;
    }

    int msg_id = esp_mqtt_client_publish(client_, topic, (const char*)buffer, len, 0, false);

    if (msg_id >= 0) {
        messages_sent_++;
        bytes_sent_ += len;
        return true;
    }

    return false;
}

bool ADSBeeMQTTClient::PublishUATPacket(const DecodedUATADSBPacket& packet) {
    if (!initialized_ || !client_ || !connected_) {
        return false;
    }

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatUATPacket(packet, buffer, sizeof(buffer), config_.format);

    if (len == 0) {
        return false;
    }

    uint32_t icao24 = packet.GetICAOAddress();
    char topic[MQTTProtocol::kMaxTopicSize];
    bool use_short = (config_.format == MQTTProtocol::kFormatBinary);

    if (!MQTTProtocol::GetTopic(icao24, "raw", topic, sizeof(topic), MQTTProtocol::kUAT, use_short, config_.device_id)) {
        return false;
    }

    int msg_id = esp_mqtt_client_publish(client_, topic, (const char*)buffer, len, 0, false);

    if (msg_id >= 0) {
        messages_sent_++;
        bytes_sent_ += len;
        return true;
    }

    return false;
}

bool ADSBeeMQTTClient::PublishAircraft(const ModeSAircraft& aircraft,
                                       MQTTProtocol::TransponderProtocol protocol) {
    if (!connected_) {
        return false;
    }

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatAircraft(aircraft, buffer, sizeof(buffer), config_.format, protocol);

    if (len == 0) {
        return false;
    }

    char topic[MQTTProtocol::kMaxTopicSize];
    bool use_short = (config_.format == MQTTProtocol::kFormatBinary);

    if (!MQTTProtocol::GetTopic(aircraft.icao_address, "status", topic, sizeof(topic), protocol, use_short, config_.device_id)) {
        return false;
    }

    int msg_id = esp_mqtt_client_publish(client_, topic, (const char*)buffer, len, 0, false);

    if (msg_id >= 0) {
        messages_sent_++;
        bytes_sent_ += len;
        return true;
    }

    return false;
}

bool ADSBeeMQTTClient::PublishTelemetry(const MQTTProtocol::TelemetryData& telemetry) {
    if (!connected_) {
        return false;
    }

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatTelemetry(telemetry, buffer, sizeof(buffer), config_.format);

    if (len == 0) {
        return false;
    }

    char topic[MQTTProtocol::kMaxTopicSize];
    bool use_short = (config_.format == MQTTProtocol::kFormatBinary);

    if (!MQTTProtocol::GetTelemetryTopic(topic, sizeof(topic), "telemetry", use_short, config_.device_id)) {
        return false;
    }

    int msg_id = esp_mqtt_client_publish(client_, topic, (const char*)buffer, len, 0, false);

    if (msg_id >= 0) {
        messages_sent_++;
        bytes_sent_ += len;
        return true;
    }

    return false;
}

bool ADSBeeMQTTClient::PublishGNSS(const MQTTProtocol::GNSSData& gnss) {
    if (!connected_) {
        return false;
    }

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatGNSS(gnss, buffer, sizeof(buffer), config_.format);

    if (len == 0) {
        return false;
    }

    char topic[MQTTProtocol::kMaxTopicSize];
    bool use_short = (config_.format == MQTTProtocol::kFormatBinary);

    if (!MQTTProtocol::GetTelemetryTopic(topic, sizeof(topic), "position", use_short, config_.device_id)) {
        return false;
    }

    int msg_id = esp_mqtt_client_publish(client_, topic, (const char*)buffer, len, 0, false);

    if (msg_id >= 0) {
        messages_sent_++;
        bytes_sent_ += len;
        return true;
    }

    return false;
}
