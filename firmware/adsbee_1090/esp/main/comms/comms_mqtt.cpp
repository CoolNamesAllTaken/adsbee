#include <ctype.h>

#include "adsbee_server.hh"  // For the aircraft count in the metrics topic.
#include "comms.hh"
#include "crc.hh"
#include "esp_crt_bundle.h"
#include "hal.hh"
#include "hardware_capabilities.hh"

// Reconnect interval of the MQTT client after its broker connection drops.
static const int kMQTTReconnectIntervalMs = 10000;
static const uint32_t kMQTTMetricsIntervalMs = 10000;
// Longest a publish may block the feed task on a slow broker before the client drops the connection.
static const int kMQTTNetworkTimeoutMs = 2000;
// Unsent messages kept by the MQTT client. Messages are dropped while the outbox is larger.
static const int kMQTTOutboxMaxBytesPSRAM = 32768;
static const int kMQTTOutboxMaxBytesInternal = 8192;
static const char kMQTTDefaultTopicPrefix[] = "adsbee";
static const char kMQTTDefaultWebSocketPath[] = "/mqtt";
static const uint16_t kMQTTTopicMaxLen = SettingsManager::Settings::kMQTTTopicPrefixMaxLen + 1 +
                                         2 * SettingsManager::Settings::kFeedReceiverIDNumBytes + 1 +
                                         SettingsManager::kReportingProtocolStrMaxLen;

static void mqtt_event_handler(void* handler_args, esp_event_base_t base, int32_t event_id, void* event_data) {
    comms_manager.MQTTEventHandler(event_id, static_cast<esp_mqtt_event_handle_t>(event_data));
}

void CommsManager::MQTTTopic(const char* suffix, char* topic, size_t topic_size) {
    const char* prefix = settings_manager.settings.mqtt_broker.topic_prefix;
    // Every feed slot carries the device's receiver ID.
    char receiver_id[2 * SettingsManager::Settings::kFeedReceiverIDNumBytes + 1];
    SettingsManager::ReceiverIDToStr(settings_manager.settings.feed_receiver_ids[0], receiver_id);
    snprintf(topic, topic_size, "%s/%s/%s", prefix[0] ? prefix : kMQTTDefaultTopicPrefix, receiver_id, suffix);
}

uint32_t CommsManager::MQTTConfigCRC() {
    const SettingsManager::Settings& s = settings_manager.settings;
    uint32_t crc = crc32_ieee_802_3(reinterpret_cast<const uint8_t*>(&s.mqtt_broker), sizeof(s.mqtt_broker));
    return crc32_ieee_802_3(s.feed_receiver_ids[0], sizeof(s.feed_receiver_ids[0]), crc);
}

void CommsManager::UpdateMQTTClient() {
    const SettingsManager::Settings& s = settings_manager.settings;
    bool needed = false;
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds && s.feeds_enabled; i++) {
        needed |= s.feed_is_active[i] && s.feed_transports[i] == SettingsManager::kFeedTransportMQTT;
    }
    needed &= s.mqtt_broker.host[0] != '\0';
    if (mqtt_client_ != nullptr && (!needed || MQTTConfigCRC() != mqtt_config_crc_)) {
        StopMQTTClient();
        mqtt_last_start_timestamp_ms_ = 0;  // Restart without waiting.
    }
    if (!needed || mqtt_client_ != nullptr) {
        return;
    }
    uint32_t timestamp_ms = get_time_since_boot_ms();
    if (mqtt_last_start_timestamp_ms_ != 0 && timestamp_ms - mqtt_last_start_timestamp_ms_ <= kMQTTReconnectIntervalMs) {
        return;
    }
    mqtt_last_start_timestamp_ms_ = timestamp_ms;
    mqtt_config_crc_ = MQTTConfigCRC();

    const SettingsManager::Settings::MQTTBroker& mqtt = s.mqtt_broker;
    char receiver_id[2 * SettingsManager::Settings::kFeedReceiverIDNumBytes + 1];
    SettingsManager::ReceiverIDToStr(settings_manager.settings.feed_receiver_ids[0], receiver_id);
    // MQTT 3.1.1 brokers must accept client IDs of up to 23 characters, so this takes the last 12 hex digits of the
    // receiver ID.
    char client_id[24];
    snprintf(client_id, sizeof(client_id), "adsbee-%.12s", receiver_id + 4);
    char status_topic[kMQTTTopicMaxLen + 1];
    MQTTTopic("status", status_topic, sizeof(status_topic));

    bool websocket = mqtt.transport == SettingsManager::kMQTTTransportWebSocket;
    esp_mqtt_client_config_t config = {};  // The client copies the strings.
    config.broker.address.hostname = mqtt.host;
    config.broker.address.port = mqtt.port;
    if (websocket) {
        config.broker.address.transport = mqtt.tls ? MQTT_TRANSPORT_OVER_WSS : MQTT_TRANSPORT_OVER_WS;
        config.broker.address.path = mqtt.websocket_path[0] ? mqtt.websocket_path : kMQTTDefaultWebSocketPath;
    } else {
        config.broker.address.transport = mqtt.tls ? MQTT_TRANSPORT_OVER_SSL : MQTT_TRANSPORT_OVER_TCP;
    }
    if (mqtt.tls) {
        config.broker.verification.crt_bundle_attach = esp_crt_bundle_attach;
    }
    config.credentials.client_id = client_id;
    if (mqtt.username[0] != '\0') {
        config.credentials.username = mqtt.username;
        config.credentials.authentication.password = mqtt.password;
    }
    // The broker publishes "offline" on the status topic if the connection is lost.
    config.session.last_will.topic = status_topic;
    config.session.last_will.msg = "offline";
    config.session.last_will.qos = 1;
    config.session.last_will.retain = 1;
    config.network.reconnect_timeout_ms = kMQTTReconnectIntervalMs;
    config.network.timeout_ms = kMQTTNetworkTimeoutMs;

    esp_mqtt_client_handle_t client = esp_mqtt_client_init(&config);
    if (client == nullptr) {
        CONSOLE_ERROR("CommsManager::UpdateMQTTClient", "Unable to create the MQTT client.");
        return;
    }
    esp_mqtt_client_register_event(client, MQTT_EVENT_ANY, mqtt_event_handler, nullptr);
    // Set before the start: the event handler ignores events of other clients.
    mqtt_client_ = client;
    if (esp_mqtt_client_start(client) != ESP_OK) {
        CONSOLE_ERROR("CommsManager::UpdateMQTTClient", "Unable to start the MQTT client.");
        mqtt_client_ = nullptr;
        esp_mqtt_client_destroy(client);
        return;
    }
    CONSOLE_INFO("CommsManager::UpdateMQTTClient", "Connecting to MQTT broker %s:%d%s%s.", mqtt.host, mqtt.port,
                 websocket ? " over WebSocket" : "", mqtt.tls ? " with TLS" : "");
}

void CommsManager::StopMQTTClient() {
    esp_mqtt_client_handle_t client = mqtt_client_;
    if (client == nullptr) {
        return;
    }
    if (mqtt_is_connected_) {
        // A clean disconnect doesn't trigger the last will.
        char status_topic[kMQTTTopicMaxLen + 1];
        MQTTTopic("status", status_topic, sizeof(status_topic));
        esp_mqtt_client_publish(client, status_topic, "offline", 0, 1, 1);
    }
    mqtt_client_ = nullptr;
    mqtt_is_connected_ = false;
    esp_mqtt_client_destroy(client);
}

void CommsManager::MQTTEventHandler(int32_t event_id, esp_mqtt_event_handle_t event) {
    if (event->client != mqtt_client_) {
        return;
    }
    const char* host = settings_manager.settings.mqtt_broker.host;
    switch (event_id) {
        case MQTT_EVENT_CONNECTED: {
            char status_topic[kMQTTTopicMaxLen + 1];
            MQTTTopic("status", status_topic, sizeof(status_topic));
            esp_mqtt_client_enqueue(event->client, status_topic, "online", 0, 1, 1, true);
            mqtt_is_connected_ = true;
            CONSOLE_INFO("CommsManager::MQTTEventHandler", "Connected to MQTT broker %s.", host);
            break;
        }
        case MQTT_EVENT_DISCONNECTED:
            if (mqtt_is_connected_) {
                CONSOLE_WARNING("CommsManager::MQTTEventHandler", "Disconnected from MQTT broker %s.", host);
            }
            mqtt_is_connected_ = false;  // The client reconnects by itself.
            break;
        case MQTT_EVENT_ERROR:
            if (event->error_handle->error_type == MQTT_ERROR_TYPE_CONNECTION_REFUSED) {
                CONSOLE_ERROR("CommsManager::MQTTEventHandler",
                              "MQTT broker %s refused the connection (return code %d): check username and password.",
                              host, event->error_handle->connect_return_code);
            } else {
                CONSOLE_ERROR("CommsManager::MQTTEventHandler",
                              "MQTT connection to %s failed: TLS error 0x%x, socket errno %d.", host,
                              event->error_handle->esp_tls_last_esp_err, event->error_handle->esp_transport_sock_errno);
            }
            break;
        default:
            break;
    }
}

bool CommsManager::ConnectFeedMQTT(uint16_t feed_index) {
    // The shared client (UpdateMQTTClient) connects; a feed is ready while it is connected.
    feed_sock_is_connected_[feed_index] = mqtt_is_connected_;
    return mqtt_is_connected_;
}

bool CommsManager::PublishFeedMQTT(uint16_t feed_index, const char* buf, uint16_t buf_len, uint16_t num_msgs) {
    esp_mqtt_client_handle_t client = mqtt_client_;
    int outbox_max_bytes = HardwareCapabilities::HasPSRAM() ? kMQTTOutboxMaxBytesPSRAM : kMQTTOutboxMaxBytesInternal;
    feed_send_heap_is_low_ = FeedSendHeapIsLow();
    if (client == nullptr || !mqtt_is_connected_ || feed_send_heap_is_low_ ||
        esp_mqtt_client_get_outbox_size(client) > outbox_max_bytes) {
        feed_num_dropped_msgs_[feed_index] += num_msgs;
        return true;
    }

    // Topic suffix: the protocol name in lower case, e.g. adsbee/bee0123456789abc/aircraft_json.
    const char* name = SettingsManager::kReportingProtocolStrs[settings_manager.settings.feed_protocols[feed_index]];
    char suffix[SettingsManager::kReportingProtocolStrMaxLen];
    size_t i = 0;
    for (; name[i] != '\0' && i < sizeof(suffix) - 1; i++) {
        suffix[i] = tolower(static_cast<unsigned char>(name[i]));
    }
    suffix[i] = '\0';
    char topic[kMQTTTopicMaxLen + 1];
    MQTTTopic(suffix, topic, sizeof(topic));

    // Text protocols end each message with a newline that a payload doesn't need.
    while (buf_len > 0 && (buf[buf_len - 1] == '\n' || buf[buf_len - 1] == '\r')) {
        buf_len--;
    }
    // Published from this task: the client task sends only one queued message per poll interval, too few for a feed.
    if (esp_mqtt_client_publish(client, topic, buf, buf_len, settings_manager.settings.mqtt_broker.qos, 0) < 0) {
        feed_num_dropped_msgs_[feed_index] += num_msgs;
        return true;
    }
    feed_mps_counter_[feed_index] += num_msgs;
    return true;
}

void CommsManager::PublishMQTTMetrics() {
    uint32_t timestamp_ms = get_time_since_boot_ms();
    if (mqtt_client_ == nullptr || !mqtt_is_connected_ ||
        timestamp_ms - mqtt_metrics_last_publish_timestamp_ms_ < kMQTTMetricsIntervalMs) {
        return;
    }
    mqtt_metrics_last_publish_timestamp_ms_ = timestamp_ms;
    char version[20];
    int version_len = snprintf(version, sizeof(version), "%d.%d.%d", ObjectDictionary::kFirmwareVersionMajor,
                               ObjectDictionary::kFirmwareVersionMinor, ObjectDictionary::kFirmwareVersionPatch);
    if (ObjectDictionary::kFirmwareVersionReleaseCandidate != 0) {
        snprintf(version + version_len, sizeof(version) - version_len, "-rc%d",
                 ObjectDictionary::kFirmwareVersionReleaseCandidate);
    }
    // Static: the feed task's stack is small.
    static char payload[512];
    int len = snprintf(payload, sizeof(payload),
                       "{\"hostname\":\"%s\",\"firmware\":\"%s\",\"uptime_s\":%lu,\"aircraft\":%u,\"msgs_per_s\":{",
                       hostname, version, (unsigned long)(timestamp_ms / 1000),
                       adsbee_server.aircraft_dictionary.GetNumAircraft());
    bool first = true;
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds && len < (int)sizeof(payload); i++) {
        if (feed_transports_in_use_[i] != SettingsManager::kFeedTransportMQTT || !feed_sock_is_connected_[i]) {
            continue;
        }
        len += snprintf(payload + len, sizeof(payload) - len, "%s\"%s\":%u", first ? "" : ",",
                        SettingsManager::kReportingProtocolStrs[settings_manager.settings.feed_protocols[i]],
                        feed_mps[i]);
        first = false;
    }
    if (len < (int)sizeof(payload)) {
        len += snprintf(payload + len, sizeof(payload) - len, "}}");
    }
    if (len >= (int)sizeof(payload)) {
        return;
    }
    char topic[kMQTTTopicMaxLen + 1];
    MQTTTopic("metrics", topic, sizeof(topic));
    esp_mqtt_client_enqueue(mqtt_client_, topic, payload, len, 0, 0, true);
}
