#include <ctype.h>

#include "adsbee_server.hh"  // For the aircraft count in the metrics topic.
#include "comms.hh"
#include "esp_crt_bundle.h"
#include "hal.hh"
#include "hardware_capabilities.hh"

// Reconnect interval of an MQTT client after its broker connection drops.
static const int kMQTTReconnectIntervalMs = 10000;
static const uint32_t kMQTTMetricsIntervalMs = 10000;
// Longest a publish may block the feed task on a slow broker before the client drops the connection.
static const int kMQTTNetworkTimeoutMs = 2000;
// Unsent messages kept per MQTT feed. Messages are dropped while the outbox is larger.
static const int kMQTTOutboxMaxBytesPSRAM = 32768;
static const int kMQTTOutboxMaxBytesInternal = 8192;
static const char kMQTTDefaultTopicPrefix[] = "adsbee";
static const uint16_t kMQTTTopicMaxLen = SettingsManager::Settings::kFeedMQTTTopicPrefixMaxLen + 1 +
                                         2 * SettingsManager::Settings::kFeedReceiverIDNumBytes + 1 +
                                         SettingsManager::kReportingProtocolStrMaxLen;

static void feed_mqtt_event_handler(void* handler_args, esp_event_base_t base, int32_t event_id, void* event_data) {
    comms_manager.FeedMQTTEventHandler(static_cast<uint16_t>(reinterpret_cast<intptr_t>(handler_args)), event_id,
                                       static_cast<esp_mqtt_event_handle_t>(event_data));
}

void CommsManager::FeedMQTTTopic(uint16_t feed_index, const char* suffix, char* topic, size_t topic_size) {
    const char* prefix = settings_manager.settings.feed_mqtt[feed_index].topic_prefix;
    char receiver_id[2 * SettingsManager::Settings::kFeedReceiverIDNumBytes + 1];
    SettingsManager::ReceiverIDToStr(settings_manager.settings.feed_receiver_ids[feed_index], receiver_id);
    snprintf(topic, topic_size, "%s/%s/%s", prefix[0] ? prefix : kMQTTDefaultTopicPrefix, receiver_id, suffix);
}

bool CommsManager::ConnectFeedMQTT(uint16_t feed_index) {
    if (feed_mqtt_clients_[feed_index] != nullptr) {
        return feed_sock_is_connected_[feed_index];
    }
    uint32_t timestamp_ms = get_time_since_boot_ms();
    if (timestamp_ms - feed_sock_last_connect_timestamp_ms_[feed_index] <= kMQTTReconnectIntervalMs) {
        return false;
    }
    feed_sock_last_connect_timestamp_ms_[feed_index] = timestamp_ms;

    const SettingsManager::Settings::FeedMQTT& mqtt = settings_manager.settings.feed_mqtt[feed_index];
    char receiver_id[2 * SettingsManager::Settings::kFeedReceiverIDNumBytes + 1];
    SettingsManager::ReceiverIDToStr(settings_manager.settings.feed_receiver_ids[feed_index], receiver_id);
    // Unique per feed: a broker drops the older of two connections with the same client ID. MQTT 3.1.1 brokers must
    // accept client IDs of up to 23 characters, so this takes the last 12 hex digits of the receiver ID.
    char client_id[32];
    snprintf(client_id, sizeof(client_id), "adsbee-%.12s-%u", receiver_id + 4, feed_index);
    char status_topic[kMQTTTopicMaxLen + 1];
    FeedMQTTTopic(feed_index, "status", status_topic, sizeof(status_topic));

    esp_mqtt_client_config_t config = {};  // The client copies the strings.
    config.broker.address.hostname = settings_manager.settings.feed_uris[feed_index];
    config.broker.address.port = settings_manager.settings.feed_ports[feed_index];
    config.broker.address.transport = mqtt.tls ? MQTT_TRANSPORT_OVER_SSL : MQTT_TRANSPORT_OVER_TCP;
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
        CONSOLE_ERROR("CommsManager::ConnectFeedMQTT", "Unable to create the MQTT client for feed %d.", feed_index);
        return false;
    }
    esp_mqtt_client_register_event(client, MQTT_EVENT_ANY, feed_mqtt_event_handler,
                                   reinterpret_cast<void*>(static_cast<intptr_t>(feed_index)));
    // Set before the start: the event handler ignores events of other clients.
    feed_mqtt_clients_[feed_index] = client;
    feed_sock_is_connecting_[feed_index] = true;
    if (esp_mqtt_client_start(client) != ESP_OK) {
        CONSOLE_ERROR("CommsManager::ConnectFeedMQTT", "Unable to start the MQTT client for feed %d.", feed_index);
        feed_mqtt_clients_[feed_index] = nullptr;
        feed_sock_is_connecting_[feed_index] = false;
        esp_mqtt_client_destroy(client);
        return false;
    }
    CONSOLE_INFO("CommsManager::ConnectFeedMQTT", "Feed %d connecting to MQTT broker %s:%d%s.", feed_index,
                 settings_manager.settings.feed_uris[feed_index], settings_manager.settings.feed_ports[feed_index],
                 mqtt.tls ? " with TLS" : "");
    return false;
}

void CommsManager::CloseFeedMQTT(uint16_t feed_index) {
    esp_mqtt_client_handle_t client = feed_mqtt_clients_[feed_index];
    if (client == nullptr) {
        return;
    }
    if (feed_sock_is_connected_[feed_index]) {
        // A clean disconnect doesn't trigger the last will.
        char status_topic[kMQTTTopicMaxLen + 1];
        FeedMQTTTopic(feed_index, "status", status_topic, sizeof(status_topic));
        esp_mqtt_client_publish(client, status_topic, "offline", 0, 1, 1);
    }
    feed_mqtt_clients_[feed_index] = nullptr;
    esp_mqtt_client_destroy(client);
}

void CommsManager::FeedMQTTEventHandler(uint16_t feed_index, int32_t event_id, esp_mqtt_event_handle_t event) {
    if (feed_index >= SettingsManager::Settings::kMaxNumFeeds || event->client != feed_mqtt_clients_[feed_index]) {
        return;
    }
    switch (event_id) {
        case MQTT_EVENT_CONNECTED: {
            char status_topic[kMQTTTopicMaxLen + 1];
            FeedMQTTTopic(feed_index, "status", status_topic, sizeof(status_topic));
            esp_mqtt_client_enqueue(event->client, status_topic, "online", 0, 1, 1, true);
            if (settings_manager.settings.feed_protocols[feed_index] == SettingsManager::kMLAT) {
                RestartMLATReceiverInfo(feed_index);  // The next report starts with a receiver info frame.
            }
            feed_sock_is_connecting_[feed_index] = false;
            feed_sock_is_connected_[feed_index] = true;
            CONSOLE_INFO("CommsManager::FeedMQTTEventHandler", "Feed %d connected to MQTT broker %s.", feed_index,
                         settings_manager.settings.feed_uris[feed_index]);
            break;
        }
        case MQTT_EVENT_DISCONNECTED:
            if (feed_sock_is_connected_[feed_index]) {
                CONSOLE_WARNING("CommsManager::FeedMQTTEventHandler", "Feed %d disconnected from MQTT broker %s.",
                                feed_index, settings_manager.settings.feed_uris[feed_index]);
            }
            feed_sock_is_connected_[feed_index] = false;
            feed_sock_is_connecting_[feed_index] = true;  // The client reconnects by itself.
            break;
        case MQTT_EVENT_ERROR:
            if (event->error_handle->error_type == MQTT_ERROR_TYPE_CONNECTION_REFUSED) {
                CONSOLE_ERROR("CommsManager::FeedMQTTEventHandler",
                              "MQTT broker %s refused feed %d (return code %d): check username and password.",
                              settings_manager.settings.feed_uris[feed_index], feed_index,
                              event->error_handle->connect_return_code);
            } else {
                CONSOLE_ERROR("CommsManager::FeedMQTTEventHandler",
                              "MQTT connection of feed %d to %s failed: TLS error 0x%x, socket errno %d.", feed_index,
                              settings_manager.settings.feed_uris[feed_index], event->error_handle->esp_tls_last_esp_err,
                              event->error_handle->esp_transport_sock_errno);
            }
            break;
        default:
            break;
    }
}

bool CommsManager::PublishFeedMQTT(uint16_t feed_index, const char* buf, uint16_t buf_len, uint16_t num_msgs) {
    esp_mqtt_client_handle_t client = feed_mqtt_clients_[feed_index];
    int outbox_max_bytes = HardwareCapabilities::HasPSRAM() ? kMQTTOutboxMaxBytesPSRAM : kMQTTOutboxMaxBytesInternal;
    feed_send_heap_is_low_ = FeedSendHeapIsLow();
    if (client == nullptr || feed_send_heap_is_low_ || esp_mqtt_client_get_outbox_size(client) > outbox_max_bytes) {
        feed_num_dropped_msgs_[feed_index] += num_msgs;
        return true;
    }

    // Topic suffix: the protocol name in lower case, e.g. adsbee/bee0123456789abc/aircraft_json.
    SettingsManager::ReportingProtocol protocol = settings_manager.settings.feed_protocols[feed_index];
    char suffix[SettingsManager::kReportingProtocolStrMaxLen];
    const char* name = SettingsManager::kReportingProtocolStrs[protocol];
    size_t i = 0;
    for (; name[i] != '\0' && i < sizeof(suffix) - 1; i++) {
        suffix[i] = tolower(static_cast<unsigned char>(name[i]));
    }
    suffix[i] = '\0';
    char topic[kMQTTTopicMaxLen + 1];
    FeedMQTTTopic(feed_index, suffix, topic, sizeof(topic));

    // Text protocols end each message with a newline that a payload doesn't need.
    while (buf_len > 0 && (buf[buf_len - 1] == '\n' || buf[buf_len - 1] == '\r')) {
        buf_len--;
    }
    // Published from this task: the client task sends only one queued message per poll interval, too few for a feed.
    int qos = settings_manager.settings.feed_mqtt[feed_index].qos;
    if (esp_mqtt_client_publish(client, topic, buf, buf_len, qos, 0) < 0) {
        feed_num_dropped_msgs_[feed_index] += num_msgs;
        return true;
    }
    feed_mps_counter_[feed_index] += num_msgs;
    return true;
}

void CommsManager::PublishFeedMQTTMetrics() {
    uint32_t timestamp_ms = get_time_since_boot_ms();
    if (timestamp_ms - feed_mqtt_metrics_last_publish_timestamp_ms_ < kMQTTMetricsIntervalMs) {
        return;
    }
    feed_mqtt_metrics_last_publish_timestamp_ms_ = timestamp_ms;
    char version[20];
    int version_len = snprintf(version, sizeof(version), "%d.%d.%d", ObjectDictionary::kFirmwareVersionMajor,
                               ObjectDictionary::kFirmwareVersionMinor, ObjectDictionary::kFirmwareVersionPatch);
    if (ObjectDictionary::kFirmwareVersionReleaseCandidate != 0) {
        snprintf(version + version_len, sizeof(version) - version_len, "-rc%d",
                 ObjectDictionary::kFirmwareVersionReleaseCandidate);
    }
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        if (feed_mqtt_clients_[i] == nullptr || !feed_sock_is_connected_[i]) {
            continue;
        }
        char topic[kMQTTTopicMaxLen + 1];
        FeedMQTTTopic(i, "metrics", topic, sizeof(topic));
        char payload[256];
        int len = snprintf(payload, sizeof(payload),
                           "{\"hostname\":\"%s\",\"firmware\":\"%s\",\"uptime_s\":%lu,\"aircraft\":%u,"
                           "\"msgs_per_s\":%u,\"protocol\":\"%s\"}",
                           hostname, version, (unsigned long)(timestamp_ms / 1000),
                           adsbee_server.aircraft_dictionary.GetNumAircraft(), feed_mps[i],
                           SettingsManager::kReportingProtocolStrs[settings_manager.settings.feed_protocols[i]]);
        esp_mqtt_client_enqueue(feed_mqtt_clients_[i], topic, payload, len, 0, 0, true);
    }
}
