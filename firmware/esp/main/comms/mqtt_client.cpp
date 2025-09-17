#include "mqtt_client.hh"
#include "esp_log.h"
#include "esp_system.h"
#include "esp_random.h"
#include <cJSON.h>
#include <cstring>
#include <algorithm>

static const char* TAG = "MQTT";

namespace MQTT {

// AircraftRateLimiter implementation
bool AircraftRateLimiter::ShouldPublish(const std::string& icao) {
    auto now = std::chrono::steady_clock::now();
    auto it = aircraft_states_.find(icao);

    if (it == aircraft_states_.end()) {
        // New aircraft, publish immediately
        aircraft_states_[icao].last_published = now;
        return true;
    }

    auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
        now - it->second.last_published);

    if (elapsed >= kMinPublishInterval) {
        it->second.last_published = now;
        return true;
    }

    return false;
}

void AircraftRateLimiter::Reset() {
    aircraft_states_.clear();
}

// MQTTClient implementation
MQTTClient::MQTTClient(const Config& config, uint16_t feed_index)
    : config_(config),
      feed_index_(feed_index),
      client_(nullptr),
      connected_(false),
      reconnect_delay_ms_(kInitialReconnectDelayMs) {

    // Initialize statistics
    stats_ = {};

    // Configure MQTT client
    esp_mqtt_client_config_t mqtt_cfg = {};

    // Build full URI
    std::string full_uri;
    if (config_.use_tls) {
        full_uri = "mqtts://" + config_.broker_uri + ":" + std::to_string(config_.port);
    } else {
        full_uri = "mqtt://" + config_.broker_uri + ":" + std::to_string(config_.port);
    }

    mqtt_cfg.broker.address.uri = full_uri.c_str();

    // Authentication
    if (!config_.username.empty()) {
        mqtt_cfg.credentials.username = config_.username.c_str();
    }
    if (!config_.password.empty()) {
        mqtt_cfg.credentials.authentication.password = config_.password.c_str();
    }

    // Client ID
    if (!config_.client_id.empty()) {
        mqtt_cfg.credentials.client_id = config_.client_id.c_str();
    } else {
        // Generate client ID from device ID
        std::string generated_client_id = "adsbee_" + config_.device_id;
        mqtt_cfg.credentials.client_id = generated_client_id.c_str();
    }

    // Last Will and Testament (LWT)
    std::string lwt_topic = GetOnlineTopic();
    mqtt_cfg.session.last_will.topic = lwt_topic.c_str();
    mqtt_cfg.session.last_will.msg = "0";
    mqtt_cfg.session.last_will.msg_len = 1;
    mqtt_cfg.session.last_will.qos = 1;
    mqtt_cfg.session.last_will.retain = true;

    // Create MQTT client
    client_ = esp_mqtt_client_init(&mqtt_cfg);
    if (client_ == nullptr) {
        ESP_LOGE(TAG, "Failed to initialize MQTT client for feed %d", feed_index_);
        return;
    }

    // Register event handler
    esp_mqtt_client_register_event(client_, MQTT_EVENT_ANY, MQTTEventHandler, this);
}

MQTTClient::~MQTTClient() {
    if (client_) {
        Disconnect();
        esp_mqtt_client_destroy(client_);
    }
}

bool MQTTClient::Connect() {
    if (!client_) {
        return false;
    }

    if (connected_) {
        return true;
    }

    // Check if enough time has passed since last attempt
    auto now = std::chrono::steady_clock::now();
    auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
        now - last_connect_attempt_).count();

    if (elapsed < reconnect_delay_ms_) {
        return false;  // Too soon to retry
    }

    last_connect_attempt_ = now;

    ESP_LOGI(TAG, "Connecting to MQTT broker %s for feed %d",
             config_.broker_uri.c_str(), feed_index_);

    esp_err_t err = esp_mqtt_client_start(client_);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to start MQTT client: %s", esp_err_to_name(err));
        stats_.last_error = "Failed to start client: " + std::string(esp_err_to_name(err));
        ScheduleReconnect();
        return false;
    }

    return true;
}

void MQTTClient::Disconnect() {
    if (client_ && connected_) {
        esp_mqtt_client_stop(client_);
        connected_ = false;
    }
}

bool MQTTClient::IsConnected() const {
    return connected_;
}

void MQTTClient::MQTTEventHandler(void* handler_args, esp_event_base_t base,
                                   int32_t event_id, void* event_data) {
    MQTTClient* self = static_cast<MQTTClient*>(handler_args);
    esp_mqtt_event_handle_t event = static_cast<esp_mqtt_event_handle_t>(event_data);

    switch (event->event_id) {
        case MQTT_EVENT_CONNECTED:
            ESP_LOGI(TAG, "Connected to MQTT broker for feed %d", self->feed_index_);
            self->HandleConnect();
            break;

        case MQTT_EVENT_DISCONNECTED:
            ESP_LOGW(TAG, "Disconnected from MQTT broker for feed %d", self->feed_index_);
            self->HandleDisconnect();
            break;

        case MQTT_EVENT_ERROR:
            ESP_LOGE(TAG, "MQTT error for feed %d: %d", self->feed_index_, event->error_handle->error_type);
            if (event->error_handle->error_type == MQTT_ERROR_TYPE_TCP_TRANSPORT) {
                self->stats_.last_error = "TCP transport error";
            } else if (event->error_handle->error_type == MQTT_ERROR_TYPE_CONNECTION_REFUSED) {
                self->stats_.last_error = "Connection refused";
            }
            break;

        default:
            break;
    }
}

void MQTTClient::HandleConnect() {
    connected_ = true;
    reconnect_delay_ms_ = kInitialReconnectDelayMs;  // Reset backoff

    // Publish online status with retain
    std::string online_topic = GetOnlineTopic();
    esp_mqtt_client_publish(client_, online_topic.c_str(), "1", 1, 1, true);

    // Clear rate limiter to start fresh
    rate_limiter_.Reset();
}

void MQTTClient::HandleDisconnect() {
    connected_ = false;
    stats_.reconnect_count++;
    ScheduleReconnect();
}

void MQTTClient::ScheduleReconnect() {
    // Apply exponential backoff with jitter
    reconnect_delay_ms_ = std::min(
        static_cast<uint32_t>(reconnect_delay_ms_ * kReconnectBackoffFactor),
        kMaxReconnectDelayMs
    );

    // Add jitter (±20%)
    uint32_t jitter = (esp_random() % (uint32_t)(reconnect_delay_ms_ * kReconnectJitterFactor * 2))
                      - (reconnect_delay_ms_ * kReconnectJitterFactor);
    reconnect_delay_ms_ += jitter;

    ESP_LOGI(TAG, "Will reconnect in %lu ms for feed %d", reconnect_delay_ms_, feed_index_);
}

std::string MQTTClient::GetStatusTopic(const std::string& icao, uint8_t band) const {
    std::string band_prefix = (band == 2) ? "uat" : "adsb";

    if (config_.format == SettingsManager::MQTTFormat::kMQTTFormatBinary) {
        // Short form for binary
        std::string short_band = (band == 2) ? "u" : "a";
        return config_.device_id + "/" + short_band + "/" + icao + "/s";
    } else {
        // Long form for JSON
        return config_.device_id + "/" + band_prefix + "/" + icao + "/status";
    }
}

std::string MQTTClient::GetRawTopic(const std::string& icao, uint8_t band) const {
    std::string band_prefix = (band == 2) ? "uat" : "adsb";
    return config_.device_id + "/" + band_prefix + "/" + icao + "/raw";
}

std::string MQTTClient::GetTelemetryTopic() const {
    if (config_.format == SettingsManager::MQTTFormat::kMQTTFormatBinary) {
        return config_.device_id + "/sys/t";
    } else {
        return config_.device_id + "/system/telemetry";
    }
}

std::string MQTTClient::GetGPSTopic() const {
    if (config_.format == SettingsManager::MQTTFormat::kMQTTFormatBinary) {
        return config_.device_id + "/sys/g";
    } else {
        return config_.device_id + "/system/gps";
    }
}

std::string MQTTClient::GetOnlineTopic() const {
    return config_.device_id + "/system/online";
}

AircraftStatus MQTTClient::PacketToStatus(const TransponderPacket& packet, uint8_t band) const {
    AircraftStatus status = {};

    // Extract ICAO address (uppercase hex)
    char icao_str[7];
    snprintf(icao_str, sizeof(icao_str), "%06X", packet.address);
    status.icao = icao_str;

    status.band = band;

    // Extract data from packet
    if (packet.HasCallsign()) {
        status.callsign = std::string(packet.callsign, 8);
        // Trim trailing spaces
        status.callsign.erase(status.callsign.find_last_not_of(' ') + 1);
    }

    if (packet.HasCategory()) {
        // Convert category to string format (e.g., "A3")
        char cat_str[3];
        snprintf(cat_str, sizeof(cat_str), "%c%d",
                 'A' + ((packet.category >> 4) & 0x0F),
                 packet.category & 0x0F);
        status.category = cat_str;
    }

    if (packet.HasPosition()) {
        status.lat = packet.latitude;
        status.lon = packet.longitude;
    }

    if (packet.HasAltitude()) {
        status.alt_ft = packet.altitude;
    }

    if (packet.HasHeading()) {
        status.hdg_deg = packet.heading;
    }

    if (packet.HasVelocity()) {
        status.spd_kts = packet.velocity;
    }

    if (packet.HasVerticalRate()) {
        status.vr_fpm = packet.vertical_rate;
    }

    if (packet.HasSquawk()) {
        char sqk_str[5];
        snprintf(sqk_str, sizeof(sqk_str), "%04o", packet.squawk);
        status.squawk = sqk_str;
    }

    status.on_ground = packet.airborne == 0;
    status.t_ms = packet.timestamp_ms;

    return status;
}

bool MQTTClient::PublishAircraftStatus(const TransponderPacket& packet, uint8_t band) {
    if (!connected_ || !packet.IsValid()) {
        return false;
    }

    // Check rate limit (1Hz per aircraft)
    char icao_str[7];
    snprintf(icao_str, sizeof(icao_str), "%06X", packet.address);

    if (!rate_limiter_.ShouldPublish(icao_str)) {
        stats_.messages_dropped++;
        return false;  // Drop to maintain 1Hz rate
    }

    // Convert packet to status
    AircraftStatus status = PacketToStatus(packet, band);

    // Generate topic
    std::string topic = GetStatusTopic(status.icao, band);

    // Serialize based on format
    int msg_id = -1;
    if (config_.format == SettingsManager::MQTTFormat::kMQTTFormatBinary) {
        std::vector<uint8_t> binary_data = SerializeStatusBinary(status);
        msg_id = esp_mqtt_client_publish(client_, topic.c_str(),
                                          (const char*)binary_data.data(),
                                          binary_data.size(), 0, false);
        stats_.bytes_sent += binary_data.size();
    } else {
        std::string json_data = SerializeStatusJSON(status);
        msg_id = esp_mqtt_client_publish(client_, topic.c_str(),
                                          json_data.c_str(),
                                          json_data.length(), 0, false);
        stats_.bytes_sent += json_data.length();
    }

    if (msg_id >= 0) {
        stats_.messages_published++;
        return true;
    } else {
        stats_.messages_dropped++;
        return false;
    }
}

bool MQTTClient::PublishTelemetry(const Telemetry& telemetry) {
    if (!connected_) {
        return false;
    }

    // Check if enough time has passed
    auto now = std::chrono::steady_clock::now();
    auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(
        now - last_telemetry_publish_).count();

    if (elapsed < config_.telemetry_interval_sec) {
        return false;
    }

    last_telemetry_publish_ = now;

    std::string topic = GetTelemetryTopic();

    int msg_id = -1;
    if (config_.format == SettingsManager::MQTTFormat::kMQTTFormatBinary) {
        std::vector<uint8_t> binary_data = SerializeTelemetryBinary(telemetry);
        msg_id = esp_mqtt_client_publish(client_, topic.c_str(),
                                          (const char*)binary_data.data(),
                                          binary_data.size(), 1, false);  // QoS 1
        stats_.bytes_sent += binary_data.size();
    } else {
        std::string json_data = SerializeTelemetryJSON(telemetry);
        msg_id = esp_mqtt_client_publish(client_, topic.c_str(),
                                          json_data.c_str(),
                                          json_data.length(), 1, false);  // QoS 1
        stats_.bytes_sent += json_data.length();
    }

    return msg_id >= 0;
}

bool MQTTClient::PublishGPS(const GPS& gps) {
    if (!connected_) {
        return false;
    }

    // Check if enough time has passed
    auto now = std::chrono::steady_clock::now();
    auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(
        now - last_gps_publish_).count();

    if (elapsed < config_.gps_interval_sec) {
        return false;
    }

    last_gps_publish_ = now;

    std::string topic = GetGPSTopic();

    int msg_id = -1;
    if (config_.format == SettingsManager::MQTTFormat::kMQTTFormatBinary) {
        std::vector<uint8_t> binary_data = SerializeGPSBinary(gps);
        msg_id = esp_mqtt_client_publish(client_, topic.c_str(),
                                          (const char*)binary_data.data(),
                                          binary_data.size(), 0, false);
        stats_.bytes_sent += binary_data.size();
    } else {
        std::string json_data = SerializeGPSJSON(gps);
        msg_id = esp_mqtt_client_publish(client_, topic.c_str(),
                                          json_data.c_str(),
                                          json_data.length(), 0, false);
        stats_.bytes_sent += json_data.length();
    }

    return msg_id >= 0;
}

// JSON Serialization
std::string MQTTClient::SerializeStatusJSON(const AircraftStatus& status) const {
    cJSON* root = cJSON_CreateObject();

    cJSON_AddStringToObject(root, "icao", status.icao.c_str());
    cJSON_AddNumberToObject(root, "band", status.band);

    if (!status.callsign.empty()) {
        cJSON_AddStringToObject(root, "call", status.callsign.c_str());
    }

    if (!status.category.empty()) {
        cJSON_AddStringToObject(root, "cat", status.category.c_str());
    }

    if (status.lat != 0 || status.lon != 0) {
        cJSON_AddNumberToObject(root, "lat", status.lat);
        cJSON_AddNumberToObject(root, "lon", status.lon);
    }

    if (status.alt_ft != 0) {
        cJSON_AddNumberToObject(root, "alt_ft", status.alt_ft);
    }

    if (status.hdg_deg != 0) {
        cJSON_AddNumberToObject(root, "hdg_deg", status.hdg_deg);
    }

    if (status.spd_kts != 0) {
        cJSON_AddNumberToObject(root, "spd_kts", status.spd_kts);
    }

    if (status.vr_fpm != 0) {
        cJSON_AddNumberToObject(root, "vr_fpm", status.vr_fpm);
    }

    if (!status.squawk.empty()) {
        cJSON_AddStringToObject(root, "sqk", status.squawk.c_str());
    }

    cJSON_AddBoolToObject(root, "on_ground", status.on_ground);
    cJSON_AddNumberToObject(root, "t_ms", status.t_ms);

    char* json_str = cJSON_PrintUnformatted(root);
    std::string result(json_str);

    cJSON_free(json_str);
    cJSON_Delete(root);

    return result;
}

std::string MQTTClient::SerializeTelemetryJSON(const Telemetry& telemetry) const {
    cJSON* root = cJSON_CreateObject();

    cJSON_AddNumberToObject(root, "uptime_sec", telemetry.uptime_sec);
    cJSON_AddNumberToObject(root, "msgs_rx", telemetry.msgs_rx);
    cJSON_AddNumberToObject(root, "msgs_tx", telemetry.msgs_tx);
    cJSON_AddNumberToObject(root, "cpu_temp_c", telemetry.cpu_temp_c);
    cJSON_AddNumberToObject(root, "mem_free_kb", telemetry.mem_free_kb);
    cJSON_AddNumberToObject(root, "noise_floor_dbm", telemetry.noise_floor_dbm);
    cJSON_AddBoolToObject(root, "rx_1090", telemetry.rx_1090);
    cJSON_AddBoolToObject(root, "rx_978", telemetry.rx_978);
    cJSON_AddBoolToObject(root, "wifi", telemetry.wifi);
    cJSON_AddBoolToObject(root, "mqtt", telemetry.mqtt);
    cJSON_AddStringToObject(root, "fw_version", telemetry.fw_version.c_str());

    if (telemetry.mps_total > 0) {
        cJSON_AddNumberToObject(root, "mps_total", telemetry.mps_total);
    }

    if (!telemetry.mps_feeds.empty()) {
        cJSON* feeds_array = cJSON_CreateArray();
        for (uint32_t mps : telemetry.mps_feeds) {
            cJSON_AddItemToArray(feeds_array, cJSON_CreateNumber(mps));
        }
        cJSON_AddItemToObject(root, "mps_feeds", feeds_array);
    }

    char* json_str = cJSON_PrintUnformatted(root);
    std::string result(json_str);

    cJSON_free(json_str);
    cJSON_Delete(root);

    return result;
}

std::string MQTTClient::SerializeGPSJSON(const GPS& gps) const {
    cJSON* root = cJSON_CreateObject();

    cJSON_AddNumberToObject(root, "lat", gps.lat);
    cJSON_AddNumberToObject(root, "lon", gps.lon);
    cJSON_AddNumberToObject(root, "alt_m", gps.alt_m);
    cJSON_AddNumberToObject(root, "fix", gps.fix);
    cJSON_AddNumberToObject(root, "sats", gps.sats);
    cJSON_AddNumberToObject(root, "hdop", gps.hdop);
    cJSON_AddNumberToObject(root, "ts", gps.ts);

    char* json_str = cJSON_PrintUnformatted(root);
    std::string result(json_str);

    cJSON_free(json_str);
    cJSON_Delete(root);

    return result;
}

// Binary Serialization (compact format as specified)
std::vector<uint8_t> MQTTClient::SerializeStatusBinary(const AircraftStatus& status) const {
    // Fixed 31 bytes for status
    std::vector<uint8_t> data(31, 0);

    // Byte 0: Message type (0 = status)
    data[0] = 0;

    // Byte 1: Band (1=1090, 2=UAT)
    data[1] = status.band;

    // Bytes 2-4: ICAO (24 bits)
    uint32_t icao = std::stoul(status.icao, nullptr, 16);
    data[2] = (icao >> 16) & 0xFF;
    data[3] = (icao >> 8) & 0xFF;
    data[4] = icao & 0xFF;

    // Byte 5: RSSI (placeholder, set to -50 dBm)
    data[5] = 206;  // -50 dBm in uint8 (256 - 50)

    // Bytes 6-9: Timestamp (ms, 32-bit)
    uint32_t t_ms = status.t_ms & 0xFFFFFFFF;
    data[6] = (t_ms >> 24) & 0xFF;
    data[7] = (t_ms >> 16) & 0xFF;
    data[8] = (t_ms >> 8) & 0xFF;
    data[9] = t_ms & 0xFF;

    // Bytes 10-13: Latitude (1e-5 degrees, signed 32-bit)
    int32_t lat = static_cast<int32_t>(status.lat * 100000);
    data[10] = (lat >> 24) & 0xFF;
    data[11] = (lat >> 16) & 0xFF;
    data[12] = (lat >> 8) & 0xFF;
    data[13] = lat & 0xFF;

    // Bytes 14-17: Longitude (1e-5 degrees, signed 32-bit)
    int32_t lon = static_cast<int32_t>(status.lon * 100000);
    data[14] = (lon >> 24) & 0xFF;
    data[15] = (lon >> 16) & 0xFF;
    data[16] = (lon >> 8) & 0xFF;
    data[17] = lon & 0xFF;

    // Bytes 18-19: Altitude (units of 25ft, unsigned 16-bit)
    uint16_t alt_25ft = static_cast<uint16_t>(status.alt_ft / 25);
    data[18] = (alt_25ft >> 8) & 0xFF;
    data[19] = alt_25ft & 0xFF;

    // Byte 20: Heading (units of 360/256 degrees)
    data[20] = static_cast<uint8_t>((status.hdg_deg * 256) / 360);

    // Byte 21: Speed (knots, capped at 255)
    data[21] = std::min(static_cast<uint8_t>(status.spd_kts), uint8_t(255));

    // Byte 22: Vertical rate (units of 64 fpm, signed)
    int8_t vr_64fpm = static_cast<int8_t>(status.vr_fpm / 64);
    data[22] = vr_64fpm;

    // Byte 23: Flags (bit 0 = on_ground)
    data[23] = status.on_ground ? 1 : 0;

    // Bytes 24-31: Callsign (8 chars, space-padded)
    for (size_t i = 0; i < 8 && i < status.callsign.length(); i++) {
        data[24 + i] = status.callsign[i];
    }

    return data;
}

std::vector<uint8_t> MQTTClient::SerializeTelemetryBinary(const Telemetry& telemetry) const {
    // Fixed 16 bytes for telemetry
    std::vector<uint8_t> data(16, 0);

    // Byte 0: Message type (1 = telemetry)
    data[0] = 1;

    // Bytes 1-4: Uptime (seconds, 32-bit)
    uint32_t uptime = telemetry.uptime_sec;
    data[1] = (uptime >> 24) & 0xFF;
    data[2] = (uptime >> 16) & 0xFF;
    data[3] = (uptime >> 8) & 0xFF;
    data[4] = uptime & 0xFF;

    // Bytes 5-6: Messages received (16-bit)
    uint16_t msgs_rx = std::min(telemetry.msgs_rx, uint32_t(0xFFFF));
    data[5] = (msgs_rx >> 8) & 0xFF;
    data[6] = msgs_rx & 0xFF;

    // Bytes 7-8: Messages transmitted (16-bit)
    uint16_t msgs_tx = std::min(telemetry.msgs_tx, uint32_t(0xFFFF));
    data[7] = (msgs_tx >> 8) & 0xFF;
    data[8] = msgs_tx & 0xFF;

    // Byte 9: CPU temperature (Celsius, signed)
    data[9] = static_cast<uint8_t>(telemetry.cpu_temp_c);

    // Bytes 10-11: Free memory (KB, 16-bit)
    uint16_t mem_kb = std::min(telemetry.mem_free_kb, uint32_t(0xFFFF));
    data[10] = (mem_kb >> 8) & 0xFF;
    data[11] = mem_kb & 0xFF;

    // Byte 12: Noise floor (dBm + 128)
    data[12] = telemetry.noise_floor_dbm + 128;

    // Byte 13: Status flags
    uint8_t flags = 0;
    if (telemetry.rx_1090) flags |= 0x01;
    if (telemetry.rx_978) flags |= 0x02;
    if (telemetry.wifi) flags |= 0x04;
    if (telemetry.mqtt) flags |= 0x08;
    data[13] = flags;

    // Bytes 14-15: Reserved
    data[14] = 0;
    data[15] = 0;

    return data;
}

std::vector<uint8_t> MQTTClient::SerializeGPSBinary(const GPS& gps) const {
    // Fixed 15 bytes for GPS
    std::vector<uint8_t> data(15, 0);

    // Byte 0: Message type (2 = GPS)
    data[0] = 2;

    // Bytes 1-4: Latitude (1e-5 degrees, signed 32-bit)
    int32_t lat = static_cast<int32_t>(gps.lat * 100000);
    data[1] = (lat >> 24) & 0xFF;
    data[2] = (lat >> 16) & 0xFF;
    data[3] = (lat >> 8) & 0xFF;
    data[4] = lat & 0xFF;

    // Bytes 5-8: Longitude (1e-5 degrees, signed 32-bit)
    int32_t lon = static_cast<int32_t>(gps.lon * 100000);
    data[5] = (lon >> 24) & 0xFF;
    data[6] = (lon >> 16) & 0xFF;
    data[7] = (lon >> 8) & 0xFF;
    data[8] = lon & 0xFF;

    // Bytes 9-10: Altitude (meters, signed 16-bit)
    int16_t alt_m = static_cast<int16_t>(gps.alt_m);
    data[9] = (alt_m >> 8) & 0xFF;
    data[10] = alt_m & 0xFF;

    // Byte 11: Fix type (0=none, 1=2D, 2=3D)
    data[11] = gps.fix;

    // Byte 12: Satellites
    data[12] = std::min(gps.sats, uint32_t(255));

    // Byte 13: HDOP (scaled by 10)
    data[13] = static_cast<uint8_t>(std::min(gps.hdop * 10, 255.0f));

    // Byte 14: Reserved
    data[14] = 0;

    return data;
}

}  // namespace MQTT