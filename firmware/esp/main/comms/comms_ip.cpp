#include "beast/beast_utils.hh"  // For beast reporting.
#include "comms.hh"
#include "esp_event.h"
#include "esp_heap_caps.h"
#include "esp_mac.h"
#include "hal.hh"
#include "lwip/dns.h"
#include "lwip/err.h"
#include "lwip/netdb.h"
#include "lwip/sockets.h"
#include "lwip/sys.h"
#include "mdns.h"
#include "mqtt_client.hh"              // For MQTT support.
#include "adsbee_server.hh"            // For aircraft_dictionary access.
#include "object_dictionary.hh"        // For device_status, firmware version constants.
#include "task_priorities.hh"

static const uint32_t kTCPSocketReconnectIntervalMs = 10000;

// Heap threshold for back-pressure. If free heap drops below this, safe_send will block.
// Set high enough to leave room for WebSocket allocations (~2KB) and other system needs.
static const uint32_t kHeapBackPressureThresholdBytes = 20480;
// DMA-capable memory threshold. WiFi TX buffers require internal DMA memory which is more constrained.
// Steady-state DMA free is typically ~14KB, so threshold must be below that to avoid perpetual back-pressure.
static const uint32_t kDMABackPressureThresholdBytes = 10240;
static const uint32_t kHeapBackPressureCheckIntervalMs = 50;
static const uint32_t kHeapBackPressureTimeoutMs = 1000;

// #define ENABLE_TCP_SOCKET_RATE_LIMITING
#ifdef ENABLE_TCP_SOCKET_RATE_LIMITING
static const uint32_t kSendBufRateLimitBytesPerSecond = 100000;  // 100 kB/s
static const uint32_t kSendBufRateLimitIntervalMs = 10;
static const uint32_t kSendBufRateLimitBytesPerInterval =
    kSendBufRateLimitBytesPerSecond / (1000 / kSendBufRateLimitIntervalMs);
static const uint32_t kRateLimitDelayDurationMs = 1;
#endif

static const uint32_t kTCPKeepAliveEnable = 1;
static const uint32_t kTCPKeepAliveIdleSecondsBeforeStartingProbe = 120;
static const uint32_t kTCPKeepAliveIntervalSecondsBetweenProbes = 30;
static const uint32_t kTCPKeepAliveMaxFailedProbesBeforeDisconnect = 3;
static const uint32_t kTCPReuseAddrEnable =
    1;  // Allow reuse of local addresses and sockets that are in the TIME_WAIT state.

/** "Pass-Through" functions used to access member functions in callbacks. **/
void ip_event_handler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    comms_manager.IPEventHandler(arg, event_base, event_id, event_data);
}
void ip_wan_task(void* pvParameters) { comms_manager.IPWANTask(pvParameters); }
void ip_wan_connection_task(void* pvParameters) { comms_manager.IPWANConnectionTask(pvParameters); }
/** End "Pass-Through" functions. **/

bool IsNotIPAddress(const char* uri) {
    // Check if the URI contains any letters
    for (const char* p = uri; *p != '\0'; p++) {
        if (isalpha(*p)) {
            return true;
        }
    }
    return false;
}

bool ResolveURIToIP(const char* url, char* ip) {
    struct addrinfo hints;
    struct addrinfo* res;
    struct in_addr addr;
    int err;

    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_STREAM;

    err = getaddrinfo(url, NULL, &hints, &res);
    if (err != 0 || res == NULL) {
        CONSOLE_ERROR("ResolveURLToIP", "DNS lookup failed for %s: %d", url, err);
        freeaddrinfo(res);
        return false;
    }

    addr.s_addr = ((struct sockaddr_in*)res->ai_addr)->sin_addr.s_addr;
    inet_ntop(AF_INET, &addr, ip, 16);
    CONSOLE_INFO("ResolveURLToIP", "DNS lookup succeeded. IP=%s", ip);

    freeaddrinfo(res);
    return true;
}

esp_err_t safe_send(int sock, const void* data, size_t total_len) {
    // 0. Back-pressure: block if heap or DMA memory is low to prevent OOM crashes
    uint32_t backpressure_start_ms = get_time_since_boot_ms();
    while (heap_caps_get_free_size(MALLOC_CAP_8BIT) < kHeapBackPressureThresholdBytes ||
           heap_caps_get_free_size(MALLOC_CAP_DMA) < kDMABackPressureThresholdBytes) {
        if (get_time_since_boot_ms() - backpressure_start_ms > kHeapBackPressureTimeoutMs) {
            CONSOLE_WARNING("safe_send", "Heap back-pressure timeout after %lu ms (heap=%u, dma=%u)",
                            kHeapBackPressureTimeoutMs, heap_caps_get_free_size(MALLOC_CAP_8BIT),
                            heap_caps_get_free_size(MALLOC_CAP_DMA));
            return ESP_ERR_TIMEOUT;
        }
        vTaskDelay(pdMS_TO_TICKS(kHeapBackPressureCheckIntervalMs));
    }

    // 1. Set socket to non-blocking mode
    int flags = fcntl(sock, F_GETFL, 0);
    fcntl(sock, F_SETFL, flags | O_NONBLOCK);

    size_t sent_total = 0;
    while (sent_total < total_len) {
        fd_set write_set;
        FD_ZERO(&write_set);
        FD_SET(sock, &write_set);

        // 2. Set a timeout for select()
        struct timeval timeout = {.tv_sec = 5,  // 5 second timeout
                                  .tv_usec = 0};

        // Wait until the socket is ready to accept data
        int res = select(sock + 1, NULL, &write_set, NULL, &timeout);

        if (res < 0) {
            CONSOLE_ERROR("safe_send", "Select error: %d", errno);
            return ESP_FAIL;
        } else if (res == 0) {
            CONSOLE_WARNING("safe_send", "Send timeout - Network congested");
            return ESP_ERR_TIMEOUT;
        }

        // 3. Socket is ready, try to send the remaining chunk
        int sent_now = send(sock, (const char*)data + sent_total, total_len - sent_total, 0);

        if (sent_now > 0) {
            sent_total += sent_now;
            // CONSOLE_INFO("safe_send", "Sent %d bytes (%zu/%zu)", sent_now, sent_total, total_len);
        } else if (sent_now < 0) {
            if (errno == EAGAIN || errno == EWOULDBLOCK) {
                // This shouldn't really happen after select() says it's ready,
                // but it's good practice to handle it.
                continue;
            } else {
                CONSOLE_ERROR("safe_send", "Socket error during send: %d", errno);
                return ESP_FAIL;
            }
        }
    }

    return ESP_OK;
}

bool CommsManager::IPInit() {
    ESP_ERROR_CHECK(esp_event_handler_register(IP_EVENT, ESP_EVENT_ANY_ID, &ip_event_handler, NULL));
    ip_event_handler_was_initialized_ = true;

    // IP WAN task stack size reduced since raw_packets_buf is now allocated on heap instead of stack.
    xTaskCreate(ip_wan_task, "ip_wan_task", 2 * 4096, &ip_wan_task_handle, kIPWANTaskPriority, NULL);
    // Connection management task handles blocking TCP connect() and MQTT connect so they don't stall packet forwarding.
    xTaskCreate(ip_wan_connection_task, "ip_wan_conn", 4096, &ip_wan_connection_task_handle,
                kIPWANConnectionTaskPriority, NULL);

    // Initialize mDNS service.
    esp_err_t err = mdns_init();
    if (err) {
        CONSOLE_ERROR("CommsManager::IPInit", "MDNS Init failed: %d\n", err);
        return false;
    }

    // Set hostname.
    err = mdns_hostname_set(settings_manager.settings.core_network_settings.hostname);
    if (err) {
        CONSOLE_ERROR("CommsManager::IPInit", "Failed setting MDNS hostname to %s: %d\n",
                      settings_manager.settings.core_network_settings.hostname, err);
        return false;
    }
    // Set default instance.
    mdns_instance_name_set("ADSBee 1090");

    CONSOLE_INFO("CommsManager::IPInit", "MDNS initialized with hostname %s.\n",
                 settings_manager.settings.core_network_settings.hostname);
    return true;
}

void CommsManager::IPEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    switch (event_id) {
        case IP_EVENT_AP_STAIPASSIGNED: {
            // A new station has connected to the ADSBee's softAP network.
            ip_event_ap_staipassigned_t* event = (ip_event_ap_staipassigned_t*)event_data;

            char client_mac_str[SettingsManager::Settings::kMACAddrStrLen + 1] = {0};
            char client_ip_str[SettingsManager::Settings::kIPAddrStrLen + 1] = {0};
            snprintf(client_mac_str, SettingsManager::Settings::kMACAddrStrLen, MACSTR, MAC2STR(event->mac));
            client_mac_str[SettingsManager::Settings::kMACAddrStrLen] = '\0';
            snprintf(client_ip_str, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&event->ip));
            client_ip_str[SettingsManager::Settings::kIPAddrStrLen] = '\0';

            CONSOLE_INFO("CommsManager::IPEventHandler",
                         "WiFi Access Point assigned IP address to client. IP: %s, MAC: %s", client_ip_str,
                         client_mac_str);

            WiFiAddClient(event->ip, event->mac);
            break;
        }
        case IP_EVENT_STA_GOT_IP: {
            // The ADSBee has connected to an external network as a WiFi station.
            ip_event_got_ip_t* event = (ip_event_got_ip_t*)event_data;
            const esp_netif_ip_info_t* ip_info = &event->ip_info;

            wifi_sta_has_ip_ = true;
            snprintf(wifi_sta_ip, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->ip));
            wifi_sta_ip[SettingsManager::Settings::kIPAddrStrLen] = '\0';
            snprintf(wifi_sta_netmask, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->netmask));
            wifi_sta_netmask[SettingsManager::Settings::kIPAddrStrLen] = '\0';
            snprintf(wifi_sta_gateway, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->gw));
            wifi_sta_gateway[SettingsManager::Settings::kIPAddrStrLen] = '\0';

            CONSOLE_INFO("CommsManager::IPEventHandler",
                         "WiFi Station got IP Address. IP: %s, Netmask: %s, Gateway: %s", wifi_sta_ip, wifi_sta_netmask,
                         wifi_sta_gateway);
            break;
        }
        case IP_EVENT_ETH_GOT_IP: {
            // The ADSBee's Ethernet interface has connected to an external network.
            ip_event_got_ip_t* event = (ip_event_got_ip_t*)event_data;
            const esp_netif_ip_info_t* ip_info = &event->ip_info;

            ethernet_has_ip_ = true;
            snprintf(ethernet_ip, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->ip));
            ethernet_ip[SettingsManager::Settings::kIPAddrStrLen] = '\0';
            snprintf(ethernet_netmask, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->netmask));
            ethernet_netmask[SettingsManager::Settings::kIPAddrStrLen] = '\0';
            snprintf(ethernet_gateway, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->gw));
            ethernet_gateway[SettingsManager::Settings::kIPAddrStrLen] = '\0';

            CONSOLE_INFO("CommsManager::IPEventHandler", "Ethernet got IP address. IP: %s, Netmask: %s, Gateway: %s",
                         ethernet_ip, ethernet_netmask, ethernet_gateway);
            break;
        }
        case IP_EVENT_ETH_LOST_IP: {
            // The ADSBee's Ethernet interface has disconnected from an external network.
            ethernet_has_ip_ = false;
            CONSOLE_INFO("CommsManager::IPEventHandler", "Ethernet lost IP address.");
            break;
        }
    }
}

// --- MQTT Feed Management Helpers ---
// Decomposed from IPWANTask to keep the main task loop readable.

struct MQTTFeedState {
    ADSBeeMQTTClient* clients[SettingsManager::Settings::kMaxNumFeeds] = {nullptr};
    uint32_t last_connect_attempt_ms[SettingsManager::Settings::kMaxNumFeeds] = {0};
    uint32_t last_telemetry_publish_ms[SettingsManager::Settings::kMaxNumFeeds] = {0};
    uint32_t last_aircraft_publish_ms[SettingsManager::Settings::kMaxNumFeeds] = {0};
};

static const uint32_t kMQTTTelemetryIntervalMs = 60000;
static const uint32_t kMQTTAircraftStatusIntervalMs = 5000;
static const uint32_t kMQTTConnectRetryIntervalMs = 5000;
static const uint32_t kIPWANConnectionTaskIntervalMs = 1000;

// File-static MQTT state shared between the forwarding task and the connection task.
// The connection task initializes clients and manages connections.
// The forwarding task uses connected clients for publishing.
static MQTTFeedState mqtt_feed_state;

/** Initialize MQTT clients for feeds configured with MQTT protocol. */
static void MQTTInitClients(MQTTFeedState& mqtt) {
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        if (!settings_manager.settings.feed_is_active[i] ||
            settings_manager.settings.feed_protocols[i] != SettingsManager::ReportingProtocol::kMQTT) {
            continue;
        }
        if (strlen(settings_manager.settings.feed_uris[i]) == 0) {
            CONSOLE_WARNING("MQTTInitClients", "Feed %d configured for MQTT but no URI set", i);
            continue;
        }

        mqtt.clients[i] = new ADSBeeMQTTClient();
        if (!mqtt.clients[i]) {
            CONSOLE_ERROR("MQTTInitClients", "Failed to allocate MQTT client for feed %d", i);
            continue;
        }

        char client_id[32];
        snprintf(client_id, sizeof(client_id), "ADSBee-%d-%06X",
                 i, (unsigned int)(esp_random() & 0xFFFFFF));

        char device_id[17];
        snprintf(device_id, sizeof(device_id), "%02x%02x%02x%02x%02x%02x%02x%02x",
                 settings_manager.settings.feed_receiver_ids[i][0],
                 settings_manager.settings.feed_receiver_ids[i][1],
                 settings_manager.settings.feed_receiver_ids[i][2],
                 settings_manager.settings.feed_receiver_ids[i][3],
                 settings_manager.settings.feed_receiver_ids[i][4],
                 settings_manager.settings.feed_receiver_ids[i][5],
                 settings_manager.settings.feed_receiver_ids[i][6],
                 settings_manager.settings.feed_receiver_ids[i][7]);

        ADSBeeMQTTClient::Config mqtt_config;
        mqtt_config.feed_index = i;
        mqtt_config.broker_uri = settings_manager.settings.feed_uris[i];
        mqtt_config.broker_port = settings_manager.settings.feed_ports[i];
        mqtt_config.client_id = client_id;
        mqtt_config.device_id = device_id;
        mqtt_config.format = static_cast<MQTTProtocol::Format>(
            settings_manager.settings.feed_mqtt_formats[i]);
        mqtt_config.mqtt_content = settings_manager.settings.feed_mqtt_content[i];
        mqtt_config.ota_enabled = settings_manager.settings.mqtt_ota_enabled[i];

        if (mqtt.clients[i]->Init(mqtt_config)) {
            CONSOLE_INFO("MQTTInitClients", "MQTT client initialized for feed %d", i);
        } else {
            delete mqtt.clients[i];
            mqtt.clients[i] = nullptr;
            CONSOLE_ERROR("MQTTInitClients", "Failed to initialize MQTT for feed %d", i);
        }
    }
}

/** Proactively attempt MQTT connection for configured feeds. */
static void MQTTConnectFeeds(MQTTFeedState& mqtt) {
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        if (!mqtt.clients[i]) continue;
        if (settings_manager.settings.feed_protocols[i] != SettingsManager::ReportingProtocol::kMQTT) continue;
        if (!settings_manager.settings.feed_is_active[i]) continue;
        if (!mqtt.clients[i]->IsConnected()) {
            uint32_t now = get_time_since_boot_ms();
            if (now - mqtt.last_connect_attempt_ms[i] > kMQTTConnectRetryIntervalMs) {
                CONSOLE_INFO("MQTTConnectFeeds", "MQTT feed %d: connecting to %s (heap=%u)",
                             i, settings_manager.settings.feed_uris[i],
                             heap_caps_get_free_size(MALLOC_CAP_8BIT));
                mqtt.clients[i]->Connect();
                mqtt.last_connect_attempt_ms[i] = now;
            }
        }
    }
}

/** Publish raw packets from a composite array to all connected MQTT feeds. */
static void MQTTPublishRawPackets(MQTTFeedState& mqtt,
                                   CompositeArray::RawPackets& composite_array,
                                   uint16_t* feed_mps_counter) {
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        if (!mqtt.clients[i] || !mqtt.clients[i]->IsConnected()) continue;
        if (settings_manager.settings.feed_protocols[i] != SettingsManager::ReportingProtocol::kMQTT) continue;
        if (!settings_manager.settings.feed_is_active[i]) continue;

        uint8_t content = mqtt.clients[i]->GetConfig().mqtt_content;
        if (content != SettingsManager::Settings::kMQTTContentAll &&
            content != SettingsManager::Settings::kMQTTContentRaw) {
            continue;
        }

        for (uint16_t p = 0; p < composite_array.header->num_mode_s_packets; p++) {
            DecodedModeSPacket decoded_packet(composite_array.mode_s_packets[p]);
            if (!decoded_packet.is_valid) continue;
            if (mqtt.clients[i]->PublishPacket(decoded_packet, MQTTProtocol::kModeS)) {
                feed_mps_counter[i]++;
            }
        }

        for (uint16_t p = 0; p < composite_array.header->num_uat_adsb_packets; p++) {
            DecodedUATADSBPacket decoded_packet(composite_array.uat_adsb_packets[p]);
            if (!decoded_packet.is_valid) continue;
            if (mqtt.clients[i]->PublishUATPacket(decoded_packet)) {
                feed_mps_counter[i]++;
            }
        }
    }
}

/** Periodically publish telemetry data on connected MQTT feeds. */
static void MQTTPublishTelemetry(MQTTFeedState& mqtt) {
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        if (!mqtt.clients[i]) continue;
        if (settings_manager.settings.feed_protocols[i] != SettingsManager::ReportingProtocol::kMQTT) continue;
        if (!settings_manager.settings.feed_is_active[i]) continue;
        if (!mqtt.clients[i]->IsConnected()) continue;

        uint32_t now = get_time_since_boot_ms();
        if (now - mqtt.last_telemetry_publish_ms[i] < kMQTTTelemetryIntervalMs) continue;

        MQTTProtocol::TelemetryData t = {};
        t.uptime_sec = now / 1000;
        uint32_t total_mps = 0;
        uint8_t mps_count = 0;
        for (uint16_t j = 0; j < SettingsManager::Settings::kMaxNumFeeds; j++) {
            total_mps += comms_manager.feed_mps[j];
            if (mps_count < MQTTProtocol::TelemetryData::kMaxFeedsForTelemetry) {
                t.mps_feeds[mps_count++] = comms_manager.feed_mps[j];
            }
        }
        t.messages_received = (uint16_t)MIN(total_mps, (uint32_t)0xFFFF);
        t.mps_total = (uint16_t)MIN(total_mps, (uint32_t)0xFFFF);
        t.mps_feed_count = mps_count;
        t.messages_sent = (uint16_t)MIN(mqtt.clients[i]->GetMessagesSent(), (uint32_t)0xFFFF);
        t.cpu_temp_c = object_dictionary.device_status.temperature_deg_c;
        t.pico_temp_c = object_dictionary.composite_device_status.rp2040.temperature_deg_c;
        t.pico_core0_pct = object_dictionary.composite_device_status.rp2040.core_0_usage_percent;
        t.pico_core1_pct = object_dictionary.composite_device_status.rp2040.core_1_usage_percent;
        t.aircraft_count = (uint16_t)adsbee_server.aircraft_dictionary.dict.size();
        t.memory_free_kb = (uint16_t)(heap_caps_get_free_size(MALLOC_CAP_8BIT) / 1024);
        t.rssi_noise_floor_dbm = 0;
        t.receiver_1090_enabled = 1;
        t.receiver_subg_enabled = 0;
        t.wifi_connected = comms_manager.WiFiStationHasIP() ? 1 : 0;
        t.mqtt_connected = 1;
        t.fw_major = ObjectDictionary::kFirmwareVersionMajor;
        t.fw_minor = ObjectDictionary::kFirmwareVersionMinor;
        t.fw_patch = ObjectDictionary::kFirmwareVersionPatch;

        if (!mqtt.clients[i]->PublishTelemetry(t)) {
            CONSOLE_WARNING("MQTTPublishTelemetry", "Failed to publish telemetry on MQTT feed %d", i);
        }
        mqtt.last_telemetry_publish_ms[i] = now;
    }
}

/** Periodically publish decoded aircraft status from the aircraft dictionary. */
static void MQTTPublishAircraftStatus(MQTTFeedState& mqtt) {
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        if (!mqtt.clients[i] || !mqtt.clients[i]->IsConnected()) continue;
        if (settings_manager.settings.feed_protocols[i] != SettingsManager::ReportingProtocol::kMQTT) continue;
        if (!settings_manager.settings.feed_is_active[i]) continue;

        uint8_t content = mqtt.clients[i]->GetConfig().mqtt_content;
        if (content != SettingsManager::Settings::kMQTTContentAll &&
            content != SettingsManager::Settings::kMQTTContentStatus) {
            continue;
        }

        uint32_t now = get_time_since_boot_ms();
        if (now - mqtt.last_aircraft_publish_ms[i] < kMQTTAircraftStatusIntervalMs) continue;

        uint32_t cutoff = mqtt.last_aircraft_publish_ms[i];
        mqtt.last_aircraft_publish_ms[i] = now;

        for (auto& itr : adsbee_server.aircraft_dictionary.dict) {
            if (ModeSAircraft* ac = get_if<ModeSAircraft>(&(itr.second)); ac) {
                if (!ac->HasBitFlag(ModeSAircraft::kBitFlagPositionValid)) continue;
                if (ac->last_message_timestamp_ms <= cutoff) continue;
                mqtt.clients[i]->PublishAircraft(*ac, MQTTProtocol::kModeS);
            } else if (UATAircraft* uat = get_if<UATAircraft>(&(itr.second)); uat) {
                if (!uat->HasBitFlag(UATAircraft::kBitFlagPositionValid)) continue;
                if (uat->last_message_timestamp_ms <= cutoff) continue;
                ModeSAircraft tmp;
                tmp.icao_address = uat->icao_address;
                strncpy(tmp.callsign, uat->callsign, sizeof(tmp.callsign));
                tmp.latitude_deg = uat->latitude_deg;
                tmp.longitude_deg = uat->longitude_deg;
                tmp.baro_altitude_ft = uat->baro_altitude_ft;
                tmp.direction_deg = uat->direction_deg;
                tmp.speed_kts = uat->speed_kts;
                tmp.baro_vertical_rate_fpm = uat->baro_vertical_rate_fpm;
                tmp.squawk = uat->squawk;
                tmp.emitter_category_raw = uat->emitter_category_raw;
                tmp.last_message_signal_strength_dbm = uat->last_message_signal_strength_dbm;
                tmp.last_message_timestamp_ms = uat->last_message_timestamp_ms;
                if (uat->HasBitFlag(UATAircraft::kBitFlagIsAirborne))
                    tmp.flags |= (1 << ModeSAircraft::kBitFlagIsAirborne);
                if (uat->HasBitFlag(UATAircraft::kBitFlagIdent))
                    tmp.flags |= (1 << ModeSAircraft::kBitFlagIdent);
                if (uat->HasBitFlag(UATAircraft::kBitFlagTCASRA))
                    tmp.flags |= (1 << ModeSAircraft::kBitFlagTCASRA);
                mqtt.clients[i]->PublishAircraft(tmp, MQTTProtocol::kUAT);
            }
        }
    }
}

// --- IPWANConnectionTask ---
// Manages TCP feed socket connections and MQTT client connections in a separate task.
// This prevents blocking connect()/DNS operations from stalling the packet forwarding loop.

void CommsManager::IPWANConnectionTask(void* pvParameters) {
    CONSOLE_INFO("CommsManager::IPWANConnectionTask", "IP WAN Connection Task started.");
    vTaskDelay(pdMS_TO_TICKS(2000));  // Allow other subsystems to initialize first.

    MQTTInitClients(mqtt_feed_state);

    while (true) {
        // Don't try establishing connections until the ESP32 has been assigned an IP address.
        while (!HasIP()) {
            vTaskDelay(1);
        }

        // Connect/disconnect TCP feed sockets as needed.
        for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
            if (!settings_manager.settings.feed_is_active[i]) {
                if (feed_sock_is_connected_[i]) {
                    CloseFeedSocket(i);
                }
                continue;
            }
            // MQTT feeds manage their own connection via the ESP-IDF MQTT library.
            if (settings_manager.settings.feed_protocols[i] == SettingsManager::ReportingProtocol::kMQTT) {
                continue;
            }
            if (!feed_sock_is_connected_[i]) {
                ConnectFeedSocket(i);  // May block on DNS resolution and TCP connect().
            }
        }

        // Connect MQTT feeds (rate-limited internally by kMQTTConnectRetryIntervalMs).
        MQTTConnectFeeds(mqtt_feed_state);

        vTaskDelay(pdMS_TO_TICKS(kIPWANConnectionTaskIntervalMs));
    }
}

// --- IPWANTask ---
// Drains the raw packet queue and forwards packets to connected feeds. Kept free of blocking
// connection operations so that packet forwarding is never stalled by slow network connections.

void CommsManager::IPWANTask(void* pvParameters) {
    CONSOLE_INFO("CommsManager::IPWANTask", "IP WAN Task started.");
    vTaskDelay(pdMS_TO_TICKS(1000));

    uint8_t* raw_packets_buf = (uint8_t*)heap_caps_malloc(CompositeArray::RawPackets::kMaxLenBytes, MALLOC_CAP_8BIT);
    if (raw_packets_buf == nullptr) {
        CONSOLE_ERROR("CommsManager::IPWANTask", "Failed to allocate raw packets buffer on heap. Task exiting.");
        vTaskDelete(NULL);
        return;
    }

    while (true) {
        // Don't try forwarding packets until the ESP32 has been assigned an IP address.
        while (!HasIP()) {
            vTaskDelay(1);
        }

        UpdateFeedMetrics();

        // Build list of active TCP report sinks from already-connected sockets.
        // Connection management is handled by IPWANConnectionTask.
        uint16_t num_active_report_sinks = 0;
        ReportSink active_report_sinks[SettingsManager::Settings::kMaxNumFeeds] = {0};
        SettingsManager::ReportingProtocol active_reporting_protocols[SettingsManager::Settings::kMaxNumFeeds] = {
            SettingsManager::ReportingProtocol::kNoReports};

        for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
            if (!settings_manager.settings.feed_is_active[i]) continue;
            // MQTT feeds are handled separately via MQTTPublishRawPackets.
            if (settings_manager.settings.feed_protocols[i] == SettingsManager::ReportingProtocol::kMQTT) continue;
            if (!feed_sock_is_connected_[i]) continue;  // Not connected yet; connection task will handle it.
            active_report_sinks[num_active_report_sinks] = i;
            active_reporting_protocols[num_active_report_sinks] = settings_manager.settings.feed_protocols[i];
            num_active_report_sinks++;
        }

        // Check if heap is too low for network sends. If so, skip forwarding to avoid failed
        // allocations (DMA exhaustion) that slow the drain loop and cause queue overflow.
        bool heap_ok_for_sends = heap_caps_get_free_size(MALLOC_CAP_8BIT) >= kHeapBackPressureThresholdBytes &&
                                 heap_caps_get_free_size(MALLOC_CAP_DMA) >= kDMABackPressureThresholdBytes;

        // Drain all queued raw packets. Always drain even if we can't forward, to prevent queue overflow.
        while (xQueueReceive(ip_wan_reporting_composite_array_queue_, raw_packets_buf, 0) == pdTRUE) {
            if (!heap_ok_for_sends) continue;  // Discard packet to keep queue moving.

            CompositeArray::RawPackets reporting_composite_array;
            if (!CompositeArray::UnpackRawPacketsBuffer(reporting_composite_array, raw_packets_buf,
                                                        CompositeArray::RawPackets::kMaxLenBytes)) {
                CONSOLE_ERROR("CommsManager::IPWANTask", "Failed to unpack CompositeArray from buffer.");
                continue;
            }

            // Update TCP-based feeds with raw and digested reports.
            if (!UpdateReporting(active_report_sinks, active_reporting_protocols, num_active_report_sinks,
                                 &reporting_composite_array)) {
                CONSOLE_ERROR("CommsManager::IPWANTask", "Error during UpdateReporting for feeds.");
            }

            MQTTPublishRawPackets(mqtt_feed_state, reporting_composite_array, feed_mps_counter_);
        }

        if (heap_ok_for_sends) {
            MQTTPublishTelemetry(mqtt_feed_state);
            MQTTPublishAircraftStatus(mqtt_feed_state);
        }

        vTaskDelay(kWiFiSTATaskUpdateIntervalTicks);
    }

    // Close all sockets while exiting.
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        CloseFeedSocket(i);
    }

    // Free heap buffer.
    heap_caps_free(raw_packets_buf);

    CONSOLE_INFO("CommsManager::IPWANTask", "IP WAN Task exiting.");
}

void CommsManager::CloseFeedSocket(uint16_t feed_index) {
    // Need to close the socket connection.
    close(feed_sock_[feed_index]);
    feed_sock_is_connected_[feed_index] = false;
    CONSOLE_INFO("CommsManager::IPWANTask", "Closed socket for feed %d.", feed_index);
}

bool CommsManager::ConnectFeedSocket(uint16_t feed_index) {
    // Meter reconnect attempt interval.
    uint32_t timestamp_ms = get_time_since_boot_ms();
    if (timestamp_ms - feed_sock_last_connect_timestamp_ms_[feed_index] <= kTCPSocketReconnectIntervalMs) {
        return false;
    }
    feed_sock_last_connect_timestamp_ms_[feed_index] = timestamp_ms;

    // Create socket.
    // IPv4, TCP
    feed_sock_[feed_index] = socket(AF_INET, SOCK_STREAM, IPPROTO_IP);
    if (feed_sock_[feed_index] <= 0) {
        CONSOLE_ERROR("CommsManager::IPWANTask", "Unable to create socket for feed %d: errno %d (%s)", feed_index,
                      errno, strerror(errno));
        CloseFeedSocket(feed_index);
        return false;
    }
    CONSOLE_INFO("CommsManager::IPWANTask", "Socket for feed %d created, connecting to %s:%d", feed_index,
                 settings_manager.settings.feed_uris[feed_index], settings_manager.settings.feed_ports[feed_index]);

    // Enable TCP keepalive
    setsockopt(feed_sock_[feed_index], SOL_SOCKET, SO_KEEPALIVE, &kTCPKeepAliveEnable, sizeof(kTCPKeepAliveEnable));
    setsockopt(feed_sock_[feed_index], IPPROTO_TCP, TCP_KEEPIDLE, &kTCPKeepAliveIdleSecondsBeforeStartingProbe,
               sizeof(kTCPKeepAliveIdleSecondsBeforeStartingProbe));
    setsockopt(feed_sock_[feed_index], IPPROTO_TCP, TCP_KEEPINTVL, &kTCPKeepAliveIntervalSecondsBetweenProbes,
               sizeof(kTCPKeepAliveIntervalSecondsBetweenProbes));
    setsockopt(feed_sock_[feed_index], IPPROTO_TCP, TCP_KEEPCNT, &kTCPKeepAliveMaxFailedProbesBeforeDisconnect,
               sizeof(kTCPKeepAliveMaxFailedProbesBeforeDisconnect));
    // Allow reuse of local addresses.
    setsockopt(feed_sock_[feed_index], SOL_SOCKET, SO_REUSEADDR, &kTCPReuseAddrEnable, sizeof(kTCPReuseAddrEnable));

    struct sockaddr_in dest_addr;
    // If the URI contains letters, resolve it to an IP address
    if (IsNotIPAddress(settings_manager.settings.feed_uris[feed_index])) {
        // Is not an IP address, try DNS resolution.
        char resolved_ip[16];
        if (!ResolveURIToIP(settings_manager.settings.feed_uris[feed_index], resolved_ip)) {
            CONSOLE_ERROR("CommsManager::IPWANTask", "Failed to resolve URL %s for feed %d",
                          settings_manager.settings.feed_uris[feed_index], feed_index);
            CloseFeedSocket(feed_index);
            return false;
        }
        inet_pton(AF_INET, resolved_ip, &dest_addr.sin_addr);
    } else {
        // Is an IP address, use it directly.
        inet_pton(AF_INET, settings_manager.settings.feed_uris[feed_index], &dest_addr.sin_addr);
    }

    dest_addr.sin_family = AF_INET;
    dest_addr.sin_port = htons(settings_manager.settings.feed_ports[feed_index]);

    int err = connect(feed_sock_[feed_index], (struct sockaddr*)&dest_addr, sizeof(dest_addr));
    if (err != 0) {
        CONSOLE_ERROR("CommsManager::IPWANTask", "Socket unable to connect to URI %s:%d for feed %d: errno %d (%s)",
                      settings_manager.settings.feed_uris[feed_index], settings_manager.settings.feed_ports[feed_index],
                      feed_index, errno, strerror(errno));
        CloseFeedSocket(feed_index);
        return false;
    }
    CONSOLE_INFO("CommsManager::IPWANTask", "Successfully connected to %s",
                 settings_manager.settings.feed_uris[feed_index]);

    // Perform beginning-of-connection actions here (before marking as connected, so the
    // forwarding task doesn't start sending before the handshake completes).
    switch (settings_manager.settings.feed_protocols[feed_index]) {
        case SettingsManager::ReportingProtocol::kBeast:
        case SettingsManager::ReportingProtocol::kBeastNoUAT:
        case SettingsManager::ReportingProtocol::kBeastNoUATUplink: {
            uint8_t beast_message_buf[2 * SettingsManager::Settings::kFeedReceiverIDNumBytes +
                                      BeastReporter::kModeSBeastFrameMaxLenBytes];
            uint16_t beast_message_len_bytes = BeastReporter::BuildFeedStartFrame(
                beast_message_buf, settings_manager.settings.feed_receiver_ids[feed_index]);
            int err = safe_send(feed_sock_[feed_index], beast_message_buf, beast_message_len_bytes);
            if (err < 0) {
                CONSOLE_ERROR("CommsManager::IPWANTask",
                              "Error occurred while sending %d Byte Beast start of feed message to feed %d "
                              "with URI %s "
                              "on port %d: "
                              "errno %d.",
                              beast_message_len_bytes, feed_index, settings_manager.settings.feed_uris[feed_index],
                              settings_manager.settings.feed_ports[feed_index], errno);
                // Mark socket as disconnected and try reconnecting in next reporting interval.
                CloseFeedSocket(feed_index);
                return false;
            }
            break;
        }
        default:
            // No start of connections actions required for other protocols.
            break;
    }
    // Mark socket as connected only after handshake is complete, so the forwarding task
    // doesn't start sending before the connection is fully established.
    feed_sock_is_connected_[feed_index] = true;
    return true;
}

// Rate limit the SendBuf function by keeping a running count of bytes sent in every 10ms interval.
#ifdef ENABLE_TCP_SOCKET_RATE_LIMITING
static uint32_t last_send_buf_counter_reset_timestamp_ms = 0;
static uint32_t send_buf_counter_bytes = 0;
#endif
bool CommsManager::SendBuf(uint16_t iface, const char* buf, uint16_t buf_len) {
    if (iface >= SettingsManager::Settings::kMaxNumFeeds) {
        CONSOLE_ERROR("CommsManager::SendBuf", "Invalid feed index %d.", iface);
        return false;
    }
    if (!feed_sock_is_connected_[iface]) {
        CONSOLE_ERROR("CommsManager::SendBuf", "Can't send to feed %d, socket not connected.", iface);
        return false;
    }

#ifdef ENABLE_TCP_SOCKET_RATE_LIMITING
    uint32_t timestamp_ms = get_time_since_boot_ms();
    if (timestamp_ms - last_send_buf_counter_reset_timestamp_ms > kSendBufRateLimitIntervalMs) {
        // Reset the counter every 10ms.
        last_send_buf_counter_reset_timestamp_ms = timestamp_ms;
        send_buf_counter_bytes = 0;
    }
    if (send_buf_counter_bytes + buf_len > kSendBufRateLimitBytesPerInterval) {
        vTaskDelay(
            pdTICKS_TO_MS(kRateLimitDelayDurationMs));  // Delay to yield to other tasks and allow buffers to clear.
    }
    send_buf_counter_bytes += buf_len;
#endif

    int err = safe_send(feed_sock_[iface], buf, buf_len);

    if (err < 0) {
        CONSOLE_ERROR("CommsManager::SendBuf",
                      "Error occurred during sending %d byte message to feed %d with URI %s "
                      "on port %d: "
                      "errno %d (%s).",
                      buf_len, iface, settings_manager.settings.feed_uris[iface],
                      settings_manager.settings.feed_ports[iface], errno, strerror(errno));
        CloseFeedSocket(iface);
        return false;
    } else {
        // CONSOLE_INFO("CommsManager::IPWANTask", "Message sent to feed %d.", i);
        feed_mps_counter_[iface]++;  // Log that a message was sent in statistics.
    }
    return true;
}

void CommsManager::UpdateFeedMetrics() {
    // Update feed statistics once per second and print them. Put this before the queue receive so that it runs even
    // if no packets are received.
    static const uint16_t kStatsMessageMaxLen = 500;
    uint32_t timestamp_ms = get_time_since_boot_ms();
    if (timestamp_ms - feed_mps_last_update_timestamp_ms_ > kMsPerSec) {
        for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
            feed_mps[i] = feed_mps_counter_[i];
            feed_mps_counter_[i] = 0;
        }
        feed_mps_last_update_timestamp_ms_ = timestamp_ms;

        char feeds_metrics_message[kStatsMessageMaxLen] = {'\0'};

        for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
            char single_feed_metrics_message[kStatsMessageMaxLen / SettingsManager::Settings::kMaxNumFeeds] = {'\0'};
            snprintf(single_feed_metrics_message, kStatsMessageMaxLen / SettingsManager::Settings::kMaxNumFeeds,
                     "%d:[%d] ", i, feed_mps[i]);
            strcat(feeds_metrics_message, single_feed_metrics_message);
        }
        CONSOLE_INFO("CommsManager::IPWANTask", "Feed msgs/s: %s", feeds_metrics_message);
    }
}
