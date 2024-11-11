#include <string.h>

#include <functional>  // for std::bind

#include "beast/beast_utils.hh"  // For beast reporting.
#include "cc.h"                  // For endiannness swapping.
#include "comms.hh"
#include "esp_event.h"
#include "esp_mac.h"
#include "hal.hh"
#include "lwip/err.h"
#include "lwip/sockets.h"
#include "lwip/sys.h"
#include "nvs_flash.h"
#include "task_priorities.hh"

static const uint16_t kWiFiNumRetries = 3;
static const uint16_t kWiFiRetryWaitTimeMs = 100;
static const uint16_t kWiFiStaMaxNumReconnectAttempts = 5;
static const uint16_t kWiFiScanDefaultListSize = 20;
static const uint32_t kWiFiTCPSocketReconnectIntervalMs = 5000;

/* FreeRTOS event group to signal when we are connected*/
static EventGroupHandle_t s_wifi_event_group;
/* The event group allows multiple bits for each event, but we only care about two events:
 * - we are connected to the AP with an IP
 * - we failed to connect after the maximum amount of retries */
#define WIFI_CONNECTED_BIT BIT0
#define WIFI_FAIL_BIT      BIT1

/** "Pass-Through" functions used to access member functions in callbacks. **/
void wifi_event_handler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    comms_manager.WiFiEventHandler(arg, event_base, event_id, event_data);
}
void ip_event_handler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    comms_manager.IPEventHandler(arg, event_base, event_id, event_data);
}

void wifi_access_point_task(void* pvParameters) { comms_manager.WiFiAccessPointTask(pvParameters); }
void wifi_station_task(void* pvParameters) { comms_manager.WiFiStationTask(pvParameters); }
/** End "Pass-Through" functions. **/

void CommsManager::WiFiEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    static int s_retry_num = 0;

    switch (event_id) {
        case WIFI_EVENT_AP_STACONNECTED: {
            wifi_event_ap_staconnected_t* event = (wifi_event_ap_staconnected_t*)event_data;
            CONSOLE_INFO("CommsManager::WiFiEventHandler", "Station " MACSTR " joined, AID=%d", MAC2STR(event->mac),
                         event->aid);
            break;
        }
        case WIFI_EVENT_AP_STADISCONNECTED: {
            wifi_event_ap_stadisconnected_t* event = (wifi_event_ap_stadisconnected_t*)event_data;
            CONSOLE_INFO("CommsManager::WiFiEventHandler", "Station " MACSTR " left, AID=%d", MAC2STR(event->mac),
                         event->aid);
            WiFiRemoveClient(event->mac);
            break;
        }
        case WIFI_EVENT_STA_START:
            CONSOLE_INFO("CommsManager::WiFiEventHandler", "WIFI_EVENT_STA_START - Attempting to connect to AP");
            ESP_ERROR_CHECK(esp_wifi_connect());
            break;
        case WIFI_EVENT_STA_DISCONNECTED: {
            wifi_event_sta_disconnected_t* event = (wifi_event_sta_disconnected_t*)event_data;
            ESP_LOGW("CommsManager::WiFiEventHandler", "WIFI_EVENT_STA_DISCONNECTED - Disconnect reason : %d",
                     event->reason);
            xEventGroupClearBits(s_wifi_event_group, WIFI_CONNECTED_BIT);

            if (s_retry_num < kWiFiStaMaxNumReconnectAttempts) {
                ESP_ERROR_CHECK(esp_wifi_connect());
                s_retry_num++;
                CONSOLE_INFO("CommsManager::WiFiEventHandler", "Retry to connect to the AP, attempt %d/%d", s_retry_num,
                             kWiFiStaMaxNumReconnectAttempts);
            } else {
                xEventGroupSetBits(s_wifi_event_group, WIFI_FAIL_BIT);
                CONSOLE_ERROR("CommsManager::WiFiEventHandler", "Failed to connect to AP after %d attempts",
                              kWiFiStaMaxNumReconnectAttempts);
            }
            break;
        }
        case WIFI_EVENT_STA_CONNECTED:
            xEventGroupSetBits(s_wifi_event_group, WIFI_CONNECTED_BIT);
            CONSOLE_INFO("CommsManager::WiFiEventHandler", "WIFI_EVENT_STA_CONNECTED - Successfully connected to AP");
            break;
    }
}

void CommsManager::IPEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    if (event_id == IP_EVENT_AP_STAIPASSIGNED) {
        ip_event_ap_staipassigned_t* event = (ip_event_ap_staipassigned_t*)event_data;
        CONSOLE_INFO("CommsManager::IPEventHandler", "Station assigned IP: " IPSTR, IP2STR(&event->ip));
        WiFiAddClient(event->ip, event->mac);
    } else if (event_id == IP_EVENT_STA_GOT_IP) {
        ip_event_got_ip_t* event = (ip_event_got_ip_t*)event_data;
        CONSOLE_INFO("CommsManager::WiFiEventHandler", "Got IP: " IPSTR, IP2STR(&event->ip_info.ip));
        wifi_sta_has_ip_ = true;
    }
}

void CommsManager::WiFiAccessPointTask(void* pvParameters) {
    NetworkMessage message;

    // Create socket.
    int sock = socket(AF_INET, SOCK_DGRAM, IPPROTO_IP);
    if (sock < 0) {
        CONSOLE_ERROR("CommsManager::WiFiAccessPointTask", "Unable to create socket: errno %d", errno);
        return;
    }

    // Set timeout
    struct timeval timeout;
    timeout.tv_sec = 10;
    timeout.tv_usec = 0;
    setsockopt(sock, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof timeout);

    while (run_wifi_ap_task_) {
        if (xQueueReceive(wifi_ap_message_queue_, &message, portMAX_DELAY) == pdTRUE) {
            struct sockaddr_in dest_addr;
            dest_addr.sin_family = AF_INET;
            dest_addr.sin_port = htons(message.port);

            xSemaphoreTake(wifi_clients_list_mutex_, portMAX_DELAY);
            for (int i = 0; i < SettingsManager::Settings::kWiFiMaxNumClients; i++) {
                if (wifi_clients_list_[i].active) {
                    dest_addr.sin_addr.s_addr = wifi_clients_list_[i].ip.addr;
                    int ret = 0;
                    uint16_t num_tries;
                    for (num_tries = 0; num_tries < kWiFiNumRetries; num_tries++) {
                        ret =
                            sendto(sock, message.data, message.len, 0, (struct sockaddr*)&dest_addr, sizeof(dest_addr));
                        // ENOMEM (errno=12) resolution: https://github.com/espressif/esp-idf/issues/390
                        // Increased the number of UDP control blocks (LWIP_MAX_UDP_PCBS) in SDK menuconfig
                        // from 16 to 96. Changed TCP/IP stack size from 3072 to 12288.
                        if (ret >= 0 || errno != ENOMEM) {
                            break;
                        }
                        vTaskDelay(kWiFiRetryWaitTimeMs /
                                   portTICK_PERIOD_MS);  // Let packet send to avoid an ENOMEM error.
                    }

                    if (ret < 0) {
                        // CONSOLE_ERROR("CommsManager::WiFiAccessPointTask", "Error occurred during sending:
                        // errno %d.", errno);
                        CONSOLE_ERROR("CommsManager::WiFiAccessPointTask",
                                      "Error occurred during sending: errno %d. Tried %d times.", errno, num_tries);
                    }
                }
            }
            xSemaphoreGive(wifi_clients_list_mutex_);

            // CONSOLE_INFO("CommsManager::WiFiUDPServerTask", "Message sent to %d clients.",
            // num_wifi_clients_);
        }
    }
    shutdown(sock, 0);
    close(sock);
}

// /**
//  * Helper function that returns whether a TCP socket is currently connected.
//  * @param[in] socket Socket to check conection status of.
//  * @retval True if socket is connected (even if no data is available), false otherwise.
//  */
// bool socket_is_connected(int sock) {
//     uint8_t buf[1];
//     int peek_ret = recv(sock, buf, 1, MSG_PEEK | MSG_DONTWAIT);
//     // 0 = closed by peer. <0 = no data available.
//     return peek_ret != 0;
// }

void CommsManager::WiFiStationTask(void* pvParameters) {
    RawTransponderPacket tpacket;

    // Don't try establishing socket connections until the ESP32 has been assigned an IP address.
    while (!wifi_sta_has_ip_) {
        vTaskDelay(1);  // Delay for 1 tick.
    }

    int feed_sock[SettingsManager::Settings::kMaxNumFeeds] = {0};
    bool feed_sock_is_connected[SettingsManager::Settings::kMaxNumFeeds] = {false};
    uint32_t feed_sock_last_connect_timestamp_ms[SettingsManager::Settings::kMaxNumFeeds] = {0};

    while (run_wifi_sta_task_) {
        // Gather packet(s) to send.
        if (xQueueReceive(wifi_sta_raw_transponder_packet_queue_, &tpacket, portMAX_DELAY) != pdTRUE) {
            // No packets available to send, wait and try again.
            vTaskDelay(1);
            continue;
        }

        // NOTE: Construct packets that are shared between feeds here!

        for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
            // Iterate through feeds, open/close and send message as required.
            if (!settings_manager.settings.feed_is_active[i]) {
                // Socket should not be fed.
                if (feed_sock_is_connected[i]) {
                    // Need to close the socket connection.
                    close(feed_sock[i]);
                    feed_sock_is_connected[i] = false;
                    CONSOLE_INFO("CommsManager::WiFiStationTask", "Closed socket for feed %d.", i);
                }
                continue;  // Don't need to do anything else if socket should be closed and is closed.
            }

            // Socket should be open.
            if (!feed_sock_is_connected[i]) {
                // Need to open the socket connection.

                // Meter reconnect attempt interval.
                uint32_t timestamp_ms = get_time_since_boot_ms();
                if (timestamp_ms - feed_sock_last_connect_timestamp_ms[i] <= kWiFiTCPSocketReconnectIntervalMs) {
                    continue;
                }
                feed_sock_last_connect_timestamp_ms[i] = timestamp_ms;

                // Create socket.
                // IPv4, TCP
                feed_sock[i] = socket(AF_INET, SOCK_STREAM, IPPROTO_IP);
                if (feed_sock[i] <= 0) {
                    CONSOLE_ERROR("CommsManager::WiFiStationTask", "Unable to create socket for feed %d: errno %d", i,
                                  errno);
                    continue;
                }
                CONSOLE_INFO("CommsManager::WiFiStationTask", "Socket for feed %d created, connecting to %s:%d", i,
                             settings_manager.settings.feed_uris[i], settings_manager.settings.feed_ports[i]);

                struct sockaddr_in dest_addr;
                inet_pton(AF_INET, settings_manager.settings.feed_uris[i], &dest_addr.sin_addr);
                // dest_addr.sin_addr.s_addr = inet_addr(settings_manager.settings.feed_uris[i]);
                dest_addr.sin_family = AF_INET;
                dest_addr.sin_port = htons(settings_manager.settings.feed_ports[i]);

                int err = connect(feed_sock[i], (struct sockaddr*)&dest_addr, sizeof(dest_addr));
                if (err != 0) {
                    CONSOLE_ERROR(
                        "CommsManager::WiFiStationTask", "Socket unable to connect to URI %s:%d for feed %d: errno %d",
                        settings_manager.settings.feed_uris[i], settings_manager.settings.feed_ports[i], i, errno);
                    close(feed_sock[i]);
                    feed_sock_is_connected[i] = false;
                    continue;
                }
                CONSOLE_INFO("CommsManager::WiFiStationTask", "Successfully connected to %s",
                             settings_manager.settings.feed_uris[i]);
                feed_sock_is_connected[i] = true;
            }

            // Send packet!
            // NOTE: Construct packets that are specific to a feed in case statements here!
            switch (settings_manager.settings.feed_protocols[i]) {
                case SettingsManager::ReportingProtocol::kBeast: {
                    // Send Beast packet.
                    // Double the length as a hack to make room for the escaped UUID.
                    uint8_t beast_message_buf[2 * SettingsManager::Settings::kFeedReceiverIDNumBytes +
                                              kBeastFrameMaxLenBytes];
                    uint16_t beast_message_len_bytes = TransponderPacketToBeastFramePrependReceiverID(
                        tpacket, beast_message_buf, settings_manager.settings.feed_receiver_ids[i],
                        SettingsManager::Settings::kFeedReceiverIDNumBytes);

                    int err = send(feed_sock[i], beast_message_buf, beast_message_len_bytes, 0);
                    if (err < 0) {
                        CONSOLE_ERROR("CommsManager::WiFiStationTask",
                                      "Error occurred during sending %d Byte beast message to feed %d with URI %s "
                                      "on port %d: "
                                      "errno %d.",
                                      beast_message_len_bytes, i, settings_manager.settings.feed_uris[i],
                                      settings_manager.settings.feed_ports[i], errno);
                        // Mark socket as disconnected and try reconnecting in next reporting interval.
                        close(feed_sock[i]);
                        feed_sock_is_connected[i] = false;
                    } else {
                        CONSOLE_INFO("CommsManager::WiFiStationTask", "Message sent to feed %d.", i);
                    }
                    break;
                }
                // TODO: add other protocols here
                default:
                    // No reporting protocol or unsupported protocol: do nothing.
                    break;
            }
        }
    }

    // Close all sockets while exiting.
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        if (feed_sock_is_connected[i]) {
            // Need to close the socket connection.
            close(feed_sock[i]);
            feed_sock_is_connected[i] = false;  // Not necessary but leaving this here in case of refactor.
        }
    }
}

static const char* get_auth_mode_name(wifi_auth_mode_t auth_mode) {
    switch (auth_mode) {
        case WIFI_AUTH_OPEN:
            return "OPEN";
        case WIFI_AUTH_WEP:
            return "WEP";
        case WIFI_AUTH_WPA_PSK:
            return "WPA_PSK";
        case WIFI_AUTH_WPA2_PSK:
            return "WPA2_PSK";
        case WIFI_AUTH_WPA_WPA2_PSK:
            return "WPA_WPA2_PSK";
        case WIFI_AUTH_WPA3_PSK:
            return "WPA3_PSK";
        case WIFI_AUTH_WPA2_WPA3_PSK:
            return "WPA2_WPA3_PSK";
        default:
            return "UNKNOWN";
    }
}

// WARNING: This function explodes the stack!
// static void wifi_scan_task(void* pvParameters) {
//     CONSOLE_INFO("WiFiScan", "Starting scan...");

//     // Configure scan settings
//     wifi_scan_config_t scan_config = {
//         .ssid = 0,
//         .bssid = 0,
//         .channel = 0,        // 0 = scan all channels
//         .show_hidden = true  // show hidden SSIDs
//     };

//     // Start scan
//     ESP_ERROR_CHECK(esp_wifi_scan_start(&scan_config, true));

//     // Get number of APs found
//     uint16_t ap_num = kWiFiScanDefaultListSize;
//     wifi_ap_record_t ap_records[kWiFiScanDefaultListSize];
//     ESP_ERROR_CHECK(esp_wifi_scan_get_ap_records(&ap_num, ap_records));

//     // Print header
//     CONSOLE_INFO("WiFiScan", "Found %d access points:", ap_num);
//     CONSOLE_INFO("WiFiScan", "               SSID              | Channel | RSSI |   Auth Mode");
//     CONSOLE_INFO("WiFiScan", "----------------------------------------------------------------");

//     // Print AP details
//     for (int i = 0; i < ap_num; i++) {
//         CONSOLE_INFO("WiFiScan", "%32s | %7d | %4d | %s", ap_records[i].ssid, ap_records[i].primary,
//         ap_records[i].rssi,
//                      get_auth_mode_name(ap_records[i].authmode));
//     }

//     // Print footer
//     CONSOLE_INFO("WiFiScan", "----------------------------------------------------------------");
// }

bool CommsManager::WiFiInit() {
    wifi_clients_list_mutex_ = xSemaphoreCreateMutex();
    wifi_ap_message_queue_ = xQueueCreate(kWiFiMessageQueueLen, sizeof(NetworkMessage));
    wifi_sta_raw_transponder_packet_queue_ = xQueueCreate(kWiFiMessageQueueLen, sizeof(RawTransponderPacket));

    s_wifi_event_group = xEventGroupCreate();
    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default());
    esp_netif_t* ap_netif = esp_netif_create_default_wifi_ap();
    assert(ap_netif);
    esp_netif_t* sta_netif = esp_netif_create_default_wifi_sta();
    ESP_ERROR_CHECK(
        esp_netif_set_hostname(sta_netif, wifi_ap_ssid));  // Reuse the AP SSID as the station hostname for now.
    assert(sta_netif);

    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    ESP_ERROR_CHECK(esp_wifi_init(&cfg));

    ESP_ERROR_CHECK(esp_event_handler_register(WIFI_EVENT, ESP_EVENT_ANY_ID, &wifi_event_handler, NULL));
    ESP_ERROR_CHECK(esp_event_handler_register(IP_EVENT, ESP_EVENT_ANY_ID, &ip_event_handler, NULL));

    wifi_mode_t wifi_mode;
    if (wifi_ap_enabled && wifi_sta_enabled) {
        wifi_mode = WIFI_MODE_APSTA;
    } else if (wifi_ap_enabled) {
        wifi_mode = WIFI_MODE_AP;
    } else {
        wifi_mode = WIFI_MODE_STA;
    }
    ESP_ERROR_CHECK(esp_wifi_set_mode(wifi_mode));

    if (wifi_ap_enabled) {
        // Access Point Configuration
        wifi_config_t wifi_config_ap = {0};

        strncpy((char*)(wifi_config_ap.ap.ssid), wifi_ap_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
        strncpy((char*)(wifi_config_ap.ap.password), wifi_ap_password,
                SettingsManager::Settings::kWiFiPasswordMaxLen + 1);
        wifi_config_ap.ap.channel = wifi_ap_channel;
        wifi_config_ap.ap.ssid_len = (uint8_t)strlen(wifi_ap_ssid);
        if (strlen(wifi_ap_password) == 0) {
            wifi_config_ap.ap.authmode = WIFI_AUTH_OPEN;
        } else {
            wifi_config_ap.ap.authmode = WIFI_AUTH_WPA_WPA2_PSK;
        }
        wifi_config_ap.ap.max_connection = SettingsManager::Settings::kWiFiMaxNumClients;

        ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_AP, &wifi_config_ap));
    }

    if (wifi_sta_enabled) {
        // Station Configuration
        wifi_config_t wifi_config_sta = {0};

        strncpy((char*)(wifi_config_sta.sta.ssid), wifi_sta_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
        strncpy((char*)(wifi_config_sta.sta.password), wifi_sta_password,
                SettingsManager::Settings::kWiFiPasswordMaxLen + 1);

        // wifi_config_sta.sta.threshold.authmode = WIFI_AUTH_WPA2_PSK;
        // wifi_config_sta.sta.pmf_cfg.capable = true;
        // wifi_config_sta.sta.pmf_cfg.required = false;

        ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_STA, &wifi_config_sta));
    }

    if (!wifi_ap_enabled && !wifi_sta_enabled) {
        ESP_ERROR_CHECK(esp_wifi_stop());
        CONSOLE_INFO("CommsManager::WiFiInit", "WiFi disabled.");
        return true;
    }

    ESP_ERROR_CHECK(esp_wifi_start());

    if (wifi_ap_enabled) {
        CONSOLE_INFO("CommsManager::WiFiInit", "WiFi AP started. SSID:%s password:%s", wifi_ap_ssid, wifi_ap_password);

        run_wifi_ap_task_ = true;
        xTaskCreatePinnedToCore(wifi_access_point_task, "wifi_ap_task", 4096, NULL, kWiFiAPTaskPriority, NULL,
                                kWiFiAPTaskCore);
    }
    if (wifi_sta_enabled) {
        char redacted_password[SettingsManager::Settings::kWiFiPasswordMaxLen];
        SettingsManager::RedactPassword(wifi_sta_password, redacted_password,
                                        SettingsManager::Settings::kWiFiPasswordMaxLen);
        CONSOLE_INFO("CommsManager::WiFiInit", "WiFi Station started. SSID:%s password:%s", wifi_sta_ssid,
                     redacted_password);

        /* Waiting until either the connection is established (WIFI_CONNECTED_BIT) or connection failed for the
         * maximum number of re-tries (WIFI_FAIL_BIT). The bits are set by event_handler() */
        EventBits_t bits = xEventGroupWaitBits(s_wifi_event_group, WIFI_CONNECTED_BIT | WIFI_FAIL_BIT, pdFALSE, pdFALSE,
                                               portMAX_DELAY);

        if (bits & WIFI_CONNECTED_BIT) {
            CONSOLE_INFO("CommsManager::WiFiInit", "Connected to ap SSID:%s password:%s", wifi_sta_ssid,
                         wifi_sta_password);
        } else if (bits & WIFI_FAIL_BIT) {
            CONSOLE_ERROR("CommsManager::WiFiInit", "Failed to connect to SSID:%s, password:%s", wifi_sta_ssid,
                          wifi_sta_password);
            // xTaskCreate(wifi_scan_task, "wifi_scan", 4096, NULL, 5, NULL);
            return false;
        } else {
            CONSOLE_ERROR("CommsManager::WiFiInit", "UNEXPECTED EVENT");
            return false;
        }

        run_wifi_sta_task_ = true;
        xTaskCreatePinnedToCore(wifi_station_task, "wifi_sta_task", 4096, NULL, kWiFiSTATaskPriority, NULL,
                                kWiFiSTATaskCore);
    }

    return true;
}

bool CommsManager::WiFiDeInit() {
    vEventGroupDelete(s_wifi_event_group);
    vSemaphoreDelete(wifi_clients_list_mutex_);
    vQueueDelete(wifi_ap_message_queue_);
    vQueueDelete(wifi_sta_raw_transponder_packet_queue_);

    return true;
}

bool CommsManager::WiFiStationSendRawTransponderPacket(RawTransponderPacket& tpacket) {
    if (!run_wifi_sta_task_) {
        CONSOLE_WARNING("CommsManager::WiFiStationSendRawTransponderPacket",
                        "Can't push to WiFi station transponder packet queue if station is not running.");
        return false;  // Task not started yet, queue not created yet. Pushing to queue would cause an abort.
    }
    int err = xQueueSend(wifi_sta_raw_transponder_packet_queue_, &tpacket, 0);
    if (err == errQUEUE_FULL) {
        CONSOLE_WARNING("CommsManager::WiFiStationSendRawTransponderPacket",
                        "Overflowed WiFi station transponder packet queue.");
        xQueueReset(wifi_sta_raw_transponder_packet_queue_);
        return false;
    } else if (err != pdTRUE) {
        CONSOLE_WARNING("CommsManager::WiFiStationSendRawTransponderPacket",
                        "Pushing transponder packet to WiFi station queue resulted in error code %d.", err);
        return false;
    }
    return true;
}

bool CommsManager::WiFiAccessPointSendMessageToAllStations(NetworkMessage& message) {
    if (!run_wifi_ap_task_) {
        CONSOLE_WARNING("CommsManager::WiFiAccessPointSendMessageToAllStations",
                        "Can't push to WiFi AP message queue if AP is not running.");
        return false;  // Task not started yet, pushing to queue could create an overflow.
    }
    int err = xQueueSend(wifi_ap_message_queue_, &message, 0);
    if (err == errQUEUE_FULL) {
        CONSOLE_WARNING("CommsManager::WiFiAccessPointSendMessageToAllStations", "Overflowed WiFi AP message queue.");
        xQueueReset(wifi_ap_message_queue_);
        return false;
    } else if (err != pdTRUE) {
        CONSOLE_WARNING("CommsManager::WiFiAccessPointSendMessageToAllStations",
                        "Pushing message to WiFi AP message queue resulted in error code %d.", err);
        return false;
    }
    return true;
}