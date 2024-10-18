#include <string.h>

#include <functional>  // for std::bind

#include "cc.h"  // For endiannness swapping.
#include "comms.hh"
#include "esp_event.h"
#include "esp_mac.h"
#include "lwip/err.h"
#include "lwip/sockets.h"
#include "lwip/sys.h"
#include "nvs_flash.h"
#include "task_priorities.hh"

static const uint16_t kGDL90Port = 4000;
static const uint16_t kWiFiNumRetries = 3;
static const uint16_t kWiFiRetryWaitTimeMs = 100;
static const uint16_t kWiFiStaMaxNumReconnectAttempts = 5;
static const uint16_t kWiFiScanDefaultListSize = 20;

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
            ESP_LOGI("CommsManager::WiFiEventHandler", "Station " MACSTR " joined, AID=%d", MAC2STR(event->mac),
                     event->aid);
            break;
        }
        case WIFI_EVENT_AP_STADISCONNECTED: {
            wifi_event_ap_stadisconnected_t* event = (wifi_event_ap_stadisconnected_t*)event_data;
            ESP_LOGI("CommsManager::WiFiEventHandler", "Station " MACSTR " left, AID=%d", MAC2STR(event->mac),
                     event->aid);
            WiFiRemoveClient(event->mac);
            break;
        }
        case WIFI_EVENT_STA_START:
            ESP_LOGI("CommsManager::WiFiEventHandler", "WIFI_EVENT_STA_START - Attempting to connect to AP");
            esp_wifi_connect();
            break;
        case WIFI_EVENT_STA_DISCONNECTED: {
            wifi_event_sta_disconnected_t* event = (wifi_event_sta_disconnected_t*)event_data;
            ESP_LOGW("CommsManager::WiFiEventHandler", "WIFI_EVENT_STA_DISCONNECTED - Disconnect reason : %d",
                     event->reason);

            if (s_retry_num < kWiFiStaMaxNumReconnectAttempts) {
                esp_wifi_connect();
                s_retry_num++;
                ESP_LOGI("CommsManager::WiFiEventHandler", "Retry to connect to the AP, attempt %d/%d", s_retry_num,
                         kWiFiStaMaxNumReconnectAttempts);
            } else {
                xEventGroupSetBits(s_wifi_event_group, WIFI_FAIL_BIT);
                ESP_LOGE("CommsManager::WiFiEventHandler", "Failed to connect to AP after %d attempts",
                         kWiFiStaMaxNumReconnectAttempts);
            }
            break;
        }
        case WIFI_EVENT_STA_CONNECTED:
            ESP_LOGI("CommsManager::WiFiEventHandler", "WIFI_EVENT_STA_CONNECTED - Successfully connected to AP");
            break;
    }
}

void CommsManager::IPEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    if (event_id == IP_EVENT_AP_STAIPASSIGNED) {
        ip_event_ap_staipassigned_t* event = (ip_event_ap_staipassigned_t*)event_data;
        ESP_LOGI("CommsManager::IPEventHandler", "Station assigned IP:" IPSTR, IP2STR(&event->ip));
        WiFiAddClient(event->ip, event->mac);
    } else if (event_id == IP_EVENT_STA_GOT_IP) {
        ip_event_got_ip_t* event = (ip_event_got_ip_t*)event_data;
        ESP_LOGI("CommsManager::WiFiEventHandler", "Got IP:" IPSTR, IP2STR(&event->ip_info.ip));
    }
}

void CommsManager::WiFiAccessPointTask(void* pvParameters) {
    NetworkMessage message;

    // Create socket.
    int sock = socket(AF_INET, SOCK_DGRAM, IPPROTO_IP);
    if (sock < 0) {
        ESP_LOGE("CommsManager::WiFiAccessPointTask", "Unable to create socket: errno %d", errno);
        return;
    }

    // Set timeout
    struct timeval timeout;
    timeout.tv_sec = 10;
    timeout.tv_usec = 0;
    setsockopt(sock, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof timeout);

    struct sockaddr_in dest_addr;
    dest_addr.sin_family = AF_INET;
    dest_addr.sin_port = htons(kGDL90Port);

    while (run_wifi_ap_task_) {
        if (xQueueReceive(wifi_message_queue_, &message, portMAX_DELAY) == pdTRUE) {
            // int send_buf_size = 16384;  // Set a larger send buffer
            // setsockopt(sock, SOL_SOCKET, SO_SNDBUF, &send_buf_size, sizeof(send_buf_size));

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
                        // ESP_LOGE("CommsManager::WiFiAccessPointTask", "Error occurred during sending:
                        // errno %d.", errno);
                        ESP_LOGE("CommsManager::WiFiAccessPointTask",
                                 "Error occurred during sending: errno %d. Tried %d times.", errno, num_tries);
                    }
                }
            }
            xSemaphoreGive(wifi_clients_list_mutex_);

            // ESP_LOGI("CommsManager::WiFiUDPServerTask", "Message sent to %d clients.",
            // num_wifi_clients_);
        }
    }
    shutdown(sock, 0);
    close(sock);
}

void CommsManager::WiFiStationTask(void* pvParameters) {
    while (true) {
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
void WiFiScan() {
    ESP_LOGI("WiFiScan", "Starting scan...");

    // Configure scan settings
    wifi_scan_config_t scan_config = {
        .ssid = 0,
        .bssid = 0,
        .channel = 0,        // 0 = scan all channels
        .show_hidden = true  // show hidden SSIDs
    };

    // Start scan
    ESP_ERROR_CHECK(esp_wifi_scan_start(&scan_config, true));

    // Get number of APs found
    uint16_t ap_num = kWiFiScanDefaultListSize;
    wifi_ap_record_t ap_records[kWiFiScanDefaultListSize];
    ESP_ERROR_CHECK(esp_wifi_scan_get_ap_records(&ap_num, ap_records));

    // Print header
    ESP_LOGI("WiFiScan", "Found %d access points:", ap_num);
    ESP_LOGI("WiFiScan", "               SSID              | Channel | RSSI |   Auth Mode");
    ESP_LOGI("WiFiScan", "----------------------------------------------------------------");

    // Print AP details
    for (int i = 0; i < ap_num; i++) {
        ESP_LOGI("WiFiScan", "%32s | %7d | %4d | %s", ap_records[i].ssid, ap_records[i].primary, ap_records[i].rssi,
                 get_auth_mode_name(ap_records[i].authmode));
    }

    // Print footer
    ESP_LOGI("WiFiScan", "----------------------------------------------------------------");
}

bool CommsManager::WiFiInit() {
    wifi_clients_list_mutex_ = xSemaphoreCreateMutex();
    wifi_message_queue_ = xQueueCreate(kWiFiMessageQueueLen, sizeof(NetworkMessage));

    s_wifi_event_group = xEventGroupCreate();
    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default());
    esp_netif_create_default_wifi_ap();
    esp_netif_t* sta_netif = esp_netif_create_default_wifi_sta();
    ESP_ERROR_CHECK(
        esp_netif_set_hostname(sta_netif, wifi_ap_ssid));  // Reuse the AP SSID as the station hostname for now.

    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    ESP_ERROR_CHECK(esp_wifi_init(&cfg));

    ESP_ERROR_CHECK(esp_event_handler_instance_register(WIFI_EVENT, ESP_EVENT_ANY_ID, wifi_event_handler, NULL, NULL));
    ESP_ERROR_CHECK(esp_event_handler_instance_register(IP_EVENT, ESP_EVENT_ANY_ID, &ip_event_handler, NULL, NULL));

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
        wifi_config_t wifi_config_ap;

        strncpy((char*)(wifi_config_ap.ap.ssid), wifi_ap_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
        strncpy((char*)(wifi_config_ap.ap.password), wifi_ap_password,
                SettingsManager::Settings::kWiFiPasswordMaxLen + 1);
        wifi_config_ap.ap.channel = wifi_ap_channel;
        wifi_config_ap.ap.ssid_len = (uint8_t)strlen(wifi_ap_ssid);
        wifi_config_ap.ap.authmode = WIFI_AUTH_WPA_WPA2_PSK;
        wifi_config_ap.ap.max_connection = SettingsManager::Settings::kWiFiMaxNumClients;

        ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_AP, &wifi_config_ap));
    }

    if (wifi_sta_enabled) {
        // Station Configuration
        wifi_config_t wifi_config_sta;

        strncpy((char*)(wifi_config_sta.sta.ssid), wifi_sta_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
        strncpy((char*)(wifi_config_sta.sta.password), wifi_sta_password,
                SettingsManager::Settings::kWiFiPasswordMaxLen + 1);
        wifi_config_sta.sta.threshold.authmode = WIFI_AUTH_WPA2_PSK;
        wifi_config_sta.sta.pmf_cfg.capable = true;
        wifi_config_sta.sta.pmf_cfg.required = false;

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

        /* Waiting until either the connection is established (WIFI_CONNECTED_BIT) or connection failed for the maximum
         * number of re-tries (WIFI_FAIL_BIT). The bits are set by event_handler() */
        EventBits_t bits = xEventGroupWaitBits(s_wifi_event_group, WIFI_CONNECTED_BIT | WIFI_FAIL_BIT, pdFALSE, pdFALSE,
                                               portMAX_DELAY);

        if (bits & WIFI_CONNECTED_BIT) {
            ESP_LOGI("CommsManager::WiFiInit", "Connected to ap SSID:%s password:%s", wifi_sta_ssid, wifi_sta_password);
            return ESP_OK;
        } else if (bits & WIFI_FAIL_BIT) {
            ESP_LOGE("CommsManager::WiFiInit", "Failed to connect to SSID:%s, password:%s", wifi_sta_ssid,
                     wifi_sta_password);
            WiFiScan();
            return ESP_FAIL;
        } else {
            ESP_LOGE("CommsManager::WiFiInit", "UNEXPECTED EVENT");
            return ESP_FAIL;
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
    vQueueDelete(wifi_message_queue_);

    return true;
}

bool CommsManager::WiFiSendMessageToAllClients(NetworkMessage& message) {
    if (xQueueSend(wifi_message_queue_, &message, 0) != pdTRUE) {
        return false;
    }
    return true;
}