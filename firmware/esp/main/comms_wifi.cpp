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
    if (event_id == WIFI_EVENT_AP_STACONNECTED) {
        wifi_event_ap_staconnected_t* event = (wifi_event_ap_staconnected_t*)event_data;
        ESP_LOGI("CommsManager::WiFiEventHandler", "Station " MACSTR " joined, AID=%d", MAC2STR(event->mac),
                 event->aid);
    } else if (event_id == WIFI_EVENT_AP_STADISCONNECTED) {
        wifi_event_ap_stadisconnected_t* event = (wifi_event_ap_stadisconnected_t*)event_data;
        ESP_LOGI("CommsManager::WiFiEventHandler", "Station " MACSTR " left, AID=%d", MAC2STR(event->mac), event->aid);
        WiFiRemoveClient(event->mac);
    }
}

void CommsManager::IPEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    if (event_id == IP_EVENT_AP_STAIPASSIGNED) {
        ip_event_ap_staipassigned_t* event = (ip_event_ap_staipassigned_t*)event_data;
        ESP_LOGI("CommsManager::IPEventHandler", "Station assigned IP:" IPSTR, IP2STR(&event->ip));
        WiFiAddClient(event->ip, event->mac);
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
                        // Increased the number of UDP control blocks (LWIP_MAX_UDP_PCBS) in SDK menuconfig from 16
                        // to 96.
                        // Changed TCP/IP stack size from 3072 to 12288.
                        if (ret >= 0 || errno != ENOMEM) {
                            break;
                        }
                        vTaskDelay(kWiFiRetryWaitTimeMs /
                                   portTICK_PERIOD_MS);  // Let packet send to avoid an ENOMEM error.
                    }

                    if (ret < 0) {
                        // ESP_LOGE("CommsManager::WiFiAccessPointTask", "Error occurred during sending: errno %d.",
                        // errno);
                        ESP_LOGE("CommsManager::WiFiAccessPointTask",
                                 "Error occurred during sending: errno %d. Tried %d times.", errno, num_tries);
                    }
                }
            }
            xSemaphoreGive(wifi_clients_list_mutex_);

            // ESP_LOGI("CommsManager::WiFiUDPServerTask", "Message sent to %d clients.", num_wifi_clients_);
        }
    }
    shutdown(sock, 0);
    close(sock);
}

void CommsManager::WiFiStationTask(void* pvParameters) {
    while (true) {
    }
}

bool CommsManager::WiFiInit() {
    wifi_clients_list_mutex_ = xSemaphoreCreateMutex();
    wifi_message_queue_ = xQueueCreate(kWiFiMessageQueueLen, sizeof(NetworkMessage));

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

        ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_STA, &wifi_config_sta));
    }

    if (!wifi_ap_enabled && !wifi_sta_enabled) {
        ESP_ERROR_CHECK(esp_wifi_stop());
        CONSOLE_INFO("CommsManager::WiFiInit", "WiFi disabled.");
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

        run_wifi_sta_task_ = true;
        xTaskCreatePinnedToCore(wifi_station_task, "wifi_sta_task", 4096, NULL, kWiFiSTATaskPriority, NULL,
                                kWiFiSTATaskCore);
    }

    return true;
}

bool CommsManager::WiFiDeInit() {
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