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

static const uint16_t kGDL90Port = 4000;

/** "Pass-Through" functions used to access member functions in callbacks. **/
void wifi_event_handler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    comms_manager.WiFiEventHandler(arg, event_base, event_id, event_data);
}

void wifi_udp_server_task(void* pvParameters) { comms_manager.WiFiUDPServerTask(pvParameters); }
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
    } else if (event_id == IP_EVENT_AP_STAIPASSIGNED) {
        ip_event_ap_staipassigned_t* event = (ip_event_ap_staipassigned_t*)event_data;
        ESP_LOGI("CommsManager::WiFiEventHandler", "Station assigned IP:" IPSTR, IP2STR(&event->ip));
        WiFiAddClient(event->ip, event->mac);
    }
}

void CommsManager::WiFiUDPServerTask(void* pvParameters) {
    NetworkMessage message;
    while (run_udp_server_) {
        if (xQueueReceive(wifi_message_queue_, &message, portMAX_DELAY) == pdTRUE) {
            int sock = socket(AF_INET, SOCK_DGRAM, IPPROTO_IP);
            if (sock < 0) {
                ESP_LOGE("CommsManager::WiFiUDPServerTask", "Unable to create socket: errno %d", errno);
                return;
            }

            struct sockaddr_in dest_addr;
            dest_addr.sin_family = AF_INET;
            dest_addr.sin_port = htons(kGDL90Port);

            xSemaphoreTake(wifi_clients_list_mutex_, portMAX_DELAY);
            for (int i = 0; i < SettingsManager::Settings::kWiFiMaxNumClients; i++) {
                if (wifi_clients_list_[i].active) {
                    dest_addr.sin_addr.s_addr = wifi_clients_list_[i].ip.addr;
                    int err =
                        sendto(sock, message.data, message.len, 0, (struct sockaddr*)&dest_addr, sizeof(dest_addr));
                    if (err < 0) {
                        ESP_LOGE("CommsManager::WiFiUDPServerTask", "Error occurred during sending: errno %d", errno);
                    }
                }
            }
            xSemaphoreGive(wifi_clients_list_mutex_);

            close(sock);

            ESP_LOGI("CommsManager::WiFiUDPServerTask", "Message sent to %d clients.", num_wifi_clients_);
        }
    }
}

bool CommsManager::WiFiInit() {
    wifi_clients_list_mutex_ = xSemaphoreCreateMutex();
    wifi_message_queue_ = xQueueCreate(kWiFiMessageQueueLen, sizeof(NetworkMessage));

    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default());
    esp_netif_create_default_wifi_ap();

    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    ESP_ERROR_CHECK(esp_wifi_init(&cfg));

    ESP_ERROR_CHECK(esp_event_handler_instance_register(WIFI_EVENT, ESP_EVENT_ANY_ID, wifi_event_handler, NULL, NULL));
    ESP_ERROR_CHECK(
        esp_event_handler_instance_register(IP_EVENT, IP_EVENT_AP_STAIPASSIGNED, &wifi_event_handler, NULL, NULL));

    wifi_config_t wifi_config = {
        .ap =
            {
                .ssid = "",
                .password = "",
                .ssid_len = (uint8_t)strlen(wifi_ssid),
                .channel = 1,
                .authmode = WIFI_AUTH_WPA_WPA2_PSK,
                .max_connection = SettingsManager::Settings::kWiFiMaxNumClients,
            },
    };
    strncpy((char*)(wifi_config.ap.ssid), wifi_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
    strncpy((char*)(wifi_config.ap.password), wifi_password, SettingsManager::Settings::kWiFiPasswordMaxLen + 1);

    ESP_ERROR_CHECK(esp_wifi_set_mode((wifi_mode_t)wifi_mode));
    ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_AP, &wifi_config));
    ESP_ERROR_CHECK(esp_wifi_start());

    CONSOLE_INFO("CommsManager::WiFiInit", "WiFi AP started. SSID:%s password:%s", wifi_ssid, wifi_password);

    run_udp_server_ = true;
    xTaskCreate(wifi_udp_server_task, "udp_server", 4096, NULL, 2, NULL);
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