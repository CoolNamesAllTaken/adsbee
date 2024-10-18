#ifndef COMMS_HH_
#define COMMS_HH_

#include "data_structures.hh"
#include "esp_log.h"
#include "esp_system.h"
#include "esp_wifi.h"
#include "freertos/FreeRTOS.h"
#include "freertos/queue.h"
#include "freertos/task.h"
#include "gdl90/gdl90_utils.hh"
#include "settings.hh"

class CommsManager {
   public:
    static const uint16_t kMaxNetworkMessageLenBytes = 256;
    static const uint16_t kWiFiMessageQueueLen = 110;
    static const uint16_t kMACAddressNumBytes = 6;

    struct NetworkMessage {
        uint16_t len = 0;
        uint8_t data[kMaxNetworkMessageLenBytes];

        NetworkMessage() { memset(data, 0x0, kMaxNetworkMessageLenBytes); }
    };

    /**
     * Helper function that converts a MAC buffer to a uint64_t that's easier to pass around and compare.
     * @param[in] mac_buf_in Buffer to read the MAC address value from.
     */
    static uint64_t MACToUint64(uint8_t* mac_buf_in) {
        uint64_t mac_out = 0;
        for (uint16_t i = 0; i < kMACAddressNumBytes; i++) {
            mac_out |= mac_buf_in[i] << ((5 - i) * 8);
        }
        return mac_out;
    }

    struct NetworkClient {
        esp_ip4_addr_t ip;
        uint64_t mac;
        bool active = false;  // "Active" flag allows reuse of open slots in the list when a client disconnects.

        /**
         * Set the MAC address from a buffer, assuming the buffer is a 6 Byte MAC address MSB first.
         * @param[in] mac_buf_in Buffer to read the MAC address value from.
         */
        void SetMAC(uint8_t* mac_buf_in) { mac = MACToUint64(mac_buf_in); }

        /**
         * Get the MAC address by writing it out to a buffer, assuming the buffer is a 6 Byte MAC address MSB first.
         */
        void GetMAC(uint8_t* mac_buf_out) {
            for (uint16_t i = 0; i < kMACAddressNumBytes; i++) {
                mac_buf_out[i] = mac >> ((5 - i) * 8);
            }
        }
    };

    bool WiFiInit();
    bool WiFiDeInit();
    bool WiFiSendMessageToAllClients(NetworkMessage& message);

    void WiFiAccessPointTask(void* pvParameters);
    void WiFiStationTask(void* pvParameters);

    // Public so that pass-through functions can access it.
    void WiFiEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data);
    void IPEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data);

    inline uint16_t GetNumWiFiClients() { return num_wifi_clients_; }

    bool wifi_ap_enabled = true;
    uint8_t wifi_ap_channel = 1;
    char wifi_ap_ssid[SettingsManager::Settings::kWiFiSSIDMaxLen + 1];          // Add space for null terminator.
    char wifi_ap_password[SettingsManager::Settings::kWiFiPasswordMaxLen + 1];  // Add space for null terminator.
    bool wifi_sta_enabled = false;
    char wifi_sta_ssid[SettingsManager::Settings::kWiFiSSIDMaxLen + 1];          // Add space for null terminator.
    char wifi_sta_password[SettingsManager::Settings::kWiFiPasswordMaxLen + 1];  // Add space for null terminator.

   private:
    /**
     * Adds a WiFi client to the WiFi client list. Takes both an IP and a MAC address because this is when the IP
     * address is assigned, and the MAC address will be needed for removing the client later.
     * @param[in] client_ip IP address of the new client.
     * @param[in] client_mac MAC address of the new client.
     */
    void WiFiAddClient(esp_ip4_addr_t client_ip, uint8_t* client_mac) {
        xSemaphoreTake(wifi_clients_list_mutex_, portMAX_DELAY);
        for (int i = 0; i < SettingsManager::Settings::kWiFiMaxNumClients; i++) {
            if (!wifi_clients_list_[i].active) {
                wifi_clients_list_[i].ip = client_ip;
                wifi_clients_list_[i].SetMAC(client_mac);
                wifi_clients_list_[i].active = true;
                num_wifi_clients_++;
                break;
            }
        }
        xSemaphoreGive(wifi_clients_list_mutex_);
    }

    /**
     * Removes a WiFi client from the WiFi client list. Takes a MAC address since disconnection events don't come with
     * an IP.
     * @param[in] mac_buf_in 6-Byte buffer containing the MAC address of the client that disconnected.
     */
    void WiFiRemoveClient(uint8_t* mac_buf_in) {
        uint64_t client_mac = MACToUint64(mac_buf_in);
        xSemaphoreTake(wifi_clients_list_mutex_, portMAX_DELAY);
        for (int i = 0; i < SettingsManager::Settings::kWiFiMaxNumClients; i++) {
            if (wifi_clients_list_[i].active && (wifi_clients_list_[i].mac == client_mac)) {
                wifi_clients_list_[i].active = false;
                num_wifi_clients_--;
                break;
            }
        }
        xSemaphoreGive(wifi_clients_list_mutex_);
    }

    NetworkClient wifi_clients_list_[SettingsManager::Settings::kWiFiMaxNumClients] = {0, 0, 0};
    uint16_t num_wifi_clients_ = 0;
    SemaphoreHandle_t wifi_clients_list_mutex_;
    QueueHandle_t wifi_message_queue_;
    bool run_wifi_ap_task_ = false;   // Flag used to tell wifi AP task to shut down.
    bool run_wifi_sta_task_ = false;  // Flag used to tell wifi station task to shut down.
};

extern CommsManager comms_manager;

#define CONSOLE_ERROR(tag, ...)   ESP_LOGE(tag, __VA_ARGS__)
#define CONSOLE_WARNING(tag, ...) ESP_LOGW(tag, __VA_ARGS__)
#define CONSOLE_INFO(tag, ...)    ESP_LOGI(tag, __VA_ARGS__)

#endif /* COMMS_HH_ */