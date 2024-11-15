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
#include "lwip/sockets.h"  // For port definition.
#include "settings.hh"

class CommsManager {
   public:
    static const uint16_t kMaxNetworkMessageLenBytes = 256;
    static const uint16_t kWiFiMessageQueueLen = 110;
    static const uint16_t kMACAddressNumBytes = 6;
    static const uint32_t kWiFiSTATaskUpdateIntervalMs = 100;
    static const uint32_t kWiFiSTATaskUpdateIntervalTicks = kWiFiSTATaskUpdateIntervalMs / portTICK_PERIOD_MS;

    struct NetworkMessage {
        in_port_t port = 0;
        uint16_t len = 0;
        uint8_t data[kMaxNetworkMessageLenBytes];

        NetworkMessage() { memset(data, 0x0, kMaxNetworkMessageLenBytes); }
    };

    CommsManager() {
        wifi_clients_list_mutex_ = xSemaphoreCreateMutex();
        wifi_ap_message_queue_ = xQueueCreate(kWiFiMessageQueueLen, sizeof(NetworkMessage));
        wifi_sta_raw_transponder_packet_queue_ = xQueueCreate(kWiFiMessageQueueLen, sizeof(RawTransponderPacket));
        wifi_event_group_ = xEventGroupCreate();
    }

    ~CommsManager() {
        vEventGroupDelete(wifi_event_group_);
        vSemaphoreDelete(wifi_clients_list_mutex_);
        vQueueDelete(wifi_ap_message_queue_);
        vQueueDelete(wifi_sta_raw_transponder_packet_queue_);
    }

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

    /**
     * Initialize the WiFi peripheral (access point and station). WiFiDeInit() and WiFiInit() should be called every
     * time network settings are chagned.
     */
    bool WiFiInit();

    /**
     * De-initialize the WiFi peripheral (access point and station).
     */
    bool WiFiDeInit();

    /**
     * Send a raw UDP message to all statiosn that are connected to the ESP32 while operating in access point mode.
     */
    bool WiFiAccessPointSendMessageToAllStations(NetworkMessage& message);

    /**
     * Send messages to stations connected to the ESP32 access point.
     */
    void WiFiAccessPointTask(void* pvParameters);

    /**
     * Returns whether the ESP32 is connected to an external WiFi network as a station.
     * @retval True if connected and assigned IP address, false otherwise.
     */
    bool WiFiStationhasIP() { return wifi_sta_has_ip_; }

    /**
     * Send messages to feeds that are being fed via an access point that the ESP32 is connected to as a station.
     */
    void WiFiStationTask(void* pvParameters);

    /**
     * Sends a raw transponder packet to feeds via the external WiFi network that the ESP32 is a station on. It's
     * recommended to only call this function if WiFiStationhasIP() returns true, otherwise it will throw a warning.
     * @param[in] tpacket RawTransponderPacket to send.
     * @retval True if packet was successfully sent, false otherwise.
     */
    bool WiFiStationSendRawTransponderPacket(RawTransponderPacket& tpacket);

    // Public so that pass-through functions can access it.
    void WiFiEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data);
    void IPEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data);

    inline uint16_t GetNumWiFiClients() { return num_wifi_clients_; }

    bool wifi_ap_enabled = true;
    uint8_t wifi_ap_channel = 1;
    esp_netif_t* wifi_ap_netif_ = nullptr;
    ;
    char wifi_ap_ssid[SettingsManager::Settings::kWiFiSSIDMaxLen + 1];          // Add space for null terminator.
    char wifi_ap_password[SettingsManager::Settings::kWiFiPasswordMaxLen + 1];  // Add space for null terminator.
    esp_netif_t* wifi_sta_netif_ = nullptr;
    bool wifi_sta_enabled = false;
    char wifi_sta_ssid[SettingsManager::Settings::kWiFiSSIDMaxLen + 1];          // Add space for null terminator.
    char wifi_sta_password[SettingsManager::Settings::kWiFiPasswordMaxLen + 1];  // Add space for null terminator.

    // Feed statistics (messages per second).
    uint16_t feed_mps[SettingsManager::Settings::kMaxNumFeeds] = {0};

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
    EventGroupHandle_t wifi_event_group_;  // FreeRTOS event group to signal when we are connected.
    QueueHandle_t wifi_ap_message_queue_;
    QueueHandle_t wifi_sta_raw_transponder_packet_queue_;
    bool run_wifi_ap_task_ = false;   // Flag used to tell wifi AP task to shut down.
    bool run_wifi_sta_task_ = false;  // Flag used to tell wifi station task to shut down.
    TaskHandle_t wifi_ap_task_handle = nullptr;
    TaskHandle_t wifi_sta_task_handle = nullptr;
    bool wifi_was_initialized_ = false;
    bool wifi_sta_has_ip_ =
        false;  // Flag to indicate when successfully connected to WiFi. Don't create sockets until STA is connected.

    uint16_t feed_mps_counter_[SettingsManager::Settings::kMaxNumFeeds] = {0};
    uint32_t feed_mps_last_update_timestamp_ms_ = 0;
};

extern CommsManager comms_manager;

#define CONSOLE_ERROR(tag, ...)   ESP_LOGE(tag, __VA_ARGS__)
#define CONSOLE_WARNING(tag, ...) ESP_LOGW(tag, __VA_ARGS__)
#define CONSOLE_INFO(tag, ...)    ESP_LOGI(tag, __VA_ARGS__)
#define CONSOLE_PRINTF(...)       printf(__VA_ARGS__);

#endif /* COMMS_HH_ */