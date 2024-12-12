#ifndef COMMS_HH_
#define COMMS_HH_

#include "data_structures.hh"
#include "driver/gpio.h"
#include "esp_eth.h"
#include "esp_log.h"
#include "esp_system.h"
#include "esp_wifi.h"
#include "freertos/FreeRTOS.h"
#include "freertos/queue.h"
#include "freertos/task.h"
#include "gdl90/gdl90_utils.hh"
#include "lwip/sockets.h"  // For port definition.
#include "object_dictionary.hh"
#include "settings.hh"

#define CONSOLE_ERROR(tag, ...)   ESP_LOGE(tag, __VA_ARGS__)
#define CONSOLE_WARNING(tag, ...) ESP_LOGW(tag, __VA_ARGS__)
#define CONSOLE_INFO(tag, ...)    ESP_LOGI(tag, __VA_ARGS__)
#define CONSOLE_PRINTF(...)       printf(__VA_ARGS__);

class CommsManager {
   public:
    static const uint16_t kMaxNetworkMessageLenBytes = 256;
    static const uint16_t kWiFiMessageQueueLen = 110;
    static const uint32_t kWiFiStaReconnectIntervalMs = 5000;
    static const uint32_t kEthernetReconnectIntervalMs = 5000;
    static const uint32_t kWiFiSTATaskUpdateIntervalMs = 100;
    static const uint32_t kWiFiSTATaskUpdateIntervalTicks = kWiFiSTATaskUpdateIntervalMs / portTICK_PERIOD_MS;

    struct CommsManagerConfig {
        int32_t aux_spi_clk_rate_hz = 40e6;  // 40 MHz (this could go up to 80MHz).
        spi_host_device_t aux_spi_handle = SPI3_HOST;
        gpio_num_t aux_spi_mosi_pin = GPIO_NUM_14;
        gpio_num_t aux_spi_miso_pin = GPIO_NUM_13;
        gpio_num_t aux_spi_clk_pin = GPIO_NUM_17;
        gpio_num_t aux_spi_cs_pin = GPIO_NUM_18;
        gpio_num_t aux_io_b_pin = GPIO_NUM_48;  // W5500 RST
        gpio_num_t aux_io_c_pin = GPIO_NUM_47;  // W5500 INT
    };

    struct NetworkMessage {
        in_port_t port = 0;
        uint16_t len = 0;
        uint8_t data[kMaxNetworkMessageLenBytes];

        NetworkMessage() { memset(data, 0x0, kMaxNetworkMessageLenBytes); }
    };

    CommsManager(CommsManagerConfig config_in) : config_(config_in) {
        wifi_clients_list_mutex_ = xSemaphoreCreateMutex();
        wifi_ap_message_queue_ = xQueueCreate(kWiFiMessageQueueLen, sizeof(NetworkMessage));
        ip_wan_decoded_transponder_packet_queue_ = xQueueCreate(kWiFiMessageQueueLen, sizeof(DecodedTransponderPacket));
    }

    ~CommsManager() {
        vSemaphoreDelete(wifi_clients_list_mutex_);
        vQueueDelete(wifi_ap_message_queue_);
        vQueueDelete(ip_wan_decoded_transponder_packet_queue_);
    }

    /**
     * Helper function that converts a MAC buffer to a uint64_t that's easier to pass around and compare.
     * @param[in] mac_buf_in Buffer to read the MAC address value from.
     */
    static uint64_t MACToUint64(uint8_t* mac_buf_in) {
        uint64_t mac_out = 0;
        for (uint16_t i = 0; i < SettingsManager::Settings::kMACAddrNumBytes; i++) {
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
            for (uint16_t i = 0; i < SettingsManager::Settings::kMACAddrNumBytes; i++) {
                mac_buf_out[i] = mac >> ((5 - i) * 8);
            }
        }
    };

    /**
     * Initialize prerequisites for WiFi and Ethernet.
     */
    bool Init() {
        if (esp_netif_init() != ESP_OK) {
            CONSOLE_ERROR("CommsManager::Init", "Failed to initialize esp_netif.");
            return false;
        }
        if (esp_event_loop_create_default() != ESP_OK) {
            CONSOLE_ERROR("CommsManager::Init", "Failed to create default event loop.");
            return false;
        }
        return true;
    }

    /**
     * Returns whether the ESP32 is connected to an external network via Ethernet.
     * @retval True if connected and assigned IP address, false otherwise.
     */
    bool EthernetHasIP() { return ethernet_has_ip_; }

    /**
     * Initialize the Ethernet peripheral (WIZNet W5500).
     */
    bool EthernetInit();

    /**
     * De-initialize the Ethernet peripheral (WIZNet W5500).
     */
    bool EthernetDeInit();

    /**
     * Handle Ethernet hardware level events.
     */
    void EthernetEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data);

    /**
     * Handle IP level events for Ethernet. Automatically initialized when either Ethernet or WiFi is initialized.
     */
    void EthernetIPEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data);

    /**
     * Get the current status of ESP32 network interfaces as an ESP32NetworkInfo struct.
     */
    ObjectDictionary::ESP32NetworkInfo GetNetworkInfo() {
        ObjectDictionary::ESP32NetworkInfo network_info;

        // Ethernet network info.
        network_info.ethernet_enabled = ethernet_enabled;
        network_info.ethernet_has_ip = ethernet_has_ip_;
        memcpy(network_info.ethernet_ip, ethernet_ip, SettingsManager::Settings::kIPAddrStrLen + 1);
        memcpy(network_info.ethernet_netmask, ethernet_netmask, SettingsManager::Settings::kIPAddrStrLen + 1);
        memcpy(network_info.ethernet_gateway, ethernet_gateway, SettingsManager::Settings::kIPAddrStrLen + 1);

        // WiFi station network info.
        network_info.wifi_sta_enabled = wifi_sta_enabled;
        memcpy(network_info.wifi_sta_ssid, wifi_sta_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
        network_info.wifi_sta_has_ip = wifi_sta_has_ip_;
        memcpy(network_info.wifi_sta_ip, wifi_sta_ip, SettingsManager::Settings::kIPAddrStrLen + 1);
        memcpy(network_info.wifi_sta_netmask, wifi_sta_netmask, SettingsManager::Settings::kIPAddrStrLen + 1);
        memcpy(network_info.wifi_sta_gateway, wifi_sta_gateway, SettingsManager::Settings::kIPAddrStrLen + 1);

        // WiFi access point network info.
        network_info.wifi_ap_enabled = wifi_ap_enabled;
        network_info.wifi_ap_num_clients = num_wifi_clients_;
        for (uint16_t i = 0; i < SettingsManager::Settings::kWiFiMaxNumClients; i++) {
            // Turn client IP address into a string.
            esp_ip4_addr_t ip = wifi_clients_list_[i].ip;
            snprintf(network_info.wifi_ap_client_ips[i], SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip));
            network_info.wifi_ap_client_ips[i][SettingsManager::Settings::kIPAddrStrLen] = '\0';

            // Turn client MAC address into a string.
            uint8_t mac[SettingsManager::Settings::kMACAddrNumBytes];
            wifi_clients_list_[i].GetMAC(mac);
            snprintf(network_info.wifi_ap_client_macs[i], SettingsManager::Settings::kMACAddrStrLen, MACSTR,
                     MAC2STR(mac));
            network_info.wifi_ap_client_macs[i][SettingsManager::Settings::kMACAddrStrLen] = '\0';
        }

        return network_info;
    }

    inline uint16_t GetNumWiFiClients() { return num_wifi_clients_; }

    /**
     * Handler for IP events associated with ethernet and WiFi. Public so that pass through functions can access it.
     */
    void IPEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data);

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
     * Returns whether the WiFi access point is currently hosting any clients. Used to avoid sending packets to the WiFi
     * AP queue when nobody is listening.
     */
    bool WiFiAccessPointHasClients() { return num_wifi_clients_ > 0; }

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
    bool WiFiStationHasIP() { return wifi_sta_has_ip_; }

    // Public so that pass-through functions can access it.
    void WiFiEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data);

    /**
     * Send messages to feeds that are being fed via an internet or LAN connection.
     */
    void IPWANTask(void* pvParameters);

    /**
     * Sends a raw transponder packet to feeds via the external WiFi network that the ESP32 is a station on. It's
     * recommended to only call this function if WiFiStationHasIP() returns true, otherwise it will throw a warning.
     * @param[in] decoded_packet DecodedTransponderPacket to send.
     * @retval True if packet was successfully sent, false otherwise.
     */
    bool IPWANSendDecodedTransponderPacket(DecodedTransponderPacket& decoded_packet);

    // Network hostname.
    char hostname[SettingsManager::Settings::kHostnameMaxLen + 1] = {0};

    // Ethernet public variables.
    bool ethernet_enabled = false;
    char ethernet_ip[SettingsManager::Settings::kIPAddrStrLen + 1] = {
        0};  // IP address of the ESP32 Ethernet interface.
    char ethernet_netmask[SettingsManager::Settings::kIPAddrStrLen + 1] = {
        0};  // Netmask of the ESP32 Ethernet interface.
    char ethernet_gateway[SettingsManager::Settings::kIPAddrStrLen + 1] = {
        0};  // Gateway of the ESP32 Ethernet interface.

    // Ethernet public variables.
    esp_eth_handle_t ethernet_handle;  // Used by pass-through functions for connect / disconnect.

    // WiFi AP public variables.
    bool wifi_ap_enabled = true;
    uint8_t wifi_ap_channel = 1;
    char wifi_ap_ssid[SettingsManager::Settings::kWiFiSSIDMaxLen + 1];          // Add space for null terminator.
    char wifi_ap_password[SettingsManager::Settings::kWiFiPasswordMaxLen + 1];  // Add space for null terminator.

    // WiFi STA public variables.
    bool wifi_sta_enabled = false;
    char wifi_sta_ssid[SettingsManager::Settings::kWiFiSSIDMaxLen + 1];          // Add space for null terminator.
    char wifi_sta_password[SettingsManager::Settings::kWiFiPasswordMaxLen + 1];  // Add space for null terminator.
    char wifi_sta_ip[SettingsManager::Settings::kIPAddrStrLen + 1] = {0};       // IP address of the ESP32 WiFi station.
    char wifi_sta_netmask[SettingsManager::Settings::kIPAddrStrLen + 1] = {0};  // Netmask of the ESP32 WiFi station.
    char wifi_sta_gateway[SettingsManager::Settings::kIPAddrStrLen + 1] = {0};  // Gateway of the ESP32 WiFi station.

    // Feed statistics (messages per second).
    uint16_t feed_mps[SettingsManager::Settings::kMaxNumFeeds] = {0};

   private:
    /**
     * Initializes the IP event handler that is common to both Ethernet and WiFi events. Automatically called by
     * WiFiInit() and EthernetInit().
     * @retval True if successfully initialized, false otherwise.
     */
    bool IPInit();

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

    CommsManagerConfig config_;

    bool ethernet_was_initialized_ = false;
    bool wifi_was_initialized_ = false;
    bool ip_event_handler_was_initialized_ = false;

    // Ethernet private variables.
    esp_netif_t* ethernet_netif_ = nullptr;
    bool ethernet_connected_ = false;
    bool ethernet_has_ip_ = false;
    uint32_t ethernet_link_up_timestamp_ms_ = 0;  // This will loop every 49.7 days or so.

    // WiFi AP private variables.
    esp_netif_t* wifi_ap_netif_ = nullptr;
    NetworkClient wifi_clients_list_[SettingsManager::Settings::kWiFiMaxNumClients] = {0, 0, 0};
    uint16_t num_wifi_clients_ = 0;
    SemaphoreHandle_t wifi_clients_list_mutex_;
    QueueHandle_t wifi_ap_message_queue_;

    // WiFi STA private variables.
    esp_netif_t* wifi_sta_netif_ = nullptr;
    QueueHandle_t ip_wan_decoded_transponder_packet_queue_;
    TaskHandle_t wifi_ap_task_handle = nullptr;
    TaskHandle_t ip_wan_task_handle = nullptr;
    bool wifi_sta_connected_ = false;
    bool wifi_sta_has_ip_ = false;
    uint32_t wifi_sta_connected_timestamp_ms_ = 0;  // This will loop every 49.7 days or so.

    uint16_t feed_mps_counter_[SettingsManager::Settings::kMaxNumFeeds] = {0};
    uint32_t feed_mps_last_update_timestamp_ms_ = 0;
};

extern CommsManager comms_manager;

#endif /* COMMS_HH_ */