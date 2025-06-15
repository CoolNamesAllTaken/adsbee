#ifndef OBJECT_DICTIONARY_HH_
#define OBJECT_DICTIONARY_HH_

#include "settings.hh"
#include "stdint.h"
#ifdef ON_ESP32
#include "adsbee_server.hh"
#include "esp_mac.h"   // For retrieving Base MAC address.
#include "esp_wifi.h"  // For retrieving WiFi Station MAC address.
#endif

class ObjectDictionary {
   public:
    static const uint8_t kFirmwareVersionMajor;
    static const uint8_t kFirmwareVersionMinor;
    static const uint8_t kFirmwareVersionPatch;
    static const uint8_t kFirmwareVersionReleaseCandidate;
    static const uint32_t kFirmwareVersion;

    static constexpr uint16_t kMACAddrLenBytes = 6;

    static constexpr uint16_t kNetworkConsoleMessageMaxLenBytes = 4000;
    static constexpr uint16_t kLogMessageMaxNumChars = 1000;

    enum Address : uint8_t {
        kAddrInvalid = 0,             // Default value.
        kAddrFirmwareVersion = 0x01,  // Firmware version as a uint32_t.
        kAddrScratch = 0x02,          // Used for testing SPI communications.
        kAddrSettingsData = 0x03,     // Used to transfer settings information.
        kAddrRaw1090Packet = 0x04,    // Used to forward raw packets from RP2040 to ESP32.
        kAddrDecoded1090Packet = 0x05,
        kAddrRaw1090PacketArray = 0x06,
        kAddrDecoded1090PacketArray = 0x07,
        kAddrAircraftDictionaryMetrics = 0x08,  // For forwarding dictionary metrics from RP2040 to ESP32.
        kAddrDeviceInfo = 0x09,                 // ESP32 MAC addresses.
        kAddrConsole = 0xA,                     // Pipe for console characters.
        kAddrNetworkInfo = 0xB,                 // Network information for ESP32.
        kAddrLogMessage = 0xC,                  // Debug message.
        kNumAddrs
    };

    /**
     * Struct used to retrieve device information from the ESP32.
     */
    struct ESP32DeviceInfo {
        uint8_t base_mac[kMACAddrLenBytes];
        uint8_t wifi_station_mac[kMACAddrLenBytes];
        uint8_t wifi_ap_mac[kMACAddrLenBytes];
        uint8_t bluetooth_mac[kMACAddrLenBytes];
        uint8_t ethernet_mac[kMACAddrLenBytes];
    };

    /**
     * Struct used to retrieve network information from the ESP32.
     */
    struct ESP32NetworkInfo {
        bool ethernet_enabled = false;
        bool ethernet_has_ip = false;
        char ethernet_ip[SettingsManager::Settings::kIPAddrStrLen + 1] = {0};
        char ethernet_netmask[SettingsManager::Settings::kIPAddrStrLen + 1] = {0};
        char ethernet_gateway[SettingsManager::Settings::kIPAddrStrLen + 1] = {0};

        bool wifi_sta_enabled = false;
        char wifi_sta_ssid[SettingsManager::Settings::kWiFiSSIDMaxLen + 1] = {0};
        bool wifi_sta_has_ip = false;
        char wifi_sta_ip[SettingsManager::Settings::kIPAddrStrLen + 1] = {0};
        char wifi_sta_netmask[SettingsManager::Settings::kIPAddrStrLen + 1] = {0};
        char wifi_sta_gateway[SettingsManager::Settings::kIPAddrStrLen + 1] = {0};

        bool wifi_ap_enabled = false;
        bool wifi_ap_num_clients = 0;
        char wifi_ap_client_ips[SettingsManager::Settings::kWiFiMaxNumClients]
                               [SettingsManager::Settings::kIPAddrStrLen + 1];
        char wifi_ap_client_macs[SettingsManager::Settings::kWiFiMaxNumClients]
                                [SettingsManager::Settings::kMACAddrStrLen + 1];

        ESP32NetworkInfo() {
            for (uint16_t i = 0; i < SettingsManager::Settings::kWiFiMaxNumClients; i++) {
                memset(wifi_ap_client_ips[i], 0x0, SettingsManager::Settings::kIPAddrStrLen + 1);
                memset(wifi_ap_client_macs[i], 0x0, SettingsManager::Settings::kMACAddrNumBytes);
            }
        }
    };

    /**
     * Struct used to pass debug messages between devices.
     */
    struct LogMessage {
        SettingsManager::LogLevel log_level;
        uint32_t num_chars;
        char message[kLogMessageMaxNumChars + 1] = {'\0'};
    };

    /**
     * Setter for writing data to the address space.
     * @param[in] addr Address to write to.
     * @param[in] buf Buffer to read from.
     * @param[in] buf_len Number of Bytes to write.
     * @param[in] offset Byte offset from beginning of object. Used for partial reads.
     * @retval Returns true if successfully wrote, false if address was invalid or something else borked.
     */
    bool SetBytes(Address addr, uint8_t* buf, uint16_t buf_len, uint16_t offset = 0);

    /**
     * Getter for reading data from the address space.
     * @param[in] addr Address to read from.
     * @param[out] buf Buffer to write to.
     * @param[in] buf_len Number of Bytes to read.
     * @param[in] offset Byte offset from beginning of object. Used for partial reads.
     * @retval Returns true if successfully read, false if address was invalid or something else borked.
     */
    bool GetBytes(Address addr, uint8_t* buf, uint16_t buf_len, uint16_t offset = 0);

    bool LogMessageToCoprocessor(SettingsManager::LogLevel log_level, const char* tag, const char* format, ...);

   private:
    uint32_t scratch_ = 0x0;  // Scratch register used for testing.
};

extern ObjectDictionary object_dictionary;

#endif /* OBJECT_DICTIONARY_HH_ */
