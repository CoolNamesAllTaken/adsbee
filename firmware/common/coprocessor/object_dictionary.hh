#ifndef OBJECT_DICTIONARY_HH_
#define OBJECT_DICTIONARY_HH_

#include "data_structures.hh"
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
    static constexpr uint16_t kLogMessageMaxNumChars = 500;
    static constexpr uint16_t kLogMessageQueueDepth = 10;

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
        kAddrDeviceStatus = 0xC,  // Struct containing number of pending log messages and current timestamp.
        kAddrLogMessages = 0xD,   // Used to retrieve log messages from ESP32 and CC1312.
        kNumAddrs
    };

    struct DeviceStatus {
        uint32_t timestamp_ms = 0;
        uint16_t num_pending_log_messages = 0;
        uint32_t pending_log_messages_packed_size_bytes = 0;
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
        static const uint16_t kHeaderSize = sizeof(SettingsManager::LogLevel) + sizeof(uint16_t);
        SettingsManager::LogLevel log_level;
        uint16_t num_chars;
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

    /**
     * Builds a buffer of log messages with empty space removed.
     * @param[out] buf Buffer to write the log messages to.
     * @param[in] buf_len Length of the buffer.
     * @param[in] log_message_queue Queue of log messages to pack.
     * @param[in] num_messages Number of log messages in the array.
     * @retval Number of bytes written to the buffer.
     */
    uint16_t PackLogMessages(uint8_t* buf, uint16_t buf_len, PFBQueue<ObjectDictionary::LogMessage>& log_message_queue,
                             uint16_t num_messages);

    /**
     * Unpacks a buffer of log messages into an array.
     * @param[in] buf Buffer to read the log messages from.
     * @param[in] buf_len Length of the buffer.
     * @param[out] log_message_queue Queue to store the unpacked log messages.
     * @param[in] max_num_messages Maximum number of log messages to unpack.
     * @retval Number of log messages unpacked.
     */
    uint16_t UnpackLogMessages(uint8_t* buf, uint16_t buf_len,
                               PFBQueue<ObjectDictionary::LogMessage>& log_message_queue, uint16_t max_num_messages);

    PFBQueue<LogMessage> log_message_queue = PFBQueue<LogMessage>({
        .buf_len_num_elements = kLogMessageQueueDepth,
        .buffer = log_message_queue_buffer_,
        .overwrite_when_full = true  // Some of you may die, but that is a sacrifice I am willing to make.
    });

   private:
    uint32_t scratch_ = 0x0;  // Scratch register used for testing.

    // On Pico, this is a queue of log messages gathered from other devices. On other devices, this is a queue of log
    // messages waiting to be slurped up by the RP2040.
    LogMessage log_message_queue_buffer_[kLogMessageQueueDepth] = {};
};

extern ObjectDictionary object_dictionary;

#endif /* OBJECT_DICTIONARY_HH_ */
