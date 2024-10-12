#ifndef SETTINGS_HH_
#define SETTINGS_HH_

#include <cstdint>
#include <cstring>     // for memset
#include <functional>  // for strtoull

#include "macros.hh"
#include "stdio.h"

static const uint32_t kSettingsVersion = 0x3;  // Change this when settings format changes!
static const uint32_t kDeviceInfoVersion = 0x1;

class SettingsManager {
   public:
    // Serial Interface enum and string conversion array.
    enum SerialInterface : uint16_t { kConsole = 0, kCommsUART, kGNSSUART, kNumSerialInterfaces };
    static const uint16_t kSerialInterfaceStrMaxLen = 30;
    static const char kSerialInterfaceStrs[SerialInterface::kNumSerialInterfaces][kSerialInterfaceStrMaxLen];

    enum LogLevel : uint16_t { kSilent = 0, kErrors, kWarnings, kInfo, kNumLogLevels };
    static const uint16_t kConsoleLogLevelStrMaxLen = 30;
    static const char kConsoleLogLevelStrs[LogLevel::kNumLogLevels][kConsoleLogLevelStrMaxLen];

    // Reporting Protocol enum and string conversion array.
    enum ReportingProtocol : uint16_t {
        kNoReports = 0,
        kRaw,
        kBeast,
        kCSBee,
        kMAVLINK1,
        kMAVLINK2,
        kGDL90,
        kNumProtocols
    };
    static const uint16_t kReportingProtocolStrMaxLen = 30;
    static const char kReportingProtocolStrs[ReportingProtocol::kNumProtocols][kReportingProtocolStrMaxLen];

    enum WiFiMode : uint8_t {
        kWiFiModeOff = 0,
        kWiFiModeStation = 1,
        kWiFiModeAccessPoint = 2,
        kWiFiModeAccessPointAndStation = 3,
        kNumWiFiModes
    };
    static const uint8_t kWiFiModeStrMaxLen = 30;
    static const char kWiFiModeStrs[WiFiMode::kNumWiFiModes][kWiFiModeStrMaxLen];

    // This struct contains nonvolatile settings that should persist across reboots but may be overwritten during a
    // firmware upgrade if the format of the settings struct changes.
    struct Settings {
        static const int kDefaultTLMV = 1500;  // [mV]
        // NOTE: Length does not include null terminator.
        static const uint16_t kWiFiSSIDMaxLen = 32;
        static const uint16_t kWiFiPasswordMaxLen = 63;  // Theoretical max is 63, but limited by CppAT arg max len.
        static const uint16_t kWiFiMaxNumClients = 6;
        static const uint32_t kDefaultCommsUARTBaudrate = 115200;
        static const uint32_t kDefaultGNSSUARTBaudrate = 9600;
        static const uint16_t kMaxNumFeeds = 6;
        static const uint16_t kFeedURIMaxNumChars = 63;
        static const uint16_t kFeedReceiverIDNumBytes = 8;

        uint32_t settings_version = kSettingsVersion;

        // ADSBee settings
        bool receiver_enabled = true;
        int tl_mv = kDefaultTLMV;
        bool bias_tee_enabled = false;

        // CommunicationsManager settings
        LogLevel log_level = LogLevel::kInfo;  // Start with highest verbosity by default.
        ReportingProtocol reporting_protocols[SerialInterface::kNumSerialInterfaces - 1] = {
            ReportingProtocol::kNoReports, ReportingProtocol::kMAVLINK1};
        uint32_t comms_uart_baud_rate = 115200;
        uint32_t gnss_uart_baud_rate = 9600;

        // ESP32 settings
        bool esp32_enabled = true;

        WiFiMode wifi_mode = kWiFiModeAccessPoint;
        char ap_wifi_ssid[kWiFiSSIDMaxLen + 1] = "";
        char ap_wifi_password[kWiFiPasswordMaxLen + 1] = "";

        char sta_wifi_ssid[kWiFiSSIDMaxLen + 1] = "";
        char sta_wifi_password[kWiFiPasswordMaxLen + 1] = "";

        char feed_uris[kMaxNumFeeds][kFeedURIMaxNumChars + 1];
        uint16_t feed_ports[kMaxNumFeeds];
        bool feed_is_active[kMaxNumFeeds];
        ReportingProtocol feed_protocols[kMaxNumFeeds];
        uint8_t feed_receiver_ids[kMaxNumFeeds][kFeedReceiverIDNumBytes];

        /**
         * Default constructor.
         */
        Settings() {
#ifdef ON_PICO
            DeviceInfo device_info;
            if (GetDeviceInfo(device_info)) {
                // If able to load device info from EEPROM, use the last 16 characters in the part code as part of the
                // WiFi SSID.
                device_info.GetDefaultSSID(ap_wifi_ssid);
                snprintf(ap_wifi_password, kWiFiPasswordMaxLen, "yummyflowers");
            }
#endif

            for (uint16_t i = 0; i < kMaxNumFeeds; i++) {
                memset(feed_uris[i], '\0', kFeedURIMaxNumChars + 1);
                feed_ports[i] = 0;
                feed_is_active[i] = false;
                feed_protocols[i] = kNoReports;
#ifdef ON_PICO
                device_info.GetDefaultFeedReceiverID(feed_receiver_ids[i]);
#else
                memset(feed_receiver_ids[i], 0, kFeedReceiverIDNumBytes);
#endif
            }
        }
    };

    // This struct contains device information that should persist across firmware upgrades.
    struct DeviceInfo {
        static const uint16_t kPartCodeLen = 26;  // NNNNNNNNNR-YYYYMMDD-VVXXXX (not counting end of string char).

        uint32_t device_info_version = kDeviceInfoVersion;
        char part_code[kPartCodeLen + 1];

        /**
         * Default constructor.
         */
        DeviceInfo() { memset(part_code, '\0', kPartCodeLen + 1); }

        static const uint16_t kDefaultSSIDLenChars = 24;  // ADSBee1090-YYYMMDDVVXXXX
        /**
         * Writes a default value for a network SSID to a buffer. The buffer must be at least kDefaultSSIDLenChars+1 so
         * that there is space for an end of string character. This default network SSID value is intended to not
         * conflict with any other ADSBee devices or future Pants for Birds products.
         * @param[out] buf Buffer to write the network SSID to.
         */
        void GetDefaultSSID(char *buf) {
            memcpy(buf, "ADSBee1090-", 11);       // [0:10] ADSBee1090-
            memcpy(buf + 11, part_code + 12, 7);  // [11:17] YYYMMDD
            memcpy(buf + 18, part_code + 20, 6);  // [18:23] VVXXXX
            buf[kDefaultSSIDLenChars] = '\0';
        }

        /**
         * Writes a default 8 Byte Unique ID to a buffer. The buffer must be at least 8 Bytes long. UID is in binary
         * (not human readable), and is of the form 0xBE 0xE0 NN NN NN NN, where the NN's represent bytes in a unique
         * value formed from the Base-10 integer YYYMMDDVVXXXX extracted from the ADSBee 1090's manufacturing code, sent
         * MSB first. The Unique ID is intended not to conflict between any two ADSBee 1090 devices. New devices in the
         * ADSBee lineup may be prefixed with 0xBE EN, where N is a value greater than 0.
         * @param[out] buf Buffer to write the 8 Byte unique ID to.
         */
        void GetDefaultFeedReceiverID(uint8_t *buf) {
            // 0xBE 0xE0 <6 Byte Binary UID, MSB first.>
            buf[0] = 0xBE;
            buf[1] = 0xE0;
            // Base the rest of the UID off of a 13-digit Base 10 number.
            char uid_digits[14];                        // YYYMMDDVVXXXX
            memcpy(uid_digits, part_code + 12, 7);      // YYYMMDD
            memcpy(uid_digits + 7, part_code + 20, 6);  // VVXXXX
            uid_digits[13] = '\0';
            // log2(10^13) = 43.18, so we need 44 (6 Bytes) bits to store the UID.
            uint64_t uid_value = strtoull(uid_digits, nullptr, 10);
            for (uint16_t i = 0; i < 6; i++) {
                buf[2 + i] = (uid_value >> (8 * (5 - i))) & 0xFF;
            }
        }
    };

    /**
     * Loads settings from EEPROM. Assumes settings are stored at address 0x0 and doesn't do any integrity check.
     * @retval True if succeeded, false otherwise.
     */
    bool Load();

    void Print() {
        printf("Settings Struct\r\n");
        printf("\tReceiver: %s\r\n", settings.receiver_enabled ? "ENABLED" : "DISABLED");
        printf("\tTrigger Level [milliVolts]: %d\r\n", settings.tl_mv);
        printf("\tBias Tee: %s\r\n", settings.bias_tee_enabled ? "ENABLED" : "DISABLED");
        printf("\tLog Level: %s\r\n", kConsoleLogLevelStrs[settings.log_level]);
        printf("\tReporting Protocols:\r\n");
        for (uint16_t i = 0; i < SerialInterface::kGNSSUART; i++) {
            // Only report protocols for CONSOLE and COMMS_UART.
            printf("\t\t%s: %s\r\n", kSerialInterfaceStrs[i], kReportingProtocolStrs[settings.reporting_protocols[i]]);
        }
        printf("\tComms UART Baud Rate: %lu baud\r\n", settings.comms_uart_baud_rate);
        printf("\tGNSS UART Baud Rate: %lu baud\r\n", settings.gnss_uart_baud_rate);
        printf("\tESP32: %s\r\n", settings.esp32_enabled ? "ENABLED" : "DISABLED");

        // Print WiFi settings.
        printf("\tWifi Mode: %s\r\n", SettingsManager::kWiFiModeStrs[settings.wifi_mode]);
        if (settings.wifi_mode == kWiFiModeAccessPoint || settings.wifi_mode == kWiFiModeAccessPointAndStation) {
            // Access Point settings. Don't censor password.
            printf("\tAP Wifi SSID: %s\r\n", settings.ap_wifi_ssid);
            printf("\tAP Wifi Password: %s\r\n", settings.ap_wifi_password);
        }
        if (settings.wifi_mode == kWiFiModeStation || settings.wifi_mode == kWiFiModeAccessPointAndStation) {
            // Station settings. Censor password.
            printf("\tSTA Wifi SSID: %s\r\n", settings.sta_wifi_ssid);
            char redacted_sta_wifi_password[Settings::kWiFiPasswordMaxLen];
            RedactPassword(settings.sta_wifi_password, redacted_sta_wifi_password, strlen(settings.sta_wifi_password));
            printf("\tSTA Wifi Password: %s\r\n", redacted_sta_wifi_password);
        }

        printf("\tFeed URIs:\r\n");
        for (uint16_t i = 0; i < Settings::kMaxNumFeeds; i++) {
            printf("\t\t%d URI:%s Port:%d %s Protocol:%s ID:0x", i, settings.feed_uris[i], settings.feed_ports[i],
                   settings.feed_is_active[i] ? "ACTIVE" : "INACTIVE",
                   kReportingProtocolStrs[settings.feed_protocols[i]]);
            for (int16_t feeder_id_byte_index = 0; feeder_id_byte_index < Settings::kFeedReceiverIDNumBytes;
                 feeder_id_byte_index++) {
                printf("%02x", settings.feed_receiver_ids[i][feeder_id_byte_index]);
            }
            printf("\r\n");
        }
    }

    /**
     * Takes a password as a string and fills a buffer with the corresponding number of asterix.
     * @param[in] password_buf Buffer to read the password from. Must be at least password_len+1 chars.
     * @param[out] redacted_password_buf Buffer to write the asterix to. Must be at least password_len+1 chars.
     * @param[in] buf_len Maximum allowable number of characteers in the password. Used to guard against falling off the
     * end of the string. Not used for actually finding ther number of asterix to print.
     */
    static void RedactPassword(char *password_buf, char *redacted_password_buf, uint16_t buf_len) {
        uint16_t password_len = MIN(strlen(password_buf), buf_len);
        memset(redacted_password_buf, '*', password_len);
        redacted_password_buf[password_len] = '\0';
    }

    /**
     * Applies internal settings to the relevant objects. This is only used after the settings struct has been updated
     * by loading it from EEPROM or by overwriting it via the coprocessor SPI bus.
     */
    void Apply();

    /**
     * Saves settings to EEPROM. Stores settings at address 0x0 and performs no integrity check.
     * @retval True if succeeded, false otherwise.
     */
    bool Save();

    /**
     * Restores settings to factory default values.
     */
    void ResetToDefaults();

#ifdef ON_PICO
    /**
     * Used to write device information to EEPROM during manufacturing. Only available on the Pico since it's the one
     * with direct access to EEPROm over I2C.
     * @param[in] device_info Reference to a DeviceInfo struct with the information to set in EEPROM.
     * @retval True if device info was set successfully, false otherwise.
     */
    static bool SetDeviceInfo(const DeviceInfo &device_info);
#endif
    /**
     * Used to retrieve device information, either directly from EEPROM or via interprocessor SPI bus.
     * @param[in] device_info DeviceInfo struct to set.
     * @retval True if device info was retrieved successfully, false otherwise.
     */
    static bool GetDeviceInfo(DeviceInfo &device_info);

    Settings settings;

   private:
};

extern SettingsManager settings_manager;

#endif /* SETTINGS_HH_ */