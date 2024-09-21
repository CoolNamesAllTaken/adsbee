#ifndef SETTINGS_HH_
#define SETTINGS_HH_

#include <cstdint>
#include <cstring>  // for memset

#include "macros.hh"
#include "stdio.h"

static const uint32_t kSettingsVersionMagicWord = 0x1;  // Change this when settings format changes!

class SettingsManager {
   public:
    static const int kDefaultTLMV = 1500;  // [mV]

    // NOTE: Length does not include null terminator.
    static const uint16_t kWiFiSSIDMaxLen = 32;
    static const uint16_t kWiFiPasswordMaxLen = 63;  // Theoretical max is 63, but limited by CppAT arg max len.

    static const uint32_t kDefaultCommsUARTBaudrate = 115200;
    static const uint32_t kDefaultGNSSUARTBaudrate = 9600;

    // Serial Interface enum and string conversion array.
    enum SerialInterface : uint16_t { kConsole = 0, kCommsUART, kGNSSUART, kNumSerialInterfaces };
    static const uint16_t kSerialInterfaceStrMaxLen = 30;
    static const char SerialInterfaceStrs[SerialInterface::kNumSerialInterfaces][kSerialInterfaceStrMaxLen];

    enum LogLevel : uint16_t { kSilent = 0, kErrors, kWarnings, kInfo, kNumLogLevels };
    static const uint16_t kConsoleLogLevelStrMaxLen = 30;
    static const char ConsoleLogLevelStrs[LogLevel::kNumLogLevels][kConsoleLogLevelStrMaxLen];

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
    static const char ReportingProtocolStrs[ReportingProtocol::kNumProtocols][kReportingProtocolStrMaxLen];

    /** ESP32 Settings **/
    static const uint16_t kMaxNumFeeds = 6;
    static const uint16_t kFeedURIMaxNumChars = 63;
    static const uint16_t kFeedReceiverIDNumBytes = 16;

    struct Settings {
        uint32_t magic_word = kSettingsVersionMagicWord;

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

        bool wifi_enabled = true;
        char wifi_ssid[kWiFiSSIDMaxLen + 1] = "";
        char wifi_password[kWiFiPasswordMaxLen + 1] = "";

        char feed_uris[kMaxNumFeeds][SettingsManager::kFeedURIMaxNumChars + 1];
        uint16_t feed_ports[kMaxNumFeeds];
        bool feed_is_active[kMaxNumFeeds];
        ReportingProtocol feed_protocols[kMaxNumFeeds];
        uint8_t feed_receiver_ids[kMaxNumFeeds][kFeedReceiverIDNumBytes];

        /**
         * Default constructor.
         */
        Settings() {
            for (uint16_t i = 0; i < kMaxNumFeeds; i++) {
                memset(feed_uris[i], '\0', kFeedURIMaxNumChars + 1);
                feed_ports[i] = 0;
                feed_is_active[i] = false;
                feed_protocols[i] = kNoReports;
                memset(feed_receiver_ids[i], 0, kFeedReceiverIDNumBytes);
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
        printf("\tLog Level: %s\r\n", ConsoleLogLevelStrs[settings.log_level]);
        printf("\tReporting Protocols:\r\n");
        for (uint16_t i = 0; i < SerialInterface::kGNSSUART; i++) {
            // Only report protocols for CONSOLE and COMMS_UART.
            printf("\t\t%s: %s\r\n", SerialInterfaceStrs[i], ReportingProtocolStrs[settings.reporting_protocols[i]]);
        }
        printf("\tComms UART Baud Rate: %lu baud\r\n", settings.comms_uart_baud_rate);
        printf("\tGNSS UART Baud Rate: %lu baud\r\n", settings.gnss_uart_baud_rate);
        printf("\tESP32: %s", settings.esp32_enabled ? "ENABLED" : "DISABLED");
        printf("\tWifi: %s", settings.wifi_enabled ? "ENABLED" : "DISABLED");
        printf("\tWifi SSID: %s\r\n", settings.wifi_ssid);
        char redacted_wifi_password[kWiFiPasswordMaxLen];
        RedactPassword(settings.wifi_password, redacted_wifi_password, strlen(settings.wifi_password));
        printf("\tWifi Password: %s\r\n", redacted_wifi_password);
        printf("\tFeed URIs:\r\n");
        for (uint16_t i = 0; i < kMaxNumFeeds; i++) {
            printf("\t\t%d URI:%s Port:%d %s Protocol:%s ID:", i, settings.feed_uris[i], settings.feed_ports[i],
                   settings.feed_is_active[i] ? "ACTIVE" : "INACTIVE",
                   ReportingProtocolStrs[settings.feed_protocols[i]]);
            for (int16_t feeder_id_byte_index = kFeedReceiverIDNumBytes - 1; feeder_id_byte_index >= 0;
                 feeder_id_byte_index--) {
                printf("%d", settings.feed_receiver_ids[i][feeder_id_byte_index]);
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
     * Saves settings to EEPROM. Stores settings at address 0x0 and performs no integrity check.
     * @retval True if succeeded, false otherwise.
     */
    bool Save();

    /**
     * Restores settings to factory default values.
     */
    void ResetToDefaults();

    Settings settings;

   private:
    /**
     * Applies internal settings to the relevant objects.
     */
    void Apply();
};

extern SettingsManager settings_manager;

#endif /* SETTINGS_HH_ */