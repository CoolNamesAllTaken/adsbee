#ifndef SETTINGS_HH_
#define SETTINGS_HH_

#include <cstdint>
#include <cstring> // for memset

static const uint32_t kSettingsVersionMagicWord = 0xBEEFBEEF; // Change this when settings format changes!

class SettingsManager
{
public:
    static const int kDefaultTLHiMV = 250; // [mV]
    static const int kDefaultTLLoMV = 200; // [mV]
    static const int kDefaultRxGain = 2;   // [unitless]

    // NOTE: Length does not include null terminator.
    static const uint16_t kWiFiSSIDMaxLen = 32;
    static const uint16_t kWiFiPasswordMaxLen = 63; // Theoretical max is 63, but limited by CppAT arg max len.

    static const uint32_t kDefaultCommsUARTBaudrate = 115200;
    static const uint32_t kDefaultGNSSUARTBaudrate = 9600;

    // Serial Interface enum and string conversion array.
    enum SerialInterface : uint16_t
    {
        kConsole = 0,
        kCommsUART,
        kGNSSUART,
        kNumSerialInterfaces
    };
    static const uint16_t kSerialInterfaceStrMaxLen = 30;
    static const char SerialInterfaceStrs[SerialInterface::kNumSerialInterfaces][kSerialInterfaceStrMaxLen];

    enum LogLevel : uint16_t
    {
        kSilent = 0,
        kErrors,
        kWarnings,
        kInfo,
        kNumLogLevels
    };
    static const uint16_t kConsoleLogLevelStrMaxLen = 30;
    static const char ConsoleLogLevelStrs[LogLevel::kNumLogLevels][kConsoleLogLevelStrMaxLen];

    // Reporting Protocol enum and string conversion array.
    enum ReportingProtocol : uint16_t
    {
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

    struct Settings
    {
        uint32_t magic_word = kSettingsVersionMagicWord;

        // ADSBee settings
        int tl_lo_mv = kDefaultTLLoMV;
        int tl_hi_mv = kDefaultTLHiMV;
        uint16_t rx_gain = kDefaultRxGain;

        // CommunicationsManager settings
        LogLevel log_level = LogLevel::kInfo; // Start with highest verbosity by default.
        ReportingProtocol reporting_protocols[SerialInterface::kNumSerialInterfaces - 1] = {
            ReportingProtocol::kNoReports, ReportingProtocol::kMAVLINK1};
        uint32_t comms_uart_baud_rate = 115200;
        uint32_t gnss_uart_baud_rate = 9600;

        bool wifi_enabled = false;
        char wifi_ssid[kWiFiSSIDMaxLen + 1] = "";
        char wifi_password[kWiFiPasswordMaxLen + 1] = "";

        // ESP32 settings
        char feed_uris[kMaxNumFeeds][SettingsManager::kFeedURIMaxNumChars + 1];
        uint16_t feed_ports[kMaxNumFeeds];
        bool feed_is_active[kMaxNumFeeds];
        ReportingProtocol feed_protocols[kMaxNumFeeds];
        uint8_t feed_receiver_ids[kMaxNumFeeds][kFeedReceiverIDNumBytes];

        /**
         * Default constructor.
         */
        Settings()
        {
            for (uint16_t i = 0; i < kMaxNumFeeds; i++)
            {
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