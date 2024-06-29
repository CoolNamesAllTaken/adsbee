#ifndef SETTINGS_HH_
#define SETTINGS_HH_

#include <cstdint>
#include "comms.hh"

class SettingsManager
{
public:
    static const int kDefaultTLHiMV = 3000; // [mV]
    static const int kDefaultTLLoMV = 2000; // [mV]
    static const int kDefaultRxGain = 50;   // [unitless]

    struct Settings
    {
        uint32_t magic_word = 0xDEADBEEF; // Change this when settings format changes!

        // ADSBee settings
        int tl_lo_mv = kDefaultTLLoMV;
        int tl_hi_mv = kDefaultTLHiMV;
        uint16_t rx_gain = kDefaultRxGain;

        // CommunicationsManager settings
        CommsManager::ReportingProtocol reporting_protocols[CommsManager::SerialInterface::kNumSerialInterfaces - 1] = {
            CommsManager::ReportingProtocol::kNoReports, CommsManager::ReportingProtocol::kMAVLINK1};
        uint32_t comms_uart_baud_rate = 115200;
        uint32_t gnss_uart_baud_rate = 9600;

        bool wifi_enabled = false;
        char wifi_ssid[CommsManager::kWiFiSSIDMaxLen + 1] = "";
        char wifi_password[CommsManager::kWiFiPasswordMaxLen + 1] = "";
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