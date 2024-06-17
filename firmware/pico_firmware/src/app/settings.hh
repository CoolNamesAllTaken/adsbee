#ifndef SETTINGS_HH_
#define SETTINGS_HH_

#include "ads_bee.hh"
#include "comms.hh"
#include "eeprom.hh"

class SettingsManager {
   public:
    struct Settings {
        uint32_t magic_word = 0xDEADBEEF;  // Change this when settings format changes!

        // ADSBee settings
        int tl_lo_mv = ADSBee::kTLLoDefaultMV;
        int tl_hi_mv = ADSBee::kTLHiDefaultMV;
        uint16_t rx_gain = ADSBee::kRxGainDefault;

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
    bool Load() {
        if (!eeprom.Load(settings)) {
            CONSOLE_ERROR("settings.h::Load: Failed load settings from EEPROM.");
            return false;
        };

        // Reset to defaults if loading from a blank EEPROM.
        if (settings.magic_word != 0xDEADBEEF) {
            ResetToDefaults();
            if (!eeprom.Save(settings)) {
                CONSOLE_ERROR("settings.h::Load: Failed to save default settings.");
                return false;
            }
        }

        Apply();

        return true;
    }

    /**
     * Saves settings to EEPROM. Stores settings at address 0x0 and performs no integrity check.
     * @retval True if succeeded, false otherwise.
     */
    bool Save() {
        settings.rx_gain = ads_bee.GetRxGain();
        settings.tl_lo_mv = ads_bee.GetTLLoMilliVolts();
        settings.tl_hi_mv = ads_bee.GetTLHiMilliVolts();

        // Save reporting protocols.
        comms_manager.GetReportingProtocol(CommsManager::SerialInterface::kCommsUART,
                                           settings.reporting_protocols[CommsManager::SerialInterface::kCommsUART]);
        comms_manager.GetReportingProtocol(CommsManager::SerialInterface::kConsole,
                                           settings.reporting_protocols[CommsManager::SerialInterface::kConsole]);

        // Save baud rates.
        comms_manager.GetBaudrate(CommsManager::SerialInterface::kCommsUART, settings.comms_uart_baud_rate);
        comms_manager.GetBaudrate(CommsManager::SerialInterface::kGNSSUART, settings.gnss_uart_baud_rate);

        // Save WiFi configuration.
        settings.wifi_enabled = comms_manager.WiFiIsEnabled();
        strncpy(settings.wifi_ssid, comms_manager.wifi_ssid, CommsManager::kWiFiSSIDMaxLen);
        settings.wifi_ssid[CommsManager::kWiFiSSIDMaxLen] = '\0';
        strncpy(settings.wifi_password, comms_manager.wifi_password, CommsManager::kWiFiPasswordMaxLen);
        settings.wifi_password[CommsManager::kWiFiPasswordMaxLen] = '\0';

        return eeprom.Save(settings);
    }

    /**
     * Restores settings to factory default values.
     */
    void ResetToDefaults() {
        Settings default_settings;
        settings = default_settings;
        Apply();
    }

    Settings settings;

   private:
    /**
     * Applies internal settings to the relevant objects.
     */
    void Apply() {
        ads_bee.SetTLLoMilliVolts(settings.tl_lo_mv);
        ads_bee.SetTLHiMilliVolts(settings.tl_hi_mv);
        ads_bee.SetRxGain(settings.rx_gain);

        // Save reporting protocols.
        comms_manager.SetReportingProtocol(CommsManager::SerialInterface::kCommsUART,
                                           settings.reporting_protocols[CommsManager::SerialInterface::kCommsUART]);
        comms_manager.SetReportingProtocol(CommsManager::SerialInterface::kConsole,
                                           settings.reporting_protocols[CommsManager::SerialInterface::kConsole]);

        // Save baud rates.
        comms_manager.SetBaudrate(CommsManager::SerialInterface::kCommsUART, settings.comms_uart_baud_rate);
        comms_manager.SetBaudrate(CommsManager::SerialInterface::kGNSSUART, settings.gnss_uart_baud_rate);

        // Set WiFi configurations.
        comms_manager.SetWiFiEnabled(settings.wifi_enabled);
        strncpy(comms_manager.wifi_ssid, settings.wifi_ssid, CommsManager::kWiFiSSIDMaxLen);
        comms_manager.wifi_ssid[CommsManager::kWiFiSSIDMaxLen] = '\0';
        strncpy(comms_manager.wifi_password, settings.wifi_password, CommsManager::kWiFiPasswordMaxLen);
        comms_manager.wifi_password[CommsManager::kWiFiPasswordMaxLen] = '\0';
    }
};

extern SettingsManager settings_manager;

#endif /* SETTINGS_HH_ */