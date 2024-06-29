#include "settings.hh"

#include "ads_bee.hh"
#include "eeprom.hh"

bool SettingsManager::Load() {
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

bool SettingsManager::Save() {
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

void SettingsManager::ResetToDefaults() {
    Settings default_settings;
    settings = default_settings;
    Apply();
}

void SettingsManager::Apply() {
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