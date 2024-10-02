#include "settings.hh"

#include "ads_bee.hh"
#include "eeprom.hh"
#include "spi_coprocessor.hh"

const uint16_t kDeviceInfoMaxSizeBytes = 200;
const uint16_t kDeviceInfoEEPROMAddress = 8e3 - kDeviceInfoMaxSizeBytes;

bool SettingsManager::Load() {
    if (!eeprom.Load(settings)) {
        CONSOLE_ERROR("settings.cc::Load", "Failed load settings from EEPROM.");
        return false;
    };

    // Reset to defaults if loading from a blank EEPROM.
    if (settings.settings_version != kSettingsVersion) {
        ResetToDefaults();
        if (!eeprom.Save(settings)) {
            CONSOLE_ERROR("settings.cc::Load", "Failed to save default settings.");
            return false;
        }
    }

    Apply();

    return true;
}

bool SettingsManager::Save() {
    settings.receiver_enabled = adsbee.ReceiverIsEnabled();
    settings.tl_mv = adsbee.GetTLMilliVolts();
    settings.bias_tee_enabled = adsbee.BiasTeeIsEnabled();

    // Save log level.
    settings.log_level = comms_manager.log_level;

    // Save reporting protocols.
    comms_manager.GetReportingProtocol(SerialInterface::kCommsUART,
                                       settings.reporting_protocols[SerialInterface::kCommsUART]);
    comms_manager.GetReportingProtocol(SerialInterface::kConsole,
                                       settings.reporting_protocols[SerialInterface::kConsole]);

    // Save baud rates.
    comms_manager.GetBaudrate(SerialInterface::kCommsUART, settings.comms_uart_baud_rate);
    comms_manager.GetBaudrate(SerialInterface::kGNSSUART, settings.gnss_uart_baud_rate);

    settings.esp32_enabled = esp32.IsEnabled();
    // Save WiFi configuration.
    settings.wifi_mode = comms_manager.wifi_mode;
    strncpy(settings.wifi_ssid, comms_manager.wifi_ssid, Settings::kWiFiSSIDMaxLen);
    settings.wifi_ssid[Settings::kWiFiSSIDMaxLen] = '\0';
    strncpy(settings.wifi_password, comms_manager.wifi_password, Settings::kWiFiPasswordMaxLen);
    settings.wifi_password[Settings::kWiFiPasswordMaxLen] = '\0';

    // Sync settings from RP2040 -> ESP32.
    if (esp32.IsEnabled()) {
        esp32.Write(ObjectDictionary::kAddrSettingsData, settings);
    }

    return eeprom.Save(settings);
}

void SettingsManager::ResetToDefaults() {
    Settings default_settings;
    settings = default_settings;
    Apply();
}

bool SettingsManager::SetDeviceInfo(const DeviceInfo &device_info) {
    return eeprom.Save(device_info, kDeviceInfoEEPROMAddress);
}

bool SettingsManager::GetDeviceInfo(DeviceInfo &device_info) {
    return eeprom.Load(device_info, kDeviceInfoEEPROMAddress);
}

void SettingsManager::Apply() {
    adsbee.SetReceiverEnable(settings.receiver_enabled);
    adsbee.SetTLMilliVolts(settings.tl_mv);
    adsbee.SetBiasTeeEnable(settings.bias_tee_enabled);

    // Apply log level.
    comms_manager.log_level = settings.log_level;

    // Apply reporting protocols.
    comms_manager.SetReportingProtocol(SerialInterface::kCommsUART,
                                       settings.reporting_protocols[SerialInterface::kCommsUART]);
    comms_manager.SetReportingProtocol(SerialInterface::kConsole,
                                       settings.reporting_protocols[SerialInterface::kConsole]);

    // Apply baud rates.
    comms_manager.SetBaudrate(SerialInterface::kCommsUART, settings.comms_uart_baud_rate);
    comms_manager.SetBaudrate(SerialInterface::kGNSSUART, settings.gnss_uart_baud_rate);

    settings.esp32_enabled ? esp32.Init() : esp32.DeInit();

    // Apply WiFi configurations.
    comms_manager.wifi_mode = settings.wifi_mode;
    strncpy(comms_manager.wifi_ssid, settings.wifi_ssid, Settings::kWiFiSSIDMaxLen);
    comms_manager.wifi_ssid[Settings::kWiFiSSIDMaxLen] = '\0';
    strncpy(comms_manager.wifi_password, settings.wifi_password, Settings::kWiFiPasswordMaxLen);
    comms_manager.wifi_password[Settings::kWiFiPasswordMaxLen] = '\0';
}