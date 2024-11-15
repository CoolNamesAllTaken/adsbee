#include "settings.hh"

#include "ads_bee.hh"
#include "comms.hh"
#include "eeprom.hh"
#include "spi_coprocessor.hh"

const uint16_t kDeviceInfoMaxSizeBytes = sizeof(SettingsManager::DeviceInfo);
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

// NOTE: This function needs to be updated separately for ESP32.
void SettingsManager::Print() {
    CONSOLE_PRINTF("Settings Struct\r\n");
    CONSOLE_PRINTF("\tReceiver: %s\r\n", settings.receiver_enabled ? "ENABLED" : "DISABLED");
    CONSOLE_PRINTF("\tTrigger Level: %d milliVolts (%d dBm)\r\n", settings.tl_mv,
                   adsbee.AD8313MilliVoltsTodBm(settings.tl_mv));
    CONSOLE_PRINTF("\tBias Tee: %s\r\n", settings.bias_tee_enabled ? "ENABLED" : "DISABLED");
    CONSOLE_PRINTF("\tWatchdog Timeout %lu seconds\r\n", settings.watchdog_timeout_sec);
    CONSOLE_PRINTF("\tLog Level: %s\r\n", kConsoleLogLevelStrs[settings.log_level]);
    CONSOLE_PRINTF("\tReporting Protocols:\r\n");
    for (uint16_t i = 0; i < SerialInterface::kGNSSUART; i++) {
        // Only report protocols for CONSOLE and COMMS_UART.
        CONSOLE_PRINTF("\t\t%s: %s\r\n", kSerialInterfaceStrs[i],
                       kReportingProtocolStrs[settings.reporting_protocols[i]]);
    }
    CONSOLE_PRINTF("\tComms UART Baud Rate: %lu baud\r\n", settings.comms_uart_baud_rate);
    CONSOLE_PRINTF("\tGNSS UART Baud Rate: %lu baud\r\n", settings.gnss_uart_baud_rate);
    CONSOLE_PRINTF("\tESP32: %s\r\n", settings.esp32_enabled ? "ENABLED" : "DISABLED");

    // Print WiFi settings.
    CONSOLE_PRINTF("\tWiFi AP: %s\r\n", settings.wifi_ap_enabled ? "ENABLED" : "DISABLED");
    if (settings.wifi_ap_enabled) {
        // Access Point settings. Don't censor password.
        CONSOLE_PRINTF("\t\tChannel: %d\r\n", settings.wifi_ap_channel);
        CONSOLE_PRINTF("\t\tSSID: %s\r\n", settings.wifi_ap_ssid);
        CONSOLE_PRINTF("\t\tPassword: %s\r\n", settings.wifi_ap_password);
    }
    CONSOLE_PRINTF("\tWiFi STA: %s\r\n", settings.wifi_sta_enabled ? "ENABLED" : "DISABLED");
    if (settings.wifi_sta_enabled) {
        // Station settings. Censor password.
        CONSOLE_PRINTF("\t\tSSID: %s\r\n", settings.wifi_sta_ssid);
        char redacted_wifi_sta_password[Settings::kWiFiPasswordMaxLen];
        RedactPassword(settings.wifi_sta_password, redacted_wifi_sta_password, strlen(settings.wifi_sta_password));
        CONSOLE_PRINTF("\t\tPassword: %s\r\n", redacted_wifi_sta_password);
    }

    CONSOLE_PRINTF("\tFeed URIs:\r\n");
    for (uint16_t i = 0; i < Settings::kMaxNumFeeds; i++) {
        CONSOLE_PRINTF("\t\t%d URI:%s Port:%d %s Protocol:%s ID:0x", i, settings.feed_uris[i], settings.feed_ports[i],
                       settings.feed_is_active[i] ? "ACTIVE" : "INACTIVE",
                       kReportingProtocolStrs[settings.feed_protocols[i]]);
        for (int16_t feeder_id_byte_index = 0; feeder_id_byte_index < Settings::kFeedReceiverIDNumBytes;
             feeder_id_byte_index++) {
            CONSOLE_PRINTF("%02x", settings.feed_receiver_ids[i][feeder_id_byte_index]);
        }
        CONSOLE_PRINTF("\r\n");
    }
}

bool SettingsManager::Save() {
    settings.receiver_enabled = adsbee.ReceiverIsEnabled();
    settings.tl_mv = adsbee.GetTLMilliVolts();
    settings.bias_tee_enabled = adsbee.BiasTeeIsEnabled();
    settings.watchdog_timeout_sec = adsbee.GetWatchdogTimeoutSec();

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
    settings.wifi_ap_enabled = comms_manager.wifi_ap_enabled;
    settings.wifi_ap_channel = comms_manager.wifi_ap_channel;
    strncpy(settings.wifi_ap_ssid, comms_manager.wifi_ap_ssid, Settings::kWiFiSSIDMaxLen);
    settings.wifi_ap_ssid[Settings::kWiFiSSIDMaxLen] = '\0';
    strncpy(settings.wifi_ap_password, comms_manager.wifi_ap_password, Settings::kWiFiPasswordMaxLen);
    settings.wifi_ap_password[Settings::kWiFiPasswordMaxLen] = '\0';

    settings.wifi_sta_enabled = comms_manager.wifi_sta_enabled;
    strncpy(settings.wifi_sta_ssid, comms_manager.wifi_sta_ssid, Settings::kWiFiSSIDMaxLen);
    settings.wifi_sta_ssid[Settings::kWiFiSSIDMaxLen] = '\0';
    strncpy(settings.wifi_sta_password, comms_manager.wifi_sta_password, Settings::kWiFiPasswordMaxLen);
    settings.wifi_sta_password[Settings::kWiFiPasswordMaxLen] = '\0';

    // Sync settings from RP2040 -> ESP32.
    if (esp32.IsEnabled()) {
        esp32.Write(ObjectDictionary::kAddrSettingsData, settings, true);  // Require ACK.
    }

    return eeprom.Save(settings);
}

void SettingsManager::ResetToDefaults() {
    Settings default_settings;
    settings = default_settings;
    Apply();
}

bool SettingsManager::SetDeviceInfo(const DeviceInfo &device_info) {
    if (eeprom.RequiresInit()) return false;
    return eeprom.Save(device_info, kDeviceInfoEEPROMAddress);
}

bool SettingsManager::GetDeviceInfo(DeviceInfo &device_info) {
    if (eeprom.RequiresInit()) return false;
    return eeprom.Load(device_info, kDeviceInfoEEPROMAddress);
}

bool SettingsManager::Apply() {
    adsbee.SetReceiverEnable(settings.receiver_enabled);
    adsbee.SetTLMilliVolts(settings.tl_mv);
    adsbee.SetBiasTeeEnable(settings.bias_tee_enabled);
    // adsbee.SetWatchdogTimeoutSec(settings.watchdog_timeout_sec);

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
    // Access Point settings
    comms_manager.wifi_ap_enabled = settings.wifi_ap_enabled;
    comms_manager.wifi_ap_channel = settings.wifi_ap_channel;
    strncpy(comms_manager.wifi_ap_ssid, settings.wifi_ap_ssid, Settings::kWiFiSSIDMaxLen);
    comms_manager.wifi_ap_ssid[Settings::kWiFiSSIDMaxLen] = '\0';
    strncpy(comms_manager.wifi_ap_password, settings.wifi_ap_password, Settings::kWiFiPasswordMaxLen);
    comms_manager.wifi_ap_password[Settings::kWiFiPasswordMaxLen] = '\0';
    // Station settings
    comms_manager.wifi_sta_enabled = settings.wifi_sta_enabled;
    strncpy(comms_manager.wifi_sta_ssid, settings.wifi_sta_ssid, Settings::kWiFiSSIDMaxLen);
    comms_manager.wifi_sta_ssid[Settings::kWiFiSSIDMaxLen] = '\0';
    strncpy(comms_manager.wifi_sta_password, settings.wifi_sta_password, Settings::kWiFiPasswordMaxLen);
    comms_manager.wifi_sta_password[Settings::kWiFiPasswordMaxLen] = '\0';

    return true;  // Not currently doing any error checking here, relying on AT commands to limit parameters to
                  // allowable ranges. Could be a problem if loading from corrupted EEPROM.
}