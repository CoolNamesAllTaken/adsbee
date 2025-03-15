#include "settings.hh"

#include "adsbee.hh"
#include "comms.hh"
#include "core1.hh"
#include "eeprom.hh"
#include "firmware_update.hh"
#include "flash_utils.hh"
#include "hardware/flash.h"
#include "spi_coprocessor.hh"

/* Original flash length: 16384k Bytes.
   FLASH MAP
       0x10000000	(176k)	FLASH_BL	Bootloader
       0x1002C000	(4k)	FLASH_HDR0	    Application 0 Header
       0x1002D000	(8096k)	FLASH_APP0	    Application 0 Data
       0x10815000	(4k)	FLASH_HDR1	    Application 1 Header
       0x10816000	(8096k)	FLASH_APP1	    Application 1 Data
       0x10FFE000	(8k)	FLASH_SETTINGS	Settings
*/

const uint16_t kDeviceInfoMaxSizeBytes = sizeof(SettingsManager::DeviceInfo);
const uint32_t kFlashSettingsStartAddr = 0x10FFE000;
const uint16_t kDeviceInfoOffset = 8e3 - kDeviceInfoMaxSizeBytes;

bool SettingsManager::Load() {
    if (bsp.has_eeprom) {
        // Load settings from external EEPROM.
        if (!eeprom.Load(settings)) {
            CONSOLE_ERROR("settings.cc::Load", "Failed load settings from EEPROM.");
            return false;
        };
    } else {
        // Load settings from flash.
        settings = *(Settings *)kFlashSettingsStartAddr;
    }

    // Reset to defaults if loading from a blank EEPROM.
    if (settings.settings_version != kSettingsVersion) {
        ResetToDefaults();
        if (bsp.has_eeprom && !eeprom.Save(settings)) {
            CONSOLE_ERROR("settings.cc::Load", "Failed to save default settings.");
            return false;
        } else {
            FlashUtils::FlashSafe();
            flash_range_erase(FirmwareUpdateManager::FlashAddrToOffset(kFlashSettingsStartAddr), sizeof(settings));
            flash_range_program(FirmwareUpdateManager::FlashAddrToOffset(kFlashSettingsStartAddr), (uint8_t *)&settings,
                                sizeof(settings));
            FlashUtils::FlashUnsafe();
        }
    }

    Apply();

    return true;
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

    if (bsp.has_eeprom) {
        return eeprom.Save(settings);
    } else {
        FlashUtils::FlashSafe();
        flash_range_erase(FirmwareUpdateManager::FlashAddrToOffset(kFlashSettingsStartAddr), sizeof(settings));
        flash_range_program(FirmwareUpdateManager::FlashAddrToOffset(kFlashSettingsStartAddr), (uint8_t *)&settings,
                            sizeof(settings));
        FlashUtils::FlashUnsafe();
        return true;
    }
}

void SettingsManager::ResetToDefaults() {
    Settings default_settings;
    settings = default_settings;
    Apply();
}

bool SettingsManager::SetDeviceInfo(const DeviceInfo &device_info) {
    if (bsp.has_eeprom) {
        // Device Info is stored on external EEPROM.
        if (eeprom.RequiresInit()) return false;
        return eeprom.Save(device_info, kDeviceInfoOffset);
    } else {
        // Device Info is stored in flash.
        FlashUtils::FlashSafe();
        flash_range_erase(FirmwareUpdateManager::FlashAddrToOffset(kFlashSettingsStartAddr + kDeviceInfoOffset),
                          sizeof(device_info));
        flash_range_program(FirmwareUpdateManager::FlashAddrToOffset(kFlashSettingsStartAddr + kDeviceInfoOffset),
                            (uint8_t *)&device_info, sizeof(device_info));
        FlashUtils::FlashUnsafe();
        return true;
    }
}

bool SettingsManager::GetDeviceInfo(DeviceInfo &device_info) {
    if (bsp.has_eeprom) {
        // Device Info is stored on external EEPROM.
        if (eeprom.RequiresInit()) return false;
        return eeprom.Load(device_info, kDeviceInfoOffset);
    } else {
        // Device Info is stored in flash.
        device_info = *(DeviceInfo *)(kFlashSettingsStartAddr + kDeviceInfoOffset);
        return true;
    }
}

bool SettingsManager::Apply() {
    adsbee.SetReceiverEnable(settings.receiver_enabled);
    adsbee.SetTLMilliVolts(settings.tl_mv);
    adsbee.SetBiasTeeEnable(settings.bias_tee_enabled);
    adsbee.SetWatchdogTimeoutSec(settings.watchdog_timeout_sec);

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