#include "settings.hh"

#include "comms.hh"

void SettingsManager::Apply() {
    comms_manager.wifi_ap_enabled = settings.wifi_ap_enabled;
    comms_manager.wifi_ap_channel = settings.wifi_ap_channel;
    strncpy(comms_manager.wifi_ap_ssid, settings.wifi_ap_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
    strncpy(comms_manager.wifi_ap_password, settings.wifi_ap_password,
            SettingsManager::Settings::kWiFiPasswordMaxLen + 1);
    comms_manager.wifi_sta_enabled = settings.wifi_sta_enabled;
    strncpy(comms_manager.wifi_sta_ssid, settings.wifi_sta_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
    strncpy(comms_manager.wifi_sta_password, settings.wifi_sta_password,
            SettingsManager::Settings::kWiFiPasswordMaxLen + 1);
}