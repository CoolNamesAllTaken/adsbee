#include "settings.hh"

#include "comms.hh"

void SettingsManager::Apply() {
    comms_manager.wifi_mode = settings.wifi_mode;
    strncpy(comms_manager.ap_wifi_ssid, settings.ap_wifi_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
    strncpy(comms_manager.ap_wifi_password, settings.ap_wifi_password,
            SettingsManager::Settings::kWiFiPasswordMaxLen + 1);
    strncpy(comms_manager.sta_wifi_ssid, settings.sta_wifi_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
    strncpy(comms_manager.sta_wifi_password, settings.sta_wifi_password,
            SettingsManager::Settings::kWiFiPasswordMaxLen + 1);
}