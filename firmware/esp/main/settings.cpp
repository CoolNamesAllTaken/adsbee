#include "settings.hh"

#include "comms.hh"

void SettingsManager::Apply() {
    comms_manager.wifi_mode = settings.wifi_mode;
    strncpy(comms_manager.wifi_ssid, settings.wifi_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
    strncpy(comms_manager.wifi_password, settings.wifi_password, SettingsManager::Settings::kWiFiPasswordMaxLen + 1);
}