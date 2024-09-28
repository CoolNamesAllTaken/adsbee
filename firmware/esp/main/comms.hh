#ifndef COMMS_HH_
#define COMMS_HH_

#include "esp_log.h"
#include "esp_system.h"
#include "esp_wifi.h"
#include "settings.hh"

class CommsManager {
   public:
    bool SetWiFiMode(SettingsManager::WiFiMode new_wifi_mode);

   private:
    static void WiFiEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data);

    static_assert(SettingsManager::WiFiMode::kWiFiModeOff == WIFI_MODE_NULL);
    static_assert(SettingsManager::kWiFiModeAccessPoint == WIFI_MODE_AP);
    static_assert(SettingsManager::kWiFiModeStation == WIFI_MODE_STA);
};

extern CommsManager comms_manager;

#define CONSOLE_ERROR(tag, ...)   ESP_LOGE(tag, __VA_ARGS__)
#define CONSOLE_WARNING(tag, ...) ESP_LOGW(tag, __VA_ARGS__)
#define CONSOLE_INFO(tag, ...)    ESP_LOGI(tag, __VA_ARGS__)

#endif /* COMMS_HH_ */