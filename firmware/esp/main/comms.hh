#ifndef COMMS_HH_
#define COMMS_HH_

#include "esp_log.h"

class CommsManager {};

extern CommsManager comms_manager;

#define CONSOLE_ERROR(tag, ...)   ESP_LOGE(tag, __VA_ARGS__)
#define CONSOLE_WARNING(tag, ...) ESP_LOGW(tag, __VA_ARGS__)
#define CONSOLE_INFO(tag, ...)    ESP_LOGI(tag, __VA_ARGS__)

#endif /* COMMS_HH_ */