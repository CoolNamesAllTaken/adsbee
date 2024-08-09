#include "esp_log.h"

#define CONSOLE_ERROR(tag, ...)   ESP_LOGE(tag, __VA_ARGS__)
#define CONSOLE_WARNING(tag, ...) ESP_LOGW(tag, __VA_ARGS__)
#define CONSOLE_INFO(tag, ...)    ESP_LOGI(tag, __VA_ARGS__)