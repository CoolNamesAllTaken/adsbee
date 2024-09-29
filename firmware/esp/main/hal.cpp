#include "hal.hh"

#include "esp_timer.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

uint32_t get_time_since_boot_ms() { return xTaskGetTickCount() * portTICK_PERIOD_MS; }

uint64_t get_time_since_boot_us() { return esp_timer_get_time(); }