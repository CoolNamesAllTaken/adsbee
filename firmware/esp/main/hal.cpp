#include "hal.hh"

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

uint32_t get_time_since_boot_ms() { return xTaskGetTickCount() / portTICK_PERIOD_MS; }