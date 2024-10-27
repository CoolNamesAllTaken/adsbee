#ifndef HAL_HH_
#define HAL_HH_

#include "stdint.h"

#ifdef ON_PICO
#include "pico/stdlib.h"
#elif ON_ESP32
#include "esp_timer.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#endif

inline uint64_t get_time_since_boot_us() {
#ifdef ON_PICO
    return to_us_since_boot(get_absolute_time());
#elif ON_ESP32
    return esp_timer_get_time();
#endif
}
inline uint32_t get_time_since_boot_ms() {
#ifdef ON_PICO
    return to_ms_since_boot(get_absolute_time());
#elif ON_ESP32
    return xTaskGetTickCount() * portTICK_PERIOD_MS;
#endif
}

#endif /* HAL_HH_ */