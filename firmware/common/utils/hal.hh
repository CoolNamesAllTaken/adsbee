#ifndef HAL_HH_
#define HAL_HH_

#include "stdint.h"

#ifdef ON_PICO
#include "pico/stdlib.h"
#elif ON_ESP32
#include "esp_timer.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#elif ON_TI
#include <ti/drivers/dpl/ClockP.h>
#else
#include "hal_god_powers.hh"
extern uint64_t time_since_boot_us;
#endif

inline uint64_t get_time_since_boot_us() {
#ifdef ON_PICO
    return to_us_since_boot(get_absolute_time());
#elif ON_ESP32
    return esp_timer_get_time();
#elif ON_TI
    return ClockP_getSystemTicks() * ClockP_getSystemTickPeriod();
#else
    return time_since_boot_us;
#endif
}
inline uint32_t get_time_since_boot_ms() {
#ifdef ON_PICO
    return to_ms_since_boot(get_absolute_time());
#elif ON_ESP32
    return xTaskGetTickCount() * portTICK_PERIOD_MS;
#elif ON_TI
    return ClockP_getSystemTicks() * ClockP_getSystemTickPeriod() * 1000;  // tickPeriod is in us.
#else
    return time_since_boot_us / 1e3;
#endif
}

inline void sleep_us_blocking(uint64_t us) {
    uint64_t timestamp_us = get_time_since_boot_us();
    while (get_time_since_boot_us() - timestamp_us < us) {
    }
}

inline void sleep_ms_blocking(uint32_t ms) {
    uint64_t timestamp_ms = get_time_since_boot_ms();
    while (get_time_since_boot_ms() - timestamp_ms < ms) {
    }
}

#endif /* HAL_HH_ */