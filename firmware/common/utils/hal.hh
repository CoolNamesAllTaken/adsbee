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
#else
    return time_since_boot_us;
#endif
}
inline uint32_t get_time_since_boot_ms() {
#ifdef ON_PICO
    return to_ms_since_boot(get_absolute_time());
#elif ON_ESP32
    return xTaskGetTickCount() * portTICK_PERIOD_MS;
#else
    return time_since_boot_us / 1e3;
#endif
}

#endif /* HAL_HH_ */