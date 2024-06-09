#ifndef HAL_GOD_POWERS_HH_
#define HAL_GOD_POWERS_HH_

#include "stdint.h"
#include "hal.hh"
#include <tuple>

// Additional God Power functions available for creating tests.
void set_time_since_boot_us(uint64_t time_us);
void inc_time_since_boot_us(uint64_t inc = 5);
void set_time_since_boot_ms(uint32_t time_ms);
void inc_time_since_boot_ms(uint32_t inc = 5);

std::tuple<uint32_t, uint32_t, uint16_t> get_last_pwm_set_vals(); // currently unused

#endif /* HAL_GOD_POWERS_HH_ */