#ifndef _HAL_GOD_POWERS_HH_
#define _HAL_GOD_POWERS_HH_

#include "stdint.h"
#include "hal.hh"

// Additional God Power functions available for creating tests.
void set_time_since_boot_us(uint64_t time_us);
void inc_time_since_boot_us(uint64_t inc=5);
void set_time_since_boot_ms(uint32_t time_ms);
void inc_time_since_boot_ms(uint32_t inc=5);

#endif /* _HAL_GOD_POWERS_HH_ */