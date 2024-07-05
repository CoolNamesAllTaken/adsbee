#include "hal.hh"

#include "hardware/spi.h"
#include "pico/stdlib.h"

uint64_t get_time_since_boot_us() { return to_us_since_boot(get_absolute_time()); }

uint32_t get_time_since_boot_ms() { return to_ms_since_boot(get_absolute_time()); }