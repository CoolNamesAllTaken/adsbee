#include "hal/hal.hh"

#include "pico/stdlib.h"

uint64_t time_since_boot_us() {
    return to_us_since_boot(get_absolute_time());
}