#include "hal.hh"
#include "hal_god_powers.hh"

static uint64_t time_since_boot_us = 0;

uint64_t get_time_since_boot_us() {
    return time_since_boot_us;
}

uint32_t get_time_since_boot_ms() {
    return time_since_boot_us / 1e3;
}

/** God Powers **/
void set_time_since_boot_us(uint64_t time_us) {
    time_since_boot_us = time_us;
}

void inc_time_since_boot_us(uint64_t inc) {
    time_since_boot_us+=inc;
}

void set_time_since_boot_ms(uint32_t time_ms) {
    time_since_boot_us = 1e3 * time_ms;
}

void inc_time_since_boot_ms(uint32_t inc) {
    time_since_boot_us += 1e3*inc;
}

