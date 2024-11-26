#ifndef BOOT_UTILS_HH_
#define BOOT_UTILS_HH_

#include "RP2040.h"
#include "hal.hh"
#include "stdio.h"

static const uint16_t kStatusLEDPin = 15;

/* Original flash length: 16384k Bytes.
    FLASH MAP
        0x10000000	(176k)	FLASH_BL	Bootloader
        0x1002C000	(4k)	FLASH_HDR0	Application 0 Header
        0x1002D000	(8096k)	FLASH_APP0	Application 0 Data
        0x10815000	(4k)	FLASH_HDR1	Application 1 Header
        0x10816000	(8096k)	FLASH_APP1	Application 1 Data
        0x10FFE000	(8k)	FLASH_EXTRA	Extra
*/

static const uint32_t kFlashAddrHdr0 = 0x1002C000;
static const uint32_t kFlashAddrApp0 = 0x1002D000;
static const uint32_t kFlashAddrHdr1 = 0x10815000;
static const uint32_t kFlashAddrApp1 = 0x10816000;

static inline void set_status_led_for_duration(bool led_on, uint16_t duration_ms) {
    gpio_put(kStatusLEDPin, led_on);
    busy_wait_ms(duration_ms);
}

static inline void disable_interrupts(void) {
    SysTick->CTRL &= ~1;

    NVIC->ICER[0] = 0xFFFFFFFF;
    NVIC->ICPR[0] = 0xFFFFFFFF;
}

static inline void reset_peripherals(void) {
    reset_block(~(RESETS_RESET_IO_QSPI_BITS | RESETS_RESET_PADS_QSPI_BITS | RESETS_RESET_SYSCFG_BITS |
                  RESETS_RESET_PLL_SYS_BITS));
}

static inline void jump_to_vtor(uint32_t vtor) {
    // Derived from the Leaf Labs Cortex-M3 bootloader.
    // Copyright (c) 2010 LeafLabs LLC.
    // Modified 2021 Brian Starkey <stark3y@gmail.com>
    // Originally under The MIT License
    uint32_t reset_vector = *(volatile uint32_t *)(vtor + 0x04);

    SCB->VTOR = (volatile uint32_t)(vtor);

    asm volatile("msr msp, %0" ::"g"(*(volatile uint32_t *)vtor));
    asm volatile("bx %0" ::"r"(reset_vector));
}

#endif