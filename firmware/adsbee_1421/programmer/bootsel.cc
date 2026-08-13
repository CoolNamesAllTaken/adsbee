#include "bootsel.hh"

#include "hardware/structs/ioqspi.h"
#include "hardware/structs/sio.h"
#include "hardware/sync.h"
#include "pico/stdlib.h"

// Reads the BOOTSEL button by briefly driving the QSPI chip select low and sampling it back. Must
// run from RAM with interrupts off, since it stalls flash access while the pad is overridden.
// RP2040 specific (the QSPI pad layout differs on RP2350). Copied from the adsbee-lp1090
// sync_pulser jig's main.cpp.
bool __no_inline_not_in_flash_func(GetBootselButton)() {
    const uint kCsPinIndex = 1;

    uint32_t flags = save_and_disable_interrupts();

    hw_write_masked(&ioqspi_hw->io[kCsPinIndex].ctrl,
                    GPIO_OVERRIDE_LOW << IO_QSPI_GPIO_QSPI_SS_CTRL_OEOVER_LSB,
                    IO_QSPI_GPIO_QSPI_SS_CTRL_OEOVER_BITS);
    // Wait for the pad to settle. No timer calls here: they may live in flash, which is stalled.
    for (int i = 0; i < 1000; i++) __asm volatile("nop");  // asm volatile keeps the loop alive.
    bool pressed = !(sio_hw->gpio_hi_in & (1u << kCsPinIndex));
    hw_write_masked(&ioqspi_hw->io[kCsPinIndex].ctrl,
                    GPIO_OVERRIDE_NORMAL << IO_QSPI_GPIO_QSPI_SS_CTRL_OEOVER_LSB,
                    IO_QSPI_GPIO_QSPI_SS_CTRL_OEOVER_BITS);

    restore_interrupts(flags);
    return pressed;
}
