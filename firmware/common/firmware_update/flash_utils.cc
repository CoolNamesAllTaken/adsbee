#include "flash_utils.hh"

#ifndef ON_PICO_BOOTLOADER
#include "adsbee.hh"
#include "core1.hh"
#endif
#include "hardware/sync.h"

// Initialize static variables.
uint32_t FlashUtils::stored_interrupts_ = 0;

void FlashUtils::FlashSafe() {
    stored_interrupts_ = save_and_disable_interrupts();
#ifndef ON_PICO_BOOTLOADER
    StopCore1();               // Reset core 1 to prevent it from executing while we erase flash.
    adsbee.DisableWatchdog();  // Flash erase can take a while, prevent watchdog from rebooting us.
#endif
}
void FlashUtils::FlashUnsafe() {
#ifndef ON_PICO_BOOTLOADER
    adsbee.EnableWatchdog();
    StartCore1();
#endif
    restore_interrupts(stored_interrupts_);
}