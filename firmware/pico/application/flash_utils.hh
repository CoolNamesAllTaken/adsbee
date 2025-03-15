#pragma once

#include "stdint.h"

// NOTE: These functions are NOT used in firmare_update.hh because it needs to be linked in the bootloader.

class FlashUtils {
   public:
    /**
     * Makes it safe to modify flash memory by disable interrupts and anything else that could screw with it.
     */
    static void FlashSafe();

    /**
     * Un-does changes made by FlashSafe().
     */
    static void FlashUnsafe();

   private:
    static uint32_t stored_interrupts_;
};
