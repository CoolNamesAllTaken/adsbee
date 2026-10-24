#pragma once

#include <stdint.h>

/**
 * RAM use for AT+DEVICE_INFO. Free stack space is filled with a pattern at boot; the lowest overwritten word marks the
 * deepest stack use. Core 0's stack starts in scratch X and grows into the top of main RAM, toward the heap.
 */
class RAMMonitor {
   public:
    struct Usage {
        uint32_t heap_in_use_bytes = 0;
        uint32_t free_bytes = 0;  // Main RAM between the heap and core 0's deepest stack use.
        uint32_t core_0_stack_peak_bytes = 0;
        uint32_t core_1_stack_peak_bytes = 0;
    };

    // Call first thing in main(), before interrupts are enabled.
    static void PaintCore0Stack();
    // Call before every core 1 launch.
    static void PaintCore1Stack();
    static Usage GetUsage();
};
