#pragma once

#include <cstdint>

uint64_t get_time_since_boot_us();
uint32_t get_time_since_boot_ms();

/**
 * Singleton class to manage the systick timer in the ARM cores
 * @attention Since this is a singleton and uses per core hardware, this should only be constructed from Core 0 to maintain consistency
 * @see https://documentation-service.arm.com/static/5f8ff05ef86e16515cdbf826 section B3.3
 * 
 */
class ClockSource {
   public:
    static ClockSource& instance();
    ~ClockSource();

    /**
     * Creates a composite timestamp using the current value of the SysTick timer (running at 125MHz) and the SysTick
     * wrap counter to simulate a timer running at 48MHz (which matches the frequency of the preamble detector PIO).
     * @retval 48MHz counter value.
     */
    uint64_t Get48MHzTickCount();

    /**
     * Creates a composite timestamp using the current value of the SysTick timer (running at 125MHz) and the SysTick
     * wrap counter to simulate a timer running at 12MHz, which matches existing decoders that use the Mode S Beast
     * protocol.
     * @retval 12MHz counter value.
     */
    uint64_t Get12MHzTickCount();

   private:
    static void HandleIRQ();

    ClockSource();
    ClockSource(const ClockSource&) = delete;
    ClockSource& operator=(const ClockSource&) = delete;
    ClockSource(ClockSource&&) = delete;
    ClockSource& operator=(const ClockSource&&) = delete;

    static volatile uint32_t interrupt_count_;
};