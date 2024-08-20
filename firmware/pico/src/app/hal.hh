#pragma once

#include <cstdint>

uint64_t get_time_since_boot_us();
uint32_t get_time_since_boot_ms();

class ClockSource {
   public:
    static ClockSource& instance();
    ~ClockSource();

    uint64_t get48MHzTickCount();
    uint64_t get12MHzTickCount();

   private:
    static void handleIrq();

    static volatile uint32_t _interruptCount;

    ClockSource();
    ClockSource(const ClockSource&) = delete;
    ClockSource& operator=(const ClockSource&) = delete;
    ClockSource(ClockSource&&) = delete;
    ClockSource& operator=(const ClockSource&&) = delete;
};