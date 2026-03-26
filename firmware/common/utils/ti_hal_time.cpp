#if defined(ON_TI)

#include <stdint.h>

#include <ti/drivers/dpl/ClockP.h>

namespace {

uint32_t s_prev_ticks = 0;
uint32_t s_tick_wrap_epoch = 0;

// 32-bit ClockP tick counter extended to 64 bits by counting wraps. No multiply here.
uint64_t ti_read_extended_ticks_u64(void) {
    const uint32_t t = ClockP_getSystemTicks();
    if (t < s_prev_ticks) {
        s_tick_wrap_epoch++;
    }
    s_prev_ticks = t;
    return (static_cast<uint64_t>(s_tick_wrap_epoch) << 32) | static_cast<uint64_t>(t);
}

// x * 1000 without hardware multiply (1000 = 1024 - 16 - 8). Used for common 1 ms RTOS ticks.
inline uint64_t mul_u64_by_1000(uint64_t x) {
    return (x << 10) - (x << 4) - (x << 3);
}

uint64_t s_us_since_boot = 0;
uint64_t s_last_tick64_for_us = 0;
bool s_timebase_initialized = false;

static uint32_t s_cached_period_us = 0;

// Advances s_us_since_boot by (delta_ticks * period_us) without multiplying full 64-bit tick counts each call.
void ti_advance_us_accumulator(void) {
    if (s_cached_period_us == 0) {
        s_cached_period_us = ClockP_getSystemTickPeriod();
    }
    const uint32_t p = s_cached_period_us;

    const uint64_t now64 = ti_read_extended_ticks_u64();
    if (!s_timebase_initialized) {
        s_last_tick64_for_us = now64;
        s_timebase_initialized = true;
        return;
    }

    const uint64_t dt = now64 - s_last_tick64_for_us;
    s_last_tick64_for_us = now64;
    if (dt == 0) {
        return;
    }

    if (p == 1U) {
        // 1 µs per tick: elapsed µs equals elapsed ticks.
        s_us_since_boot += dt;
    } else if (p == 1000U) {
        // Typical FreeRTOS-style 1 ms tick: scale by 1000 µs/tick without a multiply instruction.
        s_us_since_boot += mul_u64_by_1000(dt);
    } else {
        // Rare nonstandard period: multiply delta ticks only (not full uptime tick count × period).
        s_us_since_boot += dt * static_cast<uint64_t>(p);
    }
}

}  // namespace

uint64_t ti_get_time_since_boot_us(void) {
    ti_advance_us_accumulator();
    return s_us_since_boot;
}

uint32_t ti_get_time_since_boot_ms(void) {
    ti_advance_us_accumulator();

    if (s_cached_period_us == 1000U) {
        // 1 ms per tick: millisecond counter matches low 32 bits of tick count for API wrap semantics.
        return static_cast<uint32_t>(s_last_tick64_for_us);
    }
    return static_cast<uint32_t>(s_us_since_boot / 1000U);
}

#endif  // ON_TI
