#if defined(ON_TI)

#include <stdint.h>

#include <ti/drivers/dpl/ClockP.h>

namespace {

uint32_t s_prev_ticks = 0;
uint32_t s_tick_wrap_epoch = 0;

// 32-bit ClockP tick counter extended to 64 bits by counting wraps. No multiply here.
uint64_t ti_extended_system_ticks_u64(void) {
    const uint32_t t = ClockP_getSystemTicks();
    if (t < s_prev_ticks) {
        s_tick_wrap_epoch++;
    }
    s_prev_ticks = t;
    return (static_cast<uint64_t>(s_tick_wrap_epoch) << 32) | static_cast<uint64_t>(t);
}

}  // namespace

uint64_t ti_get_time_since_boot_us(void) {
    const uint32_t period_us = ClockP_getSystemTickPeriod();
    const uint64_t ticks = ti_extended_system_ticks_u64();
    // Prefer one 64×32-style widening multiply over casting both TI API uint32 values to uint64
    // before multiplying (which tends to compile as a full 64×64 multiply on the toolchain).
    return ticks * static_cast<uint64_t>(period_us);
}

uint32_t ti_get_time_since_boot_ms(void) {
    const uint32_t period_us = ClockP_getSystemTickPeriod();
    const uint64_t ticks = ti_extended_system_ticks_u64();
    // 1000 µs/tick ⇒ 1 ms per tick: elapsed ms matches tick count (uint32 wraps with API).
    if (period_us == 1000U) {
        return static_cast<uint32_t>(ticks);
    }
    const uint64_t us = ticks * static_cast<uint64_t>(period_us);
    return static_cast<uint32_t>(us / 1000U);
}

#endif  // ON_TI
