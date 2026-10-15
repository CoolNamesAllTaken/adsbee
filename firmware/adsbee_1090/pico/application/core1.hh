#pragma once

#include "adsbee.hh"
#include "cpu_utils.hh"
#include "mode_s_packet_decoder.hh"
#include "pico/multicore.h"

extern CPUMonitor core_1_monitor;

// Core 1 load is the time its loop spends demodulating, decoding or held up by interrupts. A loop pass with nothing to
// do takes well under this.
static constexpr uint32_t kCore1IdlePassMaxUs = 2;

#ifdef HARDWARE_UNIT_TESTS
void RunPendingTestFunctionOnCore1();  // Defined in target_test/hardware_unit_tests.cc.
#endif

inline void main_core1() {
#ifdef ISRS_ON_CORE1
    adsbee.InitISRs();
#else
    irq_set_enabled(IO_IRQ_BANK0, false);  // Disable GPIO IRQs (OnDemodBegin) on this core.
    irq_set_enabled(PIO0_IRQ_0, false);    // Disable PIO0 IRQ0 (OnDemodComplete) on this core.
#endif  // ISRS_ON_CORE1

    while (true) {
        uint32_t iteration_start_us = time_us_32();
#ifdef ISRS_ON_CORE1
        // Core 0 may try to toggle the 1090 receiver on and off. Keep an eye on it and turn it on and off here, since
        // it can't be toggle from core 0 without accidentally duplicating all the ISR stuff on that core.
        if (adsbee.Receiver1090IsEnabled() != adsbee.Receiver1090IRQIsEnabled()) {
            adsbee.SyncReceiver1090IRQEnable();
        }
#endif  // ISRS_ON_CORE1
#ifdef HARDWARE_UNIT_TESTS
        RunPendingTestFunctionOnCore1();  // Lets hardware unit tests read core 1 state, e.g. its SysTick.
#endif
        bool did_work = adsbee.DemodulateCaptures();
        did_work |= decoder.raw_mode_s_packet_in_queue.Length() > 0;
        decoder.UpdateDecoderLoop();
        uint32_t iteration_us = time_us_32() - iteration_start_us;
        if (did_work || iteration_us >= kCore1IdlePassMaxUs) {
            core_1_monitor.AddBusyTimeUs(iteration_us);
        }
    }
}

// Set by LaunchCore1(). Until then StopCore1() and StartCore1() do nothing: a flash write early in boot (a settings
// migration) must not start core 1, whose DMA channels main() would then leak when it launches core 1 itself.
inline bool core1_launched = false;

inline void LaunchCore1() {
    core1_launched = true;
    multicore_reset_core1();
    multicore_launch_core1(main_core1);
}

inline void StopCore1() {
    if (!core1_launched) {
        return;
    }
    adsbee.DeInitISRs();  // Clean up DMA channels and other ISR resources before stopping core
    multicore_reset_core1();
}

inline void StartCore1() {
    if (!core1_launched) {
        return;
    }
    multicore_launch_core1(main_core1);
}