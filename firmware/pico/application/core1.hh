#pragma once

#include "adsbee.hh"
#include "cpu_utils.hh"
#include "mode_s_packet_decoder.hh"
#include "pico/multicore.h"

extern CPUMonitor core_1_monitor;

inline void main_core1() {
#ifdef ISRS_ON_CORE1
    adsbee.InitISRs();
#else
    irq_set_enabled(IO_IRQ_BANK0, false);  // Disable GPIO IRQs on this core.
#endif  // ISRS_ON_CORE1

    while (true) {
        core_1_monitor.Tick();
        decoder.UpdateDecoderLoop();
    }
}

inline void StopCore1() { multicore_reset_core1(); }
inline void StartCore1() { multicore_launch_core1(main_core1); }