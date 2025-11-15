#pragma once

#include "adsbee.hh"
#include "cpu_utils.hh"
#include "mode_s_packet_decoder.hh"
#include "pico/multicore.h"

extern CPUMonitor core_1_monitor;

inline void main_core1() {
    // adsbee.InitISRs();

    while (true) {
        core_1_monitor.Tick();
        decoder.UpdateDecoderLoop();
    }
}

inline void StopCore1() { multicore_reset_core1(); }
inline void StartCore1() { multicore_launch_core1(main_core1); }