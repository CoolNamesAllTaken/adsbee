#pragma once

#include "mode_s_packet_decoder.hh"
#include "pico/multicore.h"

inline void main_core1() {
    while (true) {
        decoder.UpdateDecoderLoop();
    }
}

inline void StopCore1() { multicore_reset_core1(); }
inline void StartCore1() { multicore_launch_core1(main_core1); }