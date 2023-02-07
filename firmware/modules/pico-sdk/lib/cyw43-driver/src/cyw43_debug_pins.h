/*
 * This file is part of the cyw43-driver
 *
 * Copyright (C) 2019-2022 George Robotics Pty Ltd
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. Any redistribution, use, or modification in source or binary form is done
 *    solely for personal benefit and not for any commercial purpose or for
 *    monetary gain.
 *
 * THIS SOFTWARE IS PROVIDED BY THE LICENSOR AND COPYRIGHT OWNER "AS IS" AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE LICENSOR OR COPYRIGHT OWNER BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * This software is also available for use with certain devices under different
 * terms, as set out in the top level LICENSE file.  For commercial licensing
 * options please email contact@georgerobotics.com.au.
 */

#ifndef CYW43_INCLUDED_CYW43_DEBUG_PINS_H
#define CYW43_INCLUDED_CYW43_DEBUG_PINS_H

#ifdef PICO_BUILD
#include "hardware/gpio.h"
#else
#undef CYW43_LOGIC_DEBUG
#endif

static inline void logic_debug_init(void) {
    #if CYW43_LOGIC_DEBUG
    const int dbg_start = 2;
    const int dbg_end = 14;
    for (int pin = dbg_start; pin <= dbg_end; pin++) {
        gpio_init(pin);
        gpio_set_dir(pin, 1);
        gpio_put(pin, 0);
    }
    #endif
}

static inline void logic_debug_set(uint8_t pin, uint8_t value) {
    #if CYW43_LOGIC_DEBUG
    gpio_put(pin, value);
    #else
    (void)pin;
    (void)value;
    #endif
}

#define pin_BACKPLANE_WRITE 2
#define pin_BACKPLANE_READ 3
#define pin_TX_PKT 4
#define pin_RX_PKT 5
#define pin_F2_RX_READY_WAIT 6
#define pin_WIFI_TX 7
#define pin_WIFI_RX 8
#define pin_F1_NOT_READY 9
#define pin_F1_OVERFLOW 10

#endif // CYW43_INCLUDED_CYW43_DEBUG_PINS_H
