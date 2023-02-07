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

#ifndef CYW43_STATS_H
#define CYW43_STATS_H

#include <stdint.h>

#if CYW43_USE_STATS

typedef enum cyw43_stat_t_ {
    CYW43_STAT_F1_RESYNC,
    CYW43_STAT_BUS_ERROR,
    CYW43_STAT_SDIO_INT_CLEAR,
    CYW43_STAT_SPI_INT_CLEAR,
    CYW43_STAT_SPI_PACKET_AVAILABLE,
    CYW43_STAT_SLEEP_COUNT,
    CYW43_STAT_WAKE_COUNT,
    CYW43_STAT_LWIP_RUN_COUNT,
    CYW43_STAT_CYW43_RUN_COUNT,
    CYW43_STAT_PENDSV_RUN_COUNT,
    CYW43_STAT_PENDSV_DISABLED_COUNT,
    CYW43_STAT_IRQ_COUNT,
    CYW43_STAT_PACKET_IN_COUNT,
    CYW43_STAT_PACKET_OUT_COUNT,
    CYW43_STAT_LONGEST_IOCTL_TIME,
    CYW43_STAT_LAST // Add new ones before this
} cyw43_stat_t;

extern uint32_t cyw43_stats[CYW43_STAT_LAST];
#define CYW43_STAT_INC(A) cyw43_stats[CYW43_STAT_##A]++
#define CYW43_STAT_GET(A) cyw43_stats[CYW43_STAT_##A]
#define CYW43_STAT_SET(A, B) cyw43_stats[CYW43_STAT_##A] = B
#define CYW43_STAT_CLR(A) cyw43_stats[CYW43_STAT_##A] = 0

#else

#define CYW43_STAT_INC(A)
#define CYW43_STAT_GET(A)
#define CYW43_STAT_SET(A, B)
#define CYW43_STAT_CLR(A)

#endif

void cyw43_dump_stats(void);

#endif // CYW43_STATS_H
