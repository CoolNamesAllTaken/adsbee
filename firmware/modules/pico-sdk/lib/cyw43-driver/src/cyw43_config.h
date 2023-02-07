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

// Import port-specific configuration file.
#ifdef CYW43_CONFIG_FILE
#include CYW43_CONFIG_FILE
#else
#include <cyw43_configport.h>
#endif

// Bus configuration.

#ifndef CYW43_USE_SPI
#define CYW43_USE_SPI (0)
#endif

// Timing and timeout configuration.

#ifndef CYW43_IOCTL_TIMEOUT_US
#define CYW43_IOCTL_TIMEOUT_US (500000)
#endif

#ifndef CYW43_SLEEP_MAX
#define CYW43_SLEEP_MAX (50)
#endif

// Miscellaneous configuration.

// No other options right now for TCP/IP stack.
#ifndef CYW43_LWIP
#define CYW43_LWIP (1)
#endif

#ifndef CYW43_NETUTILS
#define CYW43_NETUTILS (0)
#endif

#ifndef CYW43_USE_OTP_MAC
#define CYW43_USE_OTP_MAC (0)
#endif

#ifndef CYW43_GPIO
#define CYW43_GPIO (0)
#endif

#ifndef CYW43_PRINTF
#include <stdio.h>
#define CYW43_PRINTF(...) printf(__VA_ARGS__)
#endif

#ifndef CYW43_VDEBUG
#define CYW43_VDEBUG(...) (void)0
#define CYW43_VERBOSE_DEBUG 0
#endif

#ifndef CYW43_DEBUG
#ifdef NDEBUG
#define CYW43_DEBUG(...) (void)0
#else
#define CYW43_DEBUG(...) CYW43_PRINTF(__VA_ARGS__)
#endif
#endif

#ifndef CYW43_INFO
#define CYW43_INFO(...) CYW43_PRINTF(__VA_ARGS__)
#endif

#ifndef CYW43_WARN
#define CYW43_WARN(...) CYW43_PRINTF("[CYW43] " __VA_ARGS__)
#endif

#ifndef CYW43_FAIL_FAST_CHECK
#define CYW43_FAIL_FAST_CHECK(res) (res)
#endif
