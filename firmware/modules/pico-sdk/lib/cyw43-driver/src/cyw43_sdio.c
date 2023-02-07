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

#include <stdio.h>
#include <stdbool.h>
#include "cyw43.h"
#include "cyw43_internal.h"
#include "cyw43_sdio.h"

// Performs an SDIO CMD52 transaction.
// On success returns the response byte (0-255).
// On error returns a negative errno code.
static int cyw43_sdio_cmd52(bool write, uint32_t fn, uint32_t addr, uint32_t val) {
    uint32_t arg = fn << 28 | (addr & 0x1ffff) << 9 | write << 31 | (val & 0xff);
    uint32_t resp;
    int ret = cyw43_sdio_transfer(52, arg, &resp);
    if (ret != 0) {
        return ret;
    }
    return resp & 0xff;
}

static int cyw43_sdio_cmd53(bool write, uint32_t fn, uint32_t addr, size_t len, uint8_t *buf) {
    uint32_t block_size;
    uint32_t block_mode;
    size_t sz = len;
    if (sz <= 64) {
        // SDIO_BYTE_MODE (can go up to 512 bytes)
        // in this case the SDIO chuck of data must be a single block of the length of buf
        block_size = sz;
        block_mode = 0;
    } else {
        // looks like block_size must be 64
        block_size = 64;
        block_mode = 1 << 27;
        sz /= block_size;
    }
    uint32_t arg = fn << 28 | block_mode | 1 << 26 | (addr & 0x1ffff) << 9 | write << 31 | sz;
    return cyw43_sdio_transfer_cmd53(write, block_size, arg, len, buf);
}

int cyw43_read_bytes(cyw43_int_t *self, uint32_t fn, uint32_t addr, size_t len, uint8_t *buf) {
    return cyw43_sdio_cmd53(false, fn, addr, len, buf);
}

int cyw43_write_bytes(cyw43_int_t *self, uint32_t fn, uint32_t addr, size_t len, const uint8_t *buf) {
    return cyw43_sdio_cmd53(true, fn, addr, len, (uint8_t *)buf);
}

int cyw43_read_reg_u8(cyw43_int_t *self, uint32_t fn, uint32_t reg) {
    return cyw43_sdio_cmd52(false, fn, reg, 0);
}

uint32_t cyw43_read_reg_u32(cyw43_int_t *self, uint32_t fn, uint32_t reg) {
    uint32_t val = 0;
    cyw43_sdio_cmd53(false, fn, reg, 4, (void *)&val);
    return val;
}

int cyw43_write_reg_u8(cyw43_int_t *self, uint32_t function, uint32_t reg, uint32_t val) {
    return cyw43_sdio_cmd52(true, function, reg, val);
}

int cyw43_write_reg_u32(cyw43_int_t *self, uint32_t function, uint32_t reg, uint32_t val) {
    return cyw43_sdio_cmd53(true, function, reg, 4, (void *)&val);
}
