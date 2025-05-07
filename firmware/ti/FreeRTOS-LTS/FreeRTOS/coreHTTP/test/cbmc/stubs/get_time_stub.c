/*
 * coreHTTP v3.1.1
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file get_time_stub.c
 * @brief A stub to mock the retrieval of current time.
 */
#include "stdint.h"
#include "get_time_stub.h"


uint32_t GetCurrentTimeStub( void )
{
    /* The HTTP relies on this timestamp in order to complete the network send
     * and receive loops. Returning an unbounded timestamp does not add value to
     * the proofs as the HTTP library uses this timestamp only in an arithmetic
     * operation to get the difference. In C, arithmetic operations on unsigned
     * integers are guaranteed to reliably wrap around with no adverse side
     * effects. If the time returned was unbounded, the network send and receive
     * loops could be unwound a large number of times making the proof execution
     * very long. */
    static uint32_t globalEntryTime = 0;

    return globalEntryTime++;
}
