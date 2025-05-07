/*
 * coreSNTP v1.3.1
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file Sntp_SerializeRequest_harness.c
 * @brief Implements the proof harness for Sntp_SerializeRequest function.
 */

#include <stdint.h>
#include "core_sntp_serializer.h"

void harness()
{
    SntpTimestamp_t * pRequestTime;
    uint32_t randomNumber;
    void * pBuffer;
    size_t bufferSize;
    SntpStatus_t sntpStatus;

    pRequestTime = malloc( sizeof( SntpTimestamp_t ) );

    __CPROVER_assume( bufferSize < CBMC_MAX_OBJECT_SIZE );

    pBuffer = malloc( bufferSize );

    sntpStatus = Sntp_SerializeRequest( pRequestTime, randomNumber, pBuffer, bufferSize );

    __CPROVER_assert( ( sntpStatus == SntpErrorBadParameter || sntpStatus == SntpErrorBufferTooSmall || sntpStatus == SntpSuccess ), "The return value is not a valid SNTP Status" );
}
