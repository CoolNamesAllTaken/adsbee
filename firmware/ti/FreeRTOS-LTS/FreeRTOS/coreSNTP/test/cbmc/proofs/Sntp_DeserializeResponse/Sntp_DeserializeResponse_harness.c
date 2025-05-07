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
 * @file Sntp_DeserializeResponse_harness.c
 * @brief Implements the proof harness for Sntp_DeserializeResponse function.
 */

#include <stdint.h>
#include "core_sntp_serializer.h"

void harness()
{
    SntpTimestamp_t * pRequestTime;
    SntpTimestamp_t * pResponseRxTime;
    void * pResponseBuffer;
    size_t bufferSize;
    SntpResponseData_t * pParsedResponse;
    SntpStatus_t sntpStatus;

    __CPROVER_assume( bufferSize < CBMC_MAX_OBJECT_SIZE );

    pRequestTime = malloc( sizeof( SntpTimestamp_t ) );
    pResponseRxTime = malloc( sizeof( SntpTimestamp_t ) );
    pResponseBuffer = malloc( bufferSize );
    pParsedResponse = malloc( sizeof( SntpResponseData_t ) );

    sntpStatus = Sntp_DeserializeResponse( pRequestTime, pResponseRxTime, pResponseBuffer, bufferSize, pParsedResponse );

    __CPROVER_assert( ( sntpStatus == SntpErrorBadParameter ) || ( sntpStatus == SntpErrorBufferTooSmall ) ||
                      ( sntpStatus == SntpInvalidResponse ) || ( sntpStatus == SntpSuccess ) || ( sntpStatus == SntpRejectedResponseChangeServer ) ||
                      ( sntpStatus == SntpRejectedResponseRetryWithBackoff ) || ( sntpStatus == SntpRejectedResponseOtherCode ), "This is a valid sntp return status" );
}
