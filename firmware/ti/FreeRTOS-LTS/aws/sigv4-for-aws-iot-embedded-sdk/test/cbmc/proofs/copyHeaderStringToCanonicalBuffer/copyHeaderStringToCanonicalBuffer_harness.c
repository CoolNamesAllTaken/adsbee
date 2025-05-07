/*
 * SigV4 Library v1.3.0
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
 * @file copyHeaderStringToCanonicalBuffer_harness.c
 * @brief Implements the proof harness for copyHeaderStringToCanonicalBuffer function.
 */
#include "stdlib.h"
#include "sigv4_annex.h"

void harness()
{
    const char * pData;
    size_t dataLen;
    uint32_t flags;
    char separator;
    CanonicalContext_t * canonicalRequest;
    SigV4Status_t sigv4Status;

    canonicalRequest = malloc( sizeof( CanonicalContext_t ) );

    __CPROVER_assume( canonicalRequest != NULL );


    /* The data to be written is assumed to start at a location within the processing
     * buffer and should not end past the length of the processing buffer. */
    size_t bytesConsumed;

    __CPROVER_assume( canonicalRequest->bufRemaining < SIGV4_PROCESSING_BUFFER_LENGTH );
    bytesConsumed = SIGV4_PROCESSING_BUFFER_LENGTH - canonicalRequest->bufRemaining;
    __CPROVER_assume( dataLen > 0U && dataLen < CBMC_MAX_BUFSIZE );
    canonicalRequest->uxCursorIndex = bytesConsumed;

    pData = malloc( dataLen );

    __CPROVER_assume( pData != NULL );

    sigv4Status = copyHeaderStringToCanonicalBuffer( pData, dataLen, flags, separator, canonicalRequest );

    __CPROVER_assert( ( sigv4Status == SigV4InvalidParameter || sigv4Status == SigV4Success || sigv4Status == SigV4InsufficientMemory ), "This is not a valid SIGV4 Status." );
}
