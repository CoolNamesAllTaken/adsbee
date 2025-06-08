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
 * @file SigV4_AwsIotDateToIso8601_harness.c
 * @brief Implements the proof harness for SigV4_AwsIotDateToIso8601 function.
 */

#include "stdlib.h"
#include "sigv4.h"

void harness()
{
    char * pInputDate;
    size_t dateLen;
    char * pDateISO8601;
    size_t dateISO8601Len;
    SigV4Status_t status;

    __CPROVER_assume( dateLen == SIGV4_EXPECTED_LEN_RFC_3339 || dateLen == SIGV4_EXPECTED_LEN_RFC_5322 || dateLen == 0 );

    pInputDate = malloc( dateLen );

    __CPROVER_assume( dateISO8601Len < CBMC_MAX_OBJECT_SIZE );

    pDateISO8601 = malloc( dateISO8601Len );

    status = SigV4_AwsIotDateToIso8601( pInputDate, dateLen, pDateISO8601, dateISO8601Len );

    __CPROVER_assert( status == SigV4InvalidParameter || status == SigV4Success || status == SigV4ISOFormattingError, "This is not a valid SigV4 return status" );
}
