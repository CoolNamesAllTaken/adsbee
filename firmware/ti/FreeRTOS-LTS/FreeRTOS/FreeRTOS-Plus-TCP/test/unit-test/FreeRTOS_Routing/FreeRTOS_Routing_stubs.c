/*
 * FreeRTOS+TCP V4.2.2
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* ===========================  EXTERN VARIABLES  =========================== */

BaseType_t xStubFreeRTOS_inet_ntop_TargetFamily;
const void * pvStubFreeRTOS_inet_ntop_TargetSource;
char * pcStubFreeRTOS_inet_ntop_TargetDestination;
uint32_t ulStubFreeRTOS_inet_ntop_TargetSize;
const char * pcStubFreeRTOS_inet_ntop_TargetCopySource;
uint32_t ulStubFreeRTOS_inet_ntop_CopySize;

/* ======================== Stub Callback Functions ========================= */

const char * pcStubFreeRTOS_inet_ntop( BaseType_t xAddressFamily,
                                       const void * pvSource,
                                       char * pcDestination,
                                       uint32_t ulSize,
                                       int NumCalls )
{
    ( void ) NumCalls;

    TEST_ASSERT_EQUAL( xStubFreeRTOS_inet_ntop_TargetFamily, xAddressFamily );
    TEST_ASSERT_EQUAL( pvStubFreeRTOS_inet_ntop_TargetSource, pvSource );
    TEST_ASSERT_EQUAL( pcStubFreeRTOS_inet_ntop_TargetDestination, pcDestination );
    TEST_ASSERT_EQUAL( ulStubFreeRTOS_inet_ntop_TargetSize, ulSize );

    if( ( pcDestination != NULL ) && ( pcStubFreeRTOS_inet_ntop_TargetCopySource != NULL ) )
    {
        memcpy( pcDestination, pcStubFreeRTOS_inet_ntop_TargetCopySource, ulStubFreeRTOS_inet_ntop_CopySize );
    }
}
