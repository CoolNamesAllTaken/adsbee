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

#include "FreeRTOSIPConfig.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Routing.h"

#include "catch_assert.h"

#include "FreeRTOS_TCP_Utils.h"

/* =========================== EXTERN VARIABLES =========================== */

FreeRTOS_Socket_t xSocket, * pxSocket;
NetworkEndPoint_t xEndPoint, * pxEndPoint;

/* ===========================  Unity Fixtures  =========================== */

/*! called before each test case */
void setUp( void )
{
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    pxSocket = NULL;
    pxEndPoint = NULL;
}

/* ============================== Test Cases ============================== */

/**
 * @brief Null socket handler.
 */
void test_prvSocketSetMSS_IPV6_NullSocket( void )
{
    prvSocketSetMSS_IPV6( NULL );
}

/**
 * @brief Null endpoint in socket handler.
 */
void test_prvSocketSetMSS_IPV6_NullEndPoint( void )
{
    pxSocket = &xSocket;
    pxSocket->pxEndPoint = NULL;

    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    prvSocketSetMSS_IPV6( pxSocket );
}

/**
 * @brief Pass with global IPv6 address.
 */
void test_prvSocketSetMSS_IPV6_GlobalAddress( void )
{
    uint32_t ulDiffSizeIPHeader = ( ipSIZE_OF_IPv6_HEADER - ipSIZE_OF_IPv4_HEADER );

    pxSocket = &xSocket;
    pxEndPoint = &xEndPoint;
    pxSocket->pxEndPoint = pxEndPoint;

    xIPv6_GetIPType_ExpectAndReturn( &( pxSocket->u.xTCP.xRemoteIP.xIP_IPv6 ), eIPv6_Global );
    FreeRTOS_min_uint32_ExpectAndReturn( tcpREDUCED_MSS_THROUGH_INTERNET, ipconfigTCP_MSS - ulDiffSizeIPHeader, ipconfigTCP_MSS - ulDiffSizeIPHeader );

    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    prvSocketSetMSS_IPV6( pxSocket );

    TEST_ASSERT_EQUAL( ipconfigTCP_MSS - ulDiffSizeIPHeader, pxSocket->u.xTCP.usMSS );
}

/**
 * @brief Pass with non global IPv6 address.
 */
void test_prvSocketSetMSS_IPV6_NonGlobalAddress( void )
{
    uint32_t ulDiffSizeIPHeader = ( ipSIZE_OF_IPv6_HEADER - ipSIZE_OF_IPv4_HEADER );

    pxSocket = &xSocket;
    pxEndPoint = &xEndPoint;
    pxSocket->pxEndPoint = pxEndPoint;

    xIPv6_GetIPType_ExpectAndReturn( &( pxSocket->u.xTCP.xRemoteIP.xIP_IPv6 ), eIPv6_Global + 1 );

    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    prvSocketSetMSS_IPV6( pxSocket );

    TEST_ASSERT_EQUAL( ipconfigTCP_MSS - ulDiffSizeIPHeader, pxSocket->u.xTCP.usMSS );
}
