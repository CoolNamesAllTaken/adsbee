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

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_Sockets_DiffConfig1_list_macros.h"

#include "FreeRTOS_Sockets.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* ============================ EXTERN VARIABLES ============================ */

/* 2001::1 */
static const IPv6_Address_t xIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

BaseType_t xTCPWindowLoggingLevel = 0;

/* =============================== Test Cases =============================== */

/**
 * @brief Can reuse IPv6 socket.
 * But IPv6 is disabled.
 */
void test_FreeRTOS_accept_ReuseIPv6Socket( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn, xPeerSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength = 0;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );
    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.eTCPState = eTCP_LISTEN;
    xServerSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
    xServerSocket.u.xTCP.pxPeerSocket = &xPeerSocket;
    xServerSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xServerSocket.u.xTCP.usRemotePort = 0x1234;
    xServerSocket.bits.bIsIPv6 = pdTRUE;
    memcpy( xServerSocket.u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( &xServerSocket, pxReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xServerSocket.u.xTCP.bits.bPassAccept );
    TEST_ASSERT_EQUAL( sizeof( xAddress ), xAddressLength );
}

/**
 * @brief Query socket type of IPv6 socket.
 */
void test_FreeRTOS_GetIPType_IPv6HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;

    xReturn = FreeRTOS_GetIPType( &xSocket );

    TEST_ASSERT_EQUAL( ipTYPE_IPv4, xReturn );
}
