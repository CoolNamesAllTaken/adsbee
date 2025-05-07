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
#include "mock_Sockets_DiffConfig_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_portable.h"

#include "FreeRTOSIPConfig.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_Routing.h"

#include "FreeRTOS_Sockets.h"

#include "catch_assert.h"

/* ============================ EXTERN VARIABLES ============================ */

BaseType_t xTCPWindowLoggingLevel = 0;

/* =============================== Test Cases =============================== */

/**
 * @brief Binding successful.
 */
void test_vSocketBind_TCP( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xReturn = vSocketBind( &xSocket, NULL, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRNOTAVAIL, xReturn );
}

/**
 * @brief Binding successful.
 */
void test_vSocketBind_TCP1( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( &xEndPoint );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
}
