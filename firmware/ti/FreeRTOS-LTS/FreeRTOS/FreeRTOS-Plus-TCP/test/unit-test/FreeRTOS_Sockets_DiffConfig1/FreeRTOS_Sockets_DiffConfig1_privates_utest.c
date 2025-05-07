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

#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_Sockets_DiffConfig1_list_macros.h"
#include "mock_FreeRTOS_IP_Private.h"

#include "FreeRTOS_Sockets.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

BaseType_t prvDetermineSocketSize( BaseType_t xDomain,
                                   BaseType_t xType,
                                   BaseType_t xProtocol,
                                   size_t * pxSocketSize );

BaseType_t xTCPWindowLoggingLevel = 0;

/* ============================== Test Cases ============================== */

/**
 * @brief Happy path with TCP socket size being determined.
 */
void test_prvDetermineSocketSize_TCPSocket( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    size_t xSocketSize;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    xReturn = prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), xSocketSize );
}

/**
 * @brief Happy path with TCPv6 socket size being determined.
 * But IPv6 is disabled.
 */
void test_prvDetermineSocketSize_TCPv6Socket( void )
{
    BaseType_t xDomain = FREERTOS_AF_INET6, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    size_t xSocketSize;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

/**
 * @brief Trying to bind an NULL bind address.
 */
void test_vSocketBind_CatchAssert( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxAddressLength;
    BaseType_t xInternal;

    memset( &xSocket, 0, sizeof( xSocket ) );

    catch_assert( vSocketBind( &xSocket, NULL, uxAddressLength, xInternal ) );
}
