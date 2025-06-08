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

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_task.h"
#include "mock_list.h"
#include "mock_queue.h"

#include "mock_FreeRTOS_DNS_Callback.h"
/*#include "mock_FreeRTOS_DNS_Cache.h" */
#include "mock_FreeRTOS_DNS_Parser.h"
/* #include "mock_FreeRTOS_DNS_Networking.h"*/
#include "mock_NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"


#include "catch_assert.h"
#include "FreeRTOS_DNS_Networking.h"

#include "FreeRTOSIPConfig.h"

#define LLMNR_ADDRESS     "freertos"
#define GOOD_ADDRESS      "www.freertos.org"
#define BAD_ADDRESS       "this is a bad address"
#define DOTTED_ADDRESS    "192.268.0.1"

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                struct freertos_addrinfo * /* pxAddressInfo */ );

/* ===========================   GLOBAL VARIABLES =========================== */
static int callback_called = 0;


/* ===========================  STATIC FUNCTIONS  =========================== */
static void dns_callback( const char * pcName,
                          void * pvSearchID,
                          uint32_t ulIPAddress )
{
    callback_called = 1;
}


/* ============================  TEST FIXTURES  ============================= */

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
    callback_called = 0;
}

/**
 * @brief calls at the end of each test case
 */
void tearDown( void )
{
}


/* =============================  TEST CASES  =============================== */

/**
 * @brief Ensures that when the socket is invalid, null is returned
 */
void test_CreateSocket_fail_socket( void )
{
    Socket_t s;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET,
                                     FREERTOS_SOCK_DGRAM,
                                     FREERTOS_IPPROTO_UDP,
                                     NULL );
    xSocketValid_ExpectAndReturn( NULL, pdFALSE );

    s = DNS_CreateSocket( 235 );

    TEST_ASSERT_EQUAL( NULL, s );
}

/**
 * @brief Happy path!
 */
void test_CreateSocket_success( void )
{
    Socket_t s;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET,
                                     FREERTOS_SOCK_DGRAM,
                                     FREERTOS_IPPROTO_UDP,
                                     ( Socket_t ) 235 );
    xSocketValid_ExpectAndReturn( ( Socket_t ) 235, pdTRUE );
    FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( 0 );
    FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( 0 );

    s = DNS_CreateSocket( 235 );

    TEST_ASSERT_EQUAL( ( Socket_t ) 235, s );
}

/**
 * @brief Ensures that when the socket could not be created or could not be found, null is returned
 */
void test_BindSocket_fail( void )
{
    struct freertos_sockaddr xAddress;
    Socket_t xSocket;
    uint16_t usPort;
    uint32_t ret;

    FreeRTOS_bind_ExpectAnyArgsAndReturn( 0 );

    ret = DNS_BindSocket( xSocket, usPort );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief  Happy path!
 */
void test_BindSocket_success( void )
{
    struct freertos_sockaddr xAddress;
    Socket_t xSocket;
    uint16_t usPort;
    uint32_t ret;

    FreeRTOS_bind_ExpectAnyArgsAndReturn( 1 );

    ret = DNS_BindSocket( xSocket, usPort );

    TEST_ASSERT_EQUAL( 1, ret );
}

/**
 * @brief  Happy path!
 */
void test_SendRequest_success( void )
{
    Socket_t s = ( Socket_t ) 123;
    uint32_t ret;
    struct freertos_sockaddr xAddress;
    struct xDNSBuffer pxDNSBuf;

    pxDNSBuf.uxPayloadLength = 1024;

    FreeRTOS_sendto_ExpectAnyArgsAndReturn( pxDNSBuf.uxPayloadLength );

    ret = DNS_SendRequest( s, &xAddress, &pxDNSBuf );

    TEST_ASSERT_EQUAL( pdTRUE, ret );
}

/**
 * @brief  Ensures that when SendTo fails false is returned
 */
void test_SendRequest_fail( void )
{
    Socket_t s = ( Socket_t ) 123;
    uint32_t ret;
    struct freertos_sockaddr xAddress;
    struct xDNSBuffer pxDNSBuf;

    pxDNSBuf.uxPayloadLength = 1024;
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1023 );

    ret = DNS_SendRequest( s, &xAddress, &pxDNSBuf );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief  Happy path!
 */
void test_ReadReply_success( void )
{
    Socket_t s = ( Socket_t ) 123;
    struct freertos_sockaddr xAddress;
    struct xDNSBuffer pxDNSBuf;
    BaseType_t xReturn;

    FreeRTOS_recvfrom_ExpectAnyArgsAndReturn( 600 );

    xReturn = DNS_ReadReply( s, &xAddress, &pxDNSBuf );

    TEST_ASSERT_EQUAL( 600, xReturn );
}

/**
 * @brief  Happy path!
 */
void test_CloseSocket_success( void )
{
    Socket_t s = ( Socket_t ) 123;

    FreeRTOS_closesocket_ExpectAndReturn( s, pdTRUE );

    DNS_CloseSocket( s );
}
