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
#include "mock_Sockets_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_portable.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_Stream_Buffer.h"

#include "FreeRTOS_Sockets.h"

#include "FreeRTOS_Sockets_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

BaseType_t prvTCPSendLoop( FreeRTOS_Socket_t * pxSocket,
                           const void * pvBuffer,
                           size_t uxDataLength,
                           BaseType_t xFlags );

extern List_t xBoundTCPSocketsList;

/* 2001::1 */
static IPv6_Address_t xIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

/* ============================== Test Cases ============================== */

/**
 * @brief Invalid parameters.
 */
void test_FreeRTOS_accept_InvalidParams( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );

    /* Invalid Protocol */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, pxReturn );

    /* NULL socket. */
    pxReturn = FreeRTOS_accept( NULL, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, pxReturn );

    /* Unbound Socket */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, pxReturn );

    /* Socket is not in listen mode. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.eTCPState = eTCP_LISTEN + 1;
    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, pxReturn );
}

/**
 * @brief Client socket is already taken.
 */
void test_FreeRTOS_accept_ClientSocketTaken( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn, xPeerSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );
    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );

    /* Invalid Protocol */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.eTCPState = eTCP_LISTEN;

    xServerSocket.u.xTCP.pxPeerSocket = &xPeerSocket;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Client socket is already taken.
 */
void test_FreeRTOS_accept_PeerSocketNullWithReuseSocket( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn, xPeerSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );
    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );

    /* Invalid Protocol */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.eTCPState = eTCP_LISTEN;

    xServerSocket.u.xTCP.pxPeerSocket = NULL;
    xServerSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xServerSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( &xServerSocket, pxReturn );
    TEST_ASSERT_EQUAL( NULL, xServerSocket.u.xTCP.pxPeerSocket );
}

/**
 * @brief Peer socket is NULL.
 */
void test_FreeRTOS_accept_PeerSocketNULL( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn, xPeerSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );
    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xServerSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xServerSocket.u.xTCP.eTCPState = eTCP_LISTEN;

    xServerSocket.u.xTCP.pxPeerSocket = NULL;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( NULL, pxReturn );
    TEST_ASSERT_EQUAL( NULL, xServerSocket.u.xTCP.pxPeerSocket );
}

/**
 * @brief Cannot reuse the socket.
 */
void test_FreeRTOS_accept_NotReuseSocket( void )
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

    xServerSocket.u.xTCP.pxPeerSocket = &xPeerSocket;
    xPeerSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xPeerSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = 0xAABBCCDD;
    xPeerSocket.u.xTCP.usRemotePort = 0x1234;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( &xPeerSocket, pxReturn );
    TEST_ASSERT_EQUAL( NULL, xServerSocket.u.xTCP.pxPeerSocket );
    TEST_ASSERT_EQUAL( pdFALSE, xPeerSocket.u.xTCP.bits.bPassAccept );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohl( xPeerSocket.u.xTCP.xRemoteIP.ulIP_IPv4 ), xAddress.sin_address.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xPeerSocket.u.xTCP.usRemotePort ), xAddress.sin_port );
    TEST_ASSERT_EQUAL( sizeof( xAddress ), xAddressLength );
}

/**
 * @brief Can reuse socket.
 */
void test_FreeRTOS_accept_ReuseSocket( void )
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
    xServerSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = 0xAABBCCDD;
    xServerSocket.u.xTCP.usRemotePort = 0x1234;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( &xServerSocket, pxReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xServerSocket.u.xTCP.bits.bPassAccept );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohl( xServerSocket.u.xTCP.xRemoteIP.ulIP_IPv4 ), xAddress.sin_address.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xServerSocket.u.xTCP.usRemotePort ), xAddress.sin_port );
    TEST_ASSERT_EQUAL( sizeof( xAddress ), xAddressLength );
}

/**
 * @brief Accept while passing NULL in address.
 */
void test_FreeRTOS_accept_ReuseSocket_NULLAddress( void )
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
    xServerSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = 0xAABBCCDD;
    xServerSocket.u.xTCP.usRemotePort = 0x1234;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    pxReturn = FreeRTOS_accept( &xServerSocket, NULL, NULL );
    TEST_ASSERT_EQUAL( &xServerSocket, pxReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xServerSocket.u.xTCP.bits.bPassAccept );
}

/**
 * @brief Can reuse socket. Timeout happens.
 */
void test_FreeRTOS_accept_ReuseSocket_Timeout( void )
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
    xServerSocket.u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;
    xServerSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = 0xAABBCCDD;
    xServerSocket.u.xTCP.usRemotePort = 0x1234;
    xServerSocket.xReceiveBlockTime = 0xAA;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xServerSocket.xEventGroup, eSOCKET_ACCEPT, pdTRUE, pdFALSE, 0xAA, pdFALSE );

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = FreeRTOS_accept( &xServerSocket, &xAddress, &xAddressLength );
    TEST_ASSERT_EQUAL( NULL, pxReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xServerSocket.u.xTCP.bits.bPassAccept );
}

/**
 * @brief Can reuse IPv6 socket.
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
    TEST_ASSERT_EQUAL_MEMORY( xAddress.sin_address.xIP_IPv6.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xServerSocket.u.xTCP.usRemotePort ), xAddress.sin_port );
    TEST_ASSERT_EQUAL( sizeof( xAddress ), xAddressLength );
}

/**
 * @brief Can reuse IPv6 socket.
 */
void test_FreeRTOS_accept_ReuseIPv6Socket_NullAddress( void )
{
    FreeRTOS_Socket_t xServerSocket, * pxReturn, xPeerSocket;
    socklen_t xAddressLength = 0;

    memset( &xServerSocket, 0, sizeof( xServerSocket ) );
    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );

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

    pxReturn = FreeRTOS_accept( &xServerSocket, NULL, &xAddressLength );
    TEST_ASSERT_EQUAL( &xServerSocket, pxReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xServerSocket.u.xTCP.bits.bPassAccept );
}

/**
 * @brief Invalid values.
 */
void test_FreeRTOS_recv_InvalidValues( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* NULL socket. */
    xReturn = FreeRTOS_recv( NULL, pvBuffer, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Unbound Socket */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    xFlags = FREERTOS_ZERO_COPY;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xReturn = FreeRTOS_recv( &xSocket, NULL, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Not connected socket and there is no memory in the system.
 */
void test_FreeRTOS_recv_NotConnectedAndNoMemory( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOTCONN, xReturn );

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bMallocError = pdTRUE_UNSIGNED;
    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOMEM, xReturn );
}

/**
 * @brief No wait in an established connection.
 */
void test_FreeRTOS_recv_EstablishedConnection_NoWait( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_INTR, pdTRUE, pdFALSE, 0, 0 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Timeout occurs.
 */
void test_FreeRTOS_recv_TimeOut( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Receive interrupted.
 */
void test_FreeRTOS_recv_Interrupted( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED | ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0xAA, eSOCKET_INTR );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINTR, xReturn );
}

/**
 * @brief Receive interrupted.
 */
void test_FreeRTOS_recv_Interrupted1( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED | ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0xAA, eSOCKET_RECEIVE | eSOCKET_CLOSED | eSOCKET_INTR );

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE | eSOCKET_CLOSED, 0 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINTR, xReturn );
}

/**
 * @brief Receive stream is NULl for the socket.
 */
void test_FreeRTOS_recv_RxStreamNULL( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED | ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0xAA, 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief 12 bytes are present in the Buffer when receive is called.
 */
void test_FreeRTOS_recv_12BytesAlreadyInBuffer( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) pvBuffer;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    uxStreamBufferGet_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0U, pvBuffer, ( size_t ) uxBufferLength, 0, 12 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 12, xReturn );
}

/**
 * @brief Low water mark reached when receive is called.
 */
void test_FreeRTOS_recv_LowWaterReached( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) pvBuffer;
    xSocket.u.xTCP.bits.bLowWater = pdTRUE_UNSIGNED;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    uxStreamBufferGet_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0U, pvBuffer, ( size_t ) uxBufferLength, 0, 12 );

    uxStreamBufferFrontSpace_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdTRUE );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 12, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1U, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Low water mark reached when receive is called.
 */
void test_FreeRTOS_recv_LowWaterReached2( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) pvBuffer;
    xSocket.u.xTCP.bits.bLowWater = pdTRUE_UNSIGNED;
    xSocket.u.xTCP.uxEnoughSpace = 13;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    uxStreamBufferGet_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0U, pvBuffer, ( size_t ) uxBufferLength, 0, 12 );

    uxStreamBufferFrontSpace_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 12, xReturn );
}

/**
 * @brief 12 bytes arrive to the socket after a call to receive is made.
 */
void test_FreeRTOS_recv_12BytesArriveLater( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) pvBuffer;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE | ( EventBits_t ) eSOCKET_CLOSED | ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0xAA, 0 );

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 12 );

    uxStreamBufferGetPtr_ExpectAndReturn( xSocket.u.xTCP.rxStream, ( uint8_t ** ) pvBuffer, 12 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 12, xReturn );
}

/**
 * @brief 12 bytes arrive to the socket after a call to receive is made and a timeout occurs.
 */
void test_FreeRTOS_recv_12BytesArriveLater_Timeout( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = FREERTOS_ZERO_COPY | FREERTOS_MSG_DONTWAIT;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) pvBuffer;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Socket is closing in receive procedure.
 */
void test_FreeRTOS_recv_SocketClosing( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eCLOSING;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) pvBuffer;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOTCONN, xReturn );
}

/**
 * @brief Socket is in eClose_Wait in receive procedure.
 */
void test_FreeRTOS_recv_SocketCloseWait( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 1500 ];
    size_t uxBufferLength = 1500;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;

    memset( &xSocket, 0, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eCLOSE_WAIT;
    xSocket.xReceiveBlockTime = 0xAA;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) pvBuffer;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.rxStream, 0 );

    xReturn = FreeRTOS_recv( &xSocket, pvBuffer, uxBufferLength, xFlags );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOTCONN, xReturn );
}

/**
 * @brief Invalid parameters passed to the function.
 */
void test_FreeRTOS_get_tx_head_InvalidParams( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    pucReturn = FreeRTOS_get_tx_head( &xSocket, &xLength );
    TEST_ASSERT_EQUAL( NULL, pucReturn );

    /* NULL socket. */
    pucReturn = FreeRTOS_get_tx_head( NULL, &xLength );
    TEST_ASSERT_EQUAL( NULL, pucReturn );
}

/**
 * @brief Socket with stream not yet created is passed to the function.
 */
void test_FreeRTOS_get_tx_head_NoStream( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xLength;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    const size_t uxRemainingSize = 5;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucStream, 0, ipconfigTCP_MSS );

    /* NULL stream. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    pvPortMalloc_ExpectAnyArgsAndReturn( ucStream );
    uxStreamBufferGetSpace_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, uxRemainingSize );
    pucReturn = FreeRTOS_get_tx_head( &xSocket, &xLength );
    TEST_ASSERT_EQUAL_PTR( &( ( ( StreamBuffer_t * ) ucStream )->ucArray[ 0 ] ), pucReturn );
    TEST_ASSERT_EQUAL( uxRemainingSize, xLength );
}

/**
 * @brief Socket with stream not created but malloc failed previously.
 */
void test_FreeRTOS_get_tx_head_NoStreamMallocError( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* NULL stream. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bMallocError = pdTRUE_UNSIGNED;
    pucReturn = FreeRTOS_get_tx_head( &xSocket, &xLength );
    TEST_ASSERT_EQUAL_PTR( NULL, pucReturn );
    TEST_ASSERT_EQUAL( 0, xLength );
}

/**
 * @brief All fields of the socket are NULL.
 */
void test_FreeRTOS_get_tx_head_AllNULL( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xLength;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucStream, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    uxStreamBufferGetSpace_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0 );

    pucReturn = FreeRTOS_get_tx_head( &xSocket, &xLength );
    TEST_ASSERT_EQUAL_PTR( ( ( StreamBuffer_t * ) ucStream )->ucArray, pucReturn );
    TEST_ASSERT_EQUAL( 0, xLength );
}

/**
 * @brief Less space in the head than total length.
 */
void test_FreeRTOS_get_tx_head_LessSpace( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xLength;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucStream, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    ( ( StreamBuffer_t * ) ucStream )->LENGTH = 20;
    ( ( StreamBuffer_t * ) ucStream )->uxHead = 10;

    uxStreamBufferGetSpace_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 10 );

    pucReturn = FreeRTOS_get_tx_head( &xSocket, &xLength );
    TEST_ASSERT_EQUAL_PTR( &( ( ( StreamBuffer_t * ) ucStream )->ucArray[ 10 ] ), pucReturn );
    TEST_ASSERT_EQUAL( 10, xLength );
}

/**
 * @brief More space in the head than total length.
 */
void test_FreeRTOS_get_tx_head_MoreSpace( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xLength;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucStream, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    ( ( StreamBuffer_t * ) ucStream )->LENGTH = 200;
    ( ( StreamBuffer_t * ) ucStream )->uxHead = 10;

    uxStreamBufferGetSpace_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 10 );

    pucReturn = FreeRTOS_get_tx_head( &xSocket, &xLength );
    TEST_ASSERT_EQUAL_PTR( &( ( ( StreamBuffer_t * ) ucStream )->ucArray[ 10 ] ), pucReturn );
    TEST_ASSERT_EQUAL( 10, xLength );
}

/**
 * @brief Invalid inputs to the function.
 */
void test_FreeRTOS_send_InvalidInput( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    uxDataLength = 0;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );
    TEST_ASSERT_EQUAL( 0, xReturn );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 0 );
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );
    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOSPC, xReturn );

    /* Socket is not connected any more. */
    xSocket.u.xTCP.eTCPState = eESTABLISHED + 1;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 0 );
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );
    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOTCONN, xReturn );
}

/**
 * @brief There is exact amount of space in stream buffer as the length of data we want to send.
 */
void test_FreeRTOS_send_ExactSpaceInStreamBuffer( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags;
    StreamBuffer_t xLocalStreamBuffer;

    /* 1. Last set of bytes. */
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.u.xTCP.bits.bCloseAfterSend = pdTRUE_UNSIGNED;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength );
    vTaskSuspendAll_Expect();
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength, uxDataLength );
    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bCloseRequested );


    /* 2. Not last set of bytes. */
    xSocket.u.xTCP.bits.bCloseAfterSend = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.bits.bCloseRequested = pdFALSE;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength, uxDataLength );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );
    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bCloseRequested );
}

/**
 * @brief There is more space in stream buffer than the length of data we want to send.
 */
void test_FreeRTOS_send_MoreSpaceInStreamBuffer( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.u.xTCP.bits.bCloseAfterSend = pdTRUE_UNSIGNED;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength + 20 );
    vTaskSuspendAll_Expect();
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength, uxDataLength );
    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );
    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bCloseRequested );
}

/**
 * @brief There is less space in stream buffer than the length of data we want to send, also a timeout happens.
 */
void test_FreeRTOS_send_LessSpaceInStreamBuffer_Timeout( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags = 0;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.u.xTCP.bits.bCloseAfterSend = pdTRUE_UNSIGNED;
    xSocket.xSendBlockTime = 100;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength - 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength - 20, uxDataLength - 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    vTaskSetTimeOutState_ExpectAnyArgs();
    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_SEND | eSOCKET_CLOSED, pdTRUE, pdFALSE, 100, pdFALSE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    /* Second Iteration. No space still. */
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength - 20, xReturn );
}

/**
 * @brief There is less space in stream buffer than the length of data we want to send. However,
 *        over time, space becomes available.
 */
void test_FreeRTOS_send_LessSpaceInStreamBuffer_EventuallySpaceAvailable( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags = 0;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.xSendBlockTime = 100;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength - 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength - 20, uxDataLength - 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    vTaskSetTimeOutState_ExpectAnyArgs();
    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_SEND | eSOCKET_CLOSED, pdTRUE, pdFALSE, 100, pdFALSE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    /* Second Iteration. */
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, &pvBuffer[ 80 ], 20, 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );

    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength, xReturn );
}

/**
 * @brief There is no space in stream buffer for multiple iterations.
 */
void test_FreeRTOS_send_MultipleIterationsAndNoSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags = 0;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.xSendBlockTime = 100;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength - 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength - 20, uxDataLength - 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    vTaskSetTimeOutState_ExpectAnyArgs();
    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_SEND | eSOCKET_CLOSED, pdTRUE, pdFALSE, 100, pdFALSE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    /* Second Iteration. */
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 10 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, &pvBuffer[ 80 ], 10, 10 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_SEND | eSOCKET_CLOSED, pdTRUE, pdFALSE, 100, pdFALSE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    /* Third iteration. No space still. */
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength - 10, xReturn );
}

/*
 * @brief While waiting for space, the socket gets disconnected.
 */
void test_FreeRTOS_send_DisconnectionOccursDuringWait( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags = 0;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.xSendBlockTime = 100;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength - 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength - 20, uxDataLength - 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    vTaskSetTimeOutState_ExpectAnyArgs();
    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_SEND | eSOCKET_CLOSED, pdTRUE, pdFALSE, 100, pdFALSE );

    /* Let `socketSOCKET_IS_BOUND()` return false, so that prvTCPSendCheck()
     * returns en error, so that the loop is stopped. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );

    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength - 20, xReturn );
}

/*
 * @brief IP task is calling send function with a NULL buffer (TCP zero copy).
 */
void test_FreeRTOS_send_IPTaskWithNULLBuffer( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxNettLength = 100;
    BaseType_t xFlags = 0;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xLocalStreamBuffer, 0, sizeof( xLocalStreamBuffer ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.xSendBlockTime = 100;

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxNettLength );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, NULL, uxNettLength, uxNettLength );
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xReturn = FreeRTOS_send( &xSocket, NULL, uxNettLength, xFlags );

    TEST_ASSERT_EQUAL( uxNettLength, xReturn );
}

/*
 * @brief IP task is calling send function with a NULL buffer (TCP zero copy). Also there are 20 bytes worth of space
 *        less in the stream buffer as the data length.
 */
void test_FreeRTOS_send_IPTaskWithNULLBuffer_LessSpaceInStreamBuffer( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags = 0;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.xSendBlockTime = 100;

    uxDataLength = 100;

    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength - 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, NULL, uxDataLength - 20, uxDataLength - 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xReturn = FreeRTOS_send( &xSocket, NULL, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength - 20, xReturn );
}

/**
 * @brief Send called with a don't wait flag when there is space in buffer.
 */
void test_FreeRTOS_send_DontWaitFlag( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags = FREERTOS_MSG_DONTWAIT;
    StreamBuffer_t xLocalStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.xSendBlockTime = 100;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength - 20 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength - 20, uxDataLength - 20 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength - 20, xReturn );
}

/**
 * @brief FreeRTOS_send is called from IP task.
 */
void test_FreeRTOS_send_ExactSpaceInStreamBufferInIPTask( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ ipconfigTCP_MSS ];
    size_t uxDataLength;
    BaseType_t xFlags;
    StreamBuffer_t xLocalStreamBuffer;

    /* 1. Last set of bytes. */
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( pvBuffer, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    xSocket.u.xTCP.bits.bCloseAfterSend = pdTRUE_UNSIGNED;

    uxDataLength = 100;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    uxStreamBufferGetSpace_ExpectAndReturn( xSocket.u.xTCP.txStream, uxDataLength );
    vTaskSuspendAll_Expect();
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, pvBuffer, uxDataLength, uxDataLength );
    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xReturn = FreeRTOS_send( &xSocket, pvBuffer, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength, xReturn );
}

/**
 * @brief Invalid values passed to listen.
 */
void test_FreeRTOS_listen_InvalidValues( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xBacklog;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* Unbound. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* NULL socket. */
    xReturn = FreeRTOS_listen( NULL, xBacklog );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* Invalid state. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );
}

/**
 * @brief Listen call successful.
 */
void test_FreeRTOS_listen_Success( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xBacklog = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eCLOSED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    FreeRTOS_min_int32_ExpectAndReturn( ( int32_t ) 0xffff, ( int32_t ) xBacklog, xBacklog );

    vTCPStateChange_Expect( &xSocket, eTCP_LISTEN );

    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( 0, xReturn );

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eCLOSE_WAIT;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    FreeRTOS_min_int32_ExpectAndReturn( ( int32_t ) 0xffff, ( int32_t ) xBacklog, xBacklog );

    vTCPStateChange_Expect( &xSocket, eTCP_LISTEN );

    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Listen call successful when socket is set to be reused.
 */
void test_FreeRTOS_listen_Success_WithReuseSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xBacklog = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eCLOSED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    memset( xSocket.u.xTCP.xPacket.u.ucLastPacket, 0xFF, sizeof( xSocket.u.xTCP.xPacket.u.ucLastPacket ) );
    memset( &xSocket.u.xTCP.xTCPWindow, 0xFF, sizeof( xSocket.u.xTCP.xTCPWindow ) );
    memset( &xSocket.u.xTCP.bits, 0xFF, sizeof( xSocket.u.xTCP.bits ) );

    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;

    FreeRTOS_min_int32_ExpectAndReturn( ( int32_t ) 0xffff, ( int32_t ) xBacklog, xBacklog );

    vTCPStateChange_Expect( &xSocket, eTCP_LISTEN );

    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bReuseSocket );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, xSocket.u.xTCP.xPacket.u.ucLastPacket, sizeof( xSocket.u.xTCP.xPacket.u.ucLastPacket ) );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xSocket.u.xTCP.xTCPWindow, sizeof( xSocket.u.xTCP.xTCPWindow ) );
}

/**
 * @brief Listen call successful when socket is set to be reused and the streams are non NULL.
 */
void test_FreeRTOS_listen_Success_WithReuseSocket_StreamsNonNULL( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xBacklog = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eCLOSED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    memset( xSocket.u.xTCP.xPacket.u.ucLastPacket, 0xFF, sizeof( xSocket.u.xTCP.xPacket.u.ucLastPacket ) );
    memset( &xSocket.u.xTCP.xTCPWindow, 0xFF, sizeof( xSocket.u.xTCP.xTCPWindow ) );
    memset( &xSocket.u.xTCP.bits, 0xFF, sizeof( xSocket.u.xTCP.bits ) );

    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) &xReturn;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) &xReturn;

    FreeRTOS_min_int32_ExpectAndReturn( ( int32_t ) 0xffff, ( int32_t ) xBacklog, xBacklog );

    vStreamBufferClear_Expect( xSocket.u.xTCP.rxStream );
    vStreamBufferClear_Expect( xSocket.u.xTCP.txStream );

    vTCPStateChange_Expect( &xSocket, eTCP_LISTEN );

    xReturn = FreeRTOS_listen( &xSocket, xBacklog );
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bReuseSocket );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, xSocket.u.xTCP.xPacket.u.ucLastPacket, sizeof( xSocket.u.xTCP.xPacket.u.ucLastPacket ) );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &xSocket.u.xTCP.xTCPWindow, sizeof( xSocket.u.xTCP.xTCPWindow ) );
}

/**
 * @brief Invalid values passed to shutdown.
 */
void test_FreeRTOS_shutdown_Invalid( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xHow;
    int i;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xReturn = FreeRTOS_shutdown( &xSocket, xHow );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* Unbound. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xReturn = FreeRTOS_shutdown( &xSocket, xHow );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* NULL socket. */
    xReturn = FreeRTOS_shutdown( NULL, xHow );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EOPNOTSUPP, xReturn );

    /* Invalid state. */
    for( i = 0; i < 255; i++ )
    {
        if( i != eESTABLISHED )
        {
            xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
            xSocket.u.xTCP.eTCPState = i;
            listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
            xReturn = FreeRTOS_shutdown( &xSocket, xHow );
            TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOTCONN, xReturn );
        }
    }
}

/**
 * @brief Call to shutdown successful.
 */
void test_FreeRTOS_shutdown_Success( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xHow;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFALSE );

    xReturn = FreeRTOS_shutdown( &xSocket, xHow );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bUserShutdown );
    TEST_ASSERT_EQUAL( 1U, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Invalid inputs.
 */
void test_FreeRTOS_get_rx_buf_InvalidInput( void )
{
    const struct xSTREAM_BUFFER * pxReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    pxReturn = FreeRTOS_get_rx_buf( &xSocket );
    TEST_ASSERT_EQUAL( NULL, pxReturn );

    /* NULL socket. */
    pxReturn = FreeRTOS_get_rx_buf( NULL );
    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Happy path.
 */
void test_FreeRTOS_get_rx_buf_ValidInput( void )
{
    const struct xSTREAM_BUFFER * pxReturn;
    struct xSTREAM_BUFFER xStream;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* NULL socket. */
    xSocket.u.xTCP.rxStream = &xStream;
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    pxReturn = FreeRTOS_get_rx_buf( &xSocket );
    TEST_ASSERT_EQUAL( &xStream, pxReturn );
}


/**
 * @brief Invalid protocol passed to the function.
 */
void test_FreeRTOS_tx_space_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_tx_space( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief The stream is NULL in this case.
 */
void test_FreeRTOS_tx_space_NULLStream( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.uxTxStreamSize = 0xBB;
    xReturn = FreeRTOS_tx_space( &xSocket );
    TEST_ASSERT_EQUAL( 0xBB, xReturn );
}

/**
 * @brief Stream is valid. Happy path.
 */
void test_FreeRTOS_tx_space_ValidStream( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t ucStream[ 20 ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    uxStreamBufferGetSpace_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0xABCD );

    xReturn = FreeRTOS_tx_space( &xSocket );
    TEST_ASSERT_EQUAL( 0xABCD, xReturn );
}

/**
 * @brief All combination of inputs. See below comments.
 */
void test_FreeRTOS_tx_size( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t ucStream[ 20 ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_tx_size( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Valid Protocol. Stream NULL. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xReturn = FreeRTOS_tx_size( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    /* Valid Protocol. Stream non-NULL. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;
    uxStreamBufferGetSize_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0x345 );
    xReturn = FreeRTOS_tx_size( &xSocket );
    TEST_ASSERT_EQUAL( 0x345, xReturn );
}

/**
 * @brief All combination of inputs. See below comments.
 */
void test_FreeRTOS_issocketconnected( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_issocketconnected( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Valid Protocol. Invalid State. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED - 1;
    xReturn = FreeRTOS_issocketconnected( &xSocket );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    /* Valid Protocol. Invalid State. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eCLOSE_WAIT;
    xReturn = FreeRTOS_issocketconnected( &xSocket );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    /* Valid Protocol. Valid State. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eCLOSE_WAIT - 1;
    xReturn = FreeRTOS_issocketconnected( &xSocket );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}


/**
 * @brief All combination of inputs. See below comments.
 */
void test_FreeRTOS_mss( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_mss( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Valid Protocol. Invalid State. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.usMSS = 0xFD;
    xReturn = FreeRTOS_mss( &xSocket );
    TEST_ASSERT_EQUAL( 0xFD, xReturn );
}

/**
 * @brief All combination of inputs. See below comments.
 */
void test_FreeRTOS_connstatus( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t i;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_connstatus( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Valid Protocol. Invalid State. */
    for( i = 0; i < 125; i++ )
    {
        xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
        xSocket.u.xTCP.eTCPState = i;
        xReturn = FreeRTOS_connstatus( &xSocket );
        TEST_ASSERT_EQUAL( i, xReturn );
    }
}

/**
 * @brief All combination of inputs. See below comments.
 */
void test_FreeRTOS_rx_size( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t ucStream[ 20 ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_rx_size( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Valid Protocol. Stream NULL. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xReturn = FreeRTOS_rx_size( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    /* Valid Protocol. Stream non-NULL. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) ucStream;
    uxStreamBufferGetSize_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0xAB );
    xReturn = FreeRTOS_rx_size( &xSocket );
    TEST_ASSERT_EQUAL( 0xAB, xReturn );
}

/**
 * @brief Send zero byte via prvTCPSendLoop.
 */
void test_prvTCPSendLoop_ZeroByte()
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t pvBuffer[ 10 ];
    BaseType_t xFlags = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetSpace_IgnoreAndReturn( 0 );

    xReturn = prvTCPSendLoop( &xSocket, pvBuffer, 0, xFlags );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Send NULL buffer via prvTCPSendLoop.
 */
void test_prvTCPSendLoop_NullBuffer()
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xFlags = 0;
    size_t uxDataLength = 100;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetSpace_IgnoreAndReturn( 100 );
    uxStreamBufferAdd_ExpectAndReturn( xSocket.u.xTCP.txStream, 0U, NULL, uxDataLength, uxDataLength );
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xReturn = prvTCPSendLoop( &xSocket, NULL, uxDataLength, xFlags );

    TEST_ASSERT_EQUAL( uxDataLength, xReturn );
}

/**
 * @brief Invalid parameters passed to the function.
 */
void test_FreeRTOS_get_tx_base_InvalidParams( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xLength;
    size_t uxLength = 128;
    size_t uxMallocSize;
    StreamBuffer_t * pxBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.u.xTCP.uxTxStreamSize = uxLength;

    /* Invalid Protocol. */
    pucReturn = FreeRTOS_get_tx_base( &xSocket );
    TEST_ASSERT_EQUAL( NULL, pucReturn );

    /* NULL socket. */
    pucReturn = FreeRTOS_get_tx_base( NULL );
    TEST_ASSERT_EQUAL( NULL, pucReturn );

/*  FAIL: Memory Mismatch. Byte 0 Expected 0xB0 Was 0xE0. */
/*  Function pvPortMalloc Argument xSize. Function called with unexpected argument value. */

    /* Add an extra 4 (or 8) bytes. */
    uxLength += sizeof( size_t );

    /* And make the length a multiple of sizeof( size_t ). */
    uxLength &= ~( sizeof( size_t ) - 1U );

    uxMallocSize = ( sizeof( *pxBuffer ) + uxLength ) - sizeof( pxBuffer->ucArray );

    pvPortMalloc_ExpectAndReturn( uxMallocSize, NULL );

    vTCPStateChange_Expect( &xSocket, eCLOSE_WAIT );

    /* NULL stream. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    pucReturn = FreeRTOS_get_tx_base( &xSocket );
    TEST_ASSERT_EQUAL( NULL, pucReturn );

    xSocket.u.xTCP.bits.bMallocError == pdTRUE_UNSIGNED;
    pucReturn = FreeRTOS_get_tx_base( &xSocket );
    TEST_ASSERT_EQUAL( NULL, pucReturn );
}

/**
 * @brief All fields of the socket are NULL.
 */
void test_FreeRTOS_get_tx_base_AllNULL( void )
{
    uint8_t * pucReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( ucStream, 0, ipconfigTCP_MSS );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    pucReturn = FreeRTOS_get_tx_base( &xSocket );
    TEST_ASSERT_EQUAL_PTR( ( ( StreamBuffer_t * ) ucStream )->ucArray, pucReturn );
}
