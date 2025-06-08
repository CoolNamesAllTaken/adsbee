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

#include "mock_FreeRTOS_IP_Private.h"
#include "mock_NetworkBufferManagement.h"

#include "FreeRTOS_Sockets.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* ============================ EXTERN VARIABLES ============================ */

/* 2001::1 */
static const IPv6_Address_t xIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

BaseType_t xTCPWindowLoggingLevel = 0;

/* ============================== Test Cases ============================== */

/**
 * @brief Binding already bound socket.
 * And the family of destination address is set as invalid value.
 */
void test_FreeRTOS_bind_SocketIsAlreadyBound_UseTempDestinationAddress( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xAddress, 0, sizeof( xAddress ) );
    xAddress.sin_family = FREERTOS_AF_INET + 1;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xReturn = FreeRTOS_bind( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Binding already bound socket.
 * And the family of destination address is set as FREERTOS_AF_INET6.
 */
void test_FreeRTOS_bind_SocketIsAlreadyBound_IPv6DestinationAddress( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xAddress, 0, sizeof( xAddress ) );
    xAddress.sin_family = FREERTOS_AF_INET6;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xReturn = FreeRTOS_bind( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Binding already bound socket.
 * And the family of destination address is set as FREERTOS_AF_INET.
 */
void test_FreeRTOS_bind_SocketIsAlreadyBound_IPv4DestinationAddress( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xAddress, 0, sizeof( xAddress ) );
    xAddress.sin_family = FREERTOS_AF_INET;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xReturn = FreeRTOS_bind( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Binding already bound socket.
 * And the destination address is NULL.
 */
void test_FreeRTOS_bind_SocketIsAlreadyBound_NullDestinationAddress( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xReturn = FreeRTOS_bind( &xSocket, NULL, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief All fields are NULL in the socket.
 */
void test_FreeRTOS_connect_SocketValuesNULL_UseTempDestinationAddress( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xAddress, 0, sizeof( xAddress ) );
    xAddress.sin_family = FREERTOS_AF_INET6 + 1;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EBADF, xResult );
}

/**
 * @brief All fields are NULL in the socket.
 * And the family of destination address is set as FREERTOS_AF_INET6.
 */
void test_FreeRTOS_connect_SocketValuesNULL_IPv6DestinationAddress( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xAddress, 0, sizeof( xAddress ) );
    xAddress.sin_family = FREERTOS_AF_INET6;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EBADF, xResult );
}

/**
 * @brief All fields are NULL in the socket.
 * And the family of destination address is set as FREERTOS_AF_INET.
 */
void test_FreeRTOS_connect_SocketValuesNULL_IPv4DestinationAddress( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xAddress, 0, sizeof( xAddress ) );
    xAddress.sin_family = FREERTOS_AF_INET;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EBADF, xResult );
}

/**
 * @brief All fields are NULL in the socket.
 * And the destination address is NULL.
 */
void test_FreeRTOS_connect_SocketValuesNULL_NullDestinationAddress( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    socklen_t xAddressLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xResult = FreeRTOS_connect( &xSocket, NULL, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xResult );
}

/**
 * @brief Get UDPv6 packets property string.
 * But IPv6 is disabled.
 */
void test_prvSocketProps_UDPv6()
{
    FreeRTOS_Socket_t xSocket;
    const IPv6_Address_t * pxIPv6SrcAddress = &xIPv6Address; /* 2001::1 */
    uint16_t usSrcPort = 1024U;
    const char * pcReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.bits.bIsIPv6 = pdTRUE;
    memcpy( xSocket.xLocalAddress.xIP_IPv6.ucBytes, pxIPv6SrcAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xSocket.usLocalPort = usSrcPort;

    pcReturn = prvSocketProps( &xSocket );
}

/**
 * @brief Get TCPv6 packets property string.
 * But IPv6 is disabled.
 */
void test_prvSocketProps_TCPv6()
{
    FreeRTOS_Socket_t xSocket;
    const IPv6_Address_t * pxIPv6SrcAddress = &xIPv6Address;                                                                                    /* 2001::1 */
    IPv6_Address_t xIPv6RemoteAddress = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 } }; /* 2001::2 */
    uint16_t usSrcPort = 1024U;
    uint16_t usRemotePort = 2048U;
    const char * pcReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.bits.bIsIPv6 = pdTRUE;
    memcpy( xSocket.xLocalAddress.xIP_IPv6.ucBytes, pxIPv6SrcAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xSocket.usLocalPort = usSrcPort;
    memcpy( xSocket.u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, xIPv6RemoteAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xSocket.u.xTCP.usRemotePort = usRemotePort;

    pcReturn = prvSocketProps( &xSocket );
}

/**
 * @brief Get local address from an IPv6 socket.
 * But IPv6 is disabled.
 */
void test_FreeRTOS_GetLocalAddress_IPv6( void )
{
    size_t uxReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    IPv6_Address_t xIPAddress = { { 0x20 } };

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.bits.bIsIPv6 = pdTRUE;
    xSocket.usLocalPort = 0xAB12;
    memcpy( xSocket.xLocalAddress.xIP_IPv6.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    uxReturn = FreeRTOS_GetLocalAddress( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( 0, xAddress.sin_family );
}

/**
 * @brief IPv6 happy path.
 * But IPv6 is disabled.
 */
void test_FreeRTOS_GetRemoteAddress_IPv6HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    memcpy( xSocket.u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xSocket.u.xTCP.usRemotePort = 0x1234;

    xReturn = FreeRTOS_GetRemoteAddress( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( sizeof( xAddress ), xReturn );
}

/**
 * @brief Query socket type of IPv6 socket.
 * But IPv6 is disabled, it always return IPv4.
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

/**
 * @brief This function just prints out some data.
 * But IPv6 is disabled.
 */
void test_vTCPNetStat_IPv6Socket( void )
{
    ListItem_t xLocalTCPItem, xLocalUDPItem, xIterator;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( 0 );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 0 );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    listGET_END_MARKER_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalTCPItem );
    listGET_END_MARKER_ExpectAndReturn( &xBoundUDPSocketsList, &xLocalUDPItem );

    /* First Iteration. */
    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xIterator );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xSocket );

    xTaskGetTickCount_ExpectAndReturn( 0x10 );

    /* TCP last iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xLocalTCPItem );

    /* UDP */
    /* First Iteration. */
    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundUDPSocketsList, &xIterator );

    /* Second Iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xIterator );

    /* TCP last iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xLocalUDPItem );

    vTCPNetStat();
}
