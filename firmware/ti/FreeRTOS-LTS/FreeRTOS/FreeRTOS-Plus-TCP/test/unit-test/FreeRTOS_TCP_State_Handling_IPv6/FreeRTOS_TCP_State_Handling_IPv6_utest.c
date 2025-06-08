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
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_TCP_Transmission.h"
#include "mock_FreeRTOS_TCP_Utils.h"
#include "mock_TCP_State_Handling_IPv6_list_macros.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"
#include "FreeRTOS_IP.h"

/* =========================== EXTERN VARIABLES =========================== */

FreeRTOS_Socket_t * prvHandleListen_IPV6( FreeRTOS_Socket_t * pxSocket,
                                          NetworkBufferDescriptor_t * pxNetworkBuffer );

FreeRTOS_Socket_t xSocket, * pxSocket;
NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;
NetworkEndPoint_t xEndPoint, * pxEndPoint;
uint8_t pucEthernetBuffer[ ipconfigNETWORK_MTU ];

/* 2001::1 */
const IPv6_Address_t xIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

/* ===========================  Unity Fixtures  =========================== */

/*! called before each test case */
void setUp( void )
{
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    memset( &pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    pxSocket = NULL;
    pxNetworkBuffer = NULL;
    pxEndPoint = NULL;
}

/* ============================== Test Cases ============================== */

/**
 * @brief Input with NULL socket handler.
 */
void test_prvHandleListen_IPV6_NullSocket( void )
{
    FreeRTOS_Socket_t * pxReturn;

    pxNetworkBuffer = &xNetworkBuffer;

    pxReturn = prvHandleListen_IPV6( NULL, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Input with NULL network buffer pointer.
 */
void test_prvHandleListen_IPV6_NullNetworkBuffer( void )
{
    FreeRTOS_Socket_t * pxReturn;

    pxSocket = &xSocket;

    pxReturn = prvHandleListen_IPV6( pxSocket, NULL );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Input with NULL endpoint in network buffer.
 */
void test_prvHandleListen_IPV6_NullEndpoint( void )
{
    FreeRTOS_Socket_t * pxReturn;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->pxEndPoint = NULL;

    catch_assert( prvHandleListen_IPV6( pxSocket, pxNetworkBuffer ) );
}

/**
 * @brief Fail to get random number.
 */
void test_prvHandleListen_IPV6_DifferentIP( void )
{
    FreeRTOS_Socket_t * pxReturn;
    TCPPacket_IPv6_t * pxTCPPacket = NULL;
    /* 2001::2 */
    IPv6_Address_t xDifferentIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 } };

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    /* Set different IPv6 address to endpoint & buffer. */
    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, xDifferentIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxReturn = prvHandleListen_IPV6( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Fail to get random number.
 */
void test_prvHandleListen_IPV6_GetRandomFail( void )
{
    FreeRTOS_Socket_t * pxReturn;
    TCPPacket_IPv6_t * pxTCPPacket = NULL;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    /* Set same IPv6 address to endpoint & buffer. */
    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFAIL );

    pxReturn = prvHandleListen_IPV6( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Reuse bit is set in socket handler.
 */
void test_prvHandleListen_IPV6_ReuseSocket( void )
{
    FreeRTOS_Socket_t * pxReturn;
    TCPPacket_IPv6_t * pxTCPPacket = NULL;
    uint32_t ulRandomReturn = 0x12345678;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    /* Set same IPv6 address to endpoint & buffer. */
    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdPASS );
    xApplicationGetRandomNumber_ReturnMemThruPtr_pulNumber( &ulRandomReturn, sizeof( ulRandomReturn ) );

    pxSocket->u.xTCP.bits.bReuseSocket = pdTRUE;

    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdPASS );
    vTCPStateChange_Expect( NULL, eSYN_FIRST );
    vTCPStateChange_IgnoreArg_pxSocket();

    pxReturn = prvHandleListen_IPV6( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxSocket, pxReturn );
}

/**
 * @brief Reuse bit is set in socket handler but the TCP window creation
 *        fails.
 */
void test_prvHandleListen_IPV6_ReuseSocket_CreateWindowFails( void )
{
    FreeRTOS_Socket_t * pxReturn;
    TCPPacket_IPv6_t * pxTCPPacket = NULL;
    uint32_t ulRandomReturn = 0x12345678;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    /* Set same IPv6 address to endpoint & buffer. */
    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdPASS );
    xApplicationGetRandomNumber_ReturnMemThruPtr_pulNumber( &ulRandomReturn, sizeof( ulRandomReturn ) );

    pxSocket->u.xTCP.bits.bReuseSocket = pdTRUE;

    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdFAIL );

    pxReturn = prvHandleListen_IPV6( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Number of child socket is beyond limitation.
 */
void test_prvHandleListen_IPV6_NewSocketExceedLimit( void )
{
    FreeRTOS_Socket_t * pxReturn;
    TCPPacket_IPv6_t * pxTCPPacket = NULL;
    uint32_t ulRandomReturn = 0x12345678;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    /* Set same IPv6 address to endpoint & buffer. */
    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdPASS );
    xApplicationGetRandomNumber_ReturnMemThruPtr_pulNumber( &ulRandomReturn, sizeof( ulRandomReturn ) );

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 10;
    pxSocket->u.xTCP.usBacklog = 9;

    prvTCPSendReset_ExpectAndReturn( pxNetworkBuffer, pdTRUE );

    pxReturn = prvHandleListen_IPV6( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Got NULL return when creating socket.
 */
void test_prvHandleListen_IPV6_NewSocketNull( void )
{
    FreeRTOS_Socket_t * pxReturn;
    TCPPacket_IPv6_t * pxTCPPacket = NULL;
    uint32_t ulRandomReturn = 0x12345678;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    /* Set same IPv6 address to endpoint & buffer. */
    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdPASS );
    xApplicationGetRandomNumber_ReturnMemThruPtr_pulNumber( &ulRandomReturn, sizeof( ulRandomReturn ) );

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP, NULL );
    prvTCPSendReset_ExpectAndReturn( pxNetworkBuffer, pdTRUE );

    pxReturn = prvHandleListen_IPV6( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Fail to create socket.
 */
void test_prvHandleListen_IPV6_NewSocketInvalid( void )
{
    FreeRTOS_Socket_t * pxReturn;
    TCPPacket_IPv6_t * pxTCPPacket = NULL;
    uint32_t ulRandomReturn = 0x12345678;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    /* Set same IPv6 address to endpoint & buffer. */
    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdPASS );
    xApplicationGetRandomNumber_ReturnMemThruPtr_pulNumber( &ulRandomReturn, sizeof( ulRandomReturn ) );

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP, FREERTOS_INVALID_SOCKET );
    prvTCPSendReset_ExpectAndReturn( pxNetworkBuffer, pdTRUE );

    pxReturn = prvHandleListen_IPV6( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Failure happens in copy step.
 */
void test_prvHandleListen_IPV6_NewSocketCopyFailure( void )
{
    FreeRTOS_Socket_t * pxReturn;
    TCPPacket_IPv6_t * pxTCPPacket = NULL;
    uint32_t ulRandomReturn = 0x12345678;
    FreeRTOS_Socket_t xChildSocket, * pxChildSocket;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    /* Set same IPv6 address to endpoint & buffer. */
    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdPASS );
    xApplicationGetRandomNumber_ReturnMemThruPtr_pulNumber( &ulRandomReturn, sizeof( ulRandomReturn ) );

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    memset( &xChildSocket, 0, sizeof( xChildSocket ) );
    pxChildSocket = &xChildSocket;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP, pxChildSocket );
    prvTCPSocketCopy_ExpectAndReturn( pxChildSocket, pxSocket, pdFALSE );

    pxReturn = prvHandleListen_IPV6( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Happy path.
 */
void test_prvHandleListen_IPV6_NewSocketGood( void )
{
    FreeRTOS_Socket_t * pxReturn;
    TCPPacket_IPv6_t * pxTCPPacket = NULL;
    uint32_t ulRandomReturn = 0x12345678;
    FreeRTOS_Socket_t xChildSocket, * pxChildSocket;
    uint16_t usSrcPort = 0x1234;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    /* Set same IPv6 address to endpoint & buffer. */
    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxTCPPacket->xTCPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdPASS );
    xApplicationGetRandomNumber_ReturnMemThruPtr_pulNumber( &ulRandomReturn, sizeof( ulRandomReturn ) );

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    memset( &xChildSocket, 0, sizeof( xChildSocket ) );
    pxChildSocket = &xChildSocket;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP, pxChildSocket );
    prvTCPSocketCopy_ExpectAndReturn( pxChildSocket, pxSocket, pdTRUE );
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdPASS );
    vTCPStateChange_Expect( NULL, eSYN_FIRST );
    vTCPStateChange_IgnoreArg_pxSocket();

    pxReturn = prvHandleListen_IPV6( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxReturn->bits.bIsIPv6 );
    TEST_ASSERT_EQUAL( pxEndPoint, pxReturn->pxEndPoint );
    TEST_ASSERT_EQUAL( usSrcPort, pxReturn->u.xTCP.usRemotePort );
    TEST_ASSERT_EQUAL_MEMORY( xIPv6Address.ucBytes, pxReturn->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief Create TCP window fails
 */
void test_prvHandleListen_IPV6_CreateWindowFails( void )
{
    FreeRTOS_Socket_t * pxReturn;
    TCPPacket_IPv6_t * pxTCPPacket = NULL;
    uint32_t ulRandomReturn = 0x12345678;
    FreeRTOS_Socket_t xChildSocket, * pxChildSocket;
    uint16_t usSrcPort = 0x1234;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    /* Set same IPv6 address to endpoint & buffer. */
    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxTCPPacket->xTCPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdPASS );
    xApplicationGetRandomNumber_ReturnMemThruPtr_pulNumber( &ulRandomReturn, sizeof( ulRandomReturn ) );

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    memset( &xChildSocket, 0, sizeof( xChildSocket ) );
    pxChildSocket = &xChildSocket;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP, pxChildSocket );
    prvTCPSocketCopy_ExpectAndReturn( pxChildSocket, pxSocket, pdTRUE );
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdFAIL );
    vSocketClose_ExpectAndReturn( pxChildSocket, NULL );

    pxReturn = prvHandleListen_IPV6( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}


/**
 * @brief Happy path with valid data length.
 */
void test_prvHandleListen_IPV6_NewSocketGoodValidDataLength( void )
{
    FreeRTOS_Socket_t * pxReturn;
    TCPPacket_IPv6_t * pxTCPPacket = NULL;
    uint32_t ulRandomReturn = 0x12345678;
    FreeRTOS_Socket_t xChildSocket, * pxChildSocket;
    uint16_t usSrcPort = 0x1234;

    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;
    pxNetworkBuffer->xDataLength = TCP_PACKET_SIZE + 1;

    /* Set same IPv6 address to endpoint & buffer. */
    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxTCPPacket->xTCPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxEndPoint->ipv6_settings.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdPASS );
    xApplicationGetRandomNumber_ReturnMemThruPtr_pulNumber( &ulRandomReturn, sizeof( ulRandomReturn ) );

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    memset( &xChildSocket, 0, sizeof( xChildSocket ) );
    pxChildSocket = &xChildSocket;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP, pxChildSocket );
    prvTCPSocketCopy_ExpectAndReturn( pxChildSocket, pxSocket, pdTRUE );
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdPASS );
    vTCPStateChange_Expect( NULL, eSYN_FIRST );
    vTCPStateChange_IgnoreArg_pxSocket();

    pxReturn = prvHandleListen_IPV6( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxReturn->bits.bIsIPv6 );
    TEST_ASSERT_EQUAL( pxEndPoint, pxReturn->pxEndPoint );
    TEST_ASSERT_EQUAL( usSrcPort, pxReturn->u.xTCP.usRemotePort );
    TEST_ASSERT_EQUAL_MEMORY( xIPv6Address.ucBytes, pxReturn->u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}
