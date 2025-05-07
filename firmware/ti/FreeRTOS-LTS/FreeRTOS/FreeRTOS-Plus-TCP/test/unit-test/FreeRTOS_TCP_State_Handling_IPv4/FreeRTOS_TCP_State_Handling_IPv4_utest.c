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
#include "mock_FreeRTOS_TCP_IP.h"
#include "mock_TCP_State_Handling_IPv4_list_macros.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* ===========================  EXTERN VARIABLES  =========================== */

FreeRTOS_Socket_t * prvHandleListen_IPV4( FreeRTOS_Socket_t * pxSocket,
                                          NetworkBufferDescriptor_t * pxNetworkBuffer );

FreeRTOS_Socket_t xSocket, * pxSocket;
NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;

uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( &ucEthernetBuffer, 0, sizeof( ucEthernetBuffer ) );

    pxSocket = NULL;
    pxNetworkBuffer = NULL;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief The packet IP address is not for endpoint.
 */
void test_prvHandleListen_IPV4_NotForMe( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    struct xNetworkEndPoint xEndPoint = { 0 };
    TCPPacket_t * pxTCPPacket;

    xEndPoint.ipv4_settings.ulIPAddress = 0x0700a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;

    pxTCPPacket = ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x12345678;

    pxSocket = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxSocket );
}

/**
 * @brief Flag of reuse socket is enabled.
 */
void test_prvHandleListen_IPV4_ReuseSocket( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdTRUE;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdPASS );
    vTCPStateChange_Ignore();

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxSocket, pxReturn );
    TEST_ASSERT_EQUAL( 1000, pxReturn->u.xTCP.xTCPWindow.ulOurSequenceNumber );
}

/**
 * @brief Flag of reuse socket is enabled and create TCP window failed.
 */
void test_prvHandleListen_IPV4_ReuseSocket_CreateWindowFailed( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdTRUE;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdFAIL );
    vTCPStateChange_Ignore();

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Number of child socket is beyond limitation.
 */
void test_prvHandleListen_IPV4_NewSocketExceedLimit( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 10;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Happy path.
 */
void test_prvHandleListen_IPV4_NewSocketGood( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( &MockReturnSocket );
    prvTCPSocketCopy_ExpectAndReturn( &MockReturnSocket, pxSocket, pdTRUE );
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdPASS );
    vTCPStateChange_ExpectAnyArgs();

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( &MockReturnSocket, pxReturn );
    TEST_ASSERT_EQUAL( 1000, pxReturn->u.xTCP.xTCPWindow.ulOurSequenceNumber );
}

/**
 * @brief Create TCP window failed.
 */
void test_prvHandleListen_IPV4_NewSocket_CreateWindowFailed( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( &MockReturnSocket );
    prvTCPSocketCopy_ExpectAndReturn( &MockReturnSocket, pxSocket, pdTRUE );
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdFAIL );
    vSocketClose_ExpectAndReturn( &MockReturnSocket, NULL );

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Happy path with valid data length.
 */
void test_prvHandleListen_IPV4_NewSocketGoodValidDataLength( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->xDataLength = TCP_PACKET_SIZE + 1;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( &MockReturnSocket );
    prvTCPSocketCopy_ExpectAndReturn( &MockReturnSocket, pxSocket, pdTRUE );
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdPASS );
    vTCPStateChange_ExpectAnyArgs();

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( &MockReturnSocket, pxReturn );
    TEST_ASSERT_EQUAL( 1000, pxReturn->u.xTCP.xTCPWindow.ulOurSequenceNumber );
}

/**
 * @brief Got NULL return when creating socket.
 */
void test_prvHandleListen_IPV4_NewSocketNULLSocket( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( NULL );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Fail to create socket.
 */
void test_prvHandleListen_IPV4_NewSocketInvalidSocket( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( FREERTOS_INVALID_SOCKET );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Failure happens in copy step.
 */
void test_prvHandleListen_IPV4_NewSocketSocketCopyFailure( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    FreeRTOS_Socket_t MockReturnSocket;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xIPHeader.ulDestinationIPAddress = 0x0800a8c0;

    pxSocket->u.xTCP.bits.bReuseSocket = pdFALSE;
    pxSocket->u.xTCP.usChildCount = 1;
    pxSocket->u.xTCP.usBacklog = 9;

    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 1000 );
    FreeRTOS_socket_ExpectAnyArgsAndReturn( &MockReturnSocket );
    prvTCPSocketCopy_ExpectAndReturn( &MockReturnSocket, pxSocket, pdFALSE );

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief The socket handler is NULL.
 */
void test_prvHandleListen_IPV4_NullSocket( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;

    pxReturn = prvHandleListen_IPV4( NULL, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief The network buffer pointer is NULL.
 */
void test_prvHandleListen_IPV4_NullNetworkBuffer( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;

    pxSocket = &xSocket;

    pxReturn = prvHandleListen_IPV4( pxSocket, NULL );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief The endpoint in network buffer is NULL.
 */
void test_prvHandleListen_IPV4_NullEndpoint( void )
{
    FreeRTOS_Socket_t * pxReturn = NULL;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0x0800a8c0;

    pxSocket = &xSocket;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;

    pxReturn = prvHandleListen_IPV4( pxSocket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}
