/**
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
#include "mock_FreeRTOS_UDP_IP_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_DNS.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* ===========================  EXTERN VARIABLES  =========================== */

/* The maximum segment size used by TCP, it is the maximum size of
 * the TCP payload per packet.
 * For IPv4: when MTU equals 1500, the MSS equals 1460.
 * It is recommended to use the default value defined here.
 *
 * In FreeRTOS_TCP_IP.c, there is a local macro called 'tcpREDUCED_MSS_THROUGH_INTERNET'.
 * When a TCP connection is made outside the local network, the MSS
 * will be reduced to 'tcpREDUCED_MSS_THROUGH_INTERNET' before the connection
 * is made.
 */
#ifndef ipconfigTCP_MSS
    #define ipconfigTCP_MSS    ( ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER ) )
#endif

void vProcessGeneratedUDPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );
BaseType_t xProcessReceivedUDPPacket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                      uint16_t usPort,
                                      BaseType_t * pxIsWaitingForARPResolution );

/* ==============================  Test Cases  ============================== */

/**
 * @brief Input with null network buffer pointer.
 */
void test_vProcessGeneratedUDPPacket_NullNetworkBuffer( void )
{
    vProcessGeneratedUDPPacket( NULL );
}

/**
 * @brief Pass IPv4 packet to IPv4 API to handle.
 */
void test_vProcessGeneratedUDPPacket_IPv4Packet( void )
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pucLocalEthernetBuffer );

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    vProcessGeneratedUDPPacket_IPv4_Expect( &xLocalNetworkBuffer );

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );
}

/**
 * @brief Pass IPv6 packet to IPv6 API to handle.
 */
void test_vProcessGeneratedUDPPacket_IPv6Packet( void )
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pucLocalEthernetBuffer );

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    vProcessGeneratedUDPPacket_IPv6_Expect( &xLocalNetworkBuffer );

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );
}

/**
 * @brief Do nothing if it's an unknown packet.
 */
void test_vProcessGeneratedUDPPacket_UnknownPacket( void )
{
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t xLocalNetworkBuffer;

    xLocalNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pucLocalEthernetBuffer );

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE + 1;

    vProcessGeneratedUDPPacket( &xLocalNetworkBuffer );
}

/**
 * @brief Input with null network buffer pointer.
 */
void test_xProcessReceivedUDPPacket_NullNetworkBuffer( void )
{
    uint16_t usPort = 0x1234;
    BaseType_t xIsWaitingForARPResolution = 0;

    catch_assert( xProcessReceivedUDPPacket( NULL, usPort, &xIsWaitingForARPResolution ) );
}

/**
 * @brief Input with null buffer pointer in network buffer.
 */
void test_xProcessReceivedUDPPacket_NullBuffer( void )
{
    uint16_t usPort = 0x1234;
    BaseType_t xIsWaitingForARPResolution = 0;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    xNetworkBuffer.pucEthernetBuffer = NULL;

    catch_assert( xProcessReceivedUDPPacket( &xNetworkBuffer, usPort, &xIsWaitingForARPResolution ) );
}

/**
 * @brief Pass IPv4 packet to IPv4 API to handle.
 */
void test_xProcessReceivedUDPPacket_IPv4Packet( void )
{
    BaseType_t xReturn;
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    uint16_t usPort = 0x1234;
    BaseType_t xIsWaitingForARPResolution = 0;
    NetworkBufferDescriptor_t xNetworkBuffer;
    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pucLocalEthernetBuffer );

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    xNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    xProcessReceivedUDPPacket_IPv4_ExpectAndReturn( &xNetworkBuffer, usPort, &xIsWaitingForARPResolution, pdPASS );

    xReturn = xProcessReceivedUDPPacket( &xNetworkBuffer, usPort, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief Pass IPv6 packet to IPv6 API to handle.
 */
void test_xProcessReceivedUDPPacket_IPv6Packet( void )
{
    BaseType_t xReturn;
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    uint16_t usPort = 0x1234;
    BaseType_t xIsWaitingForARPResolution = 0;
    NetworkBufferDescriptor_t xNetworkBuffer;
    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pucLocalEthernetBuffer );

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    xNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    xProcessReceivedUDPPacket_IPv6_ExpectAndReturn( &xNetworkBuffer, usPort, &xIsWaitingForARPResolution, pdPASS );

    xReturn = xProcessReceivedUDPPacket( &xNetworkBuffer, usPort, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief Return fail for unknown packet.
 */
void test_xProcessReceivedUDPPacket_UnknownPacket( void )
{
    BaseType_t xReturn;
    uint8_t pucLocalEthernetBuffer[ ipconfigTCP_MSS ];
    uint16_t usPort = 0x1234;
    BaseType_t xIsWaitingForARPResolution = 0;
    NetworkBufferDescriptor_t xNetworkBuffer;
    UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pucLocalEthernetBuffer );

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    xNetworkBuffer.pucEthernetBuffer = pucLocalEthernetBuffer;

    /* Cleanup the ethernet buffer. */
    memset( pucLocalEthernetBuffer, 0, ipconfigTCP_MSS );
    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE + 1;

    xReturn = xProcessReceivedUDPPacket( &xNetworkBuffer, usPort, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}
