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

#include "FreeRTOSIPConfig.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_FreeRTOS_UDP_IPv6_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_ND.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_Routing.h"

#include "FreeRTOS_DNS_Globals.h"
#include "FreeRTOS_UDP_IP.h"

#include "FreeRTOS_UDP_IPv6_stubs.c"
#include "catch_assert.h"

/* ===========================  EXTERN VARIABLES  =========================== */

extern NetworkEndPoint_t * pxGetEndpoint( BaseType_t xIPType,
                                          BaseType_t xIsGlobal );

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
    xIsIfOutCalled = 0;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief Trigger assertion when input network buffer pointer is NULL.
 */
void test_xProcessReceivedUDPPacket_IPv6_NullInput()
{
    BaseType_t xIsWaitingForARPResolution;

    catch_assert( xProcessReceivedUDPPacket_IPv6( NULL, 0, &xIsWaitingForARPResolution ) );
}

/**
 * @brief Trigger assertion when input buffer pointer in network buffer is NULL.
 */
void test_xProcessReceivedUDPPacket_IPv6_NullBufferPointer()
{
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    catch_assert( xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, 0, &xIsWaitingForARPResolution ) );
}

/**
 * @brief Return fail due to zero checksum.
 */
void test_xProcessReceivedUDPPacket_IPv6_ZeroChecksum()
{
    BaseType_t xReturn;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0U;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that receives DNS reply packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_DNSReplyPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipDNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives DNS reply packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_DNSReplyFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipDNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that receives LLMNR request packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_LLMNRRequestPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipLLMNR_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives LLMNR request packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_LLMNRRequestFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipLLMNR_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that receives LLMNR reply packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_LLMNRReplyPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipLLMNR_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives LLMNR reply packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_LLMNRReplyFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipLLMNR_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that receives NBNS request packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_NBNSRequestPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipNBNS_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives NBNS request packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_NBNSRequestFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipNBNS_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that receives NBNS Reply packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_NBNSReplyPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipNBNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives NBNS Reply packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_NBNSReplyFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipNBNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that no one is waiting for the packet.
 */
void test_xProcessReceivedUDPPacket_IPv6_NoSocket()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the flow that socket needs neighbor discovery.
 */
void test_xProcessReceivedUDPPacket_IPv6_SocketNeedND()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xIsWaitingForARPResolution );
}

/**
 * @brief To validate the flow that socket receive handler returns fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_SocketRecvHandlerFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = xStubUDPReceiveHandler_Fail;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the flow that list of the socket is full and return fail.
 */
void test_xProcessReceivedUDPPacket_IPv6_UDPListBufferFull()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = xStubUDPReceiveHandler_Pass;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = xSocket.u.xUDP.uxMaxPackets;

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the flow that all flows (list/event group/select/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_Pass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xSocket.xEventGroup = xEventGroup;
    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE, pdPASS );

    xSocket.pxSocketSet = &xSocketSet;
    xSocket.xSelectBits |= eSELECT_READ;
    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );

    /* xSemaphoreGive is defined as xQueueGenericSend */
    xSocket.pxUserSemaphore = ( SemaphoreHandle_t ) &xSocketSem;
    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdTRUE );
    xSendDHCPEvent_ExpectAndReturn( xNetworkBuffer.pxEndPoint, pdPASS );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow that all flows except for event group (list/select/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_PassNoEventGroup()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = NULL;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xSocket.pxSocketSet = &xSocketSet;
    xSocket.xSelectBits |= eSELECT_READ;
    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );

    /* xSemaphoreGive is defined as xQueueGenericSend */
    xSocket.pxUserSemaphore = ( SemaphoreHandle_t ) &xSocketSem;
    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdTRUE );
    xSendDHCPEvent_ExpectAndReturn( xNetworkBuffer.pxEndPoint, pdPASS );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow that all flows except for select bit (list/event group/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_PassNoSelectBit()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE, pdPASS );

    xSocket.pxSocketSet = &xSocketSet;

    /* xSemaphoreGive is defined as xQueueGenericSend */
    xSocket.pxUserSemaphore = ( SemaphoreHandle_t ) &xSocketSem;
    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdTRUE );
    xSendDHCPEvent_ExpectAndReturn( xNetworkBuffer.pxEndPoint, pdPASS );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow that all flows except for select set (list/event group/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_PassNoSelectSet()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE, pdPASS );

    /* xSemaphoreGive is defined as xQueueGenericSend */
    xSocket.pxUserSemaphore = ( SemaphoreHandle_t ) &xSocketSem;
    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdTRUE );
    xSendDHCPEvent_ExpectAndReturn( xNetworkBuffer.pxEndPoint, pdPASS );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow that all flows except for semaphore (list/event group/select/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_PassNoSem()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE, pdPASS );

    xSocket.pxSocketSet = &xSocketSet;
    xSocket.xSelectBits |= eSELECT_READ;
    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdTRUE );
    xSendDHCPEvent_ExpectAndReturn( xNetworkBuffer.pxEndPoint, pdPASS );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow that all flows except for DHCP (list/event group/select/queue) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv6_PassNoDHCP()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPv6Packet;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
    pxUDPv6Packet->xIPHeader.usPayloadLength = xNetworkBuffer.xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER );

    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1234U;
    pxUDPv6Packet->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPv6Packet->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    uxIPHeaderSizePacket_ExpectAndReturn( &xNetworkBuffer, ipSIZE_OF_IPv6_HEADER );

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.uxMaxPackets = 255U;
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = 0U;

    vTaskSuspendAll_Ignore();
    vListInsertEnd_Expect( &( xSocket.u.xUDP.xWaitingPacketsList ), &( xNetworkBuffer.xBufferListItem ) );
    xTaskResumeAll_ExpectAndReturn( pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_RECEIVE, pdPASS );

    xSocket.pxSocketSet = &xSocketSet;
    xSocket.xSelectBits |= eSELECT_READ;
    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSELECT_READ, pdPASS );

    /* xSemaphoreGive is defined as xQueueGenericSend */
    xSocket.pxUserSemaphore = ( SemaphoreHandle_t ) &xSocketSem;
    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xIsDHCPSocket_ExpectAndReturn( &xSocket, pdFALSE );

    xReturn = xProcessReceivedUDPPacket_IPv6( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow to send ping message but get failure on neighbor discovery.
 */
void test_vProcessGeneratedUDPPacket_IPv6_ICMPPingCantSend()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    ICMPPacket_IPv6_t * pxICMPv6Packet;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_ICMP_IPv6 );
    pxEndPoint = prvPrepareDefaultIPv6EndPoint();

    pxNetworkBuffer->usPort = ipPACKET_CONTAINS_ICMP_DATA;

    pxICMPv6Packet = ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eNDGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxICMPv6Packet->xEthernetHeader.xDestinationAddress ), NULL, eCantSendPacket );
    eNDGetCacheEntry_IgnoreArg_ppxEndPoint();
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );
}

/**
 * @brief To validate the flow to send ping message but get an unknown ND return.
 */
void test_vProcessGeneratedUDPPacket_IPv6_ICMPPingCacheUnknown()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    ICMPPacket_IPv6_t * pxICMPv6Packet;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_ICMP_IPv6 );
    pxEndPoint = prvPrepareDefaultIPv6EndPoint();

    pxNetworkBuffer->usPort = ipPACKET_CONTAINS_ICMP_DATA;

    pxICMPv6Packet = ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eNDGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxICMPv6Packet->xEthernetHeader.xDestinationAddress ), NULL, 0xFF );
    eNDGetCacheEntry_IgnoreArg_ppxEndPoint();
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );
}

/**
 * @brief To validate the flow to send ping message and get a cache hit.
 */
void test_vProcessGeneratedUDPPacket_IPv6_ICMPPingCacheHit()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    ICMPPacket_IPv6_t * pxICMPv6Packet;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_ICMP_IPv6 );
    pxEndPoint = prvPrepareDefaultIPv6EndPoint();

    /* To trigger checksum generation. */
    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] |= FREERTOS_SO_UDPCKSUM_OUT;

    pxNetworkBuffer->usPort = ipPACKET_CONTAINS_ICMP_DATA;

    pxICMPv6Packet = ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eNDGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxICMPv6Packet->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eNDGetCacheEntry_IgnoreArg_ppxEndPoint();
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE, ipCORRECT_CRC );

    vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( 0x60, pxICMPv6Packet->xIPHeader.ucVersionTrafficClass );
    TEST_ASSERT_EQUAL( ipPROTOCOL_ICMP_IPv6, pxICMPv6Packet->xIPHeader.ucNextHeader );
    TEST_ASSERT_EQUAL( 1, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache hit.
 */
void test_vProcessGeneratedUDPPacket_IPv6_UDPv6CacheHit()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    UDPPacket_IPv6_t * pxUDPv6Packet;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv6EndPoint();

    /* To trigger checksum generation. */
    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] |= FREERTOS_SO_UDPCKSUM_OUT;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eNDGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxUDPv6Packet->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eNDGetCacheEntry_IgnoreArg_ppxEndPoint();
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE, ipCORRECT_CRC );

    vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( 0x60, pxUDPv6Packet->xIPHeader.ucVersionTrafficClass );
    TEST_ASSERT_EQUAL( 0, pxUDPv6Packet->xIPHeader.ucTrafficClassFlow );
    TEST_ASSERT_EQUAL( 0, pxUDPv6Packet->xIPHeader.usFlowLabel );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, pxUDPv6Packet->xIPHeader.ucNextHeader );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ), FreeRTOS_ntohs( pxUDPv6Packet->xUDPHeader.usLength ) );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usBoundPort, pxUDPv6Packet->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPv6Packet->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPv6Address.ucBytes, pxUDPv6Packet->xIPHeader.xSourceAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( 1, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache hit. But the buffer length is
 * less than minimum requirement.
 */
void test_vProcessGeneratedUDPPacket_IPv6_UDPv6CacheHitLessBufferLength()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    UDPPacket_IPv6_t * pxUDPv6Packet;
    size_t xBufferLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES - 1;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv6EndPoint();

    /* To trigger checksum generation. */
    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] |= FREERTOS_SO_UDPCKSUM_OUT;
    pxNetworkBuffer->xDataLength = xBufferLength;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eNDGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxUDPv6Packet->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eNDGetCacheEntry_IgnoreArg_ppxEndPoint();
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE, ipCORRECT_CRC );

    vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( 0x60, pxUDPv6Packet->xIPHeader.ucVersionTrafficClass );
    TEST_ASSERT_EQUAL( 0, pxUDPv6Packet->xIPHeader.ucTrafficClassFlow );
    TEST_ASSERT_EQUAL( 0, pxUDPv6Packet->xIPHeader.usFlowLabel );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, pxUDPv6Packet->xIPHeader.ucNextHeader );
    TEST_ASSERT_EQUAL( xBufferLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ), FreeRTOS_ntohs( pxUDPv6Packet->xUDPHeader.usLength ) );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usBoundPort, pxUDPv6Packet->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPv6Packet->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPv6Address.ucBytes, pxUDPv6Packet->xIPHeader.xSourceAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( 1, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache hit but no matching endpoint.
 */
void test_vProcessGeneratedUDPPacket_IPv6_UDPv6CacheHitNoEndPoint()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    UDPPacket_IPv6_t * pxUDPv6Packet;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = NULL;

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eNDGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxUDPv6Packet->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eNDGetCacheEntry_IgnoreArg_ppxEndPoint();
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( 0x60, pxUDPv6Packet->xIPHeader.ucVersionTrafficClass );
    TEST_ASSERT_EQUAL( 0, pxUDPv6Packet->xIPHeader.ucTrafficClassFlow );
    TEST_ASSERT_EQUAL( 0, pxUDPv6Packet->xIPHeader.usFlowLabel );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, pxUDPv6Packet->xIPHeader.ucNextHeader );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ), FreeRTOS_ntohs( pxUDPv6Packet->xUDPHeader.usLength ) );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usBoundPort, pxUDPv6Packet->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPv6Packet->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL( 0, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache miss and
 * the IP type of network buffer/endpoint are both global.
 */
void test_vProcessGeneratedUDPPacket_IPv6_UDPv6CacheMissBothGlobal()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint, * pxEndPointNull = NULL;
    UDPPacket_IPv6_t * pxUDPv6Packet;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv6EndPoint();

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eNDGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxUDPv6Packet->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheMiss );
    eNDGetCacheEntry_IgnoreArg_ppxEndPoint();
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPointNull );
    xIPv6_GetIPType_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, pxEndPoint );
    xIPv6_GetIPType_ExpectAndReturn( &( pxEndPoint->ipv6_settings.xIPAddress ), eIPv6_Global );

    vNDSendNeighbourSolicitation_Expect( pxNetworkBuffer, &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ) );

    vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( 0, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache miss but
 * matching endpoint is found.
 */
void test_vProcessGeneratedUDPPacket_IPv6_UDPv6CacheMissButEndPointFound()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    UDPPacket_IPv6_t * pxUDPv6Packet;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv6EndPoint();

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eNDGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxUDPv6Packet->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheMiss );
    eNDGetCacheEntry_IgnoreArg_ppxEndPoint();
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );

    vNDSendNeighbourSolicitation_Expect( pxNetworkBuffer, &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ) );

    vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( 0, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache miss and
 * the IP type of network buffer is not global but endpoint is global.
 */
void test_vProcessGeneratedUDPPacket_IPv6_UDPv6CacheMissDifferentIPType()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint, * pxEndPointNull = NULL;
    UDPPacket_IPv6_t * pxUDPv6Packet;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv6EndPoint();

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eNDGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxUDPv6Packet->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheMiss );
    eNDGetCacheEntry_IgnoreArg_ppxEndPoint();
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPointNull );
    xIPv6_GetIPType_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), eIPv6_LinkLocal );

    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, pxEndPoint );
    xIPv6_GetIPType_ExpectAndReturn( &( pxEndPoint->ipv6_settings.xIPAddress ), eIPv6_Global );
    FreeRTOS_NextEndPoint_ExpectAndReturn( NULL, pxEndPoint, NULL );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( 0, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache miss and
 * the IP type of network buffer is global but endpoint is not global.
 */
void test_vProcessGeneratedUDPPacket_IPv6_UDPv6CacheMissDifferentIPType2()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint, * pxEndPointNull = NULL;
    UDPPacket_IPv6_t * pxUDPv6Packet;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv6EndPoint();

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eNDGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), &( pxUDPv6Packet->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheMiss );
    eNDGetCacheEntry_IgnoreArg_ppxEndPoint();
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPointNull );
    xIPv6_GetIPType_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.xIP_IPv6 ), eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, pxEndPoint );
    xIPv6_GetIPType_ExpectAndReturn( &( pxEndPoint->ipv6_settings.xIPAddress ), eIPv6_LinkLocal );
    FreeRTOS_NextEndPoint_ExpectAndReturn( NULL, pxEndPoint, NULL );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( 0, xIsIfOutCalled );
}


/**
 * @brief Searching IPv4 endpoint in the global list. And it always returns NULL.
 */
void test_pxGetEndpoint_IPv4()
{
    BaseType_t xIsGlobal = pdFALSE;
    NetworkEndPoint_t * pxReturnEndPoint;
    NetworkEndPoint_t * pxIPv6EndPoint = prvPrepareDefaultIPv6EndPoint();

    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, pxIPv6EndPoint );
    FreeRTOS_NextEndPoint_ExpectAndReturn( NULL, pxIPv6EndPoint, NULL );

    pxReturnEndPoint = pxGetEndpoint( ipTYPE_IPv4, xIsGlobal );

    TEST_ASSERT_EQUAL( NULL, pxReturnEndPoint );
}

/**
 * @brief No matching endpoint.
 */
void test_pxGetEndpoint_NotMatchEndpoint()
{
    BaseType_t xIsGlobal = pdFALSE;
    NetworkEndPoint_t * pxReturnEndPoint;
    NetworkEndPoint_t * pxIPv4EndPoint = prvPrepareDefaultIPv4EndPoint();
    NetworkEndPoint_t * pxIPv6EndPoint = prvPrepareDefaultIPv6EndPoint();

    FreeRTOS_FirstEndPoint_ExpectAndReturn( NULL, pxIPv4EndPoint );
    FreeRTOS_NextEndPoint_ExpectAndReturn( NULL, pxIPv4EndPoint, pxIPv6EndPoint );
    xIPv6_GetIPType_ExpectAndReturn( &( pxIPv6EndPoint->ipv6_settings.xIPAddress ), eIPv6_Global );
    FreeRTOS_NextEndPoint_ExpectAndReturn( NULL, pxIPv6EndPoint, NULL );

    pxReturnEndPoint = pxGetEndpoint( ipTYPE_IPv6, xIsGlobal );

    TEST_ASSERT_EQUAL( NULL, pxReturnEndPoint );
}
