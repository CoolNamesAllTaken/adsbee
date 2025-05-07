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

#include "FreeRTOSIPConfig.h"

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_FreeRTOS_UDP_IPv4_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_NetworkBufferManagement.h"

#include "FreeRTOS_UDP_IPv4_stubs.c"
#include "catch_assert.h"

/* ===========================  EXTERN VARIABLES  =========================== */

const uint32_t ulDefaultIPv4Address = 0x12345678;
const uint16_t ulDefaultProtoChecksum = 0xABCD;
BaseType_t xIsIfOutCalled = 0;

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
void test_xProcessReceivedUDPPacket_IPv4_NullInput()
{
    BaseType_t xIsWaitingForARPResolution;

    catch_assert( xProcessReceivedUDPPacket_IPv4( NULL, 0, &xIsWaitingForARPResolution ) );
}

/**
 * @brief Trigger assertion when input buffer pointer in network buffer is NULL.
 */
void test_xProcessReceivedUDPPacket_IPv4_NullBufferPointer()
{
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    catch_assert( xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, 0, &xIsWaitingForARPResolution ) );
}

/**
 * @brief To validate the scenario that receives DNS reply packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_DNSReplyPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipDNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives DNS reply packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv4_DNSReplyFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipDNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that receives LLMNR request packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_LLMNRRequestPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipLLMNR_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives LLMNR request packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv4_LLMNRRequestFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipLLMNR_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that receives LLMNR reply packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_LLMNRReplyPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipLLMNR_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives LLMNR reply packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv4_LLMNRReplyFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipLLMNR_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that receives MDNS request packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_MDNSRequestPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipMDNS_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives MDNS request packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv4_MDNSRequestFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipMDNS_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that receives MDNS Reply packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_MDNSReplyPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipMDNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives MDNS Reply packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv4_MDNSReplyFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipMDNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that receives MDNS request packet and pass
 * with IPv6 frame type in ethernet header.
 */
void test_xProcessReceivedUDPPacket_IPv4_MDNSRequestPassWithIPv6FrameType()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipMDNS_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    ulDNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives NBNS request packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_NBNSRequestPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipNBNS_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives NBNS request packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv4_NBNSRequestFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 1024U;
    uint16_t usDestPort = ipNBNS_PORT;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that receives NBNS Reply packet and pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_NBNSReplyPass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipNBNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief To validate the scenario that receives NBNS Reply packet and fail.
 */
void test_xProcessReceivedUDPPacket_IPv4_NBNSReplyFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = ipNBNS_PORT;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );
    vARPRefreshCacheEntry_Expect( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, xNetworkBuffer.pxEndPoint );
    ulNBNSHandlePacket_ExpectAndReturn( &xNetworkBuffer, pdFAIL );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the scenario that no one is waiting for the packet.
 */
void test_xProcessReceivedUDPPacket_IPv4_NoSocket()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, NULL );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the flow that socket has NULL endpoint.
 */
void test_xProcessReceivedUDPPacket_IPv4_SocketNullEndpoint()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;
    FreeRTOS_Socket_t xSocket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.pxEndPoint = NULL;

    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the flow that endpoint in socket handler has zero IP address.
 */
void test_xProcessReceivedUDPPacket_IPv4_SocketEndPointZeroIP()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;
    FreeRTOS_Socket_t xSocket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    xEndPoint.ipv4_settings.ulIPAddress = 0U;

    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the flow that socket needs ARP discovery.
 */
void test_xProcessReceivedUDPPacket_IPv4_SocketNeedARP()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;
    FreeRTOS_Socket_t xSocket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    xEndPoint.ipv4_settings.ulIPAddress = ulDefaultIPv4Address;

    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdTRUE );

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xIsWaitingForARPResolution );
}

/**
 * @brief To validate the flow that socket receive handler returns fail.
 */
void test_xProcessReceivedUDPPacket_IPv4_SocketRecvHandlerFail()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;
    FreeRTOS_Socket_t xSocket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    xEndPoint.ipv4_settings.ulIPAddress = ulDefaultIPv4Address;

    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
    pxUDPPacket->xIPHeader.usLength = xNetworkBuffer.xDataLength - ipSIZE_OF_ETH_HEADER;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = xStubUDPReceiveHandler_Fail;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_Ignore();

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the flow that list of the socket is full and return fail.
 */
void test_xProcessReceivedUDPPacket_IPv4_UDPListBufferFull()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;
    FreeRTOS_Socket_t xSocket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    xEndPoint.ipv4_settings.ulIPAddress = ulDefaultIPv4Address;

    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
    pxUDPPacket->xIPHeader.usLength = xNetworkBuffer.xDataLength - ipSIZE_OF_ETH_HEADER;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = xStubUDPReceiveHandler_Pass;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_Ignore();

    /* Set for listCURRENT_LIST_LENGTH */
    xSocket.u.xUDP.xWaitingPacketsList.uxNumberOfItems = xSocket.u.xUDP.uxMaxPackets;

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief To validate the flow that all flows (list/event group/select/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_Pass()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    xEndPoint.ipv4_settings.ulIPAddress = ulDefaultIPv4Address;

    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
    pxUDPPacket->xIPHeader.usLength = xNetworkBuffer.xDataLength - ipSIZE_OF_ETH_HEADER;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_Ignore();

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

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow that all flows except for event group (list/select/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_PassNoEventGroup()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;
    FreeRTOS_Socket_t xSocket;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    xEndPoint.ipv4_settings.ulIPAddress = ulDefaultIPv4Address;

    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
    pxUDPPacket->xIPHeader.usLength = xNetworkBuffer.xDataLength - ipSIZE_OF_ETH_HEADER;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = NULL;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_Ignore();

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

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow that all flows except for select bit (list/event group/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_PassNoSelectBit()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    NetworkEndPoint_t xEndPoint;
    UDPPacket_t * pxUDPPacket;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    xEndPoint.ipv4_settings.ulIPAddress = ulDefaultIPv4Address;

    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
    pxUDPPacket->xIPHeader.usLength = xNetworkBuffer.xDataLength - ipSIZE_OF_ETH_HEADER;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_Ignore();

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

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow that all flows except for select set (list/event group/queue/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_PassNoSelectSet()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    xEndPoint.ipv4_settings.ulIPAddress = ulDefaultIPv4Address;

    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
    pxUDPPacket->xIPHeader.usLength = xNetworkBuffer.xDataLength - ipSIZE_OF_ETH_HEADER;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_Ignore();

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

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow that all flows except for semaphore (list/event group/select/DHCP) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_PassNoSem()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    xEndPoint.ipv4_settings.ulIPAddress = ulDefaultIPv4Address;

    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
    pxUDPPacket->xIPHeader.usLength = xNetworkBuffer.xDataLength - ipSIZE_OF_ETH_HEADER;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_Ignore();

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

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow that all flows except for DHCP (list/event group/select/queue) are all pass.
 */
void test_xProcessReceivedUDPPacket_IPv4_PassNoDHCP()
{
    BaseType_t xReturn;
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    uint16_t usDestPortNetworkEndian = FreeRTOS_htons( usDestPort );
    BaseType_t xIsWaitingForARPResolution;
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_t * pxUDPPacket;
    FreeRTOS_Socket_t xSocket;
    EventGroupHandle_t xEventGroup;
    struct xSOCKET_SET xSocketSet;
    SemaphoreHandle_t xSocketSem;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.usPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    xEndPoint.ipv4_settings.ulIPAddress = ulDefaultIPv4Address;

    pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
    pxUDPPacket->xIPHeader.usLength = xNetworkBuffer.xDataLength - ipSIZE_OF_ETH_HEADER;

    pxUDPPacket->xUDPHeader.usChecksum = 0x1234U;
    pxUDPPacket->xUDPHeader.usSourcePort = FreeRTOS_htons( usSrcPort );
    pxUDPPacket->xUDPHeader.usDestinationPort = usDestPortNetworkEndian;

    xSocket.u.xUDP.pxHandleReceive = NULL;
    xSocket.xEventGroup = xEventGroup;

    pxUDPSocketLookup_ExpectAndReturn( usDestPortNetworkEndian, &xSocket );
    xCheckRequiresARPResolution_ExpectAndReturn( &xNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_Ignore();

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

    xReturn = xProcessReceivedUDPPacket_IPv4( &xNetworkBuffer, usDestPortNetworkEndian, &xIsWaitingForARPResolution );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief To validate the flow to send ping message but get failure on ARP get entry.
 */
void test_vProcessGeneratedUDPPacket_IPv4_ICMPPingCantSend()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    ICMPPacket_t * pxICMPPacket;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_ICMP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();

    pxNetworkBuffer->usPort = ipPACKET_CONTAINS_ICMP_DATA;

    pxICMPPacket = ( ICMPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxICMPPacket->xEthernetHeader.xDestinationAddress ), NULL, eCantSendPacket );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );
}

/**
 * @brief To validate the flow to send ping message but get an unknown ND return.
 */
void test_vProcessGeneratedUDPPacket_IPv4_ICMPPingCacheUnknown()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    ICMPPacket_t * pxICMPPacket;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_ICMP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();

    pxNetworkBuffer->usPort = ipPACKET_CONTAINS_ICMP_DATA;

    pxICMPPacket = ( ICMPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxICMPPacket->xEthernetHeader.xDestinationAddress ), NULL, 0xFF );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );
}

/**
 * @brief To validate the flow to send ping message and get a cache hit.
 */
void test_vProcessGeneratedUDPPacket_IPv4_ICMPPingCacheHit()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    ICMPPacket_t * pxICMPPacket;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_ICMP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();

    /* To trigger checksum generation. */
    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] |= FREERTOS_SO_UDPCKSUM_OUT;

    pxNetworkBuffer->usPort = ipPACKET_CONTAINS_ICMP_DATA;

    pxICMPPacket = ( ICMPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxICMPPacket->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    usGenerateChecksum_ExpectAnyArgsAndReturn( ulDefaultProtoChecksum );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE, ipCORRECT_CRC );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( ipPROTOCOL_ICMP, pxICMPPacket->xIPHeader.ucProtocol );
    TEST_ASSERT_EQUAL( 1, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache hit.
 */
void test_vProcessGeneratedUDPPacket_IPv4_UDPCacheHit()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    UDPPacket_t * pxUDPPacket;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();

    /* To trigger checksum generation. */
    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] |= FREERTOS_SO_UDPCKSUM_OUT;

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    usGenerateChecksum_ExpectAnyArgsAndReturn( ulDefaultProtoChecksum );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE, ipCORRECT_CRC );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, pxUDPPacket->xIPHeader.ucProtocol );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ), FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usBoundPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL( ulDefaultIPv4Address, pxUDPPacket->xIPHeader.ulSourceIPAddress );
    TEST_ASSERT_EQUAL( 1, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache hit. But the buffer length is
 * less than minimum requirement.
 */
void test_vProcessGeneratedUDPPacket_IPv4_UDPCacheHitLessBufferLength()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    UDPPacket_t * pxUDPPacket;
    size_t xBufferLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES - 1;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();

    /* To trigger checksum generation. */
    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] |= FREERTOS_SO_UDPCKSUM_OUT;
    pxNetworkBuffer->xDataLength = xBufferLength;

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    usGenerateChecksum_ExpectAnyArgsAndReturn( ulDefaultProtoChecksum );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE, ipCORRECT_CRC );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, pxUDPPacket->xIPHeader.ucProtocol );
    TEST_ASSERT_EQUAL( xBufferLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ), FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usBoundPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL( ulDefaultIPv4Address, pxUDPPacket->xIPHeader.ulSourceIPAddress );
    TEST_ASSERT_EQUAL( 1, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache hit with different endpoint.
 */
void test_vProcessGeneratedUDPPacket_IPv4_UDPCacheHitDiffEndPoint()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint, xDifferentEndPoint, * pxDifferentEndPoint = &xDifferentEndPoint;
    UDPPacket_t * pxUDPPacket;

    memset( &xDifferentEndPoint, 0, sizeof( xDifferentEndPoint ) );

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();

    pxNetworkBuffer->pxEndPoint = pxEndPoint;

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxDifferentEndPoint );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    usGenerateChecksum_ExpectAnyArgsAndReturn( ulDefaultProtoChecksum );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, pxUDPPacket->xIPHeader.ucProtocol );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ), FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usBoundPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL( ulDefaultIPv4Address, pxUDPPacket->xIPHeader.ulSourceIPAddress );
    TEST_ASSERT_EQUAL( 1, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send LLMNR UDP and get a cache hit.
 */
void test_vProcessGeneratedUDPPacket_IPv4_UDPCacheHitLLMNR()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    UDPPacket_t * pxUDPPacket;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();

    /* To trigger checksum generation. */
    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] |= FREERTOS_SO_UDPCKSUM_OUT;
    pxNetworkBuffer->xIPAddress.ulIP_IPv4 = ipLLMNR_IP_ADDR;

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    usGenerateChecksum_ExpectAnyArgsAndReturn( ulDefaultProtoChecksum );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE, ipCORRECT_CRC );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, pxUDPPacket->xIPHeader.ucProtocol );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ), FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usBoundPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL( ulDefaultIPv4Address, pxUDPPacket->xIPHeader.ulSourceIPAddress );
    TEST_ASSERT_EQUAL( 1, xIsIfOutCalled );
    TEST_ASSERT_EQUAL( 0x01, pxUDPPacket->xIPHeader.ucTimeToLive );
}

/**
 * @brief To validate the flow to send MDNS UDP and get a cache hit.
 */
void test_vProcessGeneratedUDPPacket_IPv4_UDPCacheHitMDNS()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    UDPPacket_t * pxUDPPacket;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();

    /* To trigger checksum generation. */
    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] |= FREERTOS_SO_UDPCKSUM_OUT;
    pxNetworkBuffer->xIPAddress.ulIP_IPv4 = ipMDNS_IP_ADDRESS;

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    usGenerateChecksum_ExpectAnyArgsAndReturn( ulDefaultProtoChecksum );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE, ipCORRECT_CRC );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, pxUDPPacket->xIPHeader.ucProtocol );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ), FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usBoundPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL( ulDefaultIPv4Address, pxUDPPacket->xIPHeader.ulSourceIPAddress );
    TEST_ASSERT_EQUAL( 1, xIsIfOutCalled );
    TEST_ASSERT_EQUAL( 0xFF, pxUDPPacket->xIPHeader.ucTimeToLive );
}

/**
 * @brief To validate the flow to send UDP and get a cache hit
 * but there is no network interface in endpoint.
 */
void test_vProcessGeneratedUDPPacket_IPv4_UDPCacheHitNoInterface()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    UDPPacket_t * pxUDPPacket;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();
    pxEndPoint->pxNetworkInterface = NULL;

    /* To trigger checksum generation. */
    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] |= FREERTOS_SO_UDPCKSUM_OUT;

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    usGenerateChecksum_ExpectAnyArgsAndReturn( ulDefaultProtoChecksum );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE, ipCORRECT_CRC );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, pxUDPPacket->xIPHeader.ucProtocol );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ), FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usBoundPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL( ulDefaultIPv4Address, pxUDPPacket->xIPHeader.ulSourceIPAddress );
    TEST_ASSERT_EQUAL( 0, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache hit
 * but there is no output function in network interface.
 */
void test_vProcessGeneratedUDPPacket_IPv4_UDPCacheHitInterfaceNoOutput()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    UDPPacket_t * pxUDPPacket;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();
    pxEndPoint->pxNetworkInterface->pfOutput = NULL;

    /* To trigger checksum generation. */
    pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] |= FREERTOS_SO_UDPCKSUM_OUT;

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    usGenerateChecksum_ExpectAnyArgsAndReturn( ulDefaultProtoChecksum );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE, ipCORRECT_CRC );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, pxUDPPacket->xIPHeader.ucProtocol );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ), FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usBoundPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL( ulDefaultIPv4Address, pxUDPPacket->xIPHeader.ulSourceIPAddress );
    TEST_ASSERT_EQUAL( 0, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache hit but no matching endpoint.
 */
void test_vProcessGeneratedUDPPacket_IPv4_UDPCacheHitNoEndPoint()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint;
    UDPPacket_t * pxUDPPacket;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = NULL;

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheHit );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();
    uxIPHeaderSizePacket_ExpectAndReturn( pxNetworkBuffer, ipSIZE_OF_IPv4_HEADER );
    usGenerateChecksum_ExpectAnyArgsAndReturn( ulDefaultProtoChecksum );
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, pxUDPPacket->xIPHeader.ucProtocol );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ), FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usBoundPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usDestinationPort );
    TEST_ASSERT_EQUAL( 0, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache miss but
 * matching endpoint is found.
 */
void test_vProcessGeneratedUDPPacket_IPv4_UDPCacheMissEndPointFound()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint, * pxEndPointNull = NULL;
    UDPPacket_t * pxUDPPacket;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheMiss );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPointNull );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();

    vARPRefreshCacheEntry_Expect( NULL, pxNetworkBuffer->xIPAddress.ulIP_IPv4, NULL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAndReturn( pxNetworkBuffer->xIPAddress.ulIP_IPv4, 0, pxEndPoint );
    FreeRTOS_FindEndPointOnNetMask_IgnoreArg_ulWhere();

    vARPGenerateRequestPacket_Expect( pxNetworkBuffer );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pxEndPoint, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( 1, xIsIfOutCalled );
}

/**
 * @brief To validate the flow to send UDP and get a cache miss and
 * matching endpoint is not found.
 */
void test_vProcessGeneratedUDPPacket_IPv4_UDPCacheMissEndPointNotFound()
{
    BaseType_t xReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    NetworkEndPoint_t * pxEndPoint, * pxEndPointNull = NULL;
    UDPPacket_t * pxUDPPacket;

    pxNetworkBuffer = prvPrepareDefaultNetworkbuffer( ipPROTOCOL_UDP );
    pxEndPoint = prvPrepareDefaultIPv4EndPoint();

    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eARPGetCacheEntry_ExpectAndReturn( &( pxNetworkBuffer->xIPAddress.ulIP_IPv4 ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), NULL, eARPCacheMiss );
    eARPGetCacheEntry_IgnoreArg_ppxEndPoint();
    eARPGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPointNull );
    eARPGetCacheEntry_IgnoreArg_pulIPAddress();

    vARPRefreshCacheEntry_Expect( NULL, pxNetworkBuffer->xIPAddress.ulIP_IPv4, NULL );
    FreeRTOS_FindEndPointOnNetMask_ExpectAndReturn( pxNetworkBuffer->xIPAddress.ulIP_IPv4, 0, NULL );
    FreeRTOS_FindEndPointOnNetMask_IgnoreArg_ulWhere();
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vProcessGeneratedUDPPacket_IPv4( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer->pxEndPoint );
    TEST_ASSERT_EQUAL( 0, xIsIfOutCalled );
}
