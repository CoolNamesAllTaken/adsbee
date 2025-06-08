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
#include "FreeRTOSIPConfig.h"
#include "mock_IPv4_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_Routing.h"

#include "FreeRTOS_IPv4.h"

#include "catch_assert.h"


/* =========================== type definitions =========================== */

struct xIPv4Address
{
    uint32_t ulAddress;
    BaseType_t bIsLoopback;
};

/* =========================== EXTERN VARIABLES =========================== */

const MACAddress_t xBroadcastMACAddress = { { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff } };

/* ============================ Unity Fixtures ============================ */

/*! called before each test case */
void setUp( void )
{
}

/*! called after each test case */
void tearDown( void )
{
}

/* ======================== Stub Callback Functions ========================= */

/* ============================== Test Cases ============================== */

/**
 * @brief test_xIsIPv4Multicast_NotMultiCast
 * To validate if xIsIPv4Multicast() judges 0x0 is not a multicast address.
 */
void test_xIsIPv4Multicast_NotMultiCast( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0;

    xReturn = xIsIPv4Multicast( ulIPAddress );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief test_xIsIPv4Multicast_NotMultiCastF0000000
 * To validate if xIsIPv4Multicast() judges 0xF0000000 is not a multicast address.
 */
void test_xIsIPv4Multicast_NotMultiCastF0000000( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = FreeRTOS_htonl( 0xF0000000 );

    xReturn = xIsIPv4Multicast( ulIPAddress );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief test_xIsIPv4Multicast_IsMultiCast
 * To validate if xIsIPv4Multicast() judges 0xEFFFFFFF is a multicast address.
 */
void test_xIsIPv4Multicast_IsMultiCast( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = FreeRTOS_htonl( 0xF0000000 - 1 );

    xReturn = xIsIPv4Multicast( ulIPAddress );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_prvAllowIPPacketIPv4_LessHeaderLength
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when ucVersionHeaderLength
 * is less than ipIPV4_VERSION_HEADER_LENGTH_MIN.
 */
void test_prvAllowIPPacketIPv4_LessHeaderLength( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ipIPV4_VERSION_HEADER_LENGTH_MIN - 1;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_FragmentedPacket
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when fragment flag (ipFRAGMENT_OFFSET_BIT_MASK)
 * is set. IP fragmentation is not supported in stack.
 */
void test_prvAllowIPPacketIPv4_FragmentedPacket( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->usFragmentOffset = ipFRAGMENT_OFFSET_BIT_MASK;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_MoreFragmentedPacket
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when fragment flag (ipFRAGMENT_FLAGS_MORE_FRAGMENTS)
 * is set. IP fragmentation is not supported in stack.
 */
void test_prvAllowIPPacketIPv4_MoreFragmentedPacket( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->usFragmentOffset = ipFRAGMENT_FLAGS_MORE_FRAGMENTS;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_GreaterHeaderLength
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when ucVersionHeaderLength
 * is greater than ipIPV4_VERSION_HEADER_LENGTH_MAX.
 */
void test_prvAllowIPPacketIPv4_GreaterHeaderLength( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->ucVersionHeaderLength = 0xFF;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_NotMatchingIP
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when no endpoint
 * matches the input packet.
 */
void test_prvAllowIPPacketIPv4_NotMatchingIP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress + 1;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */
    FreeRTOS_IsNetworkUp_ExpectAndReturn( pdTRUE );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPMatch
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * source IP is broadcast address, which is not allowed.
 */
void test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPMatch( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndpoint;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( pxEndpoint ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPBrdCast
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * source IP is broadcast address, which is not allowed. Even the
 * destination IP address is also broadcast.
 */
void test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPBrdCast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = 0xFFFFFFFF;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPLLMNR
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * source IP is broadcast address, which is not allowed. Even the
 * destination IP address is LLMNR.
 */
void test_prvAllowIPPacketIPv4_SourceIPBrdCast_DestIPLLMNR( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xAB12CD34;

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = ipLLMNR_IP_ADDR;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_SourceIPBrdCast_NoLocalIP
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * source IP is broadcast address, which is not allowed. And
 * the destination IP is 0.
 */
void test_prvAllowIPPacketIPv4_SourceIPBrdCast_NoLocalIP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = 0;

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */
    FreeRTOS_IsNetworkUp_ExpectAndReturn( pdFALSE );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_DestMACBrdCast_DestIPUnicast
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * destination MAC address is broadcast address but the IP address is not broadcast address.
 * And the endpoint is up.
 */
void test_prvAllowIPPacketIPv4_DestMACBrdCast_DestIPUnicast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = 0x00;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */
    FreeRTOS_IsNetworkUp_ExpectAndReturn( pdTRUE );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_SrcMACBrdCast
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * source MAC address is broadcast address, which is not allowed.
 */
void test_prvAllowIPPacketIPv4_SrcMACBrdCast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = 0xFFFFFFFF;

    memcpy( pxIPPacket->xEthernetHeader.xSourceAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_SrcMACBrdCastDestMACBrdCast
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * source MAC address is broadcast address, which is not allowed. Even
 * the destination MAC address is also broadcast address.
 */
void test_prvAllowIPPacketIPv4_SrcMACBrdCastDestMACBrdCast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = 0xFFFFFFFF;

    memcpy( pxIPPacket->xEthernetHeader.xSourceAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_SrcIPAddrIsMulticast
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * source IP address is multicast address, which is not allowed.
 */
void test_prvAllowIPPacketIPv4_SrcIPAddrIsMulticast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 1, sizeof( NetworkBufferDescriptor_t ) );
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxNetworkBuffer->pxEndPoint = NULL;

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = FreeRTOS_htonl( 0xE0000000 + 1 );


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_IncorrectChecksum
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * IP checksum is incorrect.
 */
void test_prvAllowIPPacketIPv4_IncorrectChecksum( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC - 1 );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_IncorrectChecksum
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * protocol checksum is incorrect.
 */
void test_prvAllowIPPacketIPv4_IncorrectProtocolChecksum( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAndReturn( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE, ( uint16_t ) ( ipCORRECT_CRC + 1 ) );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_HappyPath
 * To validate if prvAllowIPPacketIPv4() returns eProcessBuffer in happy path.
 */
void test_prvAllowIPPacketIPv4_HappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxNetworkBuffer->pxEndPoint = pxEndpoint;

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAndReturn( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_LoopbackHappyPath
 * To validate if prvAllowIPPacketIPv4() returns eProcessBuffer and skip checking
 * checksum when it's a loop-back packet.
 */
void test_prvAllowIPPacketIPv4_LoopbackHappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;
    const MACAddress_t xMACAddress = { { 0x11, 0x22, 0x33, 0x44, 0x55, 0x66 } };

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndpoint;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = 0x2300007FUL;
    pxIPHeader->ulSourceIPAddress = 0x2300007FUL;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( pxEndpoint );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_DestMacBroadcastIPNotBroadcast
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when destination MAC address is broadcast
 * but IP address is not broadcast.
 */
void test_prvAllowIPPacketIPv4_DestMacBroadcastIPNotBroadcast( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndpoint;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xE0E00102;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( pxEndpoint ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvCheckIP4HeaderOptions_HeaderLengthSmaller
 * To validate if prvCheckIP4HeaderOptions() reduces the length correctly
 * for options on IP header length.
 */
void test_prvCheckIP4HeaderOptions_HeaderLengthSmaller( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    /* Option length is 15 * 4 - 20 (IPv4 header) = 40 bytes */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS - sizeof( IPPacket_t ) );

    eResult = prvCheckIP4HeaderOptions( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
    TEST_ASSERT_EQUAL( ipconfigTCP_MSS - sizeof( IPPacket_t ) - 40, FreeRTOS_ntohs( pxIPHeader->usLength ) );
}

/**
 * @brief test_xIsIPv4Loopback_test
 * To validate if xIsIPv4Loopback() makes correct decisions.
 */
void test_xIsIPv4Loopback_test( void )
{
    BaseType_t xReturn, xIndex;
    uint32_t ulIPAddress = 0;
    static struct xIPv4Address pcAddresses[] =
    {
        { 0xC0A80205 /* 192.168.2.5     */, pdFALSE },
        { 0x7F000001 /* 127.0.0.1       */, pdTRUE  },
        { 0x7FFFFFFF /* 127.255.255.255 */, pdTRUE  },
        { 0x80000000 /* 128.0.0.0       */, pdFALSE },
    };
    BaseType_t xCount = sizeof( pcAddresses ) / sizeof( pcAddresses[ 0 ] );

    for( xIndex = 0; xIndex < xCount; xIndex++ )
    {
        ulIPAddress = FreeRTOS_htonl( pcAddresses[ xIndex ].ulAddress );

        xReturn = xIsIPv4Loopback( ulIPAddress );

        TEST_ASSERT_EQUAL( pcAddresses[ xIndex ].bIsLoopback, xReturn );
    }
}

/**
 * @brief test_xBadIPv4Loopback_test
 * To validate if xBadIPv4Loopback() makes correct decisions.
 * This function will be called 5 times each with different parameters.
 */
static void xRunBadIPv4Loopback( uint32_t ulSource,
                                 uint32_t ulTarget,
                                 eFrameProcessingResult_t eExpected )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint;
    NetworkEndPoint_t * pxEndpoint = &xEndpoint;
    const MACAddress_t xMACAddress = { { 0x10U, 0x20U, 0x30U, 0x40U, 0x50U, 0x60U } };

    uint32_t ulIPSource = 0;
    uint32_t ulIPTarget = 0;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    ulIPSource = FreeRTOS_htonl( ulSource );
    ulIPTarget = FreeRTOS_htonl( ulTarget );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxNetworkBuffer->pxEndPoint = pxEndpoint;

    pxEndpoint->ipv4_settings.ulIPAddress = ulIPTarget;

    /* An IP-header of 20 bytes long, IPv4. */
    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulSourceIPAddress = ulIPSource;
    pxIPHeader->ulDestinationIPAddress = ulIPTarget;

    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );

    if( eExpected != eReleaseBuffer )
    {
        FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

        usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC );

        usGenerateProtocolChecksum_ExpectAndReturn( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );
    }

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eExpected, eResult );
}

/**
 * @brief test_xBadIPv4Loopback_0_test
 * To validate if xBadIPv4Loopback() makes correct decisions.
 */
void test_xBadIPv4Loopback_0_test( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    NetworkEndPoint_t xEndpoint;
    NetworkEndPoint_t * pxEndpoint = &xEndpoint;
    const MACAddress_t xMACAddress = { { 0x10U, 0x20U, 0x30U, 0x40U, 0x50U, 0x60U } };

    uint32_t ulIPSource = 0;
    uint32_t ulIPTarget = 0;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    ulIPSource = FreeRTOS_htonl( 0xC0A80205 );
    ulIPTarget = FreeRTOS_htonl( 0xC0A80206 );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxNetworkBuffer->pxEndPoint = pxEndpoint;

    pxEndpoint->ipv4_settings.ulIPAddress = ulIPTarget;

    /* An IP-header of 20 bytes long, IPv4. */
    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulSourceIPAddress = ulIPSource;
    pxIPHeader->ulDestinationIPAddress = ulIPTarget;

    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( pxEndpoint );

    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    usGenerateChecksum_ExpectAndReturn( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ( size_t ) uxHeaderLength, ipCORRECT_CRC );

    usGenerateProtocolChecksum_ExpectAndReturn( ( uint8_t * ) ( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_xBadIPv4Loopback_1_test
 * To validate if xBadIPv4Loopback() makes correct decisions.
 */
void test_xBadIPv4Loopback_1_test( void )
{
    /* int ext           127.0.0.1   192.168.2.5 */
    xRunBadIPv4Loopback( 0x7F000001, 0xC0A80205, eReleaseBuffer );
}

/**
 * @brief test_xBadIPv4Loopback_2_test
 * To validate if xBadIPv4Loopback() makes correct decisions.
 */
void test_xBadIPv4Loopback_2_test( void )
{
    /* ext -> int        192.168.2.5 127.0.0.1 */
    xRunBadIPv4Loopback( 0xC0A80205, 0x7F000001, eReleaseBuffer );
}

/**
 * @brief test_xBadIPv4Loopback_3_test
 * To validate if xBadIPv4Loopback() makes correct decisions.
 */
void test_xBadIPv4Loopback_3_test( void )
{
/*  int -> int           127.0.0.1   127.0.0.2 */
    xRunBadIPv4Loopback( 0x7F000001, 0x7F000002, eProcessBuffer );
}
