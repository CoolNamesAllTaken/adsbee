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
#include "mock_IPv4_DiffConfig_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_Routing.h"

#include "FreeRTOS_IPv4.h"

/*#include "FreeRTOS_IP_stubs.c" */
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

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
 * @brief test_prvAllowIPPacketIPv4_BroadcastSourceIP
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when source IP address
 * is broadcast, which is not allowed.
 */
void test_prvAllowIPPacketIPv4_BroadcastSourceIP( void )
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

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xFFFFFFFF;

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_BufferLengthLessThanMinimum
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when buffer size is
 * less than IP packet minimum requirement.
 */
void test_prvAllowIPPacketIPv4_BufferLengthLessThanMinimum( void )
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
    pxNetworkBuffer->xDataLength = 0;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_UDPCheckSumZero
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * UDP checksum is zero, which is not allowed.
 */
void test_prvAllowIPPacketIPv4_UDPCheckSumZero( void )
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
    /* Set correct length. */
    pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t );
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( UDPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_UDP_HappyPath
 * To validate if prvAllowIPPacketIPv4() returns eProcessBuffer for UDP happy path.
 */
void test_prvAllowIPPacketIPv4_UDP_HappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndpoint;
    /* Set correct length. */
    pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t );
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( UDPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    pxProtPack = ( ( ProtocolPacket_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxHeaderLength - ipSIZE_OF_IPv4_HEADER ] ) );

    /* Non-zero checksum. */
    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0xFF12;


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_TCP_HappyPath
 * To validate if prvAllowIPPacketIPv4() returns eProcessBuffer for TCP happy path.
 */
void test_prvAllowIPPacketIPv4_TCP_HappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndpoint;
    /* Set correct length. */
    pxNetworkBuffer->xDataLength = sizeof( TCPPacket_t );
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( UDPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;


    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL ); /* From prvAllowIPPacketIPv4() */

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvCheckIP4HeaderOptions_AlwaysRelease
 * To validate if prvCheckIP4HeaderOptions() returns eReleaseBuffer in any case.
 */
void test_prvCheckIP4HeaderOptions_AlwaysRelease( void )
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer;

    eResult = prvCheckIP4HeaderOptions( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );

    eResult = prvCheckIP4HeaderOptions( NULL );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}
