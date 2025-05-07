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
#include "mock_IPv4_DiffConfig1_list_macros.h"
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
 * @brief test_prvAllowIPPacketIPv4_BufferLengthLess
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * buffer length is less than IP packet minimum requirement.
 */
void test_prvAllowIPPacketIPv4_BufferLengthLess( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = ipSIZE_OF_IPv4_HEADER;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    ProtocolPacket_t * pxProtPack;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;
    uint32_t i;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );
    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndpoint;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x46;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    for( i = 0; i < sizeof( IPPacket_t ); i++ )
    {
        pxNetworkBuffer->xDataLength = i;
        eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

        TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    }
}

/**
 * @brief test_prvAllowIPPacketIPv4_HeaderLengthLess
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * IP header length is less than minimum requirement (0x45).
 */
void test_prvAllowIPPacketIPv4_HeaderLengthLess( void )
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
    pxNetworkBuffer->xDataLength = sizeof( TCPPacket_t );
    pxNetworkBuffer->pxEndPoint = pxEndpoint;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x45 - 2;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_HeaderLengthMore
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * IP header length is greater than maximum requirement (0x4F).
 */
void test_prvAllowIPPacketIPv4_BufferLengthLessThan( void )
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
    pxNetworkBuffer->xDataLength = sizeof( TCPPacket_t );
    pxNetworkBuffer->pxEndPoint = pxEndpoint;
    /* Set correct length. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F + 2;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_BufferLengthLessThanIPRequirement
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * buffer length is less than ethernet header + IP header.
 */
void test_prvAllowIPPacketIPv4_BufferLengthLessThanIPRequirement( void )
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
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 );

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_IPPacketLengthMoreThanTotalLength
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * buffer length is less than length in IP header.
 */
void test_prvAllowIPPacketIPv4_IPPacketLengthMoreThanTotalLength( void )
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
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxIPHeader->usLength = FreeRTOS_htons( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( TCPHeader_t ) );
    pxNetworkBuffer->xDataLength = FreeRTOS_ntohs( pxIPHeader->usLength ) - 1;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_UDP_IncorrectPacketLen
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * buffer length is less than length in UDP packet minimum requirement.
 */
void test_prvAllowIPPacketIPv4_UDP_IncorrectPacketLen( void )
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
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER - 1;
    pxIPHeader->usLength = FreeRTOS_htons( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_TCP_IncorrectPacketLen
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * buffer length is less than length in TCP packet minimum requirement.
 */
void test_prvAllowIPPacketIPv4_TCP_IncorrectPacketLen( void )
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
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_TCP;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_TCP_HEADER - 1;
    pxIPHeader->usLength = FreeRTOS_htons( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_ICMP_IncorrectPacketLen
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * buffer length is less than length in ICMP packet minimum requirement.
 */
void test_prvAllowIPPacketIPv4_ICMP_IncorrectPacketLen( void )
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
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_ICMP;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMPv4_HEADER - 1;
    pxIPHeader->usLength = FreeRTOS_htons( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_IGMP_IncorrectPacketLen
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * buffer length is less than length in IGMP packet minimum requirement.
 */
void test_prvAllowIPPacketIPv4_IGMP_IncorrectPacketLen( void )
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
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_IGMP;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMPv4_HEADER - 1;
    pxIPHeader->usLength = FreeRTOS_htons( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_NoProt
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * protocol is unknown in IP header.
 */
void test_prvAllowIPPacketIPv4_NoProt( void )
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
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = 0;
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMPv4_HEADER - 1;
    pxIPHeader->usLength = FreeRTOS_htons( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_UDP_LengthLess
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * length in IP header is less than UDP packet minimum requirement.
 */
void test_prvAllowIPPacketIPv4_UDP_LengthLess( void )
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
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxIPHeader->usLength = FreeRTOS_ntohs( ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + sizeof( pxProtPack->xUDPPacket.xUDPHeader ) - 1 );
    pxNetworkBuffer->xDataLength = ( ( pxIPHeader->ucVersionHeaderLength & 0x0F ) << 2 ) + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv4_UDP_LengthMore
 * To validate if prvAllowIPPacketIPv4() returns eReleaseBuffer when
 * length in IP header is greater than UDP packet maximum size.
 */
void test_prvAllowIPPacketIPv4_UDP_LengthMore( void )
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
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );

    pxEndpoint->ipv4_settings.ulIPAddress = 0xFFFFFFFF;

    pxIPHeader->ucVersionHeaderLength = 0x4F;

    pxIPHeader->ulDestinationIPAddress = pxEndpoint->ipv4_settings.ulIPAddress;
    /* Correct protocol. */
    pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
    pxIPHeader->usLength = FreeRTOS_ntohs( ipconfigNETWORK_MTU + 1 );
    pxNetworkBuffer->xDataLength = ipconfigNETWORK_MTU + 20;

    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    pxIPHeader->ulSourceIPAddress = 0xC0C00101;

    eResult = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}
