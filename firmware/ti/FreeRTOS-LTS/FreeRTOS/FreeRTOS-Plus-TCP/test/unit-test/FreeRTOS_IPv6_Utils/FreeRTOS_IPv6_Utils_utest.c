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
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IPv6.h"
#include "mock_FreeRTOS_Routing.h"

#include "FreeRTOS_IPv6_Utils.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_IPv6_Utils_stubs.c"

/* ===========================  EXTERN VARIABLES  =========================== */

#ifndef ipconfigTCPv6_MSS
    #define ipconfigTCPv6_MSS    ( ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_TCP_HEADER ) )
#endif

/* Setting IPv6 address as "fe80::7009" */
const IPv6_Address_t xDefaultIPAddress =
{
    0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x09
};

#define ipSIZE_OF_IPv6_PAYLOAD_LEN    20

#define ipICMP_INCORRECT_MSG_IPv6     0

/* Buffer length check of ICMPv6 packet failed. */
#define ipFAIL_INVALID_LENGTH         10
/* Non Zero failure for prvChecksumIPv6Checks  */
#define ipFAIL_LEN_CHECK              1
#define ipFAIL_PACKET_CHECK           2
#define ipPASS_IPv6Checks             0

/* =============================== Test Cases =============================== */

/**
 * @brief This function verify correctly setting
 *        a MAC address.
 */
void test_vSetMultiCastIPv6MacAddress( void )
{
    IPv6_Address_t xIPAddress;
    MACAddress_t xMACAddress;

    /* Setting IPv6 address as "fe80::7009" */
    memcpy( &xIPAddress, &xDefaultIPAddress, sizeof( IPv6_Address_t ) );
    vSetMultiCastIPv6MacAddress( &xIPAddress, &xMACAddress );

    TEST_ASSERT_EQUAL( ( uint8_t ) 0x33U, xMACAddress.ucBytes[ 0 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) 0x33U, xMACAddress.ucBytes[ 1 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 12 ], xMACAddress.ucBytes[ 2 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 13 ], xMACAddress.ucBytes[ 3 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 14 ], xMACAddress.ucBytes[ 4 ] );
    TEST_ASSERT_EQUAL( xIPAddress.ucBytes[ 15 ], xMACAddress.ucBytes[ 5 ] );
}

/**
 * @brief This function validate handling of buffer length
 *        less than the minimum packet size.
 */
void test_prvChecksumIPv6Checks_InvalidLength( void )
{
    BaseType_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCPv6_MSS ];
    /* Buffer length less than the IPv6 Header size */
    size_t uxBufferLength = sizeof( IPHeader_IPv6_t ) - 1;
    BaseType_t xOutgoingPacket;
    struct xPacketSummary xSet;

    memset( pucEthernetBuffer, 0, ipconfigTCPv6_MSS );
    xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) pucEthernetBuffer );

    usReturn = prvChecksumIPv6Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    /* Return value other than zero implies length check fail */
    TEST_ASSERT_EQUAL( ipFAIL_LEN_CHECK, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function validate handling case of
 *        incomplete IPv6 packet.
 */
void test_prvChecksumIPv6Checks_IncompleteIPv6Packet( void )
{
    BaseType_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCPv6_MSS ];
    IPHeader_IPv6_t * pxIPv6Packet;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;
    struct xPacketSummary xSet;

    memset( pucEthernetBuffer, 0, ipconfigTCPv6_MSS );

    pxIPv6Packet = ( IPHeader_IPv6_t * ) pucEthernetBuffer;
    pxIPv6Packet->usPayloadLength = ipSIZE_OF_IPv6_PAYLOAD_LEN;
    xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) pucEthernetBuffer );

    xGetExtensionOrder_ExpectAndReturn( 0, 0, -1 );

    usReturn = prvChecksumIPv6Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipFAIL_PACKET_CHECK, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function validate all length checks passing
 *        successfully.
 */
void test_prvChecksumIPv6Checks_Success( void )
{
    BaseType_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCPv6_MSS ];
    IPHeader_IPv6_t * pxIPv6Packet;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 1;
    struct xPacketSummary xSet;

    memset( pucEthernetBuffer, 0, ipconfigTCPv6_MSS );

    pxIPv6Packet = ( IPHeader_IPv6_t * ) pucEthernetBuffer;
    xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) pucEthernetBuffer );

    xGetExtensionOrder_ExpectAndReturn( 0, 0, -1 );

    usReturn = prvChecksumIPv6Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipPASS_IPv6Checks, usReturn );
}

/**
 * @brief Prepare a packet with large extension header length.
 *         - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *         - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *         - ipPROTOCOL_TCP
 */
void test_prvChecksumIPv6Checks_LargeExtensionHeader( void )
{
    BaseType_t usReturn;
    struct xPacketSummary xSet;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );
    IPHeader_IPv6_t * pxIPv6Header = ( IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    size_t uxIndex = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;

    /* Modify the extension header */
    pxIPv6Header->ucNextHeader = ipIPv6_EXT_HEADER_HOP_BY_HOP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_ROUTING_HEADER;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 200U; /* Extension header length is set to 200*8 + 8, which is larger than buffer size. */
    uxIndex += 8;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipPROTOCOL_TCP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;

    xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );

    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, 0U, 1 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, ipIPv6_EXT_HEADER_ROUTING_HEADER, 1 );

    usReturn = prvChecksumIPv6Checks( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, &xSet );

    TEST_ASSERT_EQUAL( 3, usReturn );
}

/**
 * @brief Prepare a packet have extension with following order.
 *         - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *         - ipIPv6_EXT_HEADER_HOP_BY_HOP (Hop by hop must be set in first place)
 *         - ipPROTOCOL_TCP
 */
void test_prvChecksumIPv6Checks_HopByHopInWrongOrder( void )
{
    BaseType_t usReturn;
    struct xPacketSummary xSet;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );
    IPHeader_IPv6_t * pxIPv6Header = ( IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    size_t uxIndex = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;

    /* Modify the extension header */
    pxIPv6Header->ucNextHeader = ipIPv6_EXT_HEADER_ROUTING_HEADER;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_HOP_BY_HOP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipPROTOCOL_TCP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;

    xSet.pxIPPacket_IPv6 = ( ( const IPHeader_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );

    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_ROUTING_HEADER, 0U, 7 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_ROUTING_HEADER, ipIPv6_EXT_HEADER_HOP_BY_HOP, 1 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, ipPROTOCOL_TCP, 1 );

    usReturn = prvChecksumIPv6Checks( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, &xSet );

    TEST_ASSERT_EQUAL( 3, usReturn );
}

/**
 * @brief This function verify sending an invalid length.
 */
void test_prvChecksumICMPv6Checks_Default_InvalidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_ICMPv6_HEADER - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_INCORRECT_MSG_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipFAIL_INVALID_LENGTH, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function verify sending an valid length.
 */
void test_prvChecksumICMPv6Checks_Default_ValidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_ICMPv6_HEADER + 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = 0;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipPASS_IPv6Checks, usReturn );
    TEST_ASSERT_EQUAL( ipSIZE_OF_ICMPv6_HEADER, xSet.uxProtocolHeaderLength );
}

/**
 * @brief This function verify sending an invalid length
 *        for ipICMP_PING_REQUEST_IPv6.
 */
void test_prvChecksumICMPv6Checks_PingReq_InvalidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipFAIL_INVALID_LENGTH, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function verify sending an valid length
 *        for ipICMP_PING_REQUEST_IPv6.
 */
void test_prvChecksumICMPv6Checks_PingReq_ValidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) + 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipPASS_IPv6Checks, usReturn );
    TEST_ASSERT_EQUAL( sizeof( ICMPEcho_IPv6_t ), xSet.uxProtocolHeaderLength );
}

/**
 * @brief This function verify sending an invalid length
 *        for ipICMP_PING_REPLY_IPv6.
 */
void test_prvChecksumICMPv6Checks_PingReply_InvalidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipFAIL_INVALID_LENGTH, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function verify sending an valid length
 *        for ipICMP_PING_REPLY_IPv6.
 */
void test_prvChecksumICMPv6Checks_PingReply_ValidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPEcho_IPv6_t ) + 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipPASS_IPv6Checks, usReturn );
    TEST_ASSERT_EQUAL( sizeof( ICMPEcho_IPv6_t ), xSet.uxProtocolHeaderLength );
}

/**
 * @brief This function verify sending an invalid length
 *        for ipICMP_ROUTER_SOLICITATION_IPv6.
 */
void test_prvChecksumICMPv6Checks_RS_InvalidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) - 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_SOLICITATION_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipFAIL_INVALID_LENGTH, usReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief This function verify sending an valid length
 *        for ipICMP_ROUTER_SOLICITATION_IPv6.
 */
void test_prvChecksumICMPv6Checks_RS_ValidLength( void )
{
    BaseType_t usReturn;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) + 1;
    struct xPacketSummary xSet;
    ICMPHeader_IPv6_t xICMPHeaderIPv6;
    ProtocolHeaders_t xProtocolHeaders;

    memset( &xSet, 0, sizeof( struct xPacketSummary ) );
    xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_SOLICITATION_IPv6;
    xProtocolHeaders.xICMPHeaderIPv6 = xICMPHeaderIPv6;
    xSet.uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    xSet.pxProtocolHeaders = &xProtocolHeaders;

    usReturn = prvChecksumICMPv6Checks( uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( ipPASS_IPv6Checks, usReturn );
    TEST_ASSERT_EQUAL( sizeof( ICMPRouterSolicitation_IPv6_t ), xSet.uxProtocolHeaderLength );
}

/**
 * @brief Null buffer pointer in usGetExtensionHeaderLength.
 */
void test_usGetExtensionHeaderLength_NullBuffer( void )
{
    size_t uxReturn;
    size_t uxBufferLength = 0xFF;
    uint8_t ucProtocol = 0;

    uxReturn = usGetExtensionHeaderLength( NULL, uxBufferLength, &ucProtocol );

    TEST_ASSERT_EQUAL( uxBufferLength, uxReturn );
}

/**
 * @brief Null protocol pointer in usGetExtensionHeaderLength.
 */
void test_usGetExtensionHeaderLength_NullProtocol( void )
{
    size_t uxReturn;
    size_t uxBufferLength = 10;
    uint8_t ucBuffer[ 10 ] = { 0 };

    uxReturn = usGetExtensionHeaderLength( ucBuffer, uxBufferLength, NULL );

    TEST_ASSERT_EQUAL( uxBufferLength, uxReturn );
}

/**
 * @brief Prepare a TCP packet with extension header and pass the check.
 *         - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *         - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *         - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *         - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *         - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *         - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *         - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *         - ipPROTOCOL_TCP
 *            - 1 byte payload
 */
void test_usGetExtensionHeaderLength_TCPExtensionSuccess( void )
{
    BaseType_t xReturn;
    uint8_t ucProtocol = 0;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );

    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, 0U, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, ipIPv6_EXT_HEADER_ROUTING_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_ROUTING_HEADER, ipIPv6_EXT_HEADER_FRAGMENT_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_ROUTING_HEADER, ipIPv6_EXT_HEADER_FRAGMENT_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_FRAGMENT_HEADER, ipIPv6_EXT_HEADER_SECURE_PAYLOAD, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_FRAGMENT_HEADER, ipIPv6_EXT_HEADER_SECURE_PAYLOAD, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_SECURE_PAYLOAD, ipIPv6_EXT_HEADER_AUTHEN_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_SECURE_PAYLOAD, ipIPv6_EXT_HEADER_AUTHEN_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_AUTHEN_HEADER, ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_AUTHEN_HEADER, ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, ipIPv6_EXT_HEADER_MOBILITY_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, ipIPv6_EXT_HEADER_MOBILITY_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_MOBILITY_HEADER, ipPROTOCOL_TCP, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_MOBILITY_HEADER, ipPROTOCOL_TCP, 2 );

    xReturn = usGetExtensionHeaderLength( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, &ucProtocol );

    TEST_ASSERT_EQUAL( TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH, xReturn );
    TEST_ASSERT_EQUAL( ipPROTOCOL_TCP, ucProtocol );
}

/**
 * @brief Prepare a UDP packet with extension header and pass the check.
 *         - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *         - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *         - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *         - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *         - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *         - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *         - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *         - ipPROTOCOL_UDP
 *            - 1 byte payload
 */
void test_usGetExtensionHeaderLength_UDPExtensionSuccess( void )
{
    BaseType_t xReturn;
    uint8_t ucProtocol = 0;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_UDP );

    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, 0U, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, ipIPv6_EXT_HEADER_ROUTING_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_ROUTING_HEADER, ipIPv6_EXT_HEADER_FRAGMENT_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_ROUTING_HEADER, ipIPv6_EXT_HEADER_FRAGMENT_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_FRAGMENT_HEADER, ipIPv6_EXT_HEADER_SECURE_PAYLOAD, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_FRAGMENT_HEADER, ipIPv6_EXT_HEADER_SECURE_PAYLOAD, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_SECURE_PAYLOAD, ipIPv6_EXT_HEADER_AUTHEN_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_SECURE_PAYLOAD, ipIPv6_EXT_HEADER_AUTHEN_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_AUTHEN_HEADER, ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_AUTHEN_HEADER, ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, ipIPv6_EXT_HEADER_MOBILITY_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, ipIPv6_EXT_HEADER_MOBILITY_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_MOBILITY_HEADER, ipPROTOCOL_UDP, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_MOBILITY_HEADER, ipPROTOCOL_UDP, 2 );

    xReturn = usGetExtensionHeaderLength( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, &ucProtocol );

    TEST_ASSERT_EQUAL( TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH, xReturn );
    TEST_ASSERT_EQUAL( ipPROTOCOL_UDP, ucProtocol );
}

/**
 * @brief Prepare a ICMPv6 packet with extension header and pass the check.
 *         - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *         - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *         - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *         - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *         - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *         - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *         - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *         - ipPROTOCOL_ICMP_IPv6
 *            - 1 byte payload
 */
void test_usGetExtensionHeaderLength_ICMPv6ExtensionSuccess( void )
{
    BaseType_t xReturn;
    uint8_t ucProtocol = 0;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_ICMP_IPv6 );

    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, 0U, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, ipIPv6_EXT_HEADER_ROUTING_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_ROUTING_HEADER, ipIPv6_EXT_HEADER_FRAGMENT_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_ROUTING_HEADER, ipIPv6_EXT_HEADER_FRAGMENT_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_FRAGMENT_HEADER, ipIPv6_EXT_HEADER_SECURE_PAYLOAD, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_FRAGMENT_HEADER, ipIPv6_EXT_HEADER_SECURE_PAYLOAD, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_SECURE_PAYLOAD, ipIPv6_EXT_HEADER_AUTHEN_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_SECURE_PAYLOAD, ipIPv6_EXT_HEADER_AUTHEN_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_AUTHEN_HEADER, ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_AUTHEN_HEADER, ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, ipIPv6_EXT_HEADER_MOBILITY_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, ipIPv6_EXT_HEADER_MOBILITY_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_MOBILITY_HEADER, ipPROTOCOL_ICMP_IPv6, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_MOBILITY_HEADER, ipPROTOCOL_ICMP_IPv6, 2 );

    xReturn = usGetExtensionHeaderLength( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, &ucProtocol );

    TEST_ASSERT_EQUAL( TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH, xReturn );
    TEST_ASSERT_EQUAL( ipPROTOCOL_ICMP_IPv6, ucProtocol );
}

/**
 * @brief Prepare a TCP packet with extension header but the length is not enough for extension headers.
 *         - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *         - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *         - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *         - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *         - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *         - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *         - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *         - ipPROTOCOL_TCP
 *            - 1 byte payload
 */
void test_usGetExtensionHeaderLength_ShortBufferLength( void )
{
    BaseType_t xReturn;
    uint8_t ucProtocol = 0;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );

    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ( TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH - 1 );

    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, 0U, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, ipIPv6_EXT_HEADER_ROUTING_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_ROUTING_HEADER, ipIPv6_EXT_HEADER_FRAGMENT_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_ROUTING_HEADER, ipIPv6_EXT_HEADER_FRAGMENT_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_FRAGMENT_HEADER, ipIPv6_EXT_HEADER_SECURE_PAYLOAD, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_FRAGMENT_HEADER, ipIPv6_EXT_HEADER_SECURE_PAYLOAD, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_SECURE_PAYLOAD, ipIPv6_EXT_HEADER_AUTHEN_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_SECURE_PAYLOAD, ipIPv6_EXT_HEADER_AUTHEN_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_AUTHEN_HEADER, ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_AUTHEN_HEADER, ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, ipIPv6_EXT_HEADER_MOBILITY_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, ipIPv6_EXT_HEADER_MOBILITY_HEADER, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_MOBILITY_HEADER, ipPROTOCOL_TCP, 2 );

    xReturn = usGetExtensionHeaderLength( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, &ucProtocol );

    TEST_ASSERT_EQUAL( pxNetworkBuffer->xDataLength, xReturn );
}

/**
 * @brief Prepare a TCP packet with extension header but one of them in the middle is invalid.
 *         - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *         - 0xFF (invalid)
 */
void test_usGetExtensionHeaderLength_InvalidHeader( void )
{
    BaseType_t xReturn;
    uint8_t ucProtocol = 0;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ipPROTOCOL_TCP );
    IPHeader_IPv6_t * pxIPv6Header = ( IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    size_t uxIndex = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;

    /* Modify the extension header */
    pxIPv6Header->ucNextHeader = ipIPv6_EXT_HEADER_HOP_BY_HOP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = 0xFF;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipPROTOCOL_TCP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;

    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, 0U, 2 );
    xGetExtensionOrder_ExpectAndReturn( ipIPv6_EXT_HEADER_HOP_BY_HOP, 0xFF, 2 );
    xGetExtensionOrder_ExpectAndReturn( 0xFF, ipPROTOCOL_TCP, -1 );

    xReturn = usGetExtensionHeaderLength( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, &ucProtocol );

    TEST_ASSERT_EQUAL( pxNetworkBuffer->xDataLength, xReturn );
}

/* This variable will be set when pfAddAllowedMAC() is called by vIPNetworkUpCalls(). */
static BaseType_t xMACAddFunctionCalled;
static BaseType_t xMACRemoveFunctionCalled;

static void pfAddAllowedMAC( struct xNetworkInterface * pxInterface,
                             const uint8_t * pucMacAddress )
{
    xMACAddFunctionCalled = pdTRUE;
}

static void pfRemoveAllowedMAC( struct xNetworkInterface * pxInterface,
                                const uint8_t * pucMacAddress )
{
    xMACRemoveFunctionCalled = pdTRUE;
}

/**
 * @brief Check for assert if endpoint is NULL
 */
void test_vManageSolicitedNodeAddress_NoEndPoint_CatchAssert( void )
{
    catch_assert( vManageSolicitedNodeAddress( NULL, pdTRUE ) );
}


/**
 * @brief Check for assert if interface is NULL
 */
void test_vManageSolicitedNodeAddress_NoInterface_CatchAssert( void )
{
    NetworkEndPoint_t xEndPoint = { 0 };

    catch_assert( vManageSolicitedNodeAddress( &xEndPoint, pdTRUE ) );
}


/**
 * @brief Validate the case were the network is going up
 */
void test_vManageSolicitedNodeAddress_NetworkGoingUp( void )
{
    NetworkInterface_t xInterface = { 0 };
    NetworkEndPoint_t xEndPoint = { 0 };
    BaseType_t xMACAddExpected = pdFALSE;
    /* Use the local-link address fe80::7009 */
    static const uint8_t ucAddress[ 16 ] =
    {
        0xFEU, 0x80U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x70U, 0x09U
    };


    /* Happy path eIPv6_LinkLocal */
    xInterface.pfAddAllowedMAC = &pfAddAllowedMAC;
    xInterface.pfRemoveAllowedMAC = &pfRemoveAllowedMAC;
    xInterface.pxEndPoint = &xEndPoint;

    xEndPoint.bits.bEndPointUp = pdFALSE;
    xEndPoint.bits.bCallDownHook = pdFALSE_UNSIGNED;
    xEndPoint.bits.bWantDHCP = pdFALSE_UNSIGNED;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.pxNetworkInterface = &xInterface;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, ucAddress, ipSIZE_OF_IPv6_ADDRESS );

    xMACAddFunctionCalled = pdFALSE;

    xIPv6_GetIPType_ExpectAndReturn( &xEndPoint.ipv6_settings.xIPAddress, eIPv6_LinkLocal );

    vManageSolicitedNodeAddress( &xEndPoint, pdTRUE );

    TEST_ASSERT_EQUAL( pdTRUE, xMACAddFunctionCalled );

    /* No MAC address add handler */
    xInterface.pfAddAllowedMAC = NULL;
    xInterface.pfRemoveAllowedMAC = &pfRemoveAllowedMAC;
    xInterface.pxEndPoint = &xEndPoint;

    xMACAddFunctionCalled = pdFALSE;

    xIPv6_GetIPType_ExpectAndReturn( &xEndPoint.ipv6_settings.xIPAddress, eIPv6_LinkLocal );

    vManageSolicitedNodeAddress( &xEndPoint, pdTRUE );

    TEST_ASSERT_EQUAL( pdFALSE, xMACAddFunctionCalled );

    /* Happy path eIPv6_SiteLocal */
    xInterface.pfAddAllowedMAC = &pfAddAllowedMAC;
    xInterface.pfRemoveAllowedMAC = &pfRemoveAllowedMAC;
    xInterface.pxEndPoint = &xEndPoint;

    xMACAddFunctionCalled = pdFALSE;

    xIPv6_GetIPType_ExpectAndReturn( &xEndPoint.ipv6_settings.xIPAddress, eIPv6_SiteLocal );

    vManageSolicitedNodeAddress( &xEndPoint, pdTRUE );

    TEST_ASSERT_EQUAL( pdTRUE, xMACAddFunctionCalled );

    /* Happy path eIPv6_Global */
    xInterface.pfAddAllowedMAC = &pfAddAllowedMAC;
    xInterface.pfRemoveAllowedMAC = &pfRemoveAllowedMAC;
    xInterface.pxEndPoint = &xEndPoint;

    xMACAddFunctionCalled = pdFALSE;

    xIPv6_GetIPType_ExpectAndReturn( &xEndPoint.ipv6_settings.xIPAddress, eIPv6_Global );

    vManageSolicitedNodeAddress( &xEndPoint, pdTRUE );

    TEST_ASSERT_EQUAL( pdTRUE, xMACAddFunctionCalled );

    /* Unhappy path eIPv6_Loopback */
    xInterface.pfAddAllowedMAC = &pfAddAllowedMAC;
    xInterface.pfRemoveAllowedMAC = &pfRemoveAllowedMAC;
    xInterface.pxEndPoint = &xEndPoint;

    xMACAddFunctionCalled = pdFALSE;

    xIPv6_GetIPType_ExpectAndReturn( &xEndPoint.ipv6_settings.xIPAddress, eIPv6_Loopback );

    vManageSolicitedNodeAddress( &xEndPoint, pdTRUE );

    TEST_ASSERT_EQUAL( pdFALSE, xMACAddFunctionCalled );
}

/**
 * @brief Validate the case were the network is going down
 */
void test_vManageSolicitedNodeAddress_NetworkGoingDown( void )
{
    NetworkInterface_t xInterface = { 0 };
    NetworkEndPoint_t xEndPoint = { 0 };
    BaseType_t xMACAddExpected = pdFALSE;
    /* Use the local-link address fe80::7009 */
    static const uint8_t ucAddress[ 16 ] =
    {
        0xFEU, 0x80U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x70U, 0x09U
    };


    /* Happy path eIPv6_LinkLocal */
    xInterface.pfAddAllowedMAC = &pfAddAllowedMAC;
    xInterface.pfRemoveAllowedMAC = &pfRemoveAllowedMAC;
    xInterface.pxEndPoint = &xEndPoint;

    xEndPoint.bits.bEndPointUp = pdFALSE;
    xEndPoint.bits.bCallDownHook = pdFALSE_UNSIGNED;
    xEndPoint.bits.bWantDHCP = pdFALSE_UNSIGNED;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.pxNetworkInterface = &xInterface;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, ucAddress, ipSIZE_OF_IPv6_ADDRESS );

    xMACRemoveFunctionCalled = pdFALSE;

    xIPv6_GetIPType_ExpectAndReturn( &xEndPoint.ipv6_settings.xIPAddress, eIPv6_LinkLocal );

    vManageSolicitedNodeAddress( &xEndPoint, pdFALSE );

    TEST_ASSERT_EQUAL( pdTRUE, xMACRemoveFunctionCalled );

    /* No MAC address add handler */
    xInterface.pfAddAllowedMAC = NULL;
    xInterface.pfRemoveAllowedMAC = NULL;
    xInterface.pxEndPoint = &xEndPoint;

    xMACRemoveFunctionCalled = pdFALSE;

    xIPv6_GetIPType_ExpectAndReturn( &xEndPoint.ipv6_settings.xIPAddress, eIPv6_LinkLocal );

    vManageSolicitedNodeAddress( &xEndPoint, pdFALSE );

    TEST_ASSERT_EQUAL( pdFALSE, xMACRemoveFunctionCalled );

    /* Happy path eIPv6_SiteLocal */
    xInterface.pfAddAllowedMAC = &pfAddAllowedMAC;
    xInterface.pfRemoveAllowedMAC = &pfRemoveAllowedMAC;
    xInterface.pxEndPoint = &xEndPoint;

    xMACRemoveFunctionCalled = pdFALSE;

    xIPv6_GetIPType_ExpectAndReturn( &xEndPoint.ipv6_settings.xIPAddress, eIPv6_SiteLocal );

    vManageSolicitedNodeAddress( &xEndPoint, pdFALSE );

    TEST_ASSERT_EQUAL( pdTRUE, xMACRemoveFunctionCalled );

    /* Happy path eIPv6_Global */
    xInterface.pfAddAllowedMAC = &pfAddAllowedMAC;
    xInterface.pfRemoveAllowedMAC = &pfRemoveAllowedMAC;
    xInterface.pxEndPoint = &xEndPoint;

    xMACRemoveFunctionCalled = pdFALSE;

    xIPv6_GetIPType_ExpectAndReturn( &xEndPoint.ipv6_settings.xIPAddress, eIPv6_Global );

    vManageSolicitedNodeAddress( &xEndPoint, pdFALSE );

    TEST_ASSERT_EQUAL( pdTRUE, xMACRemoveFunctionCalled );

    /* Unhappy path eIPv6_Loopback */
    xInterface.pfAddAllowedMAC = &pfAddAllowedMAC;
    xInterface.pfRemoveAllowedMAC = &pfRemoveAllowedMAC;
    xInterface.pxEndPoint = &xEndPoint;

    xMACRemoveFunctionCalled = pdFALSE;

    xIPv6_GetIPType_ExpectAndReturn( &xEndPoint.ipv6_settings.xIPAddress, eIPv6_Loopback );

    vManageSolicitedNodeAddress( &xEndPoint, pdFALSE );

    TEST_ASSERT_EQUAL( pdFALSE, xMACRemoveFunctionCalled );
}
