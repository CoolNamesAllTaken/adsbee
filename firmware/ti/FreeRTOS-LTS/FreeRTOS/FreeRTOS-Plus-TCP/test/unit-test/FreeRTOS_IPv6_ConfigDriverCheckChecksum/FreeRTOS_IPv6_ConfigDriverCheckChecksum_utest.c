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

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IPv6.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"
#include "FreeRTOS_IPv6_ConfigDriverCheckChecksum_stubs.c"

/* ===========================  EXTERN VARIABLES  =========================== */

extern const struct xIPv6_Address FreeRTOS_in6addr_any;

/* =============================== Test Cases =============================== */

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_happy_path
 * Prepare a packet with valid length. Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_happy_path()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_valid_ext_header_length
 * Prepare a IPv6 packet with extension header. Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_valid_ext_header_length()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    size_t uxIndex = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;

    /* Modify the extension header */
    pxIPPacket->xIPHeader.ucNextHeader = ipIPv6_EXT_HEADER_HOP_BY_HOP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipPROTOCOL_TCP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 0U;

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_buffer_length_less_than_ip_header
 * Prepare a packet with length less than IPv6 header. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_buffer_length_less_than_ip_header()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxNetworkBuffer->xDataLength = sizeof( IPHeader_IPv6_t ) - 1U;

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_not_an_ipv6_packet
 * Prepare a packet with IPv4 version in header. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_not_an_ipv6_packet()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxIPPacket->xIPHeader.ucVersionTrafficClass = 4U << 4;

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_buffer_length_less_than_eth_ip_header
 * Prepare a packet with length less than Ethernet header + IPv6 header. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_buffer_length_less_than_eth_ip_header()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) - 1U;

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_wrong_ip_length
 * The length in IP header is not equal to real network buffer size. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_wrong_ip_length()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    /* Modify the length in IP header to be greater than data length. */
    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( sizeof( TCPHeader_t ) + TEST_DEFAULT_PROTOCOL_PAYLOAD_LENGTH + 1U );

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_large_ext_header_length
 * The extension header length larger than real network buffer size.
 * Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_large_ext_header_length()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    size_t uxIndex = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;

    /* Modify the extension header */
    pxIPPacket->xIPHeader.ucNextHeader = ipIPv6_EXT_HEADER_HOP_BY_HOP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex ] = ipPROTOCOL_TCP;
    pxNetworkBuffer->pucEthernetBuffer[ uxIndex + 1 ] = 200U; /* 200 * 8 + 8 = 1608 bytes in this extension header. */

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_unknown_protocol
 * The protocol in IP header is unknown. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_unknown_protocol()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    /* Set next header to unknown value */
    pxIPPacket->xIPHeader.ucNextHeader = 0xFF;

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_TCP_min_requirement
 * The buffer size is less than TCP packet minimal requirement. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_TCP_min_requirement()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    /* Set next header to TCP */
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_TCP;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 1;
    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( 1 );

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_UDP_min_requirement
 * The buffer size is less than UDP packet minimal requirement. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_UDP_min_requirement()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    /* Set next header to UDP */
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_UDP;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 1;
    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( 1 );

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_ICMP_min_requirement_1
 * The buffer size is less than ICMP packet minimal requirement. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_ICMP_min_requirement_1()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    /* Set next header to ICMPv6 */
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 1;
    pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] = ipICMP_ROUTER_SOLICITATION_IPv6;
    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( 1 );

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_ICMP_min_requirement_2
 * The buffer size is less than ICMP packet minimal requirement. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_ICMP_min_requirement_2()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    /* Set next header to ICMPv6 */
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 1;
    pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] = ipICMP_ROUTER_ADVERTISEMENT_IPv6;
    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( 1 );

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_ICMP_min_requirement_3
 * The buffer size is less than ICMP packet minimal requirement. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_ICMP_min_requirement_3()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    /* Set next header to ICMPv6 */
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 1;
    pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] = ipICMP_PING_REQUEST_IPv6;
    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( 1 );

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_ICMP_min_requirement_4
 * The buffer size is less than ICMP packet minimal requirement. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_ICMP_min_requirement_4()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    /* Set next header to ICMPv6 */
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 1;
    pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] = ipICMP_PING_REPLY_IPv6;
    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( 1 );

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_ICMP_min_requirement_5
 * This is the default case for all ICMPv6 packet length testing.
 * The buffer size is less than ICMP packet minimal requirement. Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_xCheckIPv6SizeFields_length_less_than_ICMP_min_requirement_5()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    IPPacket_IPv6_t * pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    /* Set next header to ICMPv6 */
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + 1;
    pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( 1 );

    eResult = prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}


/**
 * @brief test_prvAllowIPPacketIPv6_source_unspecified_address
 * Prepare a packet with unspecified address in source address.
 * Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_source_unspecified_address()
{
    IPHeader_IPv6_t xIPv6Address;
    eFrameProcessingResult_t eResult;

    memset( &xIPv6Address, 0, sizeof( xIPv6Address ) );
    memcpy( xIPv6Address.xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( xIPv6Address.xSourceAddress.ucBytes, FreeRTOS_in6addr_any.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    eResult = prvAllowIPPacketIPv6( &xIPv6Address, NULL, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}
