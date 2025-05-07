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

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IPv6.h"

/* ===========================  EXTERN VARIABLES  =========================== */

/* The basic length for one IPv6 extension headers. */
#define TEST_IPv6_EXTENSION_HEADER_LENGTH             ( 8U )

/* The default length ofIPv6 extension headers in unit test. */
#define TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH    ( 7U * TEST_IPv6_EXTENSION_HEADER_LENGTH )

/* First IPv6 address is 2001:1234:5678::5 */
const IPv6_Address_t xIPAddressFive = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05 };

/* Second IPv6 address is 2001:1234:5678::10 */
const IPv6_Address_t xIPAddressTen = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10 };

/* MAC Address for endpoint. */
const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };

/* ======================== Stub Callback Functions ========================= */

static NetworkEndPoint_t * prvInitializeEndpoint()
{
    static NetworkEndPoint_t xEndpoint;

    memset( &xEndpoint, 0, sizeof( xEndpoint ) );
    xEndpoint.bits.bIPv6 = 1U;
    memcpy( xEndpoint.ipv6_settings.xIPAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    return &xEndpoint;
}

/*
 * Prepare a packet have extension with following order. Check if eHandleIPv6ExtensionHeaders determines to process it.
 *  - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *  - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *  - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *  - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *  - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *  - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *  - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 */
static NetworkBufferDescriptor_t * prvInitializeNetworkDescriptorWithExtensionHeader( uint8_t ucProtocol )
{
    static NetworkBufferDescriptor_t xNetworkBuffer;
    /* Ethernet header + IPv6 header + Maximum protocol header + IPv6 Extension Headers + 1 payload */
    static uint8_t pcNetworkBuffer[ sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) + TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH + sizeof( ICMPHeader_IPv6_t ) + 1U ];
    EthernetHeader_t * pxEthHeader = ( EthernetHeader_t * ) pcNetworkBuffer;
    IPHeader_IPv6_t * pxIPv6Header = ( IPHeader_IPv6_t * ) &( pcNetworkBuffer[ sizeof( EthernetHeader_t ) ] );
    uint8_t * pxIPv6ExtHeader = ( uint8_t * ) &( pcNetworkBuffer[ sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) ] );
    size_t uxIndex = sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t );
    uint8_t ucProtocolHeaderSize;

    if( ucProtocol == ipPROTOCOL_TCP )
    {
        ucProtocolHeaderSize = sizeof( TCPHeader_t );
    }
    else if( ucProtocol == ipPROTOCOL_UDP )
    {
        ucProtocolHeaderSize = sizeof( UDPHeader_t );
    }
    else if( ucProtocol == ipPROTOCOL_ICMP_IPv6 )
    {
        ucProtocolHeaderSize = sizeof( ICMPHeader_IPv6_t );
    }
    else
    {
        TEST_ASSERT_TRUE( false );
    }

    /* Initialize network buffer descriptor. */
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    xNetworkBuffer.pxEndPoint = prvInitializeEndpoint();
    xNetworkBuffer.pucEthernetBuffer = ( uint8_t * ) pcNetworkBuffer;
    xNetworkBuffer.xDataLength = sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) + TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH + ucProtocolHeaderSize + 1U;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxEthHeader->xDestinationAddress.ucBytes, ucMACAddress, sizeof( ucMACAddress ) );
    memcpy( pxEthHeader->xSourceAddress.ucBytes, ucMACAddress, sizeof( ucMACAddress ) );
    pxEthHeader->usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxIPv6Header->xSourceAddress.ucBytes, xIPAddressTen.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( pxIPv6Header->xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, sizeof( IPv6_Address_t ) );
    pxIPv6Header->usPayloadLength = FreeRTOS_htons( TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH + ucProtocolHeaderSize + 1U ); /* Extension header length + protocol header + payload */
    pxIPv6Header->ucNextHeader = ipIPv6_EXT_HEADER_HOP_BY_HOP;
    /* Append extension headers */
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_ROUTING_HEADER;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_FRAGMENT_HEADER;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_SECURE_PAYLOAD;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_AUTHEN_HEADER;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_DESTINATION_OPTIONS;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ipIPv6_EXT_HEADER_MOBILITY_HEADER;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;
    pcNetworkBuffer[ uxIndex ] = ucProtocol;
    pcNetworkBuffer[ uxIndex + 1 ] = 0;
    uxIndex += 8;

    return &xNetworkBuffer;
}
