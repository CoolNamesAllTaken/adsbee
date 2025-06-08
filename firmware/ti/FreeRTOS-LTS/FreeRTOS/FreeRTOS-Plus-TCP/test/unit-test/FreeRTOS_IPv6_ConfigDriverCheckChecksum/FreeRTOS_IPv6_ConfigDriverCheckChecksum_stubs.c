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

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IPv6.h"

/* ===========================  EXTERN VARIABLES  =========================== */


/* First IPv6 address is 2001:1234:5678::5 */
const IPv6_Address_t xIPAddressFive = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05 };

/* Second IPv6 address is 2001:1234:5678::10 */
const IPv6_Address_t xIPAddressTen = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10 };

/* MAC Address for endpoint. */
const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };

/* Default payload length in this test. */
#define TEST_DEFAULT_PROTOCOL_PAYLOAD_LENGTH    ( 8U )

/* ======================== Stub Callback Functions ========================= */

NetworkEndPoint_t * prvInitializeEndpoint()
{
    static NetworkEndPoint_t xEndpoint;

    memset( &xEndpoint, 0, sizeof( xEndpoint ) );
    xEndpoint.bits.bIPv6 = 1U;
    memcpy( xEndpoint.ipv6_settings.xIPAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    return &xEndpoint;
}

/*
 * Prepare a network buffer with following format:
 *  - Ethernet Header
 *  - IPv6 Header
 *  - TCP Header
 *  - 8 Bytes Payload
 */
NetworkBufferDescriptor_t * prvInitializeNetworkDescriptor()
{
    static NetworkBufferDescriptor_t xNetworkBuffer;
    static uint8_t pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) + TEST_DEFAULT_PROTOCOL_PAYLOAD_LENGTH ];
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pcNetworkBuffer;

    /* Initialize network buffer descriptor. */
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    xNetworkBuffer.pxEndPoint = prvInitializeEndpoint();
    xNetworkBuffer.pucEthernetBuffer = ( uint8_t * ) pxTCPPacket;
    xNetworkBuffer.xDataLength = sizeof( TCPPacket_IPv6_t ) + TEST_DEFAULT_PROTOCOL_PAYLOAD_LENGTH;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucMACAddress, sizeof( ucMACAddress ) );
    memcpy( pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes, ucMACAddress, sizeof( ucMACAddress ) );
    pxTCPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xIPAddressTen.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, sizeof( IPv6_Address_t ) );
    pxTCPPacket->xIPHeader.ucVersionTrafficClass |= 6U << 4;
    pxTCPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( sizeof( TCPHeader_t ) + TEST_DEFAULT_PROTOCOL_PAYLOAD_LENGTH );
    pxTCPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_TCP;

    return &xNetworkBuffer;
}
