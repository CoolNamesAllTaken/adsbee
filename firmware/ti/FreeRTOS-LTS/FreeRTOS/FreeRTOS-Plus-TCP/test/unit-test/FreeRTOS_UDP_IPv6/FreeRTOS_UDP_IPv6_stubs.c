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
#include <unity.h>

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_Routing.h"

/* ===========================  EXTERN VARIABLES  =========================== */

#define TEST_IPV4_DEFAULT_ADDRESS    ( 0x12345678 )

BaseType_t xIsIfOutCalled = 0;

IPv6_Address_t xDefaultIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

/* ======================== Stub Callback Functions ========================= */

static void UDPReceiveHandlerChecker( Socket_t xSocket,
                                      void * pData,
                                      size_t xLength,
                                      const struct freertos_sockaddr * pxFrom,
                                      const struct freertos_sockaddr * pxDest )
{
    uint8_t * pucData = ( uint8_t * ) pData;
    UDPPacket_IPv6_t * pxUDPv6Packet = ( UDPPacket_IPv6_t * ) ( pucData - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_UDP_HEADER ) );

    TEST_ASSERT_EQUAL_MEMORY( pxUDPv6Packet->xIPHeader.xSourceAddress.ucBytes, pxFrom->sin_address.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( pxUDPv6Packet->xIPHeader.xDestinationAddress.ucBytes, pxDest->sin_address.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( pxUDPv6Packet->xUDPHeader.usSourcePort, pxFrom->sin_port );
    TEST_ASSERT_EQUAL( pxUDPv6Packet->xUDPHeader.usDestinationPort, pxDest->sin_port );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, pxFrom->sin_family );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, pxDest->sin_family );
    TEST_ASSERT_EQUAL( sizeof( struct freertos_sockaddr ), pxFrom->sin_len );
    TEST_ASSERT_EQUAL( sizeof( struct freertos_sockaddr ), pxDest->sin_len );
    TEST_ASSERT_EQUAL( pxUDPv6Packet->xIPHeader.usPayloadLength - ipSIZE_OF_UDP_HEADER, xLength );
}

static BaseType_t xStubUDPReceiveHandler_Pass( Socket_t xSocket,
                                               void * pData,
                                               size_t xLength,
                                               const struct freertos_sockaddr * pxFrom,
                                               const struct freertos_sockaddr * pxDest )
{
    UDPReceiveHandlerChecker( xSocket, pData, xLength, pxFrom, pxDest );
    return 0;
}

static BaseType_t xStubUDPReceiveHandler_Fail( Socket_t xSocket,
                                               void * pData,
                                               size_t xLength,
                                               const struct freertos_sockaddr * pxFrom,
                                               const struct freertos_sockaddr * pxDest )
{
    UDPReceiveHandlerChecker( xSocket, pData, xLength, pxFrom, pxDest );
    return -1;
}

static BaseType_t xNetworkInterfaceOutput( struct xNetworkInterface * pxDescriptor,
                                           NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                           BaseType_t xReleaseAfterSend )
{
    xIsIfOutCalled = 1;

    return pdPASS;
}

static NetworkBufferDescriptor_t * prvPrepareDefaultNetworkbuffer( uint8_t ucProtocol )
{
    static NetworkBufferDescriptor_t xNetworkBuffer;
    static uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    UDPPacket_IPv6_t * pxUDPv6Packet;
    ICMPPacket_IPv6_t * pxICMPv6Packet;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usBoundPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.usPort = FreeRTOS_htons( usDestPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    if( ucProtocol == ipPROTOCOL_UDP )
    {
        pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;
        pxUDPv6Packet->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    }
    else if( ucProtocol == ipPROTOCOL_ICMP_IPv6 )
    {
        pxICMPv6Packet = ( ICMPPacket_IPv6_t * ) pucEthernetBuffer;
    }

    return &xNetworkBuffer;
}

static NetworkEndPoint_t * prvPrepareDefaultIPv6EndPoint()
{
    static NetworkEndPoint_t xEndpoint;
    static NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t * pxEndpoint = &xEndpoint;

    memset( &xEndpoint, 0, sizeof( xEndpoint ) );
    memset( &xNetworkInterface, 0, sizeof( xNetworkInterface ) );

    xNetworkInterface.pfOutput = xNetworkInterfaceOutput;

    xEndpoint.pxNetworkInterface = &xNetworkInterface;
    memcpy( xEndpoint.ipv6_settings.xIPAddress.ucBytes, xDefaultIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xEndpoint.bits.bIPv6 = pdTRUE;

    return pxEndpoint;
}

static NetworkEndPoint_t * prvPrepareDefaultIPv4EndPoint()
{
    static NetworkEndPoint_t xEndpoint;
    static NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t * pxEndpoint = &xEndpoint;

    memset( &xEndpoint, 0, sizeof( xEndpoint ) );
    memset( &xNetworkInterface, 0, sizeof( xNetworkInterface ) );

    xNetworkInterface.pfOutput = xNetworkInterfaceOutput;

    xEndpoint.pxNetworkInterface = &xNetworkInterface;
    xEndpoint.ipv4_settings.ulIPAddress = TEST_IPV4_DEFAULT_ADDRESS;
    xEndpoint.bits.bIPv6 = pdFALSE;

    return pxEndpoint;
}


void vPortEnterCritical( void )
{
}
void vPortExitCritical( void )
{
}
