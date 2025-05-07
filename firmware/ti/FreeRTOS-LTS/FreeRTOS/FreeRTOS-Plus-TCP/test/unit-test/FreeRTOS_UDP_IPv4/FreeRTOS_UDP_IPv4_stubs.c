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

/* ===========================  EXTERN VARIABLES  =========================== */

extern const uint32_t ulDefaultIPv4Address;
extern BaseType_t xIsIfOutCalled;

/* ======================== Stub Callback Functions ========================= */

void UDPReceiveHandlerChecker( Socket_t xSocket,
                               void * pData,
                               size_t xLength,
                               const struct freertos_sockaddr * pxFrom,
                               const struct freertos_sockaddr * pxDest )
{
    uint8_t * pucData = ( uint8_t * ) pData;
    UDPPacket_t * pxUDPPacket = ( UDPPacket_t * ) ( pucData - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER ) );

    TEST_ASSERT_EQUAL( pxUDPPacket->xIPHeader.ulSourceIPAddress, pxFrom->sin_address.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( pxUDPPacket->xIPHeader.ulDestinationIPAddress, pxDest->sin_address.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( pxUDPPacket->xUDPHeader.usSourcePort, pxFrom->sin_port );
    TEST_ASSERT_EQUAL( pxUDPPacket->xUDPHeader.usDestinationPort, pxDest->sin_port );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET4, pxFrom->sin_family );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET4, pxDest->sin_family );
    TEST_ASSERT_EQUAL( sizeof( struct freertos_sockaddr ), pxFrom->sin_len );
    TEST_ASSERT_EQUAL( sizeof( struct freertos_sockaddr ), pxDest->sin_len );
    TEST_ASSERT_EQUAL( pxUDPPacket->xIPHeader.usLength - ipSIZE_OF_IPv4_HEADER - ipSIZE_OF_UDP_HEADER, xLength );
}

BaseType_t xStubUDPReceiveHandler_Pass( Socket_t xSocket,
                                        void * pData,
                                        size_t xLength,
                                        const struct freertos_sockaddr * pxFrom,
                                        const struct freertos_sockaddr * pxDest )
{
    UDPReceiveHandlerChecker( xSocket, pData, xLength, pxFrom, pxDest );
    return 0;
}

BaseType_t xStubUDPReceiveHandler_Fail( Socket_t xSocket,
                                        void * pData,
                                        size_t xLength,
                                        const struct freertos_sockaddr * pxFrom,
                                        const struct freertos_sockaddr * pxDest )
{
    UDPReceiveHandlerChecker( xSocket, pData, xLength, pxFrom, pxDest );
    return -1;
}

BaseType_t xNetworkInterfaceOutput( struct xNetworkInterface * pxDescriptor,
                                    NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t xReleaseAfterSend )
{
    xIsIfOutCalled = 1;

    return pdPASS;
}

NetworkBufferDescriptor_t * prvPrepareDefaultNetworkbuffer( uint8_t ucProtocol )
{
    static NetworkBufferDescriptor_t xNetworkBuffer;
    static uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    uint16_t usSrcPort = 2048U;
    uint16_t usDestPort = 1024U;
    UDPPacket_t * pxUDPPacket;
    ICMPPacket_t * pxICMPPacket;

    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );
    memset( pucEthernetBuffer, 0, sizeof( pucEthernetBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.usBoundPort = FreeRTOS_htons( usSrcPort );
    xNetworkBuffer.usPort = FreeRTOS_htons( usDestPort );
    xNetworkBuffer.xDataLength = ipconfigTCP_MSS;

    if( ucProtocol == ipPROTOCOL_UDP )
    {
        pxUDPPacket = ( UDPPacket_t * ) pucEthernetBuffer;
        pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    }
    else if( ucProtocol == ipPROTOCOL_ICMP )
    {
        pxICMPPacket = ( ICMPPacket_t * ) pucEthernetBuffer;
    }

    return &xNetworkBuffer;
}

NetworkEndPoint_t * prvPrepareDefaultIPv4EndPoint()
{
    static NetworkEndPoint_t xEndpoint;
    static NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t * pxEndpoint = &xEndpoint;

    memset( &xEndpoint, 0, sizeof( xEndpoint ) );
    memset( &xNetworkInterface, 0, sizeof( xNetworkInterface ) );

    xNetworkInterface.pfOutput = xNetworkInterfaceOutput;

    xEndpoint.pxNetworkInterface = &xNetworkInterface;
    xEndpoint.ipv4_settings.ulIPAddress = ulDefaultIPv4Address;
    xEndpoint.bits.bIPv6 = pdFALSE;

    return pxEndpoint;
}

void vPortEnterCritical( void )
{
}

void vPortExitCritical( void )
{
}
