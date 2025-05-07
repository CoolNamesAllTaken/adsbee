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
#include "FreeRTOS_IP_Private.h"

/* =========================== EXTERN VARIABLES =========================== */

NetworkInterface_t xInterfaces[ 1 ];

BaseType_t xCallEventHook;

QueueHandle_t xNetworkEventQueue;

/* ============================ Stubs Functions =========================== */

BaseType_t xNetworkInterfaceInitialise_returnTrue( NetworkInterface_t * xInterface )
{
    return pdTRUE;
}

BaseType_t xNetworkInterfaceInitialise_returnFalse( NetworkInterface_t * xInterface )
{
    return pdFALSE;
}

BaseType_t prvChecksumICMPv6Checks_Valid( size_t uxBufferLength,
                                          struct xPacketSummary * pxSet,
                                          int NumCalls )
{
    pxSet->uxProtocolHeaderLength = ipSIZE_OF_ICMPv6_HEADER;
    return 0;
}

BaseType_t prvChecksumICMPv6Checks_BigHeaderLength( size_t uxBufferLength,
                                                    struct xPacketSummary * pxSet,
                                                    int NumCalls )
{
    pxSet->uxProtocolHeaderLength = 0xFF;
    return 0;
}

BaseType_t prvChecksumIPv6Checks_Valid( uint8_t * pucEthernetBuffer,
                                        size_t uxBufferLength,
                                        struct xPacketSummary * pxSet,
                                        int NumCalls )
{
    IPPacket_IPv6_t * pxIPPacket;

    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;

    pxSet->xIsIPv6 = pdTRUE;

    pxSet->uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
    pxSet->usPayloadLength = FreeRTOS_ntohs( pxSet->pxIPPacket_IPv6->usPayloadLength );
    pxSet->ucProtocol = pxIPPacket->xIPHeader.ucNextHeader;
    pxSet->pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] ) );
    pxSet->usProtocolBytes = pxSet->usPayloadLength;

    return 0;
}

BaseType_t prvChecksumIPv4Checks_Valid( uint8_t * pucEthernetBuffer,
                                        size_t uxBufferLength,
                                        struct xPacketSummary * pxSet,
                                        int NumCalls )
{
    IPPacket_t * pxIPPacket;

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;

    pxSet->xIsIPv6 = pdFALSE;

    pxSet->uxIPHeaderLength = ( pxIPPacket->xIPHeader.ucVersionHeaderLength & 0x0F ) * 4;
    pxSet->usPayloadLength = FreeRTOS_ntohs( pxIPPacket->xIPHeader.usLength );
    pxSet->ucProtocol = pxIPPacket->xIPHeader.ucProtocol;
    pxSet->pxProtocolHeaders = ( ProtocolHeaders_t * ) &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + pxSet->uxIPHeaderLength ] );
    pxSet->usProtocolBytes = pxSet->usPayloadLength - ipSIZE_OF_IPv4_HEADER;

    return 0;
}

BaseType_t prvChecksumIPv4Checks_UnknownProtocol( uint8_t * pucEthernetBuffer,
                                                  size_t uxBufferLength,
                                                  struct xPacketSummary * pxSet,
                                                  int NumCalls )
{
    prvChecksumIPv4Checks_Valid( pucEthernetBuffer, uxBufferLength, pxSet, NumCalls );

    pxSet->ucProtocol = 0xFF;

    return 0;
}

BaseType_t prvChecksumIPv4Checks_InvalidLength( uint8_t * pucEthernetBuffer,
                                                size_t uxBufferLength,
                                                struct xPacketSummary * pxSet,
                                                int NumCalls )
{
    BaseType_t xReturn = 0;

    prvChecksumIPv4Checks_Valid( pucEthernetBuffer, uxBufferLength, pxSet, NumCalls );

    if( uxBufferLength < sizeof( IPPacket_t ) )
    {
        pxSet->usChecksum = ipINVALID_LENGTH;
        xReturn = 4;
    }

    return xReturn;
}
