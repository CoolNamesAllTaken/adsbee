/*
 * FreeRTOS memory safety proofs with CBMC.
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* CBMC includes. */
#include "cbmc.h"

/* Function usGenerateChecksum is proven to be correct separately.
 * Check if input buffer is readable. */
uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
    __CPROVER_assert( __CPROVER_r_ok( pucNextData, uxByteCount ), "pucNextData should be readable." );
}

/* Check if input is a valid extension header ID. */
BaseType_t xIsExtensionHeader( uint8_t ucCurrentHeader )
{
    BaseType_t xReturn = pdFALSE;

    switch( ucCurrentHeader )
    {
        case ipIPv6_EXT_HEADER_HOP_BY_HOP:
        case ipIPv6_EXT_HEADER_DESTINATION_OPTIONS:
        case ipIPv6_EXT_HEADER_ROUTING_HEADER:
        case ipIPv6_EXT_HEADER_FRAGMENT_HEADER:
        case ipIPv6_EXT_HEADER_AUTHEN_HEADER:
        case ipIPv6_EXT_HEADER_SECURE_PAYLOAD:
        case ipIPv6_EXT_HEADER_MOBILITY_HEADER:
            xReturn = pdTRUE;
            break;
    }

    return xReturn;
}

/* Abstraction of xGetExtensionOrder. To ensure the result of prepared extension headers is same. */
BaseType_t xGetExtensionOrder( uint8_t ucProtocol,
                               uint8_t ucNextHeader )
{
    BaseType_t xReturn = -1;

    if( xIsExtensionHeader( ucProtocol ) != pdFALSE )
    {
        xReturn = 1;
    }

    return xReturn;
}

/* To guarantee the remaining buffer size greater than protocol header size to avoid dereference failure. */
void prvPrepareExtensionHeaders( uint8_t * pucEthernetBuffer,
                                 size_t uxBufferLength )
{
    size_t uxMinReminingSize = sizeof( ProtocolHeaders_t );
    const IPPacket_IPv6_t * pxIPPacket_IPv6 = ( const IPPacket_IPv6_t * ) pucEthernetBuffer;
    uint8_t ucNextHeader = 0U;
    size_t uxIndex = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER;
    size_t uxHopSize = 0U;
    size_t uxReturn = uxBufferLength;
    uint8_t ucCurrentHeader;

    pxIPPacket_IPv6 = ( ( const IPPacket_IPv6_t * ) pucEthernetBuffer );
    ucCurrentHeader = pxIPPacket_IPv6->xIPHeader.ucNextHeader;

    /* Check if packet has extension header. */
    if( xIsExtensionHeader( ucCurrentHeader ) != pdFALSE )
    {
        while( ( uxIndex + 8U ) < uxBufferLength )
        {
            ucNextHeader = pucEthernetBuffer[ uxIndex ];

            /* Read the length expressed in number of octets. */
            uxHopSize = ( size_t ) pucEthernetBuffer[ uxIndex + 1U ];
            /* And multiply by 8 and add the minimum size of 8. */
            uxHopSize = ( uxHopSize * 8U ) + 8U;

            if( ( uxIndex + uxHopSize ) >= uxBufferLength )
            {
                break;
            }

            uxIndex = uxIndex + uxHopSize;

            if( ( ucNextHeader == ipPROTOCOL_TCP ) ||
                ( ucNextHeader == ipPROTOCOL_UDP ) ||
                ( ucNextHeader == ipPROTOCOL_ICMP_IPv6 ) )
            {
                /* The remaining size of buffer after extension header must be greater than size of protocol header. */
                __CPROVER_assume( uxBufferLength - uxIndex >= sizeof( ProtocolHeaders_t ) );
                break;
            }

            if( xIsExtensionHeader( ucNextHeader ) == pdFALSE )
            {
                /* The remaining size of buffer after extension header must be greater than size of protocol header. */
                __CPROVER_assume( uxBufferLength - uxIndex >= sizeof( ProtocolHeaders_t ) );
                break;
            }

            ucCurrentHeader = ucNextHeader;
        }
    }
    else
    {
        /* No extension headers. */
        /* The remaining size of buffer after extension header must be greater than size of protocol header. */
        __CPROVER_assume( uxBufferLength - uxIndex >= sizeof( ProtocolHeaders_t ) );
    }
}

void harness()
{
    size_t uxBufferLength;
    uint8_t * pucEthernetBuffer;
    BaseType_t xOutgoingPacket;
    IPPacket_IPv6_t * pxIPPacket;

    /* The buffer must contain enough buffer size for ethernet header + IPv6 header and less than MTU size. */
    __CPROVER_assume( ( uxBufferLength >= ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ProtocolHeaders_t ) ) && ( uxBufferLength < ipconfigNETWORK_MTU ) );
    pucEthernetBuffer = safeMalloc( uxBufferLength );
    __CPROVER_assume( pucEthernetBuffer != NULL );
    __CPROVER_havoc_slice( pucEthernetBuffer, uxBufferLength );

    /* This test case verifies IPv6 only. */
    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;
    __CPROVER_assume( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE );

    /* Check if buffer size is enough for extension headers + protocol headers. */
    prvPrepareExtensionHeaders( pucEthernetBuffer, uxBufferLength );

    ( void ) usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );
}
