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

/* Global variables. */
BaseType_t xIsIPv6;

/* Abstraction of prvPacketBuffer_to_NetworkBuffer. This function is proven separately. */
NetworkBufferDescriptor_t * __CPROVER_file_local_FreeRTOS_IP_Utils_c_prvPacketBuffer_to_NetworkBuffer( const void * pvBuffer,
                                                                                                       size_t uxOffset )
{
    __CPROVER_assert( pvBuffer != NULL, "pvBuffer shouldn't be NULL" );
}

void harness()
{
    size_t uxBufferLength;
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    uint8_t * pucIPType;
    void * pvBuffer;

    xIsIPv6 = nondet_bool();

    /* Reserve the buffer with ipconfigBUFFER_PADDING to store IP type. */
    if( xIsIPv6 )
    {
        __CPROVER_assume( uxBufferLength > sizeof( UDPPacket_IPv6_t ) + ipconfigBUFFER_PADDING );
    }
    else
    {
        __CPROVER_assume( uxBufferLength > sizeof( UDPPacket_t ) + ipconfigBUFFER_PADDING );
    }

    __CPROVER_assume( uxBufferLength < ipconfigNETWORK_MTU );

    pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
    __CPROVER_assume( pxNetworkBuffer != NULL );

    pxNetworkBuffer->pucEthernetBuffer = safeMalloc( uxBufferLength );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    if( xIsIPv6 )
    {
        pucIPType = &pxNetworkBuffer->pucEthernetBuffer[ ipconfigBUFFER_PADDING + sizeof( UDPPacket_IPv6_t ) - ipUDP_PAYLOAD_IP_TYPE_OFFSET ];
        pvBuffer = &pxNetworkBuffer->pucEthernetBuffer[ ipconfigBUFFER_PADDING + sizeof( UDPPacket_IPv6_t ) ];
    }
    else
    {
        pucIPType = &pxNetworkBuffer->pucEthernetBuffer[ ipconfigBUFFER_PADDING + sizeof( UDPPacket_t ) - ipUDP_PAYLOAD_IP_TYPE_OFFSET ];
        pvBuffer = &pxNetworkBuffer->pucEthernetBuffer[ ipconfigBUFFER_PADDING + sizeof( UDPPacket_t ) ];
    }

    __CPROVER_assume( ( ( *pucIPType ) & 0xf0 == ipTYPE_IPv4 ) || ( ( *pucIPType ) & 0xf0 == ipTYPE_IPv6 ) );

    ( void ) pxUDPPayloadBuffer_to_NetworkBuffer( pvBuffer );
}
