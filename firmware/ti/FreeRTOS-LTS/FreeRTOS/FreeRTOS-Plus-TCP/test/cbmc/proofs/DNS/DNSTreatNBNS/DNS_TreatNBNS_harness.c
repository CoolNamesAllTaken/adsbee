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
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DNS_Parser.h"
#include "FreeRTOS_IP_Private.h"

#include "cbmc.h"

NetworkBufferDescriptor_t xNetworkBuffer;

NetworkBufferDescriptor_t * pxUDPPayloadBuffer_to_NetworkBuffer( const void * pvBuffer )
{
    __CPROVER_assert( pvBuffer != NULL, "Precondition: pvBuffer != NULL" );
    NetworkBufferDescriptor_t * pxRBuf;

    if( nondet_bool() )
    {
        pxRBuf = NULL;
    }
    else
    {
        pxRBuf = &xNetworkBuffer;
    }

    return pxRBuf;
}

NetworkBufferDescriptor_t * pxResizeNetworkBufferWithDescriptor( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                                 size_t xNewSizeBytes )
{
    NetworkBufferDescriptor_t * pxRBuf;

    __CPROVER_assert( pxNetworkBuffer != NULL, "pxNetworkBuffer: pvBuffer != NULL" );

    uint8_t * pucNewBuffer = safeMalloc( xNewSizeBytes );
    __CPROVER_assume( pucNewBuffer != NULL );

    pxNetworkBuffer->pucEthernetBuffer = pucNewBuffer;

    if( nondet_bool() )
    {
        pxRBuf = NULL;
    }
    else
    {
        pxRBuf = pxNetworkBuffer;
    }

    return pxRBuf;
}

/* prepareReplyDNSMessage is proved separately */
void prepareReplyDNSMessage( NetworkBufferDescriptor_t * pxNetworkBuffer,
                             BaseType_t lNetLength )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "pxNetworkBuffer: pvBuffer != NULL" );
}

void harness()
{
    uint32_t ulIPAddress;

    NetworkEndPoint_t * pxNetworkEndPoint_Temp = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

    BaseType_t xDataSize;

    /* When re-adjusting the buffer, (sizeof( NBNSAnswer_t ) - 2 * sizeof( uint16_t )) more bytes are
     * required to be added to the existing buffer. Make sure total bytes doesn't exceed  ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER
     * when re-resizing. This will prevent hitting an assert if Buffer Allocation 1 is used. */
    __CPROVER_assume( ( xDataSize != 0 ) && ( xDataSize < ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER - ( sizeof( NBNSAnswer_t ) - 2 * sizeof( uint16_t ) ) ) ) );

    xNetworkBuffer.pucEthernetBuffer = safeMalloc( xDataSize );
    xNetworkBuffer.xDataLength = xDataSize;

    if( nondet_bool() )
    {
        xNetworkBuffer.pxEndPoint = pxNetworkEndPoint_Temp;
    }
    else
    {
        xNetworkBuffer.pxEndPoint = NULL;
    }

    DNS_TreatNBNS( xNetworkBuffer.pucEthernetBuffer, xNetworkBuffer.xDataLength, ulIPAddress );
}
