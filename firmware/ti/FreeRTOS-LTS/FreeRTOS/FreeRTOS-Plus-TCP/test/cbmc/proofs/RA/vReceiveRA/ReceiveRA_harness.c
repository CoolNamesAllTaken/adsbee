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
#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_ND.h"

/* CBMC includes. */
#include "../../utility/memory_assignments.c"
#include "cbmc.h"

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
ICMPPrefixOption_IPv6_t * __CPROVER_file_local_FreeRTOS_RA_c_vReceiveRA_ReadReply( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    ICMPPrefixOption_IPv6_t * pxPrefixOption = safeMalloc( sizeof( ICMPPrefixOption_IPv6_t ) );

    return pxPrefixOption;
}

/* Abstraction of pxGetNetworkBufferWithDescriptor. */
NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;

    pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) safeMalloc( sizeof( NetworkBufferDescriptor_t ) );

    if( pxNetworkBuffer )
    {
        pxNetworkBuffer->pucEthernetBuffer = safeMalloc( xRequestedSizeBytes );
        __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

        pxNetworkBuffer->xDataLength = xRequestedSizeBytes;
    }

    return pxNetworkBuffer;
}

/* Abstraction of this functions as it validation doesn't matter for the proof of this test. */
void vNDSendRouterSolicitation( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                IPv6_Address_t * pxIPAddress )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer descriptor cannot be NULL." );
    __CPROVER_assert( pxIPAddress != NULL, "The pxIPAddress cannot be NULL." );
}

void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = ensure_FreeRTOS_NetworkBuffer_is_allocated();
    NetworkInterface_t * pxInterface = ( NetworkInterface_t * ) safeMalloc( sizeof( NetworkInterface_t ) );
    uint32_t ulLen;

    /* The code does not expect pxNetworkBuffer to be NULL. */
    __CPROVER_assume( pxNetworkBuffer != NULL );

    __CPROVER_assume( ( ulLen >= sizeof( ICMPPacket_IPv6_t ) ) && ( ulLen < ipconfigNETWORK_MTU ) );
    pxNetworkBuffer->pucEthernetBuffer = safeMalloc( ulLen );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    pxNetworkBuffer->pxInterface = safeMalloc( sizeof( NetworkInterface_t ) );
    __CPROVER_assume( pxNetworkBuffer->pxInterface != NULL );

    pxNetworkBuffer->pxEndPoint = safeMalloc( sizeof( NetworkEndPoint_t ) );

    /* Initialize global Endpoint variable  */
    pxNetworkEndPoints = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );
    pxNetworkEndPoints->pxNetworkInterface = pxNetworkBuffer->pxInterface;
    __CPROVER_assume( pxNetworkEndPoints->pxNetworkInterface != NULL );
    pxNetworkEndPoints->pxNext = NULL;

    vReceiveRA( pxNetworkBuffer );
}
