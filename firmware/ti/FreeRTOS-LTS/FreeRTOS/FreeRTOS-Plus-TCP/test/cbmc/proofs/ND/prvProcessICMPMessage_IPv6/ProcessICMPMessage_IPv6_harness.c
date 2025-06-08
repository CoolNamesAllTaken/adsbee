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

extern NDCacheRow_t xNDCache[ ipconfigND_CACHE_ENTRIES ];

/* The checksum generation is stubbed out since the actual checksum
 * does not matter. The stub will return an indeterminate value each time. */
uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    uint16_t usReturn;

    __CPROVER_assert( pucEthernetBuffer != NULL, "The ethernet buffer cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pucEthernetBuffer, uxBufferLength ), "pucEthernetBuffer should be readable." );

    /* Return an indeterminate value. */
    return usReturn;
}

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void vReturnEthernetFrame( NetworkBufferDescriptor_t * pxNetworkBuffer,
                           BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer descriptor cannot be NULL." );
}

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void vReceiveNA( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer descriptor cannot be NULL." );
}

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
BaseType_t xSendEventStructToIPTask( const IPStackEvent_t * pxEvent,
                                     TickType_t uxTimeout )
{
    BaseType_t xReturn;

    __CPROVER_assume( xReturn == pdPASS || xReturn == pdFAIL );

    return xReturn;
}

/* This is an output function implemented by a third party and
 * need not be tested with this proof. */
BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxDescriptor != NULL, "The network interface cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer descriptor cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer->pucEthernetBuffer != NULL, "The Ethernet buffer cannot be NULL." );
    return 0;
}

/* Abstraction of this functions creates and return an endpoint, real endpoint doesn't matter in this test. */
NetworkEndPoint_t * FreeRTOS_InterfaceEPInSameSubnet_IPv6( const NetworkInterface_t * pxInterface,
                                                           const IPv6_Address_t * pxIPAddress )
{
    NetworkEndPoint_t * pxEndPoints = NULL;

    __CPROVER_assert( pxIPAddress != NULL, "The pxIPAddress cannot be NULL." );

    pxEndPoints = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

    if( ensure_memory_is_valid( pxEndPoints, sizeof( NetworkEndPoint_t ) ) )
    {
        /* Interface init. */
        pxEndPoints->pxNetworkInterface = ( NetworkInterface_t * ) safeMalloc( sizeof( NetworkInterface_t ) );
        __CPROVER_assume( pxEndPoints->pxNetworkInterface != NULL );

        pxEndPoints->pxNext = NULL;
        pxEndPoints->pxNetworkInterface->pfOutput = NetworkInterfaceOutputFunction_Stub;
    }

    return pxEndPoints;
}

void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = ensure_FreeRTOS_NetworkBuffer_is_allocated();
    uint32_t ulLen;
    uint16_t usEthernetBufferSize;
    NetworkBufferDescriptor_t xLocalBuffer;

    /* The code does not expect pxNetworkBuffer to be NULL. */
    __CPROVER_assume( pxNetworkBuffer != NULL );

    __CPROVER_assume( ( ulLen >= sizeof( ICMPPacket_IPv6_t ) ) && ( ulLen < ipconfigNETWORK_MTU ) );

    pxNetworkBuffer->xDataLength = ulLen;
    pxNetworkBuffer->pucEthernetBuffer = safeMalloc( ulLen );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Add an end point to the network buffer present. Its assumed that the
     * network interface layer correctly assigns the end point to the generated buffer. */
    pxNetworkBuffer->pxEndPoint = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

    /* This assumption is made because the function is validating IPv6 related functionality
     * which is validated only when bIPv6 is set*/
    __CPROVER_assume( ( pxNetworkBuffer->pxEndPoint != NULL ) && ( pxNetworkBuffer->pxEndPoint->bits.bIPv6 == pdTRUE_UNSIGNED ) );

    /* Non deterministically determine whether the pxARPWaitingNetworkBuffer will
     * point to some valid data or will it be NULL. */
    if( nondet_bool() )
    {
        /* The packet must at least be as big as an IPv6 Packet. The size is not
         * checked in the function as the pointer is stored by the IP-task itself
         * and therefore it will always be of the required size. */
        __CPROVER_assume( usEthernetBufferSize >= sizeof( IPPacket_IPv6_t ) );

        /* Add matching data length to the network buffer descriptor. */
        __CPROVER_assume( xLocalBuffer.xDataLength == usEthernetBufferSize );

        xLocalBuffer.pucEthernetBuffer = safeMalloc( usEthernetBufferSize );

        /* Since this pointer is maintained by the IP-task, either the pointer
         * pxARPWaitingNetworkBuffer will be NULL or xLocalBuffer.pucEthernetBuffer
         * will be non-NULL. */
        __CPROVER_assume( xLocalBuffer.pucEthernetBuffer != NULL );

        pxARPWaitingNetworkBuffer = &xLocalBuffer;
    }
    else
    {
        pxARPWaitingNetworkBuffer = NULL;
    }

    prvProcessICMPMessage_IPv6( pxNetworkBuffer );
}
