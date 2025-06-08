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
#include "FreeRTOS_TCP_Transmission.h"

/* CBMC includes. */
#include "../../utility/memory_assignments.c"

#include "cbmc.h"

/*
 * This function is implemented by a third party.
 * After looking through a couple of samples in the demos folder, it seems
 * like the only shared contract is that you want to add the if statement
 * for releasing the buffer to the end. Apart from that, it is up to the vendor,
 * how to write this code out to the network.
 */
BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxDescriptor != NULL, "The network interface cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer descriptor cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer->pucEthernetBuffer != NULL, "The ethernet buffer cannot be NULL." );

    if( xReleaseAfterSend != pdFALSE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

    return 0;
}

/* Abstraction of this functions creates an endpoint and assign it to network interface
 * endpoint, real endpoint doesn't matter in this test. */
void prvTCPReturn_SetEndPoint( const FreeRTOS_Socket_t * pxSocket,
                               NetworkBufferDescriptor_t * pxNetworkBuffer,
                               size_t uxIPHeaderSize )
{
    NetworkEndPoint_t * pxEndPoint = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

    __CPROVER_assume( pxEndPoint != NULL );

    /* Add an interface */
    pxEndPoint->pxNetworkInterface = ( NetworkInterface_t * ) safeMalloc( sizeof( NetworkInterface_t ) );
    __CPROVER_assume( pxEndPoint->pxNetworkInterface != NULL );

    pxEndPoint->pxNetworkInterface->pfOutput = NetworkInterfaceOutputFunction_Stub;

    pxNetworkBuffer->pxEndPoint = pxEndPoint;
}

/* Abstraction of pxDuplicateNetworkBufferWithDescriptor*/
NetworkBufferDescriptor_t * pxDuplicateNetworkBufferWithDescriptor( const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                    size_t xNewLength )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = safeMalloc( xNewLength );

    if( ensure_memory_is_valid( pxNetworkBuffer, xNewLength ) )
    {
        pxNetworkBuffer->pucEthernetBuffer = safeMalloc( sizeof( TCPPacket_t ) );
        __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer );

        /* Add an end point to the network buffer present. Its assumed that the
         * network interface layer correctly assigns the end point to the generated buffer. */
        pxNetworkBuffer->pxEndPoint = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
        __CPROVER_assume( pxNetworkBuffer->pxEndPoint != NULL );
        pxNetworkBuffer->pxEndPoint->pxNext = NULL;

        /* Add an interface */
        pxNetworkBuffer->pxEndPoint->pxNetworkInterface = ( NetworkInterface_t * ) safeMalloc( sizeof( NetworkInterface_t ) );
        __CPROVER_assume( pxNetworkBuffer->pxEndPoint->pxNetworkInterface != NULL );

        pxNetworkBuffer->pxEndPoint->pxNetworkInterface->pfOutput = NetworkInterfaceOutputFunction_Stub;
    }

    return pxNetworkBuffer;
}

uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    uint16_t usReturn;

    __CPROVER_assert( pucEthernetBuffer != NULL, "The ethernet buffer cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pucEthernetBuffer, uxBufferLength ), "pucEthernetBuffer should be readable." );

    return usReturn;
}

uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
    uint16_t usReturn;

    __CPROVER_assert( pucNextData != NULL, "The next data pointer cannot be NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pucNextData, uxByteCount ), "The pucNextData should be readable." );

    return usReturn;
}

void harness()
{
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
    NetworkBufferDescriptor_t * pxNetworkBuffer = ensure_FreeRTOS_NetworkBuffer_is_allocated();
    BaseType_t xReleaseAfterSend;
    uint32_t ulLen;

    /* The code does not expect both of these to be equal to NULL at the same time. */
    __CPROVER_assume( pxSocket != NULL || pxNetworkBuffer != NULL );

    /* If network buffer is properly created. */
    if( ensure_memory_is_valid( pxNetworkBuffer, sizeof( *pxNetworkBuffer ) ) )
    {
        /* Assume that the length is proper. */
        __CPROVER_assume( ( ulLen >= sizeof( TCPPacket_IPv6_t ) ) && ( ulLen < ipconfigNETWORK_MTU ) );
        pxNetworkBuffer->pucEthernetBuffer = safeMalloc( ulLen + ipSIZE_OF_ETH_HEADER );
        __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

        pxNetworkBuffer->xDataLength = ( size_t ) ( ulLen + ipSIZE_OF_ETH_HEADER );

        /* Add an end point to the network buffer present. Its assumed that the
         * network interface layer correctly assigns the end point to the generated buffer. */
        pxNetworkBuffer->pxEndPoint = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

        if( ensure_memory_is_valid( pxNetworkBuffer->pxEndPoint, sizeof( NetworkEndPoint_t ) ) )
        {
            /* Add an interface */
            pxNetworkBuffer->pxEndPoint->pxNetworkInterface = ( NetworkInterface_t * ) safeMalloc( sizeof( NetworkInterface_t ) );
            __CPROVER_assume( pxNetworkBuffer->pxEndPoint->pxNetworkInterface != NULL );
            pxNetworkBuffer->pxEndPoint->pxNetworkInterface->pfOutput = NetworkInterfaceOutputFunction_Stub;
        }
    }
    /* If not. */
    else
    {
        /* Assume that the length is proper. The length should be between this range. It
         * is made so by the functions up the call tree. Essentially, this is equal to a
         * TCP packet header with and without TCP options. */
        __CPROVER_assume( ( ulLen >= ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_TCP_HEADER ) &&
                          ( ulLen <= ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_TCP_HEADER + 40 /* Maximum option bytes. */ ) );
    }

    prvTCPReturnPacket( pxSocket, pxNetworkBuffer, ulLen, xReleaseAfterSend );
}
