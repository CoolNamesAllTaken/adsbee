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

#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

#include "cbmc.h"

/* eARPProcessPacket() is proved separately */
eFrameProcessingResult_t eARPProcessPacket( ARPPacket_t * const pxARPFrame )
{
    __CPROVER_assert( pxARPFrame != NULL, "pxARPFrame != NULL" );
    eFrameProcessingResult_t retVal;
    return retVal;
}

/* vReturnEthernetFrame() is proved separately */
void vReturnEthernetFrame( NetworkBufferDescriptor_t * pxNetworkBuffer,
                           BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "xNetworkBuffer != NULL" );
    __CPROVER_assert( pxNetworkBuffer->pucEthernetBuffer != NULL, "pxNetworkBuffer->pucEthernetBuffer != NULL" );

    free( pxNetworkBuffer->pucEthernetBuffer );
    free( pxNetworkBuffer );
}

/* This function has been proved to be memory safe in another proof (in parsing/ProcessIPPacket). Hence we assume it to be correct here. */
eFrameProcessingResult_t __CPROVER_file_local_FreeRTOS_IP_c_prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                                                                NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    __CPROVER_assert( pxIPPacket != NULL, "pxIPPacket cannot be NULL" );
    __CPROVER_assert( pxNetworkBuffer != NULL, "pxNetworkBuffer cannot be NULL" );

    eFrameProcessingResult_t result;

    return result;
}


void __CPROVER_file_local_FreeRTOS_IP_c_prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

/* The harness test proceeds to call prvProcessEthernetPacket with an unconstrained value */
void harness()
{
    struct xNetworkInterface xInterface;

    /* Needs a valid network buffer to be passed */
    NetworkBufferDescriptor_t * pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );

    __CPROVER_assume( pxNetworkBuffer != NULL );

    /* Minimum required length of the pxNetworkBuffer->xDataLength is at least the size of the EthernetHeader_t. */
    __CPROVER_assume( ( pxNetworkBuffer->xDataLength >= ( sizeof( EthernetHeader_t ) ) ) && ( pxNetworkBuffer->xDataLength <= ipTOTAL_ETHERNET_FRAME_SIZE ) );

    /* Needs a valid ethernet buffer to be passed */
    pxNetworkBuffer->pucEthernetBuffer = ( ( ( uint8_t * ) safeMalloc( pxNetworkBuffer->xDataLength ) ) );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Its assumed that every RX packet will have a valid network interface assigned. (Asserted in code) */
    pxNetworkBuffer->pxInterface = &xInterface;

    __CPROVER_file_local_FreeRTOS_IP_c_prvProcessEthernetPacket( pxNetworkBuffer );
}
