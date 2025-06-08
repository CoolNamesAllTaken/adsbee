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
#include "FreeRTOS_ICMP.h"
#include "FreeRTOS_IP_Private.h"

/* CBMC includes. */
#include "cbmc.h"

/* prvProcessICMPEchoRequest() is proved separately */
eFrameProcessingResult_t __CPROVER_file_local_FreeRTOS_ICMP_c_prvProcessICMPEchoRequest( ICMPPacket_t * const pxICMPPacket,
                                                                                         const NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    eFrameProcessingResult_t eReturn;

    /* Make sure prvProcessICMPEchoRequest() is never called with  or
     * pxNetworkBuffer being NULL */
    __CPROVER_assert( pxICMPPacket != NULL, "pxICMPPacket != NULL" );
    __CPROVER_assert( pxNetworkBuffer != NULL, "pxNetworkBuffer != NULL" );

    return eReturn;
}

void harness()
{
    NetworkBufferDescriptor_t xNetworkBuffer;

    /* Allocate a ICMP packet */
    ICMPPacket_t * const pxICMPPacket = safeMalloc( sizeof( ICMPPacket_t ) );

    __CPROVER_assume( pxICMPPacket != NULL );

    xNetworkBuffer.xDataLength = sizeof( ICMPPacket_t );
    xNetworkBuffer.pucEthernetBuffer = pxICMPPacket;

    ProcessICMPPacket( &xNetworkBuffer );
}
