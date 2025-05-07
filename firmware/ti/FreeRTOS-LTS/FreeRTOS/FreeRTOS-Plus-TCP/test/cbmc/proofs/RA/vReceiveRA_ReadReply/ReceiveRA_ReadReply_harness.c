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

/****************************************************************
* Signature of the function under test
****************************************************************/

ICMPPrefixOption_IPv6_t * __CPROVER_file_local_FreeRTOS_RA_c_vReceiveRA_ReadReply( const NetworkBufferDescriptor_t * pxNetworkBuffer );


void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = ensure_FreeRTOS_NetworkBuffer_is_allocated();
    uint8_t * pucBytes;
    size_t uxNeededSize = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterAdvertisement_IPv6_t );
    size_t uxDataLen = 8;
    ICMPPrefixOption_IPv6_t * pxReturn;

    /* The code does not expect pxNetworkBuffer to be NULL. */
    __CPROVER_assume( pxNetworkBuffer != NULL );

    /* Allocates min. buffer size + 8 bytes required for the proof */
    pxNetworkBuffer->xDataLength = uxNeededSize + uxDataLen;
    pxNetworkBuffer->pucEthernetBuffer = safeMalloc( uxNeededSize + uxDataLen );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    pxNetworkBuffer->pxInterface = safeMalloc( sizeof( NetworkInterface_t ) );
    __CPROVER_assume( pxNetworkBuffer->pxInterface != NULL );

    pxReturn = __CPROVER_file_local_FreeRTOS_RA_c_vReceiveRA_ReadReply( pxNetworkBuffer );
}
