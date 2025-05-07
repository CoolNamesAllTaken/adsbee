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

void harness()
{
    size_t uxBufferLength;
    uint8_t * pucEthernetBuffer;
    BaseType_t xOutgoingPacket;
    EthernetHeader_t * pxEthernetHeader;
    IPPacket_t * pxIPPacket;
    uint16_t usHeaderLength;

    /* The buffer must contain enough buffer size for ethernet header + IPv4 header and less than MTU size. */
    __CPROVER_assume( uxBufferLength >= ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + sizeof( ProtocolHeaders_t ) && uxBufferLength < ipconfigNETWORK_MTU );
    pucEthernetBuffer = safeMalloc( uxBufferLength );
    __CPROVER_assume( pucEthernetBuffer != NULL );

    /* This test case verifies IPv4 only. */
    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    __CPROVER_assume( pxIPPacket->xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE );

    /* Make sure the length of buffer is enough for protocol header.
     * CBMC checks union structure before accessing it, so we need to make sure the buffer size is enough for whole union structure. */
    usHeaderLength = pxIPPacket->xIPHeader.ucVersionHeaderLength & ( uint8_t ) 0x0FU;
    usHeaderLength = usHeaderLength << 2;
    __CPROVER_assume( uxBufferLength >= ipSIZE_OF_ETH_HEADER + usHeaderLength + sizeof( ProtocolHeaders_t ) );
    /* IPv4 header length is checked in prvProcessIPPacket. */
    __CPROVER_assume( ( usHeaderLength <= ( uxBufferLength - ipSIZE_OF_ETH_HEADER ) ) && ( usHeaderLength >= ipSIZE_OF_IPv4_HEADER ) );

    /* Set to valid input. */
    __CPROVER_assume( ( xOutgoingPacket == pdTRUE ) || ( xOutgoingPacket == pdFALSE ) );

    ( void ) usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );
}
