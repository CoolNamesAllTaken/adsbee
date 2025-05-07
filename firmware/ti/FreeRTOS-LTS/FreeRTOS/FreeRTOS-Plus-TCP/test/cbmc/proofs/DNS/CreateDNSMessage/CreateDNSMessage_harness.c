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
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"

#include "cbmc.h"

size_t __CPROVER_file_local_FreeRTOS_DNS_c_prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                                                                const char * pcHostName,
                                                                TickType_t uxIdentifier,
                                                                UBaseType_t uxHostType );

void harness()
{
    size_t uxExpectedPayloadLength;
    TickType_t uxIdentifier;
    UBaseType_t uxHostType;
    size_t len;

    /* Make sure the string has a valid but bounded length */
    __CPROVER_assume( len > 0 && len <= MAX_HOSTNAME_LEN );

    /* pcHostName is tested to be valid prior */
    char * pcHostName = malloc( len );

    if( len && pcHostName )
    {
        /* Make sure the string ends with a NULL, this is expected */
        pcHostName[ len - 1 ] = NULL;
    }

    /* prvCreateDNSMessage() is expected to be called with a ethernet buffer of
     * the following size */
    uxExpectedPayloadLength = sizeof( DNSMessage_t ) +
                              strlen( pcHostName ) +
                              sizeof( uint16_t ) +
                              sizeof( uint16_t ) + 2U;

    /* Add header size */
    if( nondet_bool() )
    {
        uxExpectedPayloadLength += ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_UDP_HEADER;
    }
    else
    {
        uxExpectedPayloadLength += ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER;
    }

    /* pucUDPPayloadBuffer is tested to be valid prior */
    uint8_t * pucUDPPayloadBuffer = malloc( uxExpectedPayloadLength );

    __CPROVER_file_local_FreeRTOS_DNS_c_prvCreateDNSMessage( pucUDPPayloadBuffer, pcHostName, uxIdentifier, uxHostType );
}
