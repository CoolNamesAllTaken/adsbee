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


/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"

/* CBMC includes. */
#include "cbmc.h"

/* Extern variables. */
extern DHCPMessage_IPv6_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPMessage;

void __CPROVER_file_local_FreeRTOS_DHCPv6_c_vDHCPv6ProcessEndPoint( BaseType_t xReset,
                                                                    NetworkEndPoint_t * pxEndPoint,
                                                                    DHCPMessage_IPv6_t * pxDHCPMessage );

BaseType_t xDHCPv6Process_PassReplyToEndPoint( struct xNetworkEndPoint * pxEndPoint );

/* vDHCPv6ProcessEndPoint proved to be memory safe else where */
static void __CPROVER_file_local_FreeRTOS_DHCPv6_c_vDHCPv6ProcessEndPoint( BaseType_t xReset,
                                                                           NetworkEndPoint_t * pxEndPoint,
                                                                           DHCPMessage_IPv6_t * pxDHCPMessage )
{
    __CPROVER_assert( pxEndPoint != NULL, "pxEndPoint != NULL" );
    __CPROVER_assert( pxDHCPMessage != NULL, "pxDHCPMessage != NULL" );
}

void harness()
{
    BaseType_t xResult;

    pxNetworkEndPoints = safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );
    pxNetworkEndPoints->pxDHCPMessage = &__CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPMessage;

    if( nondet_bool() )
    {
        pxNetworkEndPoints->pxNext = safeMalloc( sizeof( NetworkEndPoint_t ) );
        __CPROVER_assume( pxNetworkEndPoints->pxNext != NULL );
        pxNetworkEndPoints->pxNext->pxDHCPMessage = &__CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPMessage;
        pxNetworkEndPoints->pxNext->pxNext = NULL;
    }
    else
    {
        pxNetworkEndPoints->pxNext = NULL;
    }

    NetworkEndPoint_t * pxNetworkEndPoint_Temp = safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoint_Temp != NULL );
    pxNetworkEndPoint_Temp->pxNext = NULL;

    pxNetworkEndPoint_Temp->pxDHCPMessage = safeMalloc( sizeof( DHCPMessage_IPv6_t ) );
    __CPROVER_assume( pxNetworkEndPoint_Temp->pxDHCPMessage != NULL );

    /* Randomize DHCPMsg as input for different scenarios. */
    __CPROVER_havoc_object( &__CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPMessage );

    /* vDHCPv6ProcessEndPoint is checked separately. */
    if( nondet_bool() )
    {
        xResult = __CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPv6Process_PassReplyToEndPoint( pxNetworkEndPoint_Temp );
    }
    else
    {
        xResult = __CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPv6Process_PassReplyToEndPoint( pxNetworkEndPoints );
    }
}
