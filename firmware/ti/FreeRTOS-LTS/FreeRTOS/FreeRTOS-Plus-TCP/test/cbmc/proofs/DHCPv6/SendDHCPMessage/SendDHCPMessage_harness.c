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
#include "FreeRTOS_DHCPv6.h"
#include "FreeRTOS_ARP.h"

/* CBMC includes. */
#include "cbmc.h"



void __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvSendDHCPMessage( NetworkEndPoint_t * pxEndPoint );


void harness()
{
    NetworkEndPoint_t * pxNetworkEndPoint_Temp = safeMalloc( sizeof( NetworkEndPoint_t ) );

    __CPROVER_assume( pxNetworkEndPoint_Temp != NULL );

    /* The application provides the random number and time hook in a memory safe manner. */

    pxNetworkEndPoint_Temp->pxDHCPMessage = safeMalloc( sizeof( DHCPMessage_IPv6_t ) );

    /* All calls to prvSendDHCPMessage are after asserts to make sure pxDHCPMessage
     * is never NULL. [xDHCPv6ProcessEndPoint_HandleState(): configASSERT( pxDHCPMessage != NULL );] */
    __CPROVER_assume( pxNetworkEndPoint_Temp->pxDHCPMessage != NULL );

    __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvSendDHCPMessage( pxNetworkEndPoint_Temp );
}
