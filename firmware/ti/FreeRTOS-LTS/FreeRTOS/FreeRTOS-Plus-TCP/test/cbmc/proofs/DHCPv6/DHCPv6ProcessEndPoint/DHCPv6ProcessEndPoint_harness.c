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
#include "../../utility/memory_assignments.c"

/* Static members defined in FreeRTOS_DHCP.c */
extern Socket_t xDHCPv6Socket;
void __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvCreateDHCPv6Socket( NetworkEndPoint_t * pxEndPoint );

BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPv6ProcessEndPoint_HandleState( NetworkEndPoint_t * pxEndPoint,
                                                                                      DHCPMessage_IPv6_t * pxDHCPMessage )
{
    __CPROVER_assert( pxEndPoint != NULL, "pxEndPoint must not be NULL" );
    __CPROVER_assert( pxDHCPMessage != NULL, "pxDHCPMessage must not be NULL" );

    if( ( pxEndPoint->xDHCPData.eDHCPState == eLeasedAddress ) || ( pxEndPoint->xDHCPData.eDHCPState == eInitialWait ) )
    {
        __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvCreateDHCPv6Socket( pxEndPoint );
    }

    return nondet_BaseType();
}

/**
 * In DHCP, we assume that FreeRTOS_socket always returns valid socket handler.
 */
Socket_t FreeRTOS_socket( BaseType_t xDomain,
                          BaseType_t xType,
                          BaseType_t xProtocol )
{
    Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();

    __CPROVER_assume( pxSocket != NULL );

    return pxSocket;
}

/**
 * For the purpose of this proof we assume that xSocketValid returns true always.
 * This has to do with assertions in the source code that checks for socket being invalid.
 * [configASSERT( xSocketValid( xDHCPv6Socket ) == pdTRUE );]
 */
BaseType_t xSocketValid( const ConstSocket_t xSocket )
{
    __CPROVER_assert( xSocket != FREERTOS_INVALID_SOCKET, "xSocket must be valid" );
    __CPROVER_assert( xSocket != NULL, "xSocket must not be NULL" );

    return( ( xSocket != FREERTOS_INVALID_SOCKET ) && ( xSocket != NULL ) );
}

/**
 * For the purpose of this proof we assume that vSocketBind returns 0 always.
 * Or the assertion is triggered when bind is failing.
 */
BaseType_t vSocketBind( FreeRTOS_Socket_t * pxSocket,
                        struct freertos_sockaddr * pxBindAddress,
                        size_t uxAddressLength,
                        BaseType_t xInternal )
{
    /* Return value is set to zero assuming socket bind will succeed. If it doesn't, it
     * will hit an assert in the function.  */
    BaseType_t xRet = 0;

    __CPROVER_assert( pxSocket != NULL,
                      "FreeRTOS precondition: pxSocket != NULL" );
    __CPROVER_assert( pxBindAddress != NULL,
                      "FreeRTOS precondition: pxBindAddress != NULL" );

    return xRet;
}

BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPv6ProcessEndPoint_HandleAdvertise( NetworkEndPoint_t * pxEndPoint,
                                                                                          DHCPMessage_IPv6_t * pxDHCPMessage )
{
    __CPROVER_assert( pxEndPoint != NULL, "pxEndPoint must not be NULL" );
    __CPROVER_assert( pxDHCPMessage != NULL, "pxDHCPMessage must not be NULL" );

    return nondet_BaseType();
}

void __CPROVER_file_local_FreeRTOS_DHCPv6_c_vDHCPv6ProcessEndPoint_HandleReply( NetworkEndPoint_t * pxEndPoint,
                                                                                DHCPMessage_IPv6_t * pxDHCPMessage )
{
    __CPROVER_assert( pxEndPoint != NULL, "pxEndPoint must not be NULL" );
    __CPROVER_assert( pxDHCPMessage != NULL, "pxDHCPMessage must not be NULL" );
}

void __CPROVER_file_local_FreeRTOS_DHCPv6_c_vDHCPv6ProcessEndPoint( BaseType_t xReset,
                                                                    NetworkEndPoint_t * pxEndPoint,
                                                                    DHCPMessage_IPv6_t * pxDHCPMessage );

void harness()
{
    BaseType_t xReset, xGivingUp;

    NetworkEndPoint_t * pxNetworkEndPoint_Temp = safeMalloc( sizeof( NetworkEndPoint_t ) );

    __CPROVER_assume( pxNetworkEndPoint_Temp != NULL );

    DHCPMessage_IPv6_t * pxDHCPMessage = safeMalloc( sizeof( DHCPMessage_IPv6_t ) );
    __CPROVER_assume( pxDHCPMessage != NULL );

    xDHCPv6Socket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

    __CPROVER_file_local_FreeRTOS_DHCPv6_c_vDHCPv6ProcessEndPoint( xReset, pxNetworkEndPoint_Temp, pxDHCPMessage );
}
