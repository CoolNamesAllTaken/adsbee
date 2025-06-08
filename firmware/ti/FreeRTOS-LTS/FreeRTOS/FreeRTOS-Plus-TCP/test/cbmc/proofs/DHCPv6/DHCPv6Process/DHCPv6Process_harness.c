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

extern Socket_t xDHCPv6Socket;
extern DHCPMessage_IPv6_t xDHCPMessage;

void __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvCreateDHCPv6Socket( NetworkEndPoint_t * pxEndPoint );

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void __CPROVER_file_local_FreeRTOS_DHCPv6_c_vDHCPv6ProcessEndPoint( BaseType_t xReset,
                                                                    NetworkEndPoint_t * pxEndPoint,
                                                                    DHCPMessage_IPv6_t * pxDHCPMessage )
{
    __CPROVER_assert( pxEndPoint != NULL, "FreeRTOS precondition: pxEndPoint != NULL" );
    __CPROVER_assert( pxDHCPMessage != NULL, "FreeRTOS precondition: pxDHCPMessage != NULL" );
}

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvDHCPv6Analyse( struct xNetworkEndPoint * pxEndPoint,
                                                                    const uint8_t * pucAnswer,
                                                                    size_t uxTotalLength,
                                                                    DHCPMessage_IPv6_t * pxDHCPMessage )
{
    BaseType_t xResult;

    __CPROVER_assert( pxEndPoint != NULL, "FreeRTOS precondition: pxEndPoint != NULL" );
    __CPROVER_assert( pxDHCPMessage != NULL, "pxDHCPMessage is not expected to be NULL" );

    __CPROVER_assume( xResult == pdPASS || xResult == pdFAIL );
    return xResult;
}

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPv6Process_PassReplyToEndPoint( struct xNetworkEndPoint * pxEndPoint )
{
    BaseType_t xResult;

    __CPROVER_assert( pxEndPoint != NULL, "FreeRTOS precondition: pxEndPoint != NULL" );

    __CPROVER_assume( xResult == pdPASS || xResult == pdFAIL );
    return xResult;
}

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
BaseType_t __CPROVER_file_local_FreeRTOS_DHCPv6_c_xDHCPv6ProcessEndPoint_HandleState( NetworkEndPoint_t * pxEndPoint,
                                                                                      DHCPMessage_IPv6_t * pxDHCPMessage )
{
    __CPROVER_assert( pxEndPoint != NULL, "FreeRTOS precondition: pxEndPoint != NULL" );
    __CPROVER_assert( pxDHCPMessage != NULL, "pxDHCPMessage is not expected to be NULL" );
    return nondet_BaseType();
}

/**
 * For the purpose of this proof we assume that xSocketValid returns true always.
 * This has to do with assertions in the source code that checks for socket being invalid.
 * [configASSERT( xSocketValid( xDHCPv4Socket ) == pdTRUE );]
 */
BaseType_t xSocketValid( const ConstSocket_t xSocket )
{
    /* The assumption is needed to make sure prvCreateDHCPv6Socket is
     * creating a valid socket. */
    __CPROVER_assume( xSocket != FREERTOS_INVALID_SOCKET );
    __CPROVER_assume( xSocket != NULL );
    return( ( xSocket != FREERTOS_INVALID_SOCKET ) && ( xSocket != NULL ) );
}

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

/* For the DHCP process loop to be fully covered, we expect FreeRTOS_recvfrom
 * to fail after few iterations. This is because vDHCPProcessEndPoint is proved
 * separately and is stubbed out for this proof, which ideally is supposed to close
 * the socket and end the loop. */
int32_t FreeRTOS_recvfrom( Socket_t xSocket,
                           void * pvBuffer,
                           size_t uxBufferLength,
                           BaseType_t xFlags,
                           struct freertos_sockaddr * pxSourceAddress,
                           socklen_t * pxSourceAddressLength )

{
    static uint32_t recvRespCnt = 0;
    FreeRTOS_Socket_t const * pxSocket = xSocket;
    int32_t retVal = -1;

    __CPROVER_assert( pvBuffer != NULL, "FreeRTOS precondition: pvBuffer != NULL" );
    __CPROVER_assert( pxSocket != NULL, "FreeRTOS precondition: pxSocket != NULL" );

    if( ++recvRespCnt < ( FR_RECV_FROM_SUCCESS_COUNT - 1 ) )
    {
        *( ( void ** ) pvBuffer ) = ( void * ) &xDHCPMessage;
        retVal = sizeof( xDHCPMessage );
    }

    return retVal;
}

void harness()
{
    BaseType_t xReset;

    NetworkEndPoint_t * pxNetworkEndPoint = safeMalloc( sizeof( NetworkEndPoint_t ) );

    __CPROVER_assume( pxNetworkEndPoint != NULL );

    if( nondet_bool() )
    {
        pxNetworkEndPoint->pxNext = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
        __CPROVER_assume( pxNetworkEndPoint->pxNext != NULL );
        pxNetworkEndPoint->pxNext->pxNext = NULL;
    }
    else
    {
        pxNetworkEndPoint->pxNext = NULL;
    }

    pxNetworkEndPoint->pxDHCPMessage = safeMalloc( sizeof( DHCPMessage_IPv6_t ) );

    if( xReset == pdFALSE )
    {
        /* The pxDHCPmessage is not expected to be NULL when
         * it is not a state machine reset. */
        __CPROVER_assume( pxNetworkEndPoint->pxDHCPMessage != NULL );
    }

    /****************************************************************
    * Assume a valid socket in most states of the DHCP state machine.
    *
    * The socket is created in the eWaitingSendFirstDiscover state.
    * xReset==True resets the state to eWaitingSendFirstDiscover.
    ****************************************************************/
    if( !( ( pxNetworkEndPoint->xDHCPData.eDHCPState == eInitialWait ) ||
           ( xReset != pdFALSE ) ) )
    {
        __CPROVER_file_local_FreeRTOS_DHCPv6_c_prvCreateDHCPv6Socket( pxNetworkEndPoint );
    }

    /* Assume vDHCPProcess is only called on IPv6 endpoints which is
     * validated before the call to vDHCPProcess */
    __CPROVER_assume( pxNetworkEndPoint->bits.bIPv6 == 1 );

    vDHCPv6Process( xReset, pxNetworkEndPoint );
}
