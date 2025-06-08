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
#include "FreeRTOS_ARP.h"

#include "NetworkBufferManagement.h"

#include "cbmc.h"

#include "../../utility/memory_assignments.c"

/* Static members defined in FreeRTOS_DHCP.c */
extern DHCPData_t xDHCPData;
extern Socket_t xDHCPv4Socket;
void prvCreateDHCPSocket( NetworkEndPoint_t * pxEndPoint );

/* Static member defined in freertos_api.c */
#ifdef CBMC_GETNETWORKBUFFER_FAILURE_BOUND
    extern uint32_t GetNetworkBuffer_failure_count;
#endif



/****************************************************************
* The signature of the function under test.
****************************************************************/

void __CPROVER_file_local_FreeRTOS_DHCP_c_vDHCPProcessEndPoint( BaseType_t xReset,
                                                                BaseType_t xDoCheck,
                                                                NetworkEndPoint_t * pxEndPoint );

/****************************************************************
* Abstract prvProcessDHCPReplies proved memory safe in ProcessDHCPReplies.
****************************************************************/

BaseType_t __CPROVER_file_local_FreeRTOS_DHCP_c_prvProcessDHCPReplies( BaseType_t xExpectedMessageType,
                                                                       NetworkEndPoint_t * pxEndPoint )
{
    return nondet_BaseType();
}

/**
 * For the purpose of this proof we assume that xSocketValid returns true always.
 * This has to do with assertions in the source code that checks for socket being invalid.
 * [configASSERT( xSocketValid( xDHCPv4Socket ) == pdTRUE );]
 */
BaseType_t xSocketValid( const ConstSocket_t xSocket )
{
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


/*We assume that the pxGetNetworkBufferWithDescriptor function is implemented correctly and returns a valid data structure. */
/*This is the mock to mimic the correct expected behavior. If this allocation fails, this might invalidate the proof. */
NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) safeMalloc( sizeof( NetworkBufferDescriptor_t ) );

    __CPROVER_assume( pxNetworkBuffer != NULL );
    __CPROVER_assume( ( xRequestedSizeBytes > ( dhcpFIRST_OPTION_BYTE_OFFSET + sizeof( MACAddress_t ) + ipIP_TYPE_OFFSET ) ) && ( xRequestedSizeBytes < ipconfigNETWORK_MTU ) );

    pxNetworkBuffer->pucEthernetBuffer = ( ( uint8_t * ) safeMalloc( xRequestedSizeBytes + ( ipIP_TYPE_OFFSET ) ) );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Increment with expected buffer padding */
    pxNetworkBuffer->pucEthernetBuffer += ipIP_TYPE_OFFSET;

    pxNetworkBuffer->xDataLength = xRequestedSizeBytes;
    return pxNetworkBuffer;
}

void FreeRTOS_ReleaseUDPPayloadBuffer( void * pvBuffer )
{
    __CPROVER_assert( pvBuffer != NULL,
                      "FreeRTOS precondition: pvBuffer != NULL" );

    /* Free buffer after adjusting offsets. */
    free( ( ( ( uint8_t * ) pvBuffer ) - ( ipUDP_PAYLOAD_OFFSET_IPv4 + ipIP_TYPE_OFFSET ) ) );
}

/* Abstraction of FreeRTOS_socket. Return NULL or valid socket handler. */
Socket_t FreeRTOS_socket( BaseType_t xDomain,
                          BaseType_t xType,
                          BaseType_t xProtocol )
{
    return ensure_FreeRTOS_Socket_t_is_allocated();
}


/****************************************************************
* The proof of vDHCPProcess
****************************************************************/

void harness()
{
    BaseType_t xReset;
    BaseType_t xDoCheck;

    pxNetworkEndPoints = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );

    /* Interface init. */
    pxNetworkEndPoints->pxNetworkInterface = ( NetworkInterface_t * ) safeMalloc( sizeof( NetworkInterface_t ) );
    __CPROVER_assume( pxNetworkEndPoints->pxNetworkInterface != NULL );

    if( nondet_bool() )
    {
        pxNetworkEndPoints->pxNext = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
        __CPROVER_assume( pxNetworkEndPoints->pxNext != NULL );
        pxNetworkEndPoints->pxNext->pxNext = NULL;
        pxNetworkEndPoints->pxNext->pxNetworkInterface = pxNetworkEndPoints->pxNetworkInterface;
    }
    else
    {
        pxNetworkEndPoints->pxNext = NULL;
    }

    NetworkEndPoint_t * pxNetworkEndPoint_Temp = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoint_Temp != NULL );
    pxNetworkEndPoint_Temp->pxNext = NULL;
    pxNetworkEndPoint_Temp->xDHCPData.xDHCPSocket = NULL;

    /****************************************************************
    * Initialize the counter used to bound the number of times
    * GetNetworkBufferWithDescriptor can fail.
    ****************************************************************/

    #ifdef CBMC_GETNETWORKBUFFER_FAILURE_BOUND
        GetNetworkBuffer_failure_count = 0;
    #endif

    xDHCPv4Socket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

    /****************************************************************
    * Assume a valid socket in most states of the DHCP state machine.
    *
    * The socket is created in the eWaitingSendFirstDiscover state.
    * xReset==True resets the state to eWaitingSendFirstDiscover.
    ****************************************************************/

    if( !( ( pxNetworkEndPoint_Temp->xDHCPData.eDHCPState == eInitialWait ) ||
           ( xReset != pdFALSE ) ) )
    {
        prvCreateDHCPSocket( pxNetworkEndPoint_Temp );
    }

    __CPROVER_file_local_FreeRTOS_DHCP_c_vDHCPProcessEndPoint( xReset, xDoCheck, pxNetworkEndPoint_Temp );
}
