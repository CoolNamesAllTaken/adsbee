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

/* Static members defined in FreeRTOS_DHCP.c */
extern DHCPData_t xDHCPData;
extern Socket_t xDHCPv4Socket;
void prvCreateDHCPSocket( NetworkEndPoint_t * pxEndPoint );

uint32_t uxSocketCloseCnt = 0;

DHCPMessage_IPv4_t xDHCPMessage;


void __CPROVER_file_local_FreeRTOS_DHCP_c_prvCloseDHCPSocket( const NetworkEndPoint_t * pxEndPoint );

/****************************************************************
* vDHCPProcessEndPoint() is proved separately
****************************************************************/

void __CPROVER_file_local_FreeRTOS_DHCP_c_vDHCPProcessEndPoint( BaseType_t xReset,
                                                                BaseType_t xDoCheck,
                                                                NetworkEndPoint_t * pxEndPoint )
{
    __CPROVER_assert( pxEndPoint != NULL,
                      "FreeRTOS precondition: pxEndPoint != NULL" );
}

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
    __CPROVER_assume( xRequestedSizeBytes > ( dhcpFIRST_OPTION_BYTE_OFFSET + sizeof( MACAddress_t ) + ipIP_TYPE_OFFSET ) );

    pxNetworkBuffer->pucEthernetBuffer = ( ( uint8_t * ) safeMalloc( xRequestedSizeBytes + ( ipIP_TYPE_OFFSET ) ) );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Increment with expected buffer padding */
    pxNetworkBuffer->pucEthernetBuffer += ipIP_TYPE_OFFSET;

    pxNetworkBuffer->xDataLength = xRequestedSizeBytes;
    return pxNetworkBuffer;
}

/* FreeRTOS_ReleaseUDPPayloadBuffer is mocked here and the memory
 * is not freed as the buffer allocated by the FreeRTOS_recvfrom is static
 * memory */
void FreeRTOS_ReleaseUDPPayloadBuffer( void * pvBuffer )
{
    __CPROVER_assert( pvBuffer != NULL,
                      "FreeRTOS precondition: pvBuffer != NULL" );
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
    int32_t retVal = -1;

    __CPROVER_assert( pvBuffer != NULL,
                      "FreeRTOS precondition: pvBuffer != NULL" );

    if( ++recvRespCnt < ( FR_RECV_FROM_SUCCESS_COUNT - 1 ) )
    {
        *( ( void ** ) pvBuffer ) = ( void * ) &xDHCPMessage;
        retVal = sizeof( xDHCPMessage );
    }

    return retVal;
}

/****************************************************************
* The proof of vDHCPProcess
****************************************************************/

void harness()
{
    BaseType_t xReset;
    eDHCPState_t eExpectedState;

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

    if( !( ( pxNetworkEndPoints->xDHCPData.eDHCPState == eInitialWait ) ||
           ( xReset != pdFALSE ) ) )
    {
        prvCreateDHCPSocket( pxNetworkEndPoints );
    }

    /* Assume vDHCPProcess is only called on IPv4 endpoints which is
     * validated before the call to vDHCPProcess */
    __CPROVER_assume( pxNetworkEndPoints->bits.bIPv6 == 0 );

    vDHCPProcess( xReset, pxNetworkEndPoints );

    __CPROVER_file_local_FreeRTOS_DHCP_c_prvCloseDHCPSocket( pxNetworkEndPoints );
}
