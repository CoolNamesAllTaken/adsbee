/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"

#include "cbmc.h"

/****************************************************************
* Signature of function under test
****************************************************************/

BaseType_t prvCheckOptions( FreeRTOS_Socket_t * pxSocket,
                            const NetworkBufferDescriptor_t * pxNetworkBuffer );

size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer );

int32_t __CPROVER_file_local_FreeRTOS_TCP_IP_c_prvSingleStepTCPHeaderOptions( const uint8_t * const pucPtr,
                                                                              size_t uxTotalLength,
                                                                              FreeRTOS_Socket_t * const pxSocket,
                                                                              BaseType_t xHasSYNFlag );

/****************************************************************
* Declare the buffer size external to the harness so it can be
* accessed by the preconditions of prvSingleStepTCPHeaderOptions, and
* give the buffer size an unconstrained value in the harness itself.
****************************************************************/
size_t buffer_size;
size_t uxIPHeaderSizePacket_uxResult;

/****************************************************************
* Function contract proved correct by CheckOptionsOuter
****************************************************************/

int32_t __CPROVER_file_local_FreeRTOS_TCP_Reception_c_prvSingleStepTCPHeaderOptions( const uint8_t * const pucPtr,
                                                                                     size_t uxTotalLength,
                                                                                     FreeRTOS_Socket_t * const pxSocket,
                                                                                     BaseType_t xHasSYNFlag )
{
    /* CBMC model of pointers limits the size of the buffer */

    /* Preconditions */
    __CPROVER_assert( buffer_size < CBMC_MAX_OBJECT_SIZE,
                      "prvSingleStepTCPHeaderOptions: buffer_size < CBMC_MAX_OBJECT_SIZE" );
    __CPROVER_assert( 8 <= buffer_size,
                      "prvSingleStepTCPHeaderOptions: 8 <= buffer_size" );
    __CPROVER_assert( pucPtr != NULL,
                      "prvSingleStepTCPHeaderOptions: pucPtr != NULL" );
    __CPROVER_assert( uxTotalLength <= buffer_size,
                      "prvSingleStepTCPHeaderOptions: uxTotalLength <= buffer_size" );
    __CPROVER_assert( pxSocket != NULL,
                      "prvSingleStepTCPHeaderOptions: pxSocket != NULL" );

    /* Postconditions */
    int32_t index;

    __CPROVER_assume( ( index == -1 ) || ( index == 1 ) || ( index <= uxTotalLength ) );

    return index;
}

size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "pxNetworkBuffer should not be NULL" );
    return uxIPHeaderSizePacket_uxResult;
}

/****************************************************************
* Proof of CheckOptions
****************************************************************/

void harness()
{
    /* Give buffer_size an unconstrained value */
    size_t buf_size;

    if( nondet_bool() )
    {
        uxIPHeaderSizePacket_uxResult = ipSIZE_OF_IPv6_HEADER;
    }
    else
    {
        uxIPHeaderSizePacket_uxResult = ipSIZE_OF_IPv4_HEADER;
    }

    __CPROVER_assume( buf_size > ( ipSIZE_OF_ETH_HEADER + uxIPHeaderSizePacket_uxResult + sizeof( TCPHeader_t ) ) );

    buffer_size = buf_size;

    /* pxSocket can be any socket */
    FreeRTOS_Socket_t pxSocket;

    /* pxNetworkBuffer can be any buffer descriptor with any buffer */
    NetworkBufferDescriptor_t pxNetworkBuffer;

    pxNetworkBuffer.pucEthernetBuffer = malloc( buffer_size );
    __CPROVER_assume( pxNetworkBuffer.pucEthernetBuffer != NULL );
    pxNetworkBuffer.xDataLength = buffer_size;

    /****************************************************************
    * Specification and proof of CheckOptions
    ****************************************************************/

    /* CBMC model of pointers limits the size of the buffer */
    __CPROVER_assume( buffer_size < CBMC_MAX_OBJECT_SIZE );

    /* Bound required to bound iteration over the buffer */
    __CPROVER_assume( buffer_size <= BUFFER_SIZE );

    /* Buffer must be big enough to hold pxTCPPacket and pxTCPHeader */
    __CPROVER_assume( buffer_size > 47 );

    prvCheckOptions( &pxSocket, &pxNetworkBuffer );
}
