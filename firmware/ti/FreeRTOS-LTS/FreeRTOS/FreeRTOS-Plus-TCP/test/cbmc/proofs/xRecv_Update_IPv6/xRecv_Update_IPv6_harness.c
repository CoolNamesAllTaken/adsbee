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
#include "FreeRTOS_IPv6_Sockets.h"

/* CBMC includes. */
#include "cbmc.h"

void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
    uint8_t * pxEthBuffer = safeMalloc( ipTOTAL_ETHERNET_FRAME_SIZE + ipIP_TYPE_OFFSET );
    struct freertos_sockaddr * pxSourceAddress = safeMalloc( sizeof( struct freertos_sockaddr ) );

    /* Network buffer is checked in FreeRTOS_recvfrom. */
    __CPROVER_assume( pxNetworkBuffer != NULL );

    /* Ethernet buffer is checked in xProcessReceivedUDPPacket_IPv6 before adding to the list. */
    __CPROVER_assume( pxEthBuffer != NULL );

    /* Points to ethernet buffer offset by ipIP_TYPE_OFFSET, this make sure the buffer allocation is similar
     * to the pxGetNetworkBufferWithDescriptor */
    pxNetworkBuffer->pucEthernetBuffer = &( pxEthBuffer[ ipIP_TYPE_OFFSET ] );

    /* Randomize address as input for different scenarios. */
    __CPROVER_havoc_object( pxSourceAddress );

    xRecv_Update_IPv6( pxNetworkBuffer, pxSourceAddress );
}
