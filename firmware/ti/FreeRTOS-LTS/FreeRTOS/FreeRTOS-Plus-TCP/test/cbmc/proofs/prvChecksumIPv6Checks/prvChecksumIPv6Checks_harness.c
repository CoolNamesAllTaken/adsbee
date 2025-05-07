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
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_IPv6_Utils.h"

/* CBMC includes. */
#include "cbmc.h"

void harness()
{
    size_t uxBufferSize;
    uint8_t * pucEthernetBuffer;
    struct xPacketSummary xSet;

    /* We must have ethernet header to get frame type. */
    __CPROVER_assume( uxBufferSize >= sizeof( IPPacket_IPv6_t ) && uxBufferSize <= ipconfigNETWORK_MTU );

    /* Ethernet buffer is not possible to be NULL. */
    pucEthernetBuffer = ( uint8_t * ) safeMalloc( uxBufferSize );
    __CPROVER_assume( pucEthernetBuffer != NULL );

    /* This is set before calling prvChecksumIPv6Checks. */
    xSet.pxIPPacket = ( const IPPacket_t * ) pucEthernetBuffer;
    xSet.pxIPPacket_IPv6 = ( const IPHeader_IPv6_t * ) ( pucEthernetBuffer + ipSIZE_OF_ETH_HEADER );

    prvChecksumIPv6Checks( pucEthernetBuffer,
                           uxBufferSize,
                           &xSet );
}
