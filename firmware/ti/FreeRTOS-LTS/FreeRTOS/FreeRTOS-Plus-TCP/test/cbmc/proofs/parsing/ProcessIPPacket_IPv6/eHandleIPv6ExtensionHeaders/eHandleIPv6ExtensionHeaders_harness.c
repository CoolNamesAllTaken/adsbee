/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IPv6.h"
#include "FreeRTOS_IP_Private.h"

/* CBMC includes. */
#include "cbmc.h"

/* In this test case, we configure ipconfigNETWORK_MTU to fasten the execution. */

void harness()
{
    BaseType_t xDoRemove;
    NetworkBufferDescriptor_t * const pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
    uint8_t * pucEthernetBuffer = ( uint8_t * ) safeMalloc( ipTOTAL_ETHERNET_FRAME_SIZE + ipIP_TYPE_OFFSET );

    /* xDoRemove must be pdTRUE or pdFALSE. */
    __CPROVER_assume( xDoRemove == pdTRUE || xDoRemove == pdFALSE );

    /* Network buffer must be valid, it's checked in prvProcessEthernetPacket. */
    __CPROVER_assume( pxNetworkBuffer != NULL );
    /* Ethernet buffer in network buffer must be valid, the data length is checked in prvProcessEthernetPacket. */
    __CPROVER_assume( pucEthernetBuffer != NULL );

    /* Points to ethernet buffer offset by ipIP_TYPE_OFFSET, this make sure the buffer allocation is similar
     * to the pxGetNetworkBufferWithDescriptor */
    pxNetworkBuffer->pucEthernetBuffer = &( pucEthernetBuffer[ ipIP_TYPE_OFFSET ] );

    /* Minimum length of the pxNetworkBuffer->xDataLength is at least the size of the IPPacket_IPv6_t. */
    __CPROVER_assume( ( pxNetworkBuffer->xDataLength >= sizeof( IPPacket_IPv6_t ) ) &&
                      ( pxNetworkBuffer->xDataLength <= ipTOTAL_ETHERNET_FRAME_SIZE ) );

    IPPacket_IPv6_t * pxIPv6Packet = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    /* Next protocol must be extension header. Checked in prvProcessIPPacket. */
    __CPROVER_assume( pxIPv6Packet->xIPHeader.ucNextHeader == ipIPv6_EXT_HEADER_HOP_BY_HOP ||
                      pxIPv6Packet->xIPHeader.ucNextHeader == ipIPv6_EXT_HEADER_DESTINATION_OPTIONS ||
                      pxIPv6Packet->xIPHeader.ucNextHeader == ipIPv6_EXT_HEADER_ROUTING_HEADER ||
                      pxIPv6Packet->xIPHeader.ucNextHeader == ipIPv6_EXT_HEADER_FRAGMENT_HEADER ||
                      pxIPv6Packet->xIPHeader.ucNextHeader == ipIPv6_EXT_HEADER_AUTHEN_HEADER ||
                      pxIPv6Packet->xIPHeader.ucNextHeader == ipIPv6_EXT_HEADER_SECURE_PAYLOAD ||
                      pxIPv6Packet->xIPHeader.ucNextHeader == ipIPv6_EXT_HEADER_MOBILITY_HEADER );

    eHandleIPv6ExtensionHeaders( pxNetworkBuffer, xDoRemove );
}
