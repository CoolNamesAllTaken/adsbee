/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IPv6.h"
#include "FreeRTOS_IP_Private.h"

/* CBMC includes. */
#include "cbmc.h"

eFrameProcessingResult_t prvAllowIPPacketIPv6( const IPHeader_IPv6_t * const pxIPv6Header,
                                               const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                               UBaseType_t uxHeaderLength );

/* Create an endpoint and return, real endpoint doesn't matter in this test. */
NetworkEndPoint_t * FreeRTOS_FindEndPointOnIP_IPv6( const IPv6_Address_t * pxIPAddress )
{
    NetworkEndPoint_t * pxReturn = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

    __CPROVER_assert( pxIPAddress != NULL, "pxIPAddress shouldn't be NULL" );

    return pxReturn;
}

/* Return either pdTRUE or pdFALSE in FreeRTOS_IsNetworkUp. */
BaseType_t FreeRTOS_IsNetworkUp( void )
{
    BaseType_t xReturn;

    return xReturn;
}

/* Create an endpoint and return, real endpoint doesn't matter in this test. */
NetworkEndPoint_t * FreeRTOS_FindEndPointOnMAC( const MACAddress_t * pxMACAddress,
                                                const NetworkInterface_t * pxInterface )
{
    NetworkEndPoint_t * pxReturn = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );

    __CPROVER_assert( pxMACAddress != NULL, "MAC address shouldn't be NULL" );

    return pxReturn;
}

/* The checksum generation is stubbed out since the actual checksum
 * does not matter. The stub will return an indeterminate value each time. */
uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    uint16_t usReturn;

    __CPROVER_assert( pucEthernetBuffer != NULL, "Ethernet buffer cannot be NULL" );

    /* Return an indeterminate value. */
    return usReturn;
}

void harness()
{
    NetworkBufferDescriptor_t * const pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
    uint8_t * pucEthernetBuffer = ( uint8_t * ) safeMalloc( ipTOTAL_ETHERNET_FRAME_SIZE + ipIP_TYPE_OFFSET );

    /* Network buffer must be valid, it's checked in prvProcessEthernetPacket. */
    __CPROVER_assume( pxNetworkBuffer != NULL );
    /* Ethernet buffer in network buffer must be valid, the data length is checked in prvProcessEthernetPacket. */
    __CPROVER_assume( pucEthernetBuffer != NULL );

    /* Points to ethernet buffer offset by ipIP_TYPE_OFFSET, this make sure the buffer allocation is similar
     * to the pxGetNetworkBufferWithDescriptor */
    pxNetworkBuffer->pucEthernetBuffer = &( pucEthernetBuffer[ ipIP_TYPE_OFFSET ] );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Minimum length of the pxNetworkBuffer->xDataLength is at least the size of the IPPacket_IPv6_t. */
    __CPROVER_assume( ( pxNetworkBuffer->xDataLength >= sizeof( IPPacket_IPv6_t ) ) &&
                      ( pxNetworkBuffer->xDataLength <= ipTOTAL_ETHERNET_FRAME_SIZE ) );

    pxNetworkEndPoints = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );

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

    pxNetworkBuffer->pxEndPoint = pxNetworkEndPoints;

    IPPacket_IPv6_t * const pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    prvAllowIPPacketIPv6( &pxIPPacket->xIPHeader, pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER );
}
