/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* CBMC includes. */
#include "cbmc.h"

eFrameProcessingResult_t __CPROVER_file_local_FreeRTOS_IP_c_prvProcessIPPacket( const IPPacket_t * pxIPPacket,
                                                                                NetworkBufferDescriptor_t * const pxNetworkBuffer );

/* proof is done separately */
BaseType_t xProcessReceivedTCPPacket( NetworkBufferDescriptor_t * pxNetworkBuffer )
{
}

/* proof is done separately */
BaseType_t xProcessReceivedUDPPacket( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                      uint16_t usPort )
{
}

/* This proof was done before. Hence we assume it to be correct here. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                            const uint32_t ulIPAddress )
{
}

eFrameProcessingResult_t publicProcessIPPacket( IPPacket_t * const pxIPPacket,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer );

#if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )

/* The checksum generation is stubbed out since the actual checksum
 * does not matter. The stub will return an indeterminate value each time. */
    uint16_t usGenerateChecksum( uint16_t usSum,
                                 const uint8_t * pucNextData,
                                 size_t uxByteCount )
    {
        uint16_t usReturn;

        __CPROVER_assert( pucNextData != NULL, "Next data cannot be NULL" );

        /* Return an indeterminate value. */
        return usReturn;
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
#endif /* if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 ) */

void harness()
{
    NetworkBufferDescriptor_t * const pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
    uint8_t * pucEthernetBuffer = ( uint8_t * ) safeMalloc( ipTOTAL_ETHERNET_FRAME_SIZE + ipIP_TYPE_OFFSET );

    __CPROVER_assume( pxNetworkBuffer != NULL );
    __CPROVER_assume( pucEthernetBuffer != NULL );

    /* Points to ethernet buffer offset by ipIP_TYPE_OFFSET, this make sure the buffer allocation is similar
     * to the pxGetNetworkBufferWithDescriptor */
    pxNetworkBuffer->pucEthernetBuffer = &( pucEthernetBuffer[ ipIP_TYPE_OFFSET ] );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /* Minimum length of the pxNetworkBuffer->xDataLength is at least the size of the IPPacket_t. */
    __CPROVER_assume( pxNetworkBuffer->xDataLength >= sizeof( IPPacket_t ) && pxNetworkBuffer->xDataLength <= ipTOTAL_ETHERNET_FRAME_SIZE );

    pxNetworkEndPoints = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );
    __CPROVER_assume( pxNetworkEndPoints->pxNext == NULL );

    IPPacket_t * const pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

    __CPROVER_file_local_FreeRTOS_IP_c_prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );
}
