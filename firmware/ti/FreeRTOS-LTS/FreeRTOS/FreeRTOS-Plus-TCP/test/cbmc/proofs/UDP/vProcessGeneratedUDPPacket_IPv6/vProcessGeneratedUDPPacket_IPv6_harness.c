/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "list.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ND.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"

/* Include the stubs for APIs. */
#include "memory_assignments.c"
#include "freertos_api.c"

/* We do not need to calculate the actual checksum for the proof to be complete.
 * Neither does the checksum matter for completeness. */
uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
    uint16_t usChecksum;

    __CPROVER_assert( pucNextData != NULL, "Next data in GenerateChecksum cannot be NULL" );
    /* Return any random value of checksum since it does not matter for CBMC checks. */
    return usChecksum;
}


/* We do not need to calculate the actual checksum for the proof to be complete.
 * Neither does the checksum matter for completeness. */
uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    uint16_t usProtocolChecksum;

    __CPROVER_assert( pucEthernetBuffer != NULL, "The Ethernet buffer cannot be NULL while generating Protocol Checksum" );

    /* Return random value of checksum since it does not matter for CBMC checks. */
    return usProtocolChecksum;
}

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
eARPLookupResult_t eNDGetCacheEntry( IPv6_Address_t * pxIPAddress,
                                     MACAddress_t * const pxMACAddress,
                                     struct xNetworkEndPoint ** ppxEndPoint )
{
    eARPLookupResult_t eResult;

    __CPROVER_assert( pxIPAddress != NULL, "pxIPAddress cannot be NULL" );
    __CPROVER_assert( pxMACAddress != NULL, "pxMACAddress cannot be NULL" );

    return eResult;
}

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void vNDSendNeighbourSolicitation( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                   const IPv6_Address_t * pxIPAddress )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer descriptor cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer->pucEthernetBuffer != NULL, "The Ethernet buffer cannot be NULL." );
    __CPROVER_assert( pxIPAddress != NULL, "pxIPAddress cannot be NULL." );
}

BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    BaseType_t ret;

    __CPROVER_assert( pxDescriptor != NULL, "The network interface cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer descriptor cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer->pucEthernetBuffer != NULL, "The Ethernet buffer cannot be NULL." );

    return ret;
}


void harness()
{
    size_t xRequestedSizeBytes;

    /* Assume that the size of packet must be greater than that of UDP-Packet and less than
     * that of the Ethernet Frame Size. */
    __CPROVER_assume( xRequestedSizeBytes >= sizeof( UDPPacket_IPv6_t ) && xRequestedSizeBytes <= ipTOTAL_ETHERNET_FRAME_SIZE );

    /* Second parameter is not used from CBMC's perspective. */
    NetworkBufferDescriptor_t * const pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( xRequestedSizeBytes, 0 );

    /* The buffer cannot be NULL for the function call. */
    __CPROVER_assume( pxNetworkBuffer != NULL );
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    /*
     * Add an end point to the network buffer present. Its assumed that the
     * network interface layer correctly assigns the end point to the generated buffer.
     */
    pxNetworkBuffer->pxEndPoint = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkBuffer->pxEndPoint != NULL );
    pxNetworkBuffer->pxEndPoint->pxNext = NULL;

    /* Add an interface */
    pxNetworkBuffer->pxEndPoint->pxNetworkInterface = ( NetworkInterface_t * ) safeMalloc( sizeof( NetworkInterface_t ) );
    __CPROVER_assume( pxNetworkBuffer->pxEndPoint->pxNetworkInterface != NULL );

    /* Add few endpoints to global pxNetworkEndPoints */
    pxNetworkEndPoints = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );

    pxNetworkEndPoints->pxNetworkInterface = pxNetworkBuffer->pxEndPoint->pxNetworkInterface;

    if( nondet_bool() )
    {
        pxNetworkEndPoints->pxNext = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
        __CPROVER_assume( pxNetworkEndPoints->pxNext != NULL );
        pxNetworkEndPoints->pxNext->pxNetworkInterface = pxNetworkBuffer->pxEndPoint->pxNetworkInterface;
        pxNetworkEndPoints->pxNext->pxNext = NULL;
    }
    else
    {
        pxNetworkEndPoints->pxNext = NULL;
    }

    pxNetworkBuffer->pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    vProcessGeneratedUDPPacket_IPv6( pxNetworkBuffer );
}
