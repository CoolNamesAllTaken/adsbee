#include "cbmc.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_Routing.h"

/* This pointer is maintained by the IP-task. Defined in FreeRTOS_IP.c */
extern NetworkBufferDescriptor_t * pxARPWaitingNetworkBuffer;

/* This is an output function and need not be tested with this proof. */
void FreeRTOS_OutputARPRequest_Multi( NetworkEndPoint_t * pxEndPoint,
                                      uint32_t ulIPAddress )
{
}

/* This function is proved elsewhere hence stubbing it out */
eARPLookupResult_t eARPGetCacheEntry( uint32_t * pulIPAddress,
                                      MACAddress_t * const pxMACAddress,
                                      struct xNetworkEndPoint ** ppxEndPoint )
{
    eARPLookupResult_t eReturn;

    __CPROVER_assert( pulIPAddress != NULL, "pulIPAddress cannot be NULL." );
    __CPROVER_assert( pxMACAddress != NULL, "pxMACAddress cannot be NULL." );
    __CPROVER_assert( ppxEndPoint != NULL, "ppxEndPoint cannot be NULL." );

    /* Return random value */
    return eReturn;
}

void harness()
{
    NetworkBufferDescriptor_t xLocalBuffer;
    uint16_t usEthernetBufferSize;

    /* Non deterministically determine whether the pxARPWaitingNetworkBuffer will
     * point to some valid data or will it be NULL. */
    if( nondet_bool() )
    {
        /* The packet must at least be as big as an IP Packet. The size is not
         * checked in the function as the pointer is stored by the IP-task itself
         * and therefore it will always be of the required size. */
        __CPROVER_assume( usEthernetBufferSize >= sizeof( IPPacket_t ) );

        /* Add matching data length to the network buffer descriptor. */
        __CPROVER_assume( xLocalBuffer.xDataLength == usEthernetBufferSize );

        xLocalBuffer.pucEthernetBuffer = malloc( usEthernetBufferSize );

        /* Since this pointer is maintained by the IP-task, either the pointer
         * pxARPWaitingNetworkBuffer will be NULL or xLocalBuffer.pucEthernetBuffer
         * will be non-NULL. */
        __CPROVER_assume( xLocalBuffer.pucEthernetBuffer != NULL );

        pxARPWaitingNetworkBuffer = &xLocalBuffer;
    }
    else
    {
        pxARPWaitingNetworkBuffer = NULL;
    }

    /*
     * The assumption made here is that the buffer pointed by pucEthernetBuffer
     * is at least allocated to sizeof(ARPPacket_t) size but eventually an even larger buffer.
     * This is not checked inside eARPProcessPacket.
     */
    uint8_t ucBUFFER_SIZE;

    void * xBuffer = malloc( ucBUFFER_SIZE + sizeof( ARPPacket_t ) );

    __CPROVER_assume( xBuffer != NULL );

    NetworkBufferDescriptor_t xNetworkBuffer2;

    xNetworkBuffer2.pucEthernetBuffer = xBuffer;
    xNetworkBuffer2.xDataLength = ucBUFFER_SIZE + sizeof( ARPPacket_t );

    /*
     * This proof assumes one end point is present.
     */
    xNetworkBuffer2.pxEndPoint = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( xNetworkBuffer2.pxEndPoint != NULL );
    xNetworkBuffer2.pxEndPoint->pxNext = NULL;

    /* eARPProcessPacket will be called in the source code only after checking if
     * xNetworkBuffer2.pucEthernetBuffer is not NULL, hence, __CPROVER_assume( xBuffer != NULL );   */
    eARPProcessPacket( &xNetworkBuffer2 );
}
