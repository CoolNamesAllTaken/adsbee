/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"

void harness()
{
    /*
     * The assumption made here is that the buffer pointed by pucEthernetBuffer
     * is at least allocated to sizeof(ARPPacket_t) size but eventually a even larger buffer.
     * This is not checked inside vARPGenerateRequestPacket.
     */
    uint8_t ucBUFFER_SIZE;

    __CPROVER_assume( ucBUFFER_SIZE >= sizeof( ARPPacket_t ) && ucBUFFER_SIZE < 2 * sizeof( ARPPacket_t ) );
    void * xBuffer = malloc( ucBUFFER_SIZE );

    __CPROVER_assume( xBuffer != NULL );

    NetworkBufferDescriptor_t xNetworkBuffer2;

    xNetworkBuffer2.pucEthernetBuffer = xBuffer;
    xNetworkBuffer2.xDataLength = ucBUFFER_SIZE;

    /*
     * This proof assumes one end point is present.
     */
    xNetworkBuffer2.pxEndPoint = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( xNetworkBuffer2.pxEndPoint != NULL );
    xNetworkBuffer2.pxEndPoint->pxNext = NULL;

    /* vARPGenerateRequestPacket asserts buffer has room for a packet */
    __CPROVER_assume( xNetworkBuffer2.xDataLength >= sizeof( ARPPacket_t ) );
    vARPGenerateRequestPacket( &xNetworkBuffer2 );
}
