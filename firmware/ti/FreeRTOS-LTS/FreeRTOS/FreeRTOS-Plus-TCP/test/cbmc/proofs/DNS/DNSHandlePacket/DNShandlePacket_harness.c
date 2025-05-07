/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"

/* Function prvParseDNSReply is proven to be correct separately. */
uint32_t prvParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                           size_t xBufferLength,
                           BaseType_t xExpected )
{
}

void harness()
{
    NetworkBufferDescriptor_t xNetworkBuffer;

    xNetworkBuffer.pucEthernetBuffer = malloc( sizeof( UDPPacket_t ) + sizeof( DNSMessage_t ) );
    ulDNSHandlePacket( &xNetworkBuffer );
}
