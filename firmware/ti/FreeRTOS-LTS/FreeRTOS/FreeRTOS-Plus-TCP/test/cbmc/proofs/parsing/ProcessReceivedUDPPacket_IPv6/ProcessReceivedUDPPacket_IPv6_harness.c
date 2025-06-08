/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* CBMC includes. */
#include "cbmc.h"

/*This proof assumes that pxUDPSocketLookup is implemented correctly. */

/* This proof was done before. Hence we assume it to be correct here. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                            const uint32_t ulIPAddress )
{
}

/* This proof was done before. Hence we assume it to be correct here. */
BaseType_t xIsDHCPSocket( Socket_t xSocket )
{
}

/* This proof was done before. Hence we assume it to be correct here. */
uint32_t ulDNSHandlePacket( NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    /* ulDNSHandlePacket always returns pdFAIL. */
    return pdFAIL;
}

/* This proof was done before. Hence we assume it to be correct here. */
uint32_t ulNBNSHandlePacket( NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    /* ulNBNSHandlePacket always returns pdFAIL. */
    return pdFAIL;
}

/* Abstraction of pxUDPSocketLookup */
FreeRTOS_Socket_t * pxUDPSocketLookup( UBaseType_t uxLocalPort )
{
    return safeMalloc( sizeof( FreeRTOS_Socket_t ) );
}

/* This proof was done before. Hence we assume it to be correct here. */
BaseType_t xCheckRequiresARPResolution( NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    BaseType_t xReturn;

    __CPROVER_assume( ( xReturn == pdTRUE ) || ( xReturn == pdFALSE ) );

    return xReturn;
}

/* Abstraction of vNDRefreshCacheEntry */
void vNDRefreshCacheEntry( const MACAddress_t * pxMACAddress,
                           const IPv6_Address_t * pxIPAddress,
                           NetworkEndPoint_t * pxEndPoint )
{
}

/* Abstraction of uxIPHeaderSizePacket */
size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    /* To enter xProcessReceivedUDPPacket_IPv6, the frame type of ethernet header must be IPv6. */
    return ipSIZE_OF_IPv6_HEADER;
}

/* Abstraction of xSendDHCPEvent */
BaseType_t xSendDHCPEvent( struct xNetworkEndPoint * pxEndPoint )
{
    BaseType_t xReturn;

    __CPROVER_assume( ( xReturn == pdTRUE ) || ( xReturn == pdFALSE ) );

    return xReturn;
}

void harness()
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );
    BaseType_t * pxIsWaitingForARPResolution;
    NetworkEndPoint_t xEndpoint;
    uint16_t usPort;

    pxIsWaitingForARPResolution = safeMalloc( sizeof( BaseType_t ) );

    /* The function under test is only called by the IP-task. The below pointer is an
     * address of a local variable which is being passed to the function under test.
     * Thus, it cannot ever be NULL. */
    __CPROVER_assume( pxIsWaitingForARPResolution != NULL );

    /* The network buffer must not be NULL, checked in prvProcessEthernetPacket. */
    __CPROVER_assume( pxNetworkBuffer != NULL );

    pxNetworkBuffer->pucEthernetBuffer = safeMalloc( sizeof( UDPPacket_IPv6_t ) );
    pxNetworkBuffer->pxEndPoint = &xEndpoint;

    /* The ethernet buffer must be valid. */
    __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

    xProcessReceivedUDPPacket_IPv6( pxNetworkBuffer, usPort, pxIsWaitingForARPResolution );
}
