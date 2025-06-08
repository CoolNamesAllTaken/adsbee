/* Include Unity header */
#include <unity.h>

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* ===========================  EXTERN VARIABLES  =========================== */

BaseType_t NetworkInterfaceOutputFunction_Stub_Called = 0;

/* ======================== Stub Callback Functions ========================= */

BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    NetworkInterfaceOutputFunction_Stub_Called++;
    return 0;
}

/**
 * @brief Called by prvTCPReturnPacket(), this function makes sure that the network buffer
 *        has 'pxEndPoint' set properly.
 * @param[in] pxSocket The socket on which the packet is being sent.
 * @param[in] pxNetworkBuffer The network buffer carrying the outgoing message.
 * @param[in] uxIPHeaderSize The size of the IP-header, which depends on the IP-type.
 */
void prvTCPReturn_SetEndPoint( const FreeRTOS_Socket_t * pxSocket,
                               NetworkBufferDescriptor_t * pxNetworkBuffer,
                               size_t uxIPHeaderSize )
{
    const IPHeader_IPv6_t * pxIPHeader_IPv6 = NULL;

    if( ( pxSocket != NULL ) && ( pxSocket->pxEndPoint != NULL ) )
    {
        pxNetworkBuffer->pxEndPoint = pxSocket->pxEndPoint;
    }
    else
    {
        /* Not able to find the endpoint */
        pxNetworkBuffer->pxEndPoint = NULL;
    }
}

/**
 * Called by prvTCPReturnPacket(), this function will set the the window
 * size on this side: 'xTCPHeader.usWindow'.
 */
void prvTCPReturn_CheckTCPWindow( FreeRTOS_Socket_t * pxSocket,
                                  const NetworkBufferDescriptor_t * pxNetworkBuffer,
                                  size_t uxIPHeaderSize )
{
}

/*
 * Called by prvTCPReturnPacket(), this function sets the sequence and ack numbers
 * in the TCP-header.
 */
void prvTCPReturn_SetSequenceNumber( FreeRTOS_Socket_t * pxSocket,
                                     const NetworkBufferDescriptor_t * pxNetworkBuffer,
                                     size_t uxIPHeaderSize,
                                     uint32_t ulLen )
{
}

/*
 * Return or send a packet to the other party.
 */
void prvTCPReturnPacket( FreeRTOS_Socket_t * pxSocket,
                         NetworkBufferDescriptor_t * pxDescriptor,
                         uint32_t ulLen,
                         BaseType_t xReleaseAfterSend )
{
}
