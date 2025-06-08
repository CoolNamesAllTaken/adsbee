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

/** @brief The pointer to buffer with packet waiting for ARP resolution. This variable
 *  is defined in FreeRTOS_IP.c.
 *  This pointer is for internal use only. */
NetworkBufferDescriptor_t * pxARPWaitingNetworkBuffer;

BaseType_t NetworkInterfaceOutputFunction_Stub_Called = 0;

/* ======================== Stub Callback Functions ========================= */

BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    NetworkInterfaceOutputFunction_Stub_Called++;
    return pdFALSE;
}

/**
 * @brief Receive and analyse a RA ( Router Advertisement ) message.
 *        If the reply is satisfactory, the end-point will do SLAAC: choose an IP-address using the
 *        prefix offered, and completed with random bits.  It will start testing if another device
 *        already exists that uses the same IP-address.
 *
 * @param[in] pxNetworkBuffer The buffer that contains the message.
 */
void vReceiveRA( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
}


/**
 * @brief Receive a NA ( Neighbour Advertisement ) message to see if a chosen IP-address is already in use.
 *
 * @param[in] pxNetworkBuffer The buffer that contains the message.
 */
void vReceiveNA( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
}

/*-----------------------------------------------------------*/
