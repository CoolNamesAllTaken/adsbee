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

/* ======================== Stub Callback Functions ========================= */

/*
 * @brief Send a neighbour solicitation.
 * @param[in] pxIPAddress: A network buffer big enough to hold the ICMP packet.
 * @param[in,out] pxMACAddress: When found, the array of 6 bytes will be filled
 *                with the MAC-address.
 * @param[in,out] ppxEndPoint: The pointer to a pointer will point to an
 *                             end-point to which the device has responded.
 *
 * @note Look for ulIPAddress in the ND cache.  If the IP address exists, copy the
 * associated MAC address into pxMACAddress, refresh the ND cache entry's
 * age, and return eARPCacheHit.  If the IP address does not exist in the ND
 * cache return eARPCacheMiss.  If the packet cannot be sent for any reason
 * (maybe DHCP is still in process, or the addressing needs a gateway but there
 * isn't a gateway defined) then return eCantSendPacket.
 */
eARPLookupResult_t eNDGetCacheEntry( IPv6_Address_t * pxIPAddress,
                                     MACAddress_t * const pxMACAddress,
                                     struct xNetworkEndPoint ** ppxEndPoint )
{
    memset( pxMACAddress, 0, sizeof( MACAddress_t ) );

    return eARPCacheHit;
}

/**
 * @brief Create an IPv16 address, based on a prefix.
 *
 * @param[out] pxIPAddress: The location where the new IPv6 address
 *                          will be stored.
 * @param[in] pxPrefix: The prefix to be used.
 * @param[in] uxPrefixLength: The length of the prefix.
 * @param[in] xDoRandom: A non-zero value if the bits after the
 *                       prefix should have a random value.
 *
 * @return pdPASS if the operation was successful. Or pdFAIL in
 *         case xApplicationGetRandomNumber()
 *         returned an error.
 */
BaseType_t FreeRTOS_CreateIPv6Address( IPv6_Address_t * pxIPAddress,
                                       const IPv6_Address_t * pxPrefix,
                                       size_t uxPrefixLength,
                                       BaseType_t xDoRandom )
{
}

/**
 * @brief Send a neighbour solicitation.
 * @param[in] pxNetworkBuffer: A network buffer big enough to hold the ICMP packet.
 * @param[in] pxIPAddress: The IPv6 address of the target device.
 *
 * @note Send out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 * add an entry into the ND table that indicates that an ND reply is
 * outstanding so re-transmissions can be generated.
 */
void vNDSendNeighbourSolicitation( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                   const IPv6_Address_t * pxIPAddress )
{
}
