/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"

extern ARPCacheRow_t xARPCache[ ipconfigARP_CACHE_ENTRIES ];

static NetworkEndPoint_t xEndPoint_Temp;

void harness()
{
    MACAddress_t xMACAddress;
    uint32_t ulIPAddress;

    NetworkInterface_t ** ppxInterface = ( NetworkInterface_t ** ) malloc( sizeof( NetworkInterface_t * ) );

    if( ppxInterface )
    {
        *ppxInterface = ( NetworkInterface_t * ) malloc( sizeof( NetworkInterface_t ) );
        __CPROVER_assume( *ppxInterface != NULL );
    }

    eARPGetCacheEntryByMac( &xMACAddress, &ulIPAddress, ppxInterface );
}
