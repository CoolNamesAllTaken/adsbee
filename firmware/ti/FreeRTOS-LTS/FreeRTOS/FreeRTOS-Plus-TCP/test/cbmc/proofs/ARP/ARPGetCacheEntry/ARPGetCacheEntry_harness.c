/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"


void harness()
{
    uint32_t ulIPAddress;
    MACAddress_t xMACAddress;

    /*
     * For this proof, its assumed that the endpoints and interfaces are correctly
     * initialised and the pointers are set correctly.
     * Assumes one endpoint and interface is present.
     */

    pxNetworkEndPoints = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );

    /* Interface init. */
    pxNetworkEndPoints->pxNetworkInterface = ( NetworkInterface_t * ) malloc( sizeof( NetworkInterface_t ) );
    __CPROVER_assume( pxNetworkEndPoints->pxNetworkInterface != NULL );

    if( nondet_bool() )
    {
        pxNetworkEndPoints->pxNext = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );
        __CPROVER_assume( pxNetworkEndPoints->pxNext != NULL );
        pxNetworkEndPoints->pxNext->pxNext = NULL;
        pxNetworkEndPoints->pxNext->pxNetworkInterface = pxNetworkEndPoints->pxNetworkInterface;
    }
    else
    {
        pxNetworkEndPoints->pxNext = NULL;
    }

    NetworkInterface_t ** ppxInterface = ( NetworkInterface_t ** ) malloc( sizeof( NetworkInterface_t * ) );

    if( ppxInterface )
    {
        *ppxInterface = ( NetworkInterface_t * ) malloc( sizeof( NetworkInterface_t ) );
        __CPROVER_assume( *ppxInterface != NULL );
    }

    eARPGetCacheEntry( &ulIPAddress, &xMACAddress, ppxInterface );
}
