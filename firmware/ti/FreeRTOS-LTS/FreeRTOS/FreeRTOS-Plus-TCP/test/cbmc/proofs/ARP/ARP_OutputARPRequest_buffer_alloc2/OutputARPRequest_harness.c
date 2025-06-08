/* This harness is linked against
 * libraries/freertos_plus/standard/freertos_plus_tcp/source/portable/BufferManagement/BufferAllocation_2.goto
 */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#if ( ipconfigUSE_LLMNR == 1 )
    #include "FreeRTOS_DNS.h"
#endif /* ipconfigUSE_LLMNR */
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"

void * pvPortMalloc( size_t xWantedSize )
{
    void * ptr = malloc( xWantedSize );

    __CPROVER_assume( ptr != NULL );
    return ptr;
}


void vPortFree( void * pv )
{
    free( pv );
}

/*
 * This function function writes a buffer to the network.  We stub it
 * out here, and assume it has no side effects relevant to memory safety.
 */
BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxDescriptor != NULL, "The network interface cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer descriptor cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer->pucEthernetBuffer != NULL, "The ethernet buffer cannot be NULL." );

    if( xReleaseAfterSend != pdFALSE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }
}

void harness()
{
    BaseType_t xRes = xNetworkBuffersInitialise();

    /*
     * For this proof, its assumed that the endpoints and interfaces are correctly
     * initialised and the pointers are set correctly.
     * Assumes one endpoint and interface is present.
     */

    pxNetworkEndPoints = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );
    pxNetworkEndPoints->pxNext = NULL;

    /* Interface init. */
    pxNetworkEndPoints->pxNetworkInterface = ( NetworkInterface_t * ) malloc( sizeof( NetworkInterface_t ) );
    pxNetworkEndPoints->pxNetworkInterface->pxNext = NULL;

    pxNetworkEndPoints->pxNetworkInterface->pfOutput = NetworkInterfaceOutputFunction_Stub;
    /* No assumption is added for pfOutput as its pointed to a static object/memory location. */

    if( xRes == pdPASS )
    {
        uint32_t ulIPAddress;
        FreeRTOS_OutputARPRequest( ulIPAddress );
    }
}
