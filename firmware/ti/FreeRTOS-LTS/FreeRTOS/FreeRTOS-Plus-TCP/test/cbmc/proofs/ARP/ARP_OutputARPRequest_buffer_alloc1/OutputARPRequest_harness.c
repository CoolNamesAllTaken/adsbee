/* This harness is linked against
 * libraries/freertos_plus/standard/freertos_plus_tcp/source/portable/BufferManagement/BufferAllocation_1.goto
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

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    for( int x = 0; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++ )
    {
        NetworkBufferDescriptor_t * current = &pxNetworkBuffers[ x ];
        #if ( ipconfigETHERNET_MINIMUM_PACKET_BYTES > 0 )
            current->pucEthernetBuffer = malloc( sizeof( ARPPacket_t ) + ( ipconfigETHERNET_MINIMUM_PACKET_BYTES - sizeof( ARPPacket_t ) ) );
        #else
            current->pucEthernetBuffer = malloc( sizeof( ARPPacket_t ) );
        #endif
        __CPROVER_assume( current->pucEthernetBuffer != NULL );
        current->xDataLength = sizeof( ARPPacket_t );
    }
}

/* The code expects that the Semaphore creation relying on pvPortMalloc
 * is successful. This is checked by an assert statement, that gets
 * triggered when the allocation fails. Nevertheless, the code is perfectly
 * guarded against a failing Semaphore allocation. To make the assert pass,
 * it is assumed for now, that pvPortMalloc doesn't fail. Using a model allowing
 * failures of the allocation might be possible
 * after removing the assert in l.105 of BufferAllocation_1.c, from a memory
 * safety point of view. */
void * pvPortMalloc( size_t xWantedSize )
{
    void * ptr = malloc( xWantedSize );

    __CPROVER_assume( ptr != NULL );
    return ptr;
}

/*
 * This function is implemented by a third party.
 * After looking through a couple of samples in the demos folder, it seems
 * like the only shared contract is that you want to add the if statement
 * for releasing the buffer to the end. Apart from that, it is up to the vendor,
 * how to write this code out to the network.
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
