/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"

#include "freertos_api.c"
#include "memory_assignments.c"

/* The memory safety of vTCPWindowDestroy has already been proved in
 * proofs/TCPWin/vTCPWindowDestroy. */
void vTCPWindowDestroy( TCPWindow_t const * xWindow )
{
    __CPROVER_assert( xWindow != NULL, "xWindow cannot be NULL" );

    /* Do nothing. */
}

void harness()
{
    size_t xRequestedSizeBytes;
    TickType_t xBlockTimeTicks;
    FreeRTOS_Socket_t * pxSocket = safeMalloc( sizeof( FreeRTOS_Socket_t ) );

    /* Socket cannot be NULL or invalid for this proof. This is allowed since vSocketClose is called by IP task only. */
    __CPROVER_assume( pxSocket != NULL );
    __CPROVER_assume( pxSocket != FREERTOS_INVALID_SOCKET );

    /* Request a random number of bytes keeping in mind the maximum bound of CBMC. */
    __CPROVER_assume( xRequestedSizeBytes < ( CBMC_MAX_OBJECT_SIZE - ipBUFFER_PADDING ) );

    /* Non-deterministically malloc the callback function. */
    pxSocket->pxUserWakeCallback = safeMalloc( sizeof( SocketWakeupCallback_t ) );

    /* Non deterministically add an event group. */
    if( nondet_bool() )
    {
        pxSocket->xEventGroup = xEventGroupCreate();
        __CPROVER_assume( pxSocket->xEventGroup != NULL );
    }
    else
    {
        pxSocket->xEventGroup = NULL;
    }

    /* Create and fill the socket in the bound socket list. This socket will then be
     * removed by a call to the vSocketClose. */
    List_t BoundSocketList;
    vListInitialise( &BoundSocketList );

    /* Non-deterministically add the socket to bound socket list. */
    if( nondet_bool() )
    {
        vListInitialiseItem( &( pxSocket->xBoundSocketListItem ) );
        pxSocket->xBoundSocketListItem.pxContainer = &( BoundSocketList );
        vListInsertEnd( &BoundSocketList, &( pxSocket->xBoundSocketListItem ) );
    }
    else
    {
        pxSocket->xBoundSocketListItem.pxContainer = NULL;
    }

    /* See Configurations.json for details. Protocol can be UDP or TCP. */
    pxSocket->ucProtocol = PROTOCOL;

    NetworkBufferDescriptor_t * NetworkBuffer;

    /* Get a network buffer descriptor with requested bytes. See the constraints
     * on the number of requested bytes above. And block for random timer ticks. */
    if( pxSocket->ucProtocol == FREERTOS_IPPROTO_TCP )
    {
        pxSocket->u.xTCP.rxStream = malloc( sizeof( StreamBuffer_t ) );
        pxSocket->u.xTCP.txStream = malloc( sizeof( StreamBuffer_t ) );

        /* Non deterministically allocate/not-allocate the network buffer descriptor. */
        if( nondet_bool() )
        {
            pxSocket->u.xTCP.pxAckMessage = pxGetNetworkBufferWithDescriptor( xRequestedSizeBytes, xBlockTimeTicks );
        }
        else
        {
            pxSocket->u.xTCP.pxAckMessage = NULL;
        }
    }
    else if( pxSocket->ucProtocol == FREERTOS_IPPROTO_UDP )
    {
        /* Initialise the waiting packet list. */
        vListInitialise( &( pxSocket->u.xUDP.xWaitingPacketsList ) );

        /* Non-deterministically either add/not-add item to the waiting packet list. */
        if( nondet_bool() )
        {
            NetworkBuffer = pxGetNetworkBufferWithDescriptor( xRequestedSizeBytes, xBlockTimeTicks );
            /* Assume non-NULL network buffer for this case. */
            __CPROVER_assume( NetworkBuffer != NULL );

            /* Initialise the buffer list item. */
            vListInitialiseItem( &( NetworkBuffer->xBufferListItem ) );

            /*Set the item owner as the buffer itself. */
            listSET_LIST_ITEM_OWNER( &( NetworkBuffer->xBufferListItem ), ( void * ) NetworkBuffer );

            /* Set the container of the buffer list item as the waiting packet list. */
            NetworkBuffer->xBufferListItem.pxContainer = &( pxSocket->u.xUDP.xWaitingPacketsList );

            /* Insert the list-item into the waiting packet list. */
            vListInsertEnd( &( pxSocket->u.xUDP.xWaitingPacketsList ), &( NetworkBuffer->xBufferListItem ) );
        }
    }

    /* Call to init the socket list. */
    vNetworkSocketsInit();

    /* Call the function. */
    vSocketClose( pxSocket );

    /* No post checking to be done. */
}
