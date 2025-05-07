/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_TCP_WIN.h"

/* Rx/Tx list items to be used in the proof. */
TCPSegment_t xRxSegmentListItem;
TCPSegment_t xTxSegmentListItem;

/* Definition of this function in FreeRTOS_TCP_WIN.c. */
void __CPROVER_file_local_FreeRTOS_TCP_WIN_c_vListInsertGeneric( List_t * const pxList,
                                                                 ListItem_t * const pxNewListItem,
                                                                 MiniListItem_t * const pxWhere );

/* Segment List is defined in FreeRTOS_TCP_WIN.c */
extern List_t xSegmentList;

void harness()
{
    /* Create a TCP Window to be destroyed and fill it with random data. */
    TCPWindow_t xWindow;

    /* Initialise the segment list. */
    vListInitialise( &xSegmentList );

    /* Initialise the Rx and Tx lists of the window. */
    vListInitialise( &xWindow.xRxSegments );
    vListInitialise( &xWindow.xTxSegments );

    if( nondet_bool() )
    {
        /********************** Fill in Rx segments ********************/
        xRxSegmentListItem.xSegmentItem.pvOwner = &( xRxSegmentListItem );

        /* Make the container of the queue item is NULL. */
        xRxSegmentListItem.xQueueItem.pxContainer = NULL;

        __CPROVER_file_local_FreeRTOS_TCP_WIN_c_vListInsertGeneric( &xWindow.xRxSegments,
                                                                    &( xRxSegmentListItem.xSegmentItem ), &xWindow.xRxSegments.xListEnd );
    }

    if( nondet_bool() )
    {
        /********************** Fill in Tx segments ********************/
        xTxSegmentListItem.xSegmentItem.pvOwner = &( xTxSegmentListItem );

        /* Make the container of the queue item is NULL. */
        xTxSegmentListItem.xQueueItem.pxContainer = NULL;

        __CPROVER_file_local_FreeRTOS_TCP_WIN_c_vListInsertGeneric( &xWindow.xTxSegments,
                                                                    &( xTxSegmentListItem.xSegmentItem ), &xWindow.xTxSegments.xListEnd );
    }

    /* Call the function. The function is internally called from just one location
     * where it is made sure that the parameter passed to the function is non-NULL.
     * Therefore, a non-NULL value is passed to the function. */
    vTCPWindowDestroy( &xWindow );
}
