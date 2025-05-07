/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"
#include "event_groups.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"

#include "memory_assignments.c"


/*********************************************************************************
 *
 * The below structure definitions are just copy pasted from the FreeRTOS-Kernel.
 * To understand the proof, you need not understand the structures and they can
 * be ignored safely.
 *
 ********************************************************************************/

/* Define the bits used by Kernel. */
#define eventEVENT_BITS_CONTROL_BYTES    0xff000000UL

typedef struct EventGroupDef_t
{
    EventBits_t uxEventBits;
    List_t xTasksWaitingForBits;

    #if ( configUSE_TRACE_FACILITY == 1 )
        UBaseType_t uxEventGroupNumber;
    #endif

    #if ( ( configSUPPORT_STATIC_ALLOCATION == 1 ) && ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) )
        uint8_t ucStaticallyAllocated;
    #endif
} EventGroup_t;

typedef struct QueuePointers
{
    int8_t * pcTail;
    int8_t * pcReadFrom;
} QueuePointers_t;

typedef struct SemaphoreData
{
    TaskHandle_t xMutexHolder;
    UBaseType_t uxRecursiveCallCount;
} SemaphoreData_t;

typedef struct QueueDefinition
{
    int8_t * pcHead;
    int8_t * pcWriteTo;

    union
    {
        QueuePointers_t xQueue;
        SemaphoreData_t xSemaphore;
    } u;

    List_t xTasksWaitingToSend;
    List_t xTasksWaitingToReceive;

    volatile UBaseType_t uxMessagesWaiting;
    UBaseType_t uxLength;
    UBaseType_t uxItemSize;

    volatile int8_t cRxLock;
    volatile int8_t cTxLock;

    #if ( ( configSUPPORT_STATIC_ALLOCATION == 1 ) && ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) )
        uint8_t ucStaticallyAllocated;
    #endif

    #if ( configUSE_QUEUE_SETS == 1 )
        struct QueueDefinition * pxQueueSetContainer;
    #endif

    #if ( configUSE_TRACE_FACILITY == 1 )
        UBaseType_t uxQueueNumber;
        uint8_t ucQueueType;
    #endif
} xQUEUE;

/********************************************************/
/********* End Kernel cut-paste section *****************/
/********************************************************/


/* The memory safety of xQueueGenericSend has been proved before.
 * See github.com/FreeRTOS/FreeRTOS/FreeRTOS/Test/CBMC/proofs/Queue/QueueGenericSend.
 */
BaseType_t xQueueGenericSend( QueueHandle_t xQueue,
                              const void * const pvItemToQueue,
                              TickType_t xTicksToWait,
                              const BaseType_t xCopyPosition )
{
    BaseType_t xResult;

    /* These asserts are copied over from the original function itself. */
    __CPROVER_assert( xQueue != NULL, "xQueue cannot be NULL" );
    __CPROVER_assert( !( ( pvItemToQueue == NULL ) && ( xQueue->uxItemSize != ( UBaseType_t ) 0U ) ),
                      "If itemsize is non-zero, then pvItemToQueue cannot be NULL." );
    __CPROVER_assert( !( ( xCopyPosition == queueOVERWRITE ) && ( xQueue->uxLength != 1 ) ),
                      "If length is one, then check the copy position" );

    /* Return any random value. */
    return xResult;
}


EventBits_t xEventGroupSetBits( EventGroupHandle_t xEventGroup,
                                const EventBits_t uxBitsToSet )
{
    EventBits_t uxReturnBits;

    /* The below asserts are copied over from the original function itself. */
    __CPROVER_assert( xEventGroup != NULL,
                      "The event group cannot be NULL" );
    __CPROVER_assert( ( uxBitsToSet & eventEVENT_BITS_CONTROL_BYTES ) == 0,
                      "Cannot set Kernel bits" );

    /* Return any random value. */
    return uxReturnBits;
}

void SocketWakeupCallback_Stub( struct xSOCKET * pxSocket )
{
    __CPROVER_assert( pxSocket != NULL,
                      "The pxSocket cannot be NULL" );
}

void harness()
{
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();

    __CPROVER_assume( pxSocket != NULL );
    __CPROVER_assume( pxSocket != FREERTOS_INVALID_SOCKET );

    pxSocket->pxUserWakeCallback = SocketWakeupCallback_Stub;

    pxSocket->pxSocketSet = safeMalloc( sizeof( struct xSOCKET_SET ) );

    if( pxSocket->pxSocketSet != NULL )
    {
        pxSocket->pxSocketSet->xSelectGroup = safeMalloc( sizeof( struct EventGroupDef_t ) );

        /* The event group cannot be NULL. */
        __CPROVER_assume( pxSocket->pxSocketSet->xSelectGroup != NULL );
    }

    pxSocket->pxUserSemaphore = safeMalloc( sizeof( xQUEUE ) );

    if( pxSocket->pxUserSemaphore != NULL )
    {
        /* The item size must be zero since this queue will act as a semaphore.  */
        __CPROVER_assume( pxSocket->pxUserSemaphore->uxItemSize == 0 );
    }

    pxSocket->xEventGroup = safeMalloc( sizeof( struct EventGroupDef_t ) );

    /* Call to init the socket list. */
    vNetworkSocketsInit();

    vSocketWakeUpUser( pxSocket );
}
