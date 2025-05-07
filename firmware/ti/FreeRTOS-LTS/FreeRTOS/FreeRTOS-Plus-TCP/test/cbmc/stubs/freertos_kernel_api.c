/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

#include "cbmc.h"

/****************************************************************
* This is a collection of abstractions of methods in the FreeRTOS Kernel
* API.  The abstractions simply perform minimal validation of
* function arguments, and return unconstrained values of the
* appropriate type.
****************************************************************/

/****************************************************************
* Abstract vTaskSuspendAll
****************************************************************/
void vTaskSuspendAll( void )
{
}

/****************************************************************/

/****************************************************************
* Abstract vPortEnterCritical
****************************************************************/
void vPortEnterCritical( void )
{
}

/****************************************************************/

/****************************************************************
* Abstract vListInsertEnd
****************************************************************/
void vListInsertEnd( List_t * const pxList,
                     ListItem_t * const pxNewListItem )
{
}

/****************************************************************/

/****************************************************************
* Abstract vPortExitCritical
****************************************************************/
void vPortExitCritical( void )
{
}

/****************************************************************/

/****************************************************************
* Abstract xTaskResumeAll
****************************************************************/
BaseType_t xTaskResumeAll( void )
{
    BaseType_t xReturn;

    __CPROVER_assume( ( xReturn == pdTRUE ) || ( xReturn == pdFALSE ) );

    return xReturn;
}

/****************************************************************/

/****************************************************************
* Abstract xEventGroupSetBits
****************************************************************/
EventBits_t xEventGroupSetBits( EventGroupHandle_t xEventGroup,
                                const EventBits_t uxBitsToSet )
{
    EventBits_t xReturn;

    return xReturn;
}

/****************************************************************/
