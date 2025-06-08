/*
 * FreeRTOS-Cellular-Interface v1.4.0
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 */

#ifndef __CELLULAR_PLATFORM_H__
#define __CELLULAR_PLATFORM_H__

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

/*-----------------------------------------------------------*/


/**
 * @brief Cellular library platform event group APIs.
 *
 * Cellular library use platform event group for process synchronization.
 *
 * The EventGroup functions in the following link can be referenced as function prototype.
 * https://www.freertos.org/event-groups-API.html
 *
 */

#undef LogError
#define LogError
#undef LogDebug
#define LogDebug
#undef LogWarn
#define LogWarn
#undef LogInfo
#define LogInfo

#define configASSERT

#define Platform_Delay

typedef void * PVOID;

#define PlatformEventGroupHandle_t           uint16_t
#define PlatformEventGroup_Delete            MockPlatformEventGroup_Delete
#define PlatformEventGroup_ClearBits         MockPlatformEventGroup_ClearBits
#define PlatformEventGroup_Create            MockPlatformEventGroup_Create
#define PlatformEventGroup_GetBits           MockPlatformEventGroup_GetBits
#define PlatformEventGroup_SetBits
#define PlatformEventGroup_SetBitsFromISR    MockPlatformEventGroup_SetBitsFromISR
#define PlatformEventGroup_WaitBits          MockPlatformEventGroup_WaitBits
#define PlatformEventGroup_EventBits         uint32_t

#define vQueueDelete                         MockvQueueDelete
#define xQueueSend                           MockxQueueSend
#define xQueueReceive                        MockxQueueReceive
#define xQueueCreate                         MockxQueueCreate

#define PlatformMutex_Create                 MockPlatformMutex_Create
#define PlatformMutex_Destroy                MockPlatformMutex_Destroy
#define PlatformMutex_Lock                   MockPlatformMutex_Lock
#define PlatformMutex_TryLock                MockPlatformMutex_TryLock
#define PlatformMutex_Unlock                 MockPlatformMutex_Unlock

#define Platform_CreateDetachedThread        MockPlatform_CreateDetachedThread

#define taskENTER_CRITICAL()    PVOID
#define taskEXIT_CRITICAL()     PVOID

#define pdFALSE             ( 0x0 )
#define pdTRUE              ( 0x1 )
#define pdPASS              ( 0x1 )

#define PlatformTickType    uint64_t

/* Converts a time in milliseconds to a time in ticks.  This macro can be
 * overridden by a macro of the same name defined in FreeRTOSConfig.h in case the
 * definition here is not suitable for your application. */
#ifndef pdMS_TO_TICKS
    #define pdMS_TO_TICKS( xTimeInMs )    ( ( TickType_t ) ( ( ( TickType_t ) ( xTimeInMs ) * ( TickType_t ) 1000 ) / ( TickType_t ) 1000U ) )
#endif

#define CELLULAR_URC_HANDLER_TABLE_SIZE                ( sizeof( CellularUrcHandlerTable ) / sizeof( CellularAtParseTokenMap_t ) )
#define CELLULAR_SRC_TOKEN_ERROR_TABLE_SIZE            ( sizeof( CellularSrcTokenErrorTable ) / sizeof( char * ) )
#define CELLULAR_SRC_TOKEN_SUCCESS_TABLE_SIZE          ( sizeof( CellularSrcTokenSuccessTable ) / sizeof( char * ) )
#define CELLULAR_URC_TOKEN_WO_PREFIX_TABLE_SIZE        ( sizeof( CellularUrcTokenWoPrefixTable ) / sizeof( char * ) )
#define CELLULAR_SRC_EXTRA_TOKEN_SUCCESS_TABLE_SIZE    ( sizeof( CellularSrcExtraTokenSuccessTable ) / sizeof( char * ) )

#if ( configUSE_16_BIT_TICKS == 1 )
    typedef uint16_t TickType_t;
    #define portMAX_DELAY    ( TickType_t ) 0xffff
#else
    typedef uint64_t TickType_t;
    #define portMAX_DELAY    ( TickType_t ) 0xffffffffUL
#endif

/*
 * The type that holds event bits always matches TickType_t - therefore the
 * number of bits it holds is set by configUSE_16_BIT_TICKS (16 bits if set to 1,
 * 32 bits if set to 0.
 *
 * \defgroup EventBits_t EventBits_t
 * \ingroup EventGroup
 */
typedef TickType_t   EventBits_t;

/**
 * @brief Cellular library platform thread API and configuration.
 *
 * Cellular library create a detached thread by this API.
 * The threadRoutine should be called with pArgument in the created thread.
 *
 * PLATFORM_THREAD_DEFAULT_STACK_SIZE and PLATFORM_THREAD_DEFAULT_PRIORITY defines
 * the platform related stack size and priority.
 */

bool Platform_CreateDetachedThread( void ( * threadRoutine )( void * pArgument ),
                                    void * pArgument,
                                    size_t priority,
                                    size_t stackSize );

#define PLATFORM_THREAD_DEFAULT_STACK_SIZE    ( 2048U )
#define PLATFORM_THREAD_DEFAULT_PRIORITY      ( 5U )

/*-----------------------------------------------------------*/

/*
 * Definition of the queue used by the scheduler.
 * Items are queued by copy, not reference.  See the following link for the
 * rationale: https://www.FreeRTOS.org/Embedded-RTOS-Queues.html
 */
struct QueueDefinition  /* The old naming convention is used to prevent breaking kernel aware debuggers. */
{
    int8_t * pcHead;    /*< Points to the beginning of the queue storage area. */
    int8_t * pcWriteTo; /*< Points to the free next place in the storage area. */
};

/**
 * Type by which queues are referenced.  For example, a call to xQueueCreate()
 * returns an QueueHandle_t variable that can then be used as a parameter to
 * xQueueSend(), xQueueReceive(), etc.
 */
struct QueueDefinition; /* Using old naming convention so as not to break kernel aware debuggers. */
typedef struct QueueDefinition * QueueHandle_t;

/*
 * In line with software engineering best practice, especially when supplying a
 * library that is likely to change in future versions, FreeRTOS implements a
 * strict data hiding policy.  This means the Queue structure used internally by
 * FreeRTOS is not accessible to application code.  However, if the application
 * writer wants to statically allocate the memory required to create a queue
 * then the size of the queue object needs to be know.  The StaticQueue_t
 * structure below is provided for this purpose.  Its sizes and alignment
 * requirements are guaranteed to match those of the genuine structure, no
 * matter which architecture is being used, and no matter how the values in
 * FreeRTOSConfig.h are set.  Its contents are somewhat obfuscated in the hope
 * users will recognise that it would be unwise to make direct use of the
 * structure members.
 */
typedef struct xSTATIC_QUEUE
{
    void * pvDummy1[ 3 ];
} StaticQueue_t;
typedef StaticQueue_t StaticSemaphore_t;

/**
 * @brief Cellular library platform mutex APIs.
 *
 * Cellular library use platform mutex to protect resource.
 *
 * The IotMutex_ functions can be referenced as function prototype for
 * PlatfromMutex_ prefix function in the following link.
 * https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/platform/platform_threads_functions.html
 *
 */
typedef long          BaseType_t;
typedef struct PlatformMutex
{
    StaticSemaphore_t xMutex; /**< FreeRTOS mutex. */
    BaseType_t recursive;     /**< Type; used for indicating if this is reentrant or normal. */
    bool created;
} PlatformMutex_t;

bool PlatformMutex_Create( PlatformMutex_t * pNewMutex,
                           bool recursive );
void PlatformMutex_Destroy( PlatformMutex_t * pMutex );
void PlatformMutex_Lock( PlatformMutex_t * pMutex );
bool PlatformMutex_TryLock( PlatformMutex_t * pMutex );
void PlatformMutex_Unlock( PlatformMutex_t * pMutex );
int32_t PlatformEventGroup_SetBitsFromISR( PlatformEventGroupHandle_t groupEvent,
                                           EventBits_t event,
                                           BaseType_t * pHigherPriorityTaskWoken );
void * safeMalloc( size_t xWantedSize );
void allocateSocket( void * pCellularHandle );
bool MockxQueueReceive( int32_t * queue,
                        void * data,
                        uint32_t time );
uint16_t MockPlatformEventGroup_Create();
uint16_t MockPlatformEventGroup_WaitBits();

QueueHandle_t xQueueCreate( int32_t uxQueueLength,
                            uint32_t uxItemSize );
uint16_t vQueueDelete( QueueHandle_t queue );
BaseType_t xQueueSend( QueueHandle_t queue,
                       void * data,
                       uint32_t time );

uint16_t PlatformEventGroup_ClearBits( PlatformEventGroupHandle_t xEventGroup,
                                       TickType_t uxBitsToClear );
uint16_t PlatformEventGroup_Delete( PlatformEventGroupHandle_t groupEvent );
uint16_t PlatformEventGroup_GetBits( PlatformEventGroupHandle_t groupEvent );

/*-----------------------------------------------------------*/

/**
 * @brief Cellular library platform memory allocation APIs.
 *
 * Cellular library use platform memory allocation APIs to allocate memory dynamically.
 * The FreeRTOS memory management document can be referenced for these APIs.
 * https://www.freertos.org/a00111.html
 *
 */

#define Platform_Malloc    safeMalloc
#define Platform_Free      free

#endif /* __CELLULAR_PLATFORM_H__ */
