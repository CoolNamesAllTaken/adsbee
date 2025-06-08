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

/**
 * @file cellular_platform.c
 * @brief cbmc wrapper functions in cellular_platform.h.
 */

/* Include paths for public enums, structures, and macros. */
#include "cellular_platform.h"

void MockPlatformMutex_Unlock( PlatformMutex_t * pMutex )
{
    ( void ) pMutex;
}

void MockPlatformMutex_Lock( PlatformMutex_t * pMutex )
{
    ( void ) pMutex;
}

void MockPlatformMutex_Destroy( PlatformMutex_t * pMutex )
{
    pMutex->created = false;
}

bool MockPlatformMutex_Create( PlatformMutex_t * pNewMutex,
                               bool recursive )
{
    ( void ) recursive;
    pNewMutex->created = true;
    return true;
}

int32_t MockPlatformEventGroup_SetBitsFromISR( PlatformEventGroupHandle_t groupEvent,
                                               EventBits_t event,
                                               BaseType_t * pHigherPriorityTaskWoken )
{
    bool flag = nondet_bool();
    int32_t ret;

    ( void ) groupEvent;
    ( void ) event;
    ( void ) pHigherPriorityTaskWoken;

    if( flag )
    {
        if( nondet_bool() )
        {
            *pHigherPriorityTaskWoken = pdTRUE;
        }
        else
        {
            *pHigherPriorityTaskWoken = pdFALSE;
        }

        ret = pdPASS;
    }
    else
    {
        ret = pdFALSE;
    }

    return ret;
}

/* ========================================================================== */

QueueHandle_t MockxQueueCreate( int32_t uxQueueLength,
                                uint32_t uxItemSize )
{
    ( void ) uxQueueLength;
    ( void ) uxItemSize;

    if( nondet_bool() )
    {
        QueueHandle_t test = malloc( sizeof( struct QueueDefinition ) );
        return test;
    }

    return NULL;
}


uint16_t MockvQueueDelete( QueueHandle_t queue )
{
    free( queue );
    queue = 0;
    return 1;
}

BaseType_t MockxQueueSend( QueueHandle_t queue,
                           void * data,
                           uint32_t time )
{
    ( void ) queue;
    ( void ) time;

    if( nondet_bool() )
    {
        return true;
    }
    else
    {
        return false;
    }
}

/* ========================================================================== */


uint16_t MockPlatformEventGroup_ClearBits( PlatformEventGroupHandle_t xEventGroup,
                                           TickType_t uxBitsToClear )
{
    ( void ) xEventGroup;
    ( void ) uxBitsToClear;
    return 0;
}

bool MockPlatform_CreateDetachedThread( void ( * threadRoutine )( void * pArgument ),
                                        void * pArgument,
                                        size_t priority,
                                        size_t stackSize )
{
    ( void ) pArgument;
    ( void ) priority;
    ( void ) stackSize;

    bool threadReturn = nondet_bool();

    if( threadReturn )
    {
        threadRoutine( pArgument );
    }

    return threadReturn;
}

uint16_t MockPlatformEventGroup_Delete( PlatformEventGroupHandle_t groupEvent )
{
    ( void ) groupEvent;
    return 0U;
}

uint16_t MockPlatformEventGroup_GetBits( PlatformEventGroupHandle_t groupEvent )
{
    ( void ) groupEvent;

    uint16_t ret = nondet_unsigned_int();

    return ret;
}
