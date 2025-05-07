/*
 * FreeRTOS+TCP V4.2.2
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */


/* Include Unity header */
#include <unity.h>

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* =========================== EXTERN VARIABLES =========================== */

QueueHandle_t xNetworkEventQueue = NULL;

FreeRTOS_Socket_t xGlobalSocket;

UBaseType_t uxGlobalCallbackCount;

uint32_t xRandomNumberToReturn;
BaseType_t xRNGStatus;

BaseType_t xLocalReceiveCallback_Return;
uint8_t xLocalReceiveCallback_Called = 0;

BaseType_t xTCPWindowLoggingLevel = 0;

/* ======================== Stub Callback Functions ========================= */

EventBits_t xStubForEventGroupWaitBits( EventGroupHandle_t xEventGroup,
                                        const EventBits_t uxBitsToWaitFor,
                                        const BaseType_t xClearOnExit,
                                        const BaseType_t xWaitForAllBits,
                                        TickType_t xTicksToWait,
                                        int CallbackCount )
{
    xGlobalSocket.u.xTCP.eTCPState = eESTABLISHED;
}

void vStub_vTaskSetTimeOutState_socketError( TimeOut_t * const pxTimeOut,
                                             int numCalls )
{
    xGlobalSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
}

static void vUserCallbackLocal( FreeRTOS_Socket_t * xSocket )
{
    uxGlobalCallbackCount++;
}

static BaseType_t xStubApplicationGetRandomNumber( uint32_t * xRndNumber,
                                                   int count )
{
    ( void ) count;
    *xRndNumber = xRandomNumberToReturn;
    return xRNGStatus;
}

static void vpxListFindListItemWithValue_NotFound( void )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );
}

static void vpxListFindListItemWithValue_Found( const List_t * pxList,
                                                TickType_t xWantedItemValue,
                                                const ListItem_t * pxReturn )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( pxList->xListEnd ), ( ListItem_t * ) pxReturn );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( pxReturn, xWantedItemValue );
}

static BaseType_t xLocalReceiveCallback( Socket_t xSocket,
                                         void * pvData,
                                         size_t xLength )
{
    xLocalReceiveCallback_Called++;
    return xLocalReceiveCallback_Return;
}

void vPortEnterCritical( void )
{
}
void vPortExitCritical( void )
{
}
