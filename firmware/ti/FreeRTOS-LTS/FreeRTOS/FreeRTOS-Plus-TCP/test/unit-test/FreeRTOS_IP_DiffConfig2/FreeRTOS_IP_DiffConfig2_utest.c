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
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_IP_DiffConfig2_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_Routing.h"

#include "FreeRTOS_IP.h"

#include "FreeRTOS_IP_DiffConfig2_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer );
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

extern BaseType_t xIPTaskInitialised;
extern BaseType_t xNetworkDownEventPending;
extern BaseType_t xNetworkUp;
extern UBaseType_t uxQueueMinimumSpace;

/* ============================ Unity Fixtures ============================ */

/*! called before each test case */
void setUp( void )
{
    pxNetworkEndPoints = NULL;
    pxNetworkInterfaces = NULL;
    xNetworkDownEventPending = pdFALSE;
}

/*! called after each test case */
void tearDown( void )
{
}

/* ======================== Stub Callback Functions ========================= */

TaskHandle_t IPInItHappyPath_xTaskHandleToSet = ( TaskHandle_t ) 0xCDBA9087;
static BaseType_t StubxTaskCreate( TaskFunction_t pxTaskCode,
                                   const char * const pcName, /*lint !e971 Unqualified char types are allowed for strings and single characters only. */
                                   const configSTACK_DEPTH_TYPE uxStackDepth,
                                   void * const pvParameters,
                                   UBaseType_t uxPriority,
                                   TaskHandle_t * const pxCreatedTask,
                                   int cmock_num_calls )
{
    *pxCreatedTask = IPInItHappyPath_xTaskHandleToSet;
    return pdPASS;
}

/* ============================== Test Cases ============================== */

/**
 * @brief test_FreeRTOS_IPInit_HappyPathDHCP
 * To validate if FreeRTOS_IPInit() works with DHCP enabled.
 */
void test_FreeRTOS_IPInit_HappyPathDHCP( void )
{
    const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC0, 0xB0, 0xAB, 0x12 };
    const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC1, 0xB2, 0xAC, 0x13 };
    const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC2, 0xB3, 0xAC, 0x14 };
    const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ] = { 0xC3, 0xB4, 0xAD, 0x15 };
    const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF };
    BaseType_t xReturn;
    QueueHandle_t ulPointerToQueue = ( QueueHandle_t ) 0x1234ABCD;
    NetworkInterface_t * pxNetworkInterface;
    NetworkEndPoint_t xEndPoint = { 0 };

    /* Set the local IP to something other than 0. */
    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD;
    pxNetworkEndPoints = &xEndPoint;

    FreeRTOS_FillEndPoint_Ignore();
    FreeRTOS_FirstNetworkInterface_IgnoreAndReturn( pxNetworkInterface );
    pxFillInterfaceDescriptor_IgnoreAndReturn( pxNetworkInterface );

    vPreCheckConfigs_Expect();

    xQueueGenericCreate_ExpectAndReturn( ipconfigEVENT_QUEUE_LENGTH, sizeof( IPStackEvent_t ), 0U, ulPointerToQueue );

    #if ( configQUEUE_REGISTRY_SIZE > 0 )
        vQueueAddToRegistry_Expect( ulPointerToQueue, "NetEvnt" );
    #endif

    xNetworkBuffersInitialise_ExpectAndReturn( pdPASS );

    vNetworkSocketsInit_Expect();

    xTaskCreate_Stub( StubxTaskCreate );

    xReturn = FreeRTOS_IPInit( ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL( IPInItHappyPath_xTaskHandleToSet, FreeRTOS_GetIPTaskHandle() );
}
