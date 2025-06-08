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
#include "mock_IP_Timers_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_TCP_IP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_DNS_Callback.h"
#include "mock_FreeRTOS_ND.h"

#include "FreeRTOS_IP_Timers.h"

#include "FreeRTOS_IP_Timers_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

void prvIPTimerStart( IPTimer_t * pxTimer,
                      TickType_t xTime );
BaseType_t prvIPTimerCheck( IPTimer_t * pxTimer );

extern IPTimer_t xARPTimer;
#if ( ipconfigUSE_TCP != 0 )
    /** @brief TCP timer, to check for timeouts, resends. */
    extern IPTimer_t xTCPTimer;
#endif
#if ( ipconfigDNS_USE_CALLBACKS != 0 )
    /** @brief DNS timer, to check for timeouts when looking-up a domain. */
    extern IPTimer_t xDNSTimer;
#endif

extern IPTimer_t xARPResolutionTimer;
extern BaseType_t xAllNetworksUp;
extern IPTimer_t xNetworkTimer;

/* ============================ Unity Fixtures ============================ */

/*! called before each test case */
void setUp( void )
{
    static NetworkEndPoint_t xEndpoint;

    memset( &xEndpoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndpoint.bits.bIPv6 = pdFALSE_UNSIGNED;
    xEndpoint.bits.bWantDHCP = pdTRUE_UNSIGNED;

    pxNetworkEndPoints = &xEndpoint;
    pxNetworkInterfaces = NULL;

    xAllNetworksUp = pdFALSE;

    /* Reset all timers. */
    memset( &xARPTimer, 0, sizeof( IPTimer_t ) );
    memset( &xDNSTimer, 0, sizeof( IPTimer_t ) );
    memset( &xTCPTimer, 0, sizeof( IPTimer_t ) );
    memset( &xARPResolutionTimer, 0, sizeof( IPTimer_t ) );
    memset( &xNetworkTimer, 0, sizeof( IPTimer_t ) );
}

/*! called after each test case */
void tearDown( void )
{
}

/* ============================== Test Cases ============================== */

/**
 * @brief test_xCalculateSleepTime_AllTimersInactive
 * To validate if xCalculateSleepTime() returns ipconfigMAX_IP_TASK_SLEEP_TIME
 * when all timers are inactive.
 */
void test_xCalculateSleepTime_AllTimersInactive( void )
{
    TickType_t uxTicks;

    xARPTimer.bActive = pdFALSE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME, uxTicks );
}

/**
 * @brief test_xCalculateSleepTime_AllTimersActive_AllTimesGreater
 * To validate if xCalculateSleepTime() returns ipconfigMAX_IP_TASK_SLEEP_TIME
 * when remaining time of all timers are greater than or equal to ipconfigMAX_IP_TASK_SLEEP_TIME.
 */
void test_xCalculateSleepTime_AllTimersActive_AllTimesGreater( void )
{
    TickType_t uxTicks;

    xARPTimer.bActive = pdTRUE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdTRUE;

    xARPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    pxNetworkEndPoints->xDHCP_RATimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME + 1;
    xTCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME + 2;
    xDNSTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME + 3;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME, uxTicks );
}

/**
 * @brief test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptARP
 * To validate if xCalculateSleepTime() returns the shortest remaining time
 * of all active timers. In this case, ARP timer has the shortest remaining time.
 */
void test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptARP( void )
{
    TickType_t uxTicks;

    xARPTimer.bActive = pdTRUE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdTRUE;

    xARPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME - 10;
    pxNetworkEndPoints->xDHCP_RATimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xTCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xDNSTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME - 10, uxTicks );
}

/**
 * @brief test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptDHCP
 * To validate if xCalculateSleepTime() returns the shortest remaining time
 * of all active timers. In this case, DHCP timer has the shortest remaining time.
 */
void test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptDHCP( void )
{
    TickType_t uxTicks;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( pxEndpoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkEndPoints = pxEndpoint;

    xARPTimer.bActive = pdTRUE;
    pxEndpoint->xDHCP_RATimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdTRUE;

    xARPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    pxEndpoint->xDHCP_RATimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME - 10;
    xTCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xDNSTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME - 10, uxTicks );
}

/**
 * @brief test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptTCP
 * To validate if xCalculateSleepTime() returns the shortest remaining time
 * of all active timers. In this case, TCP timer has the shortest remaining time.
 */
void test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptTCP( void )
{
    TickType_t uxTicks;

    xARPTimer.bActive = pdTRUE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdTRUE;

    xARPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    pxNetworkEndPoints->xDHCP_RATimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xTCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME - 10;
    xDNSTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME - 10, uxTicks );
}

/**
 * @brief test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptDNS
 * To validate if xCalculateSleepTime() returns the shortest remaining time
 * of all active timers. In this case, DNS timer has the shortest remaining time.
 */
void test_xCalculateSleepTime_AllTimersActive_AllTimesGreaterExceptDNS( void )
{
    TickType_t uxTicks;

    xARPTimer.bActive = pdTRUE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdTRUE;

    xARPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    pxNetworkEndPoints->xDHCP_RATimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xTCPTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME;
    xDNSTimer.ulRemainingTime = ipconfigMAX_IP_TASK_SLEEP_TIME - 10;

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( ipconfigMAX_IP_TASK_SLEEP_TIME - 10, uxTicks );
}

/**
 * @brief test_xCalculateSleepTime_MultipleDHCPTimers
 * To validate if xCalculateSleepTime() returns the shortest remaining time
 * of all active DHCP timers.
 */
void test_xCalculateSleepTime_MultipleDHCPTimers( void )
{
    TickType_t uxTicks;
    NetworkEndPoint_t xEndpoints[ 3 ];

    /* First endpoint is inactive but has shortest remaining time. */
    memset( &xEndpoints[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndpoints[ 0 ].xDHCP_RATimer.bActive = pdFALSE;
    xEndpoints[ 0 ].xDHCP_RATimer.ulRemainingTime = 1U;

    /* Second endpoint is active but has shorter remaining time than third endpoint. */
    memset( &xEndpoints[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndpoints[ 1 ].xDHCP_RATimer.bActive = pdTRUE;
    xEndpoints[ 1 ].xDHCP_RATimer.ulRemainingTime = 2U;

    /* Third endpoint is active and has longest remaining time. */
    memset( &xEndpoints[ 2 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndpoints[ 2 ].xDHCP_RATimer.bActive = pdTRUE;
    xEndpoints[ 2 ].xDHCP_RATimer.ulRemainingTime = 3U;

    /* Append these endpoints to global list. */
    pxNetworkEndPoints = &xEndpoints[ 0 ];
    pxNetworkEndPoints->pxNext = &xEndpoints[ 1 ];
    pxNetworkEndPoints->pxNext->pxNext = &xEndpoints[ 2 ];

    uxTicks = xCalculateSleepTime();

    TEST_ASSERT_EQUAL( 2U, uxTicks );
}

/**
 * @brief test_vCheckNetworkTimers_AllTimersDisabled
 * To validate if vCheckNetworkTimers() runs normally when all timers are inactive.
 */
void test_vCheckNetworkTimers_AllTimersDisabled( void )
{
    xARPTimer.bActive = pdFALSE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

/**
 * @brief test_vCheckNetworkTimers_ARPTimerActiveAndExpired
 * To validate if vCheckNetworkTimers() handles ARP timer expired event as expected.
 */
void test_vCheckNetworkTimers_ARPTimerActiveAndExpired( void )
{
    xARPTimer.bActive = pdTRUE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;

    xARPTimer.bExpired = pdTRUE;

    vTaskSetTimeOutState_Expect( &( xARPTimer.xTimeOut ) );

    xSendEventToIPTask_ExpectAndReturn( eARPTimerEvent, pdTRUE );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

/**
 * @brief test_vCheckNetworkTimers_ARPResolutionTimerActiveAndExpiredNullBuffer
 * To validate if vCheckNetworkTimers() handles ARP resolution timer expired event as expected.
 * And there is no buffer waiting for ARP reply.
 */
void test_vCheckNetworkTimers_ARPResolutionTimerActiveAndExpiredNullBuffer( void )
{
    xARPTimer.bActive = pdFALSE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdTRUE;

    xARPResolutionTimer.bExpired = pdTRUE;

    pxARPWaitingNetworkBuffer = NULL;

    vTaskSetTimeOutState_Expect( &( xARPResolutionTimer.xTimeOut ) );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();

    TEST_ASSERT_EQUAL( pdTRUE, xARPResolutionTimer.bExpired );
}

/**
 * @brief test_vCheckNetworkTimers_ARPResolutionTimerActiveAndExpired
 * To validate if vCheckNetworkTimers() handles ARP resolution timer expired event as expected.
 * And there is a buffer waiting for ARP reply.
 */
void test_vCheckNetworkTimers_ARPResolutionTimerActiveAndExpired( void )
{
    xARPTimer.bActive = pdFALSE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdTRUE;

    xARPResolutionTimer.bExpired = pdTRUE;

    pxARPWaitingNetworkBuffer = ( NetworkBufferDescriptor_t * ) 0x1234ABCD;

    vTaskSetTimeOutState_Expect( &( xARPResolutionTimer.xTimeOut ) );

    vReleaseNetworkBufferAndDescriptor_Expect( pxARPWaitingNetworkBuffer );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();

    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xARPResolutionTimer.bActive );
    TEST_ASSERT_EQUAL_PTR( NULL, pxARPWaitingNetworkBuffer );
}

/**
 * @brief test_vCheckNetworkTimers_DHCPTimerActiveAndExpired
 * To validate if vCheckNetworkTimers() handles DHCP timer expired event as expected.
 */
void test_vCheckNetworkTimers_DHCPTimerActiveAndExpired( void )
{
    xARPTimer.bActive = pdFALSE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdFALSE;

    pxNetworkEndPoints->xDHCP_RATimer.bExpired = pdTRUE;

    vTaskSetTimeOutState_Expect( &( pxNetworkEndPoints->xDHCP_RATimer.xTimeOut ) );

    xSendDHCPEvent_ExpectAnyArgsAndReturn( pdTRUE );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

/**
 * @brief test_vCheckNetworkTimers_DHCPv6TimerActiveAndExpired
 * To validate if vCheckNetworkTimers() handles DHCPv6 timer expired event as expected.
 */
void test_vCheckNetworkTimers_DHCPv6TimerActiveAndExpired( void )
{
    pxNetworkEndPoints->bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdTRUE;
    pxNetworkEndPoints->xDHCP_RATimer.bExpired = pdTRUE;

    vTaskSetTimeOutState_Expect( &( pxNetworkEndPoints->xDHCP_RATimer.xTimeOut ) );

    xSendDHCPEvent_ExpectAnyArgsAndReturn( pdTRUE );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

/**
 * @brief test_vCheckNetworkTimers_RATimerActiveAndExpired
 * To validate if vCheckNetworkTimers() handles RA timer expired event as expected.
 */
void test_vCheckNetworkTimers_RATimerActiveAndExpired( void )
{
    xARPTimer.bActive = pdFALSE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdTRUE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdFALSE;

    pxNetworkEndPoints->xDHCP_RATimer.bExpired = pdTRUE;
    pxNetworkEndPoints->bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints->bits.bWantDHCP = pdFALSE;
    pxNetworkEndPoints->bits.bWantRA = pdTRUE;

    vTaskSetTimeOutState_Expect( &( pxNetworkEndPoints->xDHCP_RATimer.xTimeOut ) );

    vRAProcess_Expect( pdFALSE, pxNetworkEndPoints );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

/**
 * @brief test_vCheckNetworkTimers_DNSTimerActiveAndExpired
 * To validate if vCheckNetworkTimers() handles DNS timer expired event as expected.
 */
void test_vCheckNetworkTimers_DNSTimerActiveAndExpired( void )
{
    NetworkEndPoint_t xEndPoint = { 0 };

    xARPTimer.bActive = pdFALSE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdTRUE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdFALSE;

    xDNSTimer.bExpired = pdTRUE;

    xEndPoint.pxNext = NULL;
    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;
    xEndPoint.xDHCP_RATimer.bActive = pdFALSE;
    xEndPoint.xDHCP_RATimer.bExpired = pdTRUE;
    pxNetworkEndPoints = &xEndPoint;

    vTaskSetTimeOutState_Expect( &( pxNetworkEndPoints->xDHCP_RATimer.xTimeOut ) );

    vDNSCheckCallBack_Expect( NULL );

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

/**
 * @brief test_vCheckNetworkTimers_NetworkTimerActiveAndExpired
 * To validate if vCheckNetworkTimers() handles network timer expired event as expected.
 */
void test_vCheckNetworkTimers_NetworkTimerActiveAndExpired( void )
{
    NetworkInterface_t xInterface[ 2 ];

    /* First interface is up, but second one is down. */
    memset( &xInterface[ 0 ], 0, sizeof( NetworkInterface_t ) );
    xInterface[ 0 ].bits.bInterfaceUp = pdTRUE_UNSIGNED;
    memset( &xInterface[ 1 ], 0, sizeof( NetworkInterface_t ) );
    xInterface[ 1 ].bits.bInterfaceUp = pdFALSE_UNSIGNED;

    /* Append the interfaces to the global list. */
    pxNetworkInterfaces = &xInterface[ 0 ];
    pxNetworkInterfaces->pxNext = &xInterface[ 1 ];

    xNetworkTimer.bActive = pdTRUE;
    xNetworkTimer.bExpired = pdTRUE;

    xAllNetworksUp = pdFALSE;

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vTaskSetTimeOutState_Expect( &( xNetworkTimer.xTimeOut ) );

    FreeRTOS_NetworkDown_Expect( &xInterface[ 1 ] );

    vCheckNetworkTimers();
}

/**
 * @brief test_vCheckNetworkTimers_NetworkTimerActiveAndExpired
 * To validate if vCheckNetworkTimers() handles network timer expired event as expected.
 */
void test_vCheckNetworkTimers_NetworkInterfacesAllUp( void )
{
    NetworkInterface_t xInterface[ 2 ];

    /* First interface is up, but second one is down. */
    memset( &xInterface[ 0 ], 0, sizeof( NetworkInterface_t ) );
    xInterface[ 0 ].bits.bInterfaceUp = pdTRUE_UNSIGNED;
    memset( &xInterface[ 1 ], 0, sizeof( NetworkInterface_t ) );
    xInterface[ 1 ].bits.bInterfaceUp = pdTRUE_UNSIGNED;

    /* Append the interfaces to the global list. */
    pxNetworkInterfaces = &xInterface[ 0 ];
    pxNetworkInterfaces->pxNext = &xInterface[ 1 ];

    xNetworkTimer.bActive = pdTRUE;
    xNetworkTimer.bExpired = pdTRUE;

    xAllNetworksUp = pdFALSE;

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vTaskSetTimeOutState_Expect( &( xNetworkTimer.xTimeOut ) );

    vCheckNetworkTimers();

    TEST_ASSERT_EQUAL( pdTRUE, xAllNetworksUp );
}

/**
 * @brief test_vCheckNetworkTimers_NetworkInterfacesAlreadyUp
 * To validate if vCheckNetworkTimers() skip handling network timer when all interfaces are up.
 */
void test_vCheckNetworkTimers_NetworkInterfacesAlreadyUp( void )
{
    NetworkInterface_t xInterface[ 2 ];

    /* First interface is up, but second one is down. */
    memset( &xInterface[ 0 ], 0, sizeof( NetworkInterface_t ) );
    xInterface[ 0 ].bits.bInterfaceUp = pdTRUE_UNSIGNED;
    memset( &xInterface[ 1 ], 0, sizeof( NetworkInterface_t ) );
    xInterface[ 1 ].bits.bInterfaceUp = pdTRUE_UNSIGNED;

    /* Append the interfaces to the global list. */
    pxNetworkInterfaces = &xInterface[ 0 ];
    pxNetworkInterfaces->pxNext = &xInterface[ 1 ];

    xNetworkTimer.bActive = pdTRUE;
    xNetworkTimer.bExpired = pdTRUE;

    xAllNetworksUp = pdTRUE;

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

/**
 * @brief test_vCheckNetworkTimers_AllTimersInactivePendingMessages
 * To validate if vCheckNetworkTimers() handles the flow that all timers are inactive,
 * and there are messages pending in the queue.
 */
void test_vCheckNetworkTimers_AllTimersInactivePendingMessages( void )
{
    xARPTimer.bActive = pdFALSE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdFALSE;

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdTRUE );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();
}

/**
 * @brief test_vCheckNetworkTimers_AllTimersInactivePendingMessages
 * To validate if vCheckNetworkTimers() handles the flow that all timers are inactive,
 * and there is no messages pending in the queue.
 */
void test_vCheckNetworkTimers_AllTimersInactive_2( void )
{
    xARPTimer.bActive = pdFALSE;
    pxNetworkEndPoints->xDHCP_RATimer.bActive = pdFALSE;
    xDNSTimer.bActive = pdFALSE;
    xTCPTimer.bActive = pdFALSE;
    xARPResolutionTimer.bActive = pdFALSE;

    uxQueueMessagesWaiting_ExpectAnyArgsAndReturn( pdFALSE );

    xTCPTimerCheck_ExpectAndReturn( pdTRUE, 0x123 );

    vTaskSetTimeOutState_Expect( &( xTCPTimer.xTimeOut ) );

    vSocketCloseNextTime_Expect( NULL );

    vSocketListenNextTime_Expect( NULL );

    vCheckNetworkTimers();

    TEST_ASSERT_EQUAL( 0x123, xTCPTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xTCPTimer.bExpired );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xTCPTimer.bActive );
}

/**
 * @brief test_prvIPTimerStart_NonZeroTime
 * To validate if prvIPTimerStart() activate the timer with non zero time.
 */
void test_prvIPTimerStart_NonZeroTime( void )
{
    IPTimer_t xTimer;
    TickType_t xTime = 0xABCD;

    vTaskSetTimeOutState_Expect( &xTimer.xTimeOut );

    prvIPTimerStart( &xTimer, xTime );

    TEST_ASSERT_EQUAL( xTime, xTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xTimer.bExpired );
}

/**
 * @brief test_prvIPTimerStart_ZeroTime
 * To validate if prvIPTimerStart() activate the timer with zero time.
 * Timer must be expired after calling.
 */
void test_prvIPTimerStart_ZeroTime( void )
{
    IPTimer_t xTimer;
    TickType_t xTime = 0x00;

    vTaskSetTimeOutState_Expect( &xTimer.xTimeOut );

    prvIPTimerStart( &xTimer, xTime );

    TEST_ASSERT_EQUAL( xTime, xTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xTimer.bActive );
    TEST_ASSERT_EQUAL( pdTRUE, xTimer.bExpired );
}

/**
 * @brief test_vIPTimerStartARPResolution
 * To validate if vIPTimerStartARPResolution() activate the ARP resolution timer
 * with zero time. Timer must be expired after calling.
 */
void test_vIPTimerStartARPResolution( void )
{
    TickType_t xTime = 0x00;

    vTaskSetTimeOutState_Expect( &xARPResolutionTimer.xTimeOut );

    vIPTimerStartARPResolution( xTime );

    TEST_ASSERT_EQUAL( xTime, xARPResolutionTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xARPResolutionTimer.bActive );
    TEST_ASSERT_EQUAL( pdTRUE, xARPResolutionTimer.bExpired );
}

/**
 * @brief test_vIPTimerStartARPResolution
 * To validate if vTCPTimerReload() activate the TCP timer with non-zero time.
 */
void test_vTCPTimerReload( void )
{
    TickType_t xTime = 0x12A;

    vTaskSetTimeOutState_Expect( &xTCPTimer.xTimeOut );

    vTCPTimerReload( xTime );

    TEST_ASSERT_EQUAL( 0x12A, xTCPTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( xTime, xTCPTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xTCPTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xTCPTimer.bExpired );
}

/**
 * @brief test_vARPTimerReload
 * To validate if vARPTimerReload() activate the ARP timer with non-zero time.
 */
void test_vARPTimerReload( void )
{
    TickType_t xTime = 0x12A;

    vTaskSetTimeOutState_Expect( &xARPTimer.xTimeOut );

    vARPTimerReload( xTime );

    TEST_ASSERT_EQUAL( 0x12A, xARPTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( xTime, xARPTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xARPTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xARPTimer.bExpired );
}

/**
 * @brief test_vDHCP_RATimerReload
 * To validate if vTCPTimerReload() activate the DHCP timer with non-zero time.
 */
void test_vDHCP_RATimerReload( void )
{
    TickType_t xTime = 0x12A;
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.pxNext = NULL;
    xEndPoint.bits.bWantDHCP = pdTRUE_UNSIGNED;
    xEndPoint.xDHCP_RATimer.bActive = pdTRUE;
    xEndPoint.xDHCP_RATimer.bExpired = pdTRUE;
    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;

    vTaskSetTimeOutState_Expect( &( xEndPoint.xDHCP_RATimer.xTimeOut ) );

    vDHCP_RATimerReload( &xEndPoint, xTime );

    TEST_ASSERT_EQUAL( 0x12A, xEndPoint.xDHCP_RATimer.ulReloadTime );
    TEST_ASSERT_EQUAL( xTime, xEndPoint.xDHCP_RATimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xEndPoint.xDHCP_RATimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xEndPoint.xDHCP_RATimer.bExpired );
}

/**
 * @brief test_vDNSTimerReload
 * To validate if vDNSTimerReload() activate the DNS timer with non-zero time.
 */
void test_vDNSTimerReload( void )
{
    TickType_t xTime = 0x12A;

    vTaskSetTimeOutState_Expect( &xDNSTimer.xTimeOut );

    vDNSTimerReload( xTime );

    TEST_ASSERT_EQUAL( 0x12A, xDNSTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( xTime, xDNSTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xDNSTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xDNSTimer.bExpired );
}

/**
 * @brief test_vNetworkTimerReload
 * To validate if vNetworkTimerReload() activate the network timer with non-zero time.
 */
void test_vNetworkTimerReload( void )
{
    TickType_t xTime = 0x12A;

    vTaskSetTimeOutState_Expect( &xNetworkTimer.xTimeOut );

    vNetworkTimerReload( xTime );

    TEST_ASSERT_EQUAL( 0x12A, xNetworkTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( xTime, xNetworkTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xNetworkTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xNetworkTimer.bExpired );
}

/**
 * @brief test_prvIPTimerCheck_TimerDisabled
 * To validate if prvIPTimerCheck() returns pdFALSE when timer is inactive.
 */
void test_prvIPTimerCheck_TimerDisabled( void )
{
    BaseType_t xResult;
    IPTimer_t xTimer;

    xTimer.bActive = pdFALSE;

    xResult = prvIPTimerCheck( &xTimer );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/**
 * @brief test_prvIPTimerCheck_TimerDisabled
 * To validate if prvIPTimerCheck() returns pdTRUE when timer is expired.
 */
void test_prvIPTimerCheck_TimerExpired( void )
{
    BaseType_t xResult;
    IPTimer_t xTimer;

    xTimer.bActive = pdTRUE;
    xTimer.bExpired = pdTRUE;
    xTimer.ulReloadTime = 0xAA;

    vTaskSetTimeOutState_Expect( &xTimer.xTimeOut );

    xResult = prvIPTimerCheck( &xTimer );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    TEST_ASSERT_EQUAL( 0xAA, xTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( 0xAA, xTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xTimer.bExpired );
}

/**
 * @brief test_prvIPTimerCheck_TimerNotExpired
 * To validate if prvIPTimerCheck() returns pdFALSE when timer is not expired yet.
 */
void test_prvIPTimerCheck_TimerNotExpired( void )
{
    BaseType_t xResult;
    IPTimer_t xTimer;

    xTimer.bActive = pdTRUE;
    xTimer.bExpired = pdFALSE;
    xTimer.ulReloadTime = 0xAA;

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xResult = prvIPTimerCheck( &xTimer );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/**
 * @brief test_prvIPTimerCheck_TimerExpiredInxTaskCheckForTimeOut
 * To validate if prvIPTimerCheck() returns pdTRUE when timer expired in xTaskCheckForTimeOut().
 */
void test_prvIPTimerCheck_TimerExpiredInxTaskCheckForTimeOut( void )
{
    BaseType_t xResult;
    IPTimer_t xTimer;

    xTimer.bActive = pdTRUE;
    xTimer.bExpired = pdFALSE;
    xTimer.ulReloadTime = 0xAA;

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    vTaskSetTimeOutState_Expect( &xTimer.xTimeOut );

    xResult = prvIPTimerCheck( &xTimer );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    TEST_ASSERT_EQUAL( 0xAA, xTimer.ulReloadTime );
    TEST_ASSERT_EQUAL( 0xAA, xTimer.ulRemainingTime );
    TEST_ASSERT_EQUAL( pdTRUE, xTimer.bActive );
    TEST_ASSERT_EQUAL( pdFALSE, xTimer.bExpired );
}

/**
 * @brief test_vIPSetTCPTimerExpiredState_False
 * To validate if vIPSetTCPTimerExpiredState() sets TCP timer to non expired state.
 */
void test_vIPSetTCPTimerExpiredState_False( void )
{
    BaseType_t xExpiredState = pdFALSE;

    vIPSetTCPTimerExpiredState( xExpiredState );

    TEST_ASSERT_EQUAL( xExpiredState, xTCPTimer.bExpired );
}

/**
 * @brief test_vIPSetTCPTimerExpiredState_False
 * To validate if vIPSetTCPTimerExpiredState() sets TCP timer to expired state.
 */
void test_vIPSetTCPTimerExpiredState_True( void )
{
    BaseType_t xExpiredState = pdTRUE;

    vIPSetTCPTimerExpiredState( xExpiredState );

    TEST_ASSERT_EQUAL( xExpiredState, xTCPTimer.bExpired );
}

/**
 * @brief test_vIPSetARPTimerEnableState_False
 * To validate if vIPSetARPTimerEnableState() sets ARP timer to non expired state.
 */
void test_vIPSetARPTimerEnableState_False( void )
{
    BaseType_t xEnableState = pdFALSE;

    vIPSetARPTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xARPTimer.bActive );
}

/**
 * @brief test_vIPSetARPTimerEnableState_True
 * To validate if vIPSetARPTimerEnableState() sets ARP timer to expired state.
 */
void test_vIPSetARPTimerEnableState_True( void )
{
    BaseType_t xEnableState = pdTRUE;

    vIPSetARPTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xARPTimer.bActive );
}

/**
 * @brief test_vIPSetARPResolutionTimerEnableState_False
 * To validate if vIPSetARPResolutionTimerEnableState() sets ARP resolution timer
 * to non expired state.
 */
void test_vIPSetARPResolutionTimerEnableState_False( void )
{
    BaseType_t xEnableState = pdFALSE;

    vIPSetARPResolutionTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xARPResolutionTimer.bActive );
}

/**
 * @brief test_vIPSetARPResolutionTimerEnableState_True
 * To validate if vIPSetARPResolutionTimerEnableState() sets ARP resolution timer
 * to expired state.
 */
void test_vIPSetARPResolutionTimerEnableState_True( void )
{
    BaseType_t xEnableState = pdTRUE;

    vIPSetARPResolutionTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xARPResolutionTimer.bActive );
}

/**
 * @brief test_vIPSetDHCP_RATimerEnableState_False
 * To validate if vIPSetDHCP_RATimerEnableState() sets DHCP timer
 * to non expired state.
 */
void test_vIPSetDHCP_RATimerEnableState_False( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 };
    BaseType_t xEnableState = pdFALSE;

    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;
    vIPSetDHCP_RATimerEnableState( &xEndPoint, xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, pxNetworkEndPoints->xDHCP_RATimer.bActive );
}

/**
 * @brief test_vIPSetDHCP_RATimerEnableState_False
 * To validate if vIPSetDHCP_RATimerEnableState() sets DHCP timer
 * to expired state.
 */
void test_vIPSetDHCP_RATimerEnableState_True( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 };
    BaseType_t xEnableState = pdTRUE;

    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;
    vIPSetDHCP_RATimerEnableState( &xEndPoint, xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xEndPoint.xDHCP_RATimer.bActive );
}

/**
 * @brief test_vIPSetDNSTimerEnableState_False
 * To validate if vIPSetDNSTimerEnableState() sets DNS timer
 * to non expired state.
 */
void test_vIPSetDNSTimerEnableState_False( void )
{
    BaseType_t xEnableState = pdFALSE;

    vIPSetDNSTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xDNSTimer.bActive );
}

/**
 * @brief test_vIPSetDNSTimerEnableState_True
 * To validate if vIPSetDNSTimerEnableState() sets DNS timer
 * to expired state.
 */
void test_vIPSetDNSTimerEnableState_True( void )
{
    BaseType_t xEnableState = pdTRUE;

    vIPSetDNSTimerEnableState( xEnableState );

    TEST_ASSERT_EQUAL( xEnableState, xDNSTimer.bActive );
}
