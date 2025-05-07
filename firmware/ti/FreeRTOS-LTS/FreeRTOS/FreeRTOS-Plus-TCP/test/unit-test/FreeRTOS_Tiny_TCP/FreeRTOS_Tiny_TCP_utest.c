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
#include <stdio.h>


#include "FreeRTOS.h"

#include "catch_assert.h"

#include "FreeRTOSConfig.h"
#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_TCP_WIN.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_task.h"

extern BaseType_t xTCPWindowLoggingLevel;

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
}

/**
 * @brief calls at the end of each test case
 */
void tearDown( void )
{
}

void test_test( void )
{
    TEST_PASS();
}

void test_lTCPWindowRxCheck_diff_seq_numbers( void )
{
    int32_t lReturn;
    uint32_t ulSequenceNumber = 23;
    uint32_t ulLength = 100;
    uint32_t ulSpace = 200;
    TCPWindow_t xWindow;
    uint32_t ulSkipCount;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber + 1;

    lReturn = lTCPWindowRxCheck( &xWindow, ulSequenceNumber,
                                 ulLength, ulSpace,
                                 &ulSkipCount );
    TEST_ASSERT_EQUAL( -1, lReturn );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_space_lt_length( void )
{
    int32_t lReturn;
    uint32_t ulSequenceNumber = 23;
    uint32_t ulLength = 300;
    uint32_t ulSpace = 200;
    TCPWindow_t xWindow;
    uint32_t ulSkipCount;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;

    lReturn = lTCPWindowRxCheck( &xWindow, ulSequenceNumber,
                                 ulLength, ulSpace,
                                 &ulSkipCount );
    TEST_ASSERT_EQUAL( -1, lReturn );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_seq_num_eq( void )
{
    int32_t lReturn;
    uint32_t ulSequenceNumber = 23;
    uint32_t ulLength = 300;
    uint32_t ulSpace = 400;
    TCPWindow_t xWindow;
    uint32_t ulSkipCount;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;

    lReturn = lTCPWindowRxCheck( &xWindow, ulSequenceNumber,
                                 ulLength, ulSpace,
                                 &ulSkipCount );
    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowTxAdd_length_gt_zero( void )
{
    int32_t lResult;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };
    uint32_t ulLength = 200;
    int32_t lPosition = 2;
    int32_t lMax = 300;

    xSegment.lDataLength = 4;

    xWindow.xTxSegment = xSegment;

    lResult = lTCPWindowTxAdd( &xWindow,
                               ulLength,
                               lPosition,
                               lMax );

    TEST_ASSERT_EQUAL( 0, lResult );
}

void test_lTCPWindowTxAdd_length_eq_zero( void )
{
    int32_t lResult;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };
    uint32_t ulLength = 200;
    int32_t lPosition = 2;
    int32_t lMax = 300;

    xSegment.lDataLength = 0;
    xWindow.xTxSegment = xSegment;

    /* ->vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 0 );

    lResult = lTCPWindowTxAdd( &xWindow,
                               ulLength,
                               lPosition,
                               lMax );

    TEST_ASSERT_EQUAL( 0, lResult );
}

void test_lTCPWindowTxAdd_length_eq_zero_with_logging( void )
{
    int32_t lResult;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };
    uint32_t ulLength = 200;
    int32_t lPosition = 2;
    int32_t lMax = 300;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    xSegment.lDataLength = 0;
    xWindow.xTxSegment = xSegment;

    xTCPWindowLoggingLevel = 2;

    /* ->vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 0 );

    lResult = lTCPWindowTxAdd( &xWindow,
                               ulLength,
                               lPosition,
                               lMax );

    xTCPWindowLoggingLevel = xBackup;

    TEST_ASSERT_EQUAL( 0, lResult );
}

void test_lTCPWindowTxAdd_length_gt_maxlen( void )
{
    int32_t lResult;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };
    uint32_t ulLength = 200;
    int32_t lPosition = 2;
    int32_t lMax = 300;

    xSegment.lDataLength = 0;
    xSegment.lMaxLength = 300;
    xWindow.xTxSegment = xSegment;

    /* ->vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 0 );

    lResult = lTCPWindowTxAdd( &xWindow,
                               ulLength,
                               lPosition,
                               lMax );

    TEST_ASSERT_EQUAL( 200, lResult );
}

void test_lTCPWindowTxAdd_length_gt_maxlen_with_logging( void )
{
    int32_t lResult;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };
    uint32_t ulLength = 200;
    int32_t lPosition = 2;
    int32_t lMax = 300;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    xSegment.lDataLength = 0;
    xSegment.lMaxLength = 300;
    xWindow.xTxSegment = xSegment;

    xTCPWindowLoggingLevel = 2;

    /* ->vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 0 );

    lResult = lTCPWindowTxAdd( &xWindow,
                               ulLength,
                               lPosition,
                               lMax );

    xTCPWindowLoggingLevel = xBackup;

    TEST_ASSERT_EQUAL( 200, lResult );
}

void test_ulTCPWindowTxGet_length_eq_zero( void )
{
    uint32_t ulLength;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };
    uint32_t ulWindowSize = 20;
    int32_t plPosition = 3;

    xSegment.lDataLength = 0;
    xWindow.xTxSegment = xSegment;

    ulLength = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &plPosition );
    TEST_ASSERT_EQUAL( 0, ulLength );
}

void test_ulTCPWindowTxGet_length_ne_zero_bit_outstanding_eq_false( void )
{
    uint32_t ulLength;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };
    uint32_t ulWindowSize = 20;
    int32_t plPosition = 3;

    xSegment.lDataLength = 3;
    xSegment.u.bits.bOutstanding = pdFALSE_UNSIGNED;
    xWindow.xTxSegment = xSegment;
    /* ->vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 2 );
    ulLength = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &plPosition );
    TEST_ASSERT_EQUAL( 3, ulLength );
}

void test_ulTCPWindowTxGet_length_ne_zero_bit_outstanding_eq_true( void )
{
    uint32_t ulLength;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };
    uint32_t ulWindowSize = 20;
    int32_t plPosition = 3;

    xSegment.lDataLength = 3;
    xSegment.u.bits.bOutstanding = pdTRUE_UNSIGNED;
    xSegment.u.bits.ucTransmitCount = 3;
    xWindow.xTxSegment = xSegment;
    xWindow.lSRTT = 2;

    /* ->ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 500000 );
    /* <ulTCPWindowTxGet */
    /* ->vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 500000 );
    ulLength = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &plPosition );
    TEST_ASSERT_EQUAL( 3, ulLength );
}

void test_ulTCPWindowTxGet_length_ne_zero_bit_outstanding_eq_true_timer_ne_expired( void )
{
    uint32_t ulLength;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };
    uint32_t ulWindowSize = 20;
    int32_t plPosition = 3;

    xSegment.lDataLength = 3;
    xSegment.u.bits.bOutstanding = pdTRUE_UNSIGNED;
    xSegment.u.bits.ucTransmitCount = 3;
    xWindow.xTxSegment = xSegment;
    xWindow.lSRTT = 2;

    /* ->ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 10 );

    ulLength = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &plPosition );
    TEST_ASSERT_EQUAL( 0, ulLength );
}

void test_xTCPWindowTxDone_seg_datalength_eq_zero( void )
{
    BaseType_t xReturn;
    TCPWindow_t xWindow = { 0 };

    xWindow.xTxSegment.lDataLength = 0;

    xReturn = xTCPWindowTxDone( &xWindow );

    TEST_ASSERT_TRUE( xReturn );
}

void test_xTCPWindowTxDone_seg_datalength_ne_zero( void )
{
    BaseType_t xReturn;
    TCPWindow_t xWindow = { 0 };

    xWindow.xTxSegment.lDataLength = 3;

    xReturn = xTCPWindowTxDone( &xWindow );

    TEST_ASSERT_FALSE( xReturn );
}


void test_xTCPWindowTxHasData( void )
{
    BaseType_t xReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 20;
    TickType_t ulDelay;

    xWindow.xTxSegment.lDataLength = 5;
    xWindow.xTxSegment.u.bits.bOutstanding = pdFALSE_UNSIGNED;

    xReturn = xTCPWindowTxHasData( &xWindow,
                                   ulWindowSize,
                                   &ulDelay );
    TEST_ASSERT_TRUE( xReturn );
}

void test_xTCPWindowTxHasData_txData_eq_zero( void )
{
    BaseType_t xReturn;
    TCPWindow_t xWindow;
    uint32_t ulWindowSize = 20;
    TickType_t ulDelay;

    xWindow.xTxSegment.lDataLength = 0;

    xReturn = xTCPWindowTxHasData( &xWindow,
                                   ulWindowSize,
                                   &ulDelay );
    TEST_ASSERT_FALSE( xReturn );
}

void test_xTCPWindowTxHasData_outstanding_bits( void )
{
    BaseType_t xReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 20;
    TickType_t ulDelay = 0;

    xWindow.xTxSegment.lDataLength = 5;
    xWindow.xTxSegment.u.bits.bOutstanding = pdTRUE_UNSIGNED;
    xWindow.xTxSegment.u.bits.ucTransmitCount = 2;
    xWindow.xTxSegment.xTransmitTimer.uxBorn = 0;
    xWindow.lSRTT = 2;

    /* ->ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 23 );
    xReturn = xTCPWindowTxHasData( &xWindow,
                                   ulWindowSize,
                                   &ulDelay );
    TEST_ASSERT_TRUE( xReturn );
    TEST_ASSERT_EQUAL( 0, ulDelay );
}

void test_xTCPWindowTxHasData_outstanding_bits_2( void )
{
    BaseType_t xReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 20;
    TickType_t ulDelay = 0;

    xWindow.xTxSegment.lDataLength = 5;
    xWindow.xTxSegment.u.bits.bOutstanding = pdTRUE_UNSIGNED;
    xWindow.xTxSegment.u.bits.ucTransmitCount = 2;
    xWindow.lSRTT = 6;
    xWindow.xTxSegment.xTransmitTimer.uxBorn = 0;

    /* ->ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 23 );
    xReturn = xTCPWindowTxHasData( &xWindow,
                                   ulWindowSize,
                                   &ulDelay );
    TEST_ASSERT_TRUE( xReturn );
    uint32_t age_diff = ( ( 1U << xWindow.xTxSegment.u.bits.ucTransmitCount ) * ( uint32_t ) xWindow.lSRTT ) - 23;
    TEST_ASSERT_EQUAL( age_diff, ulDelay );
}

void test_xTCPWindowTxHasData_tx_window_no_space( void )
{
    BaseType_t xReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 20;
    TickType_t ulDelay;

    xWindow.xTxSegment.lDataLength = 5;
    xWindow.xTxSegment.u.bits.bOutstanding = pdFALSE_UNSIGNED;
    xWindow.usMSSInit = 300;

    xReturn = xTCPWindowTxHasData( &xWindow,
                                   ulWindowSize,
                                   &ulDelay );
    TEST_ASSERT_FALSE( xReturn );
}

void test_ulTCPWindowTxAck_datalen_eq_zero( void )
{
    uint32_t ulDataLength;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 10;

    xWindow.xTxSegment.lDataLength = 0;

    ulDataLength = ulTCPWindowTxAck( &xWindow,
                                     ulSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulDataLength );
}

void test_ulTCPWindowTxAck_datalen_neq( void )
{
    uint32_t ulDataLength;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 10;

    xWindow.xTxSegment.lDataLength = 20;
    xWindow.tx.ulCurrentSequenceNumber = 10;

    ulDataLength = ulTCPWindowTxAck( &xWindow,
                                     ulSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulDataLength );
}

void test_ulTCPWindowTxAck_nothing_to_send( void )
{
    uint32_t ulDataLength;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 10;

    xWindow.xTxSegment.lDataLength = 20;
    xWindow.tx.ulCurrentSequenceNumber = 10;

    ulDataLength = ulTCPWindowTxAck( &xWindow,
                                     ulSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulDataLength );
}

void test_ulTCPWindowTxAck_seq_gt_current_plus_length( void )
{
    uint32_t ulDataLength;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 40;

    xWindow.xTxSegment.lDataLength = 20;
    xWindow.tx.ulCurrentSequenceNumber = 10;

    ulDataLength = ulTCPWindowTxAck( &xWindow,
                                     ulSequenceNumber );
    TEST_ASSERT_EQUAL( 20, ulDataLength );
    TEST_ASSERT_EQUAL( 0, xWindow.xTxSegment.lDataLength );
}

void test_ulTCPWindowTxAck_seq_gt_current_plus_length_w_logging( void )
{
    uint32_t ulDataLength;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 40;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    xWindow.xTxSegment.lDataLength = 20;
    xWindow.tx.ulCurrentSequenceNumber = 10;

    xTCPWindowLoggingLevel = 2;

    ulDataLength = ulTCPWindowTxAck( &xWindow,
                                     ulSequenceNumber );

    xTCPWindowLoggingLevel = xBackup;

    TEST_ASSERT_EQUAL( 20, ulDataLength );
    TEST_ASSERT_EQUAL( 0, xWindow.xTxSegment.lDataLength );
}

void test_xTCPWindowRxEmpty_not_empty( void )
{
    BaseType_t xReturn;
    TCPWindow_t xWindow = { 0 };

    xWindow.rx.ulCurrentSequenceNumber = 2;
    xWindow.rx.ulHighestSequenceNumber = 0;

    xReturn = xTCPWindowRxEmpty( &xWindow );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

void test_xTCPWindowRxEmpty_Empty( void )
{
    BaseType_t xReturn;
    TCPWindow_t xWindow = { 0 };

    xWindow.rx.ulCurrentSequenceNumber = 0;
    xWindow.rx.ulHighestSequenceNumber = 2;

    xReturn = xTCPWindowRxEmpty( &xWindow );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

void test_vTCPWindowDestroy_empty_function( void )
{
    TCPWindow_t xWindow = { 0 };

    vTCPWindowDestroy( &xWindow );
    TEST_PASS();
}
