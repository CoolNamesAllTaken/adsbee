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

#include "mock_list.h"
#include "mock_FreeRTOS_TCP_WIN_list_macros.h"
#include "mock_portable.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_task.h"


static void initializeList( List_t * const pxList );

extern TCPSegment_t * xTCPSegments;
extern List_t xSegmentList;
extern BaseType_t xTCPWindowLoggingLevel;

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
    initializeList( &xSegmentList );
}

/**
 * @brief calls at the end of each test case
 */
void tearDown( void )
{
    xTCPSegments = NULL;
}


static void initializeList( List_t * const pxList )
{
    pxList->pxIndex = ( ListItem_t * ) &( pxList->xListEnd ); /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */

    /* The list end value is the highest possible value in the list to
     * ensure it remains at the end of the list. */
    pxList->xListEnd.xItemValue = portMAX_DELAY;

    /* The list end next and previous pointers point to itself so we know
     * when the list is empty. */
    pxList->xListEnd.pxNext = ( ListItem_t * ) &( pxList->xListEnd );     /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */
    pxList->xListEnd.pxPrevious = ( ListItem_t * ) &( pxList->xListEnd ); /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */

    pxList->uxNumberOfItems = ( UBaseType_t ) 0U;
}
static void initializeListItem( ListItem_t * const listItem )
{
    listItem->pxNext = NULL;
    listItem->pxPrevious = NULL;
    listItem->pxContainer = NULL;
}

void test_xSequenceLessThan_a_lt_b( void )
{
    BaseType_t xRet;

    xRet = xSequenceLessThan( 1, 2 );
    TEST_ASSERT_EQUAL( pdTRUE, xRet );
}

void test_xSequenceLessThan_a_gb_b( void )
{
    BaseType_t xRet;

    xRet = xSequenceLessThan( 2, 1 );
    TEST_ASSERT_EQUAL( pdFALSE, xRet );
}

void test_xSequenceGreaterThan_a_lt_b( void )
{
    BaseType_t xRet;

    xRet = xSequenceGreaterThan( 1, 2 );
    TEST_ASSERT_EQUAL( pdFALSE, xRet );
}

void test_xSequenceGreaterThan_a_gt_b( void )
{
    BaseType_t xRet;

    xRet = xSequenceGreaterThan( 2, 1 );
    TEST_ASSERT_EQUAL( pdTRUE, xRet );
}

void test_xTCPWindowRxEmpty_empty_list( void )
{
    BaseType_t xRet;
    TCPWindow_t xWindow = { 0 };

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );

    xRet = xTCPWindowRxEmpty( &xWindow );

    TEST_ASSERT_EQUAL( pdFALSE, xRet );
}

void test_xTCPWindowRxEmpty_greater_sequence( void )
{
    BaseType_t xRet;
    TCPWindow_t xWindow = { 0 };

    xWindow.rx.ulCurrentSequenceNumber = 1;
    xWindow.rx.ulHighestSequenceNumber = 3;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    xRet = xTCPWindowRxEmpty( &xWindow );

    TEST_ASSERT_EQUAL( pdFALSE, xRet );
}

void test_xTCPWindowRxEmpty_smaller_sequence( void )
{
    BaseType_t xRet;
    TCPWindow_t xWindow = { 0 };

    xWindow.rx.ulCurrentSequenceNumber = 2;
    xWindow.rx.ulHighestSequenceNumber = 1;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    xRet = xTCPWindowRxEmpty( &xWindow );

    TEST_ASSERT_EQUAL( pdTRUE, xRet );
}

void test_vTCPWindowDestroy_uninitialised_segment_list( void )
{
    TCPWindow_t xWindow = { 0 };

    listLIST_IS_INITIALISED_ExpectAnyArgsAndReturn( pdFALSE );
    listLIST_IS_INITIALISED_ExpectAnyArgsAndReturn( pdFALSE );

    vTCPWindowDestroy( &xWindow );
}

void test_vTCPWindowDestroy_list_length_zero( void )
{
    TCPWindow_t xWindow = { 0 };

    listLIST_IS_INITIALISED_ExpectAnyArgsAndReturn( pdFALSE );
    listLIST_IS_INITIALISED_ExpectAnyArgsAndReturn( pdTRUE );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    vTCPWindowDestroy( &xWindow );
}

void test_vTCPWindowDestroy_list_length_not_zero( void )
{
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };

    xSegment.xQueueItem.pvContainer = &xWindow.xPriorityQueue;
    xSegment.xSegmentItem.pvContainer = &xWindow.xPriorityQueue;

    listLIST_IS_INITIALISED_ExpectAnyArgsAndReturn( pdFALSE );
    listLIST_IS_INITIALISED_ExpectAnyArgsAndReturn( pdTRUE );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1 );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xSegment );
    /* ->vTCPWindowFree */
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    vTCPWindowDestroy( &xWindow );
}

void test_vTCPWindowDestroy_list_no_queue_container( void )
{
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };

    xSegment.xQueueItem.pxContainer = NULL;

    listLIST_IS_INITIALISED_ExpectAnyArgsAndReturn( pdFALSE );
    listLIST_IS_INITIALISED_ExpectAnyArgsAndReturn( pdTRUE );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1 );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xSegment );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    vTCPWindowDestroy( &xWindow );
}

void test_vTCPWindowDestroy_list_no_segment_container( void )
{
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };

    xSegment.xSegmentItem.pxContainer = NULL;

    listLIST_IS_INITIALISED_ExpectAnyArgsAndReturn( pdFALSE );
    listLIST_IS_INITIALISED_ExpectAnyArgsAndReturn( pdTRUE );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1 );
    listGET_OWNER_OF_HEAD_ENTRY_ExpectAnyArgsAndReturn( &xSegment );
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    vTCPWindowDestroy( &xWindow );
}

void test_xTCPWindowCreate_success( void )
{
    TCPWindow_t xWindow = { 0 };
    uint32_t ulRxWindowLength = 0;
    uint32_t ulTxWindowLength = 0;
    uint32_t ulAckNumber = 0;
    uint32_t ulSequenceNumber = 0;
    uint32_t ulMSS = 0;
    BaseType_t xReturn;

    void * mlc = malloc( ipconfigTCP_WIN_SEG_COUNT * sizeof( xTCPSegments[ 0 ] ) );

    /* ->prvCreateSectors */
    vListInitialise_ExpectAnyArgs();
    pvPortMalloc_ExpectAnyArgsAndReturn( mlc );
    listSET_LIST_ITEM_OWNER_ExpectAnyArgs();
    listSET_LIST_ITEM_OWNER_ExpectAnyArgs();

    listSET_LIST_ITEM_OWNER_ExpectAnyArgs();
    listSET_LIST_ITEM_OWNER_ExpectAnyArgs();

    /* back */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();


    xReturn = xTCPWindowCreate( &xWindow,
                                ulRxWindowLength,
                                ulTxWindowLength,
                                ulAckNumber,
                                ulSequenceNumber,
                                ulMSS );
    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    free( mlc );
}

void test_xTCPWindowCreate_AllocationFailed( void )
{
    TCPWindow_t xWindow = { 0 };
    uint32_t ulRxWindowLength = 0;
    uint32_t ulTxWindowLength = 0;
    uint32_t ulAckNumber = 0;
    uint32_t ulSequenceNumber = 0;
    uint32_t ulMSS = 0;
    BaseType_t xReturn;

    /* ->prvCreateSectors */
    vListInitialise_ExpectAnyArgs();
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );

    /* back */
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();


    xReturn = xTCPWindowCreate( &xWindow,
                                ulRxWindowLength,
                                ulTxWindowLength,
                                ulAckNumber,
                                ulSequenceNumber,
                                ulMSS );
    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xTCPWindowCreate_tcp_segment_null( void )
{
    TCPWindow_t xWindow = { 0 };
    uint32_t ulRxWindowLength = 0;
    uint32_t ulTxWindowLength = 0;
    uint32_t ulAckNumber = 0;
    uint32_t ulSequenceNumber = 0;
    uint32_t ulMSS = 0;
    BaseType_t xReturn;

    /* ->prvCreateSectors */
    vListInitialise_ExpectAnyArgs();
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );

    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();


    xReturn = xTCPWindowCreate( &xWindow,
                                ulRxWindowLength,
                                ulTxWindowLength,
                                ulAckNumber,
                                ulSequenceNumber,
                                ulMSS );
    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

void test_xTCPWindowCreate_null_tcpSegment( void )
{
    TCPWindow_t xWindow = { 0 };
    uint32_t ulRxWindowLength = 0;
    uint32_t ulTxWindowLength = 0;
    uint32_t ulAckNumber = 0;
    uint32_t ulSequenceNumber = 0;
    uint32_t ulMSS = 0;
    BaseType_t xReturn;

    xTCPSegments = ( TCPSegment_t * ) 32;

    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();
    vListInitialise_ExpectAnyArgs();

    xReturn = xTCPWindowCreate( &xWindow,
                                ulRxWindowLength,
                                ulTxWindowLength,
                                ulAckNumber,
                                ulSequenceNumber,
                                ulMSS );
    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL( ulRxWindowLength, xWindow.xSize.ulRxWindowLength );
    TEST_ASSERT_EQUAL( ulTxWindowLength, xWindow.xSize.ulTxWindowLength );
}

void test_vTCPWindowInit_MSS_not_zero( void )
{
    TCPWindow_t xWindow = { 0 };
    uint32_t ulAckNumber = 0;
    uint32_t ulSequenceNumber = 0;
    uint32_t ulMSS = 1;

    xWindow.usMSSInit = 2;
    xWindow.usMSS = 2;

    vTCPWindowInit( &xWindow, ulAckNumber, ulSequenceNumber, ulMSS );

    TEST_ASSERT_EQUAL( ulMSS, xWindow.usMSSInit );
    TEST_ASSERT_EQUAL( ulMSS, xWindow.usMSS );
}

void test_vTCPWindowInit_MSS_not_zero_mssInit_zero( void )
{
    TCPWindow_t xWindow = { 0 };
    uint32_t ulAckNumber = 0;
    uint32_t ulSequenceNumber = 0;
    uint32_t ulMSS = 2;

    xWindow.usMSSInit = 0;
    xWindow.usMSS = 2;

    vTCPWindowInit( &xWindow, ulAckNumber, ulSequenceNumber, ulMSS );

    TEST_ASSERT_EQUAL( 0, xWindow.usMSSInit );
    TEST_ASSERT_EQUAL( ulMSS, xWindow.usMSS );
}

void test_vTCPWindowInit_MSS_not_zero_mss_zero( void )
{
    TCPWindow_t xWindow = { 0 };
    uint32_t ulAckNumber = 0;
    uint32_t ulSequenceNumber = 0;
    uint32_t ulMSS = 2;

    xWindow.usMSSInit = 0;
    xWindow.usMSS = 0;

    vTCPWindowInit( &xWindow, ulAckNumber, ulSequenceNumber, ulMSS );

    TEST_ASSERT_EQUAL( 0, xWindow.usMSSInit );
    TEST_ASSERT_EQUAL( ulMSS, xWindow.usMSS );
}


void test_vTCPSegmentCleanup_segment_null( void )
{
    xTCPSegments = NULL;
    vTCPSegmentCleanup();
}

void test_vTCPSegmentCleanup_segment_not_null( void )
{
    /* will be freed by the function under test */
    TCPSegment_t * pxTCPSegment = malloc( sizeof( TCPSegment_t ) );

    xTCPSegments = pxTCPSegment;

    vPortFree_Expect( xTCPSegments );
    vTCPSegmentCleanup();
    TEST_ASSERT_NULL( xTCPSegments );
    free( pxTCPSegment );
}

void test_lTCPWindowRxCheck_sequence_nums_equal( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( ( ulSequenceNumber + ulLength ),
                       xWindow.rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_equal_prvTCPWindowRX_ExpectedRX( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;

    /* ->prvTCPWindowRX_ExpectedRX */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 4 );
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( ( ulSequenceNumber + ulLength ),
                       xWindow.rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_equal_prvTCPWindowRX_ExpectedRX_2( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    TCPSegment_t xSegment = { 0 };
    ListItem_t xIterator;
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;
    xSegment.ulSequenceNumber = 23;


    /* ->prvTCPWindowRX_ExpectedRX */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 4 );
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( ( ulSequenceNumber + ulLength ),
                       xWindow.rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_equal_prvTCPWindowRX_ExpectedRX_3( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    TCPSegment_t xSegment = { 0 };
    ListItem_t xIterator;
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;
    xSegment.ulSequenceNumber = 39;

    /* ->prvTCPWindowRX_ExpectedRX */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 4 );
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* ->prvTCPWindowRX_ExpectedRX */
    /* <-prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( ( ulSequenceNumber + ulLength ),
                       xWindow.rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_equal_prvTCPWindowRX_ExpectedRX_4( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    TCPSegment_t xSegment = { 0 };
    ListItem_t xIterator;
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;
    xSegment.ulSequenceNumber = 39;

    /* ->prvTCPWindowRX_ExpectedRX */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 4 );
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* ->prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( ( ulSequenceNumber + ulLength ),
                       xWindow.rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_equal_prvTCPWindowRX_ExpectedRX_5( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 3;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    TCPSegment_t xSegment = { 0 };
    ListItem_t xIterator;
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;
    xSegment.ulSequenceNumber = 39;

    /* ->prvTCPWindowRX_ExpectedRX */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 4 );
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* ->prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( ( ulSequenceNumber + ulLength ),
                       xWindow.rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_equal_prvTCPWindowRX_ExpectedRX_6( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    TCPSegment_t xSegment = { 0 };
    ListItem_t xIterator;
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;
    xSegment.ulSequenceNumber = 39;
    xSegment.lDataLength = ulLength;

    /* ->prvTCPWindowRX_ExpectedRX */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 4 );
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* ->prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRX_ExpectedRX */
    /* ->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( ( ulSequenceNumber + ulLength ),
                       xWindow.rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_equal_prvTCPWindowRX_ExpectedRX_7( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 39;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    TCPSegment_t xSegment = { 0 };
    uint32_t ulSkipCount = 0;
    ListItem_t xIterator;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;
    xSegment.ulSequenceNumber = 39;
    xSegment.lDataLength = ulLength + 6;

    /* ->prvTCPWindowRX_ExpectedRX */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 4 );
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* ->prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRX_ExpectedRX */
    /* ->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( ( ulSequenceNumber + ulLength ),
                       xWindow.rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_equal_prvTCPWindowRX_ExpectedRX_8( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    TCPSegment_t xSegment = { 0 };
    /*TCPSegment_t xBest; */
    ListItem_t xIterator;
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;
    xSegment.ulSequenceNumber = 34;
    xSegment.lDataLength = ulLength;

    /* ->prvTCPWindowRX_ExpectedRX */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 4 );
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRX_ExpectedRX */
    /* ->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( ( ulSequenceNumber + ulLength ),
                       xWindow.rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_equal_prvTCPWindowRX_ExpectedRX_9( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    TCPSegment_t xSegment = { 0 };
    TCPSegment_t xSegment2 = { 0 };
    TCPSegment_t xBest = { 0 };
    ListItem_t xIterator;
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;
    xSegment.ulSequenceNumber = 35;
    xSegment.lDataLength = ( int32_t ) ulLength;
    xBest.ulSequenceNumber = 34;

    xSegment2.ulSequenceNumber = ulLength + ulSequenceNumber;
    xSegment2.lDataLength = 500;

    /* ->prvTCPWindowRX_ExpectedRX */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 4 );
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xBest );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment2 );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( ( 500UL + ulLength + ulSequenceNumber ),
                       xWindow.rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_equal_prvTCPWindowRX_ExpectedRX_10( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    TCPSegment_t xSegment = { 0 };
    ListItem_t xIterator;
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;
    xSegment.ulSequenceNumber = 34;
    xSegment.lDataLength = ( int32_t ) ulLength;

    /* ->prvTCPWindowRX_ExpectedRX */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 4 );
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* ->prvTCPWindowRX_ExpectedRX */
    /* -->xTCPWindowRXConfirm */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRX_ExpectedRX */
    /* ->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EQUAL( ( ulSequenceNumber + ulLength ),
                       xWindow.rx.ulCurrentSequenceNumber );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_equal_length_gt_space( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength - 3U; /* space < length */
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber;

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( -1, lReturn );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_sequence_nums_plus_1( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow;
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 0;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber + 1U;

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( -1, lReturn );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_current_sequence_lt_sequence( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength - 9U; /* space > length */
    uint32_t ulSkipCount = 0;

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber - 2U;

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( -1, lReturn );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_current_sequence_lt_sequence_prvTCPWindowRX( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    ListItem_t xIterator;
    TCPSegment_t xSegment;
    uint32_t ulSkipCount = 0;

    initializeListItem( &xIterator );

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber - 2U;
    xSegment.ulSequenceNumber = ulSequenceNumber - 2U;

    /* ->prvTCPWindowRx_UnexpectedRX */
    /* ->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* -> xTCPWindowNew */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( -1, lReturn );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_current_sequence_lt_sequence_prvTCPWindowRX_2( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    ListItem_t xIterator;
    TCPSegment_t xSegment;
    uint32_t ulSkipCount = 0;

    initializeListItem( &xIterator );
    initializeList( &xWindow.xRxSegments );

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber - 2U;
    xSegment.ulSequenceNumber = ulSequenceNumber + ulLength;

    /* ->prvTCPWindowRx_UnexpectedRX */
    /* ->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );

    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* -> xTCPWindowNew */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xSegment );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xIterator );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* -->vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 23 );
    /* <-xTCPWindowNew */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 23 );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( 2, lReturn );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_current_sequence_lt_sequence_prvTCPWindowRX_3( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    ListItem_t xIterator;
    TCPSegment_t xSegment;
    uint32_t ulSkipCount = 0;

    initializeListItem( &xIterator );

    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber - 2U;
    xSegment.ulSequenceNumber = ulSequenceNumber;

    /* ->prvTCPWindowRx_UnexpectedRX */
    /* -->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xRxSegments.xListEnd );
    /* <-prvTCPWindowRx_UnexpectedRX */
    /* -->xTCPWindowRxFind */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &xSegment );

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( -1, lReturn );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_distance_eq_zero( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 34;
    uint32_t ulLength = 34;
    uint32_t ulSpace = ulLength + 3U; /* space > length */
    uint32_t ulSkipCount = 0;

    /* make ldistance <= 0 */
    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber + ulLength;

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( -1, lReturn );
    TEST_ASSERT_EQUAL( 0, ulSkipCount );
}

void test_lTCPWindowRxCheck_distance_gt_space( void )
{
    int32_t lReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulSequenceNumber = 15;
    uint32_t ulLength = 64;
    uint32_t ulSpace = 3U; /* space > length */
    uint32_t ulSkipCount = 0;

    /* make ldistance >= ulSpace */
    xWindow.rx.ulCurrentSequenceNumber = ulSequenceNumber + 2U;

    lReturn = lTCPWindowRxCheck( &xWindow,
                                 ulSequenceNumber,
                                 ulLength,
                                 ulSpace,
                                 &ulSkipCount );

    TEST_ASSERT_EQUAL( -1, lReturn );
    TEST_ASSERT_EQUAL( 2, ulSkipCount );
}

void test_lTCPWindowTxAdd_nothing_to_do( void )
{
    int32_t lDone;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t xSegment = { 0 };
    uint32_t ulLength = 0;
    int32_t lPosition = 0;
    int32_t lMax = 0;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    /* in real code, this points to a list of segments */
    xWindow.pxHeadSegment = &xSegment;

    xTCPWindowLoggingLevel = 3;

    lDone = lTCPWindowTxAdd( &xWindow,
                             ulLength,
                             lPosition,
                             lMax );

    TEST_ASSERT_EQUAL( 0, lDone );

    xTCPWindowLoggingLevel = xBackup;
}

void test_lTCPWindowTxAdd_null_txSegment( void )
{
    int32_t lDone;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulLength = 0;
    int32_t lPosition = 0;
    int32_t lMax = 0;

    xWindow.pxHeadSegment = NULL;


    lDone = lTCPWindowTxAdd( &xWindow,
                             ulLength,
                             lPosition,
                             lMax );

    TEST_ASSERT_EQUAL( 0, lDone );
}

void test_lTCPWindowTxAdd_true_outstanding_bits( void )
{
    int32_t lDone;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulLength = 0;
    int32_t lPosition = 0;
    int32_t lMax = 0;

    /* in real code, this points to a list of segments */
    xWindow.pxHeadSegment = malloc( sizeof( TCPSegment_t ) );
    xWindow.pxHeadSegment->lMaxLength = 300;
    xWindow.pxHeadSegment->lDataLength = xWindow.pxHeadSegment->lMaxLength - 3;
    xWindow.pxHeadSegment->u.bits.bOutstanding = pdTRUE_UNSIGNED;


    lDone = lTCPWindowTxAdd( &xWindow,
                             ulLength,
                             lPosition,
                             lMax );

    TEST_ASSERT_EQUAL( 0, lDone );
    free( xWindow.pxHeadSegment );
}

void test_lTCPWindowTxAdd_data_length_zero( void )
{
    int32_t lDone;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulLength = 0;
    int32_t lPosition = 0;
    int32_t lMax = 0;

    /* in real code, this points to a list of segments */
    xWindow.pxHeadSegment = malloc( sizeof( TCPSegment_t ) );
    xWindow.pxHeadSegment->lMaxLength = 300;
    xWindow.pxHeadSegment->lDataLength = 0;
    xWindow.pxHeadSegment->u.bits.bOutstanding = pdFALSE_UNSIGNED;


    lDone = lTCPWindowTxAdd( &xWindow,
                             ulLength,
                             lPosition,
                             lMax );

    TEST_ASSERT_EQUAL( 0, lDone );
    free( xWindow.pxHeadSegment );
}

void test_lTCPWindowTxAdd_bytes_left_gt_zero( void )
{
    int32_t lDone;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulLength = 0;
    int32_t lPosition = 0;
    int32_t lMax = 0;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    /* in real code, this points to a list of segments */
    xWindow.pxHeadSegment = malloc( sizeof( TCPSegment_t ) );
    xWindow.pxHeadSegment->lMaxLength = 300;
    xWindow.pxHeadSegment->lDataLength = 200;
    xWindow.pxHeadSegment->u.bits.bOutstanding = pdFALSE_UNSIGNED;

    xTCPWindowLoggingLevel = 2;

    FreeRTOS_min_int32_ExpectAnyArgsAndReturn( 20 );
    lDone = lTCPWindowTxAdd( &xWindow,
                             ulLength,
                             lPosition,
                             lMax );

    TEST_ASSERT_EQUAL( 20, lDone );
    TEST_ASSERT_NOT_NULL( xWindow.pxHeadSegment );
    free( xWindow.pxHeadSegment );

    xTCPWindowLoggingLevel = xBackup;
}

void test_lTCPWindowTxAdd_len_gt_max_len( void )
{
    int32_t lDone;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulLength = 20;
    int32_t lPosition = 0;
    int32_t lMax = 300;
    void * xHeadSegmentSave;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    xTCPWindowLoggingLevel = 0;
    /* in real code, this points to a list of segments */
    xWindow.pxHeadSegment = malloc( sizeof( TCPSegment_t ) );
    xHeadSegmentSave = xWindow.pxHeadSegment;
    xWindow.pxHeadSegment->lMaxLength = 300;
    xWindow.pxHeadSegment->lDataLength = 200;
    xWindow.pxHeadSegment->u.bits.bOutstanding = pdFALSE_UNSIGNED;


    FreeRTOS_min_int32_ExpectAnyArgsAndReturn( 200 );
    lDone = lTCPWindowTxAdd( &xWindow,
                             ulLength,
                             lPosition,
                             lMax );

    TEST_ASSERT_EQUAL( 200, lDone );
    TEST_ASSERT_NULL( xWindow.pxHeadSegment );
    free( xHeadSegmentSave );
    xTCPWindowLoggingLevel = xBackup;
}

void test_lTCPWindowTxAdd_lBytesLeft_gt_zero_pxSegment_NULL( void )
{
    int32_t lDone;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulLength = 20;
    int32_t lPosition = 0;
    int32_t lMax = 0;

    /* in real code, this points to a list of segments */
    xWindow.pxHeadSegment = malloc( sizeof( TCPSegment_t ) );
    xWindow.pxHeadSegment->lMaxLength = 300;
    xWindow.pxHeadSegment->lDataLength = 200;
    xWindow.pxHeadSegment->u.bits.bOutstanding = pdTRUE_UNSIGNED;


    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    lDone = lTCPWindowTxAdd( &xWindow,
                             ulLength,
                             lPosition,
                             lMax );

    TEST_ASSERT_EQUAL( 0, lDone );
    TEST_ASSERT_NOT_NULL( xWindow.pxHeadSegment );
    free( xWindow.pxHeadSegment );
}

void test_lTCPWindowTxAdd_lBytesLeft_gt_zero_data_length_gt_maxlen( void )
{
    int32_t lDone;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    uint32_t ulLength = 20;
    int32_t lPosition = 0;
    int32_t lMax = 0;

    /* in real code, this points to a list of segments */
    TCPSegment_t * pxTCPSegment = malloc( sizeof( TCPSegment_t ) );

    xWindow.pxHeadSegment = pxTCPSegment;
    xWindow.pxHeadSegment->lMaxLength = 300;
    xWindow.pxHeadSegment->lDataLength = 200;
    xWindow.pxHeadSegment->u.bits.bOutstanding = pdTRUE_UNSIGNED;

    xWindow.usMSS = 20;

    mockSegment.lMaxLength = 200;
    mockSegment.lDataLength = mockSegment.lMaxLength + 3;
    initializeList( &xWindow.xTxQueue );
    initializeList( &xWindow.xTxSegments );

    /* ->xTCPWindowNew */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* -->vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 3000 );
    /* ->xTCPWindowNew */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( ipconfigTCP_WIN_SEG_COUNT - 1 );

    /* back to API */
    FreeRTOS_min_int32_ExpectAnyArgsAndReturn( 25 );

    lDone = lTCPWindowTxAdd( &xWindow,
                             ulLength,
                             lPosition,
                             lMax );

    TEST_ASSERT_EQUAL( 25, lDone );
    TEST_ASSERT_NULL( xWindow.pxHeadSegment );
    free( pxTCPSegment );
}

void test_lTCPWindowTxAdd_lBytesLeft_gt_zero_data_length_lt_maxlen( void )
{
    int32_t lDone;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    uint32_t ulLength = 20;
    int32_t lPosition = 0;
    int32_t lMax = 0;

    /* in real code, this points to a list of segments */
    xWindow.pxHeadSegment = malloc( sizeof( TCPSegment_t ) );
    xWindow.pxHeadSegment->lMaxLength = 300;
    xWindow.pxHeadSegment->lDataLength = 200;
    xWindow.pxHeadSegment->u.bits.bOutstanding = pdTRUE_UNSIGNED;

    xWindow.usMSS = 300;

    xWindow.pxHeadSegment->lMaxLength = 300;
    xWindow.pxHeadSegment->lDataLength = 1;

    initializeList( &xWindow.xTxQueue );
    initializeList( &xWindow.xTxSegments );

    /* -> xTCPWindowTxNew */ /* xTCPWindowNew */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( xWindow.pxHeadSegment );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* --> vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 3000 );
    /* -> xTCPWindowNew */
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( ipconfigTCP_WIN_SEG_COUNT - 1 );

    /* back to API */
    FreeRTOS_min_int32_ExpectAnyArgsAndReturn( 23 );

    lDone = lTCPWindowTxAdd( &xWindow,
                             ulLength,
                             lPosition,
                             lMax );

    TEST_ASSERT_EQUAL( 23, lDone );
    TEST_ASSERT_NOT_NULL( xWindow.pxHeadSegment );
    free( xWindow.pxHeadSegment );
}


void test_lTCPWindowTxAdd_assert_null( void )
{
    TCPWindow_t xWindow = { 0 };
    uint32_t ulLength = 20;
    int32_t lPosition = 0;
    int32_t lMax = 0;
    ListItem_t mockListItem;

    /* -> xTCPWindowTxNew */ /* xTCPWindowNew */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( NULL );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( xWindow.pxHeadSegment );
    catch_assert( lTCPWindowTxAdd( &xWindow,
                                   ulLength,
                                   lPosition,
                                   lMax ) );

    /* -> xTCPWindowTxNew */ /* xTCPWindowNew */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( NULL );
    catch_assert( lTCPWindowTxAdd( &xWindow,
                                   ulLength,
                                   lPosition,
                                   lMax ) );
}



void test_xTCPWindowTxDone( void )
{
    BaseType_t xRet = pdFALSE;
    TCPWindow_t tcpWin = { 0 };

    initializeList( &tcpWin.xTxSegments );

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    xRet = xTCPWindowTxDone( &tcpWin );

    TEST_ASSERT_TRUE( xRet );
}

void test_xTCPWindowTxHasData_empty_list( void )
{
    BaseType_t xReturn;

    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 34;
    TickType_t ulDelay = 33;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );

    xReturn = xTCPWindowTxHasData( &xWindow, ulWindowSize, &ulDelay );

    TEST_ASSERT_TRUE( xReturn );
}

void test_xTCPWindowTxHasData_null_segment( void )
{
    BaseType_t xReturn;

    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 34;
    TickType_t ulDelay = 33;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = xTCPWindowTxHasData( &xWindow, ulWindowSize, &ulDelay );

    TEST_ASSERT_FALSE( xReturn );
}

void test_xTCPWindowTxHasData_non_null_segment_maxage_lt_age( void )
{
    BaseType_t xReturn;

    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    uint32_t ulWindowSize = 34;
    TickType_t ulDelay = 33;

    mockSegment.u.bits.ucTransmitCount = 1;
    mockSegment.xTransmitTimer.uxBorn = 2;
    xWindow.lSRTT = 1;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 2333 );

    xReturn = xTCPWindowTxHasData( &xWindow, ulWindowSize, &ulDelay );

    TEST_ASSERT_TRUE( xReturn );
}

void test_xTCPWindowTxHasData_non_null_segment_maxAge_gt_age( void )
{
    BaseType_t xReturn;

    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    uint32_t ulWindowSize = 34;
    TickType_t ulDelay = 33;

    mockSegment.u.bits.ucTransmitCount = 7;
    mockSegment.xTransmitTimer.uxBorn = 2;
    xWindow.lSRTT = 1;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 23 );

    xReturn = xTCPWindowTxHasData( &xWindow, ulWindowSize, &ulDelay );

    TEST_ASSERT_TRUE( xReturn );
}

void test_xTCPWindowTxHasData_no_space( void )
{
    BaseType_t xReturn;

    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    uint32_t ulWindowSize = 34;
    TickType_t ulDelay = 33;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> prvTCPWindowTxHasSpace */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = xTCPWindowTxHasData( &xWindow, ulWindowSize, &ulDelay );

    TEST_ASSERT_FALSE( xReturn );
}

void test_xTCPWindowTxHasData_no_space_size_lt_datalength( void )
{
    BaseType_t xReturn;

    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    uint32_t ulWindowSize = 34;
    TickType_t ulDelay = 33;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> prvTCPWindowTxHasSpace */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> prvTCPWindowTxHasSpace */
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 300 );

    xReturn = xTCPWindowTxHasData( &xWindow, ulWindowSize, &ulDelay );

    TEST_ASSERT_TRUE( xReturn );
}

void test_xTCPWindowTxHasData_datalength_lt_maxlength( void )
{
    BaseType_t xReturn;

    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    uint32_t ulWindowSize = 34;
    TickType_t ulDelay = 33;

    mockSegment.lMaxLength = 7;
    xWindow.u.bits.bSendFullSize = pdTRUE_UNSIGNED;
    mockSegment.lDataLength = mockSegment.lMaxLength - 3;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> prvTCPWindowTxHasSpace */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> prvTCPWindowTxHasSpace */
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 300 );

    xReturn = xTCPWindowTxHasData( &xWindow, ulWindowSize, &ulDelay );

    TEST_ASSERT_FALSE( xReturn );
}

void test_xTCPWindowTxHasData_SendFullSize( void )
{
    BaseType_t xReturn;

    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    uint32_t ulWindowSize = 34;
    TickType_t ulDelay = 33;

    mockSegment.lMaxLength = 7;
    xWindow.u.bits.bSendFullSize = pdTRUE_UNSIGNED;
    mockSegment.lDataLength = mockSegment.lMaxLength + 3;

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> prvTCPWindowTxHasSpace */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> prvTCPWindowTxHasSpace */
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 300 );

    xReturn = xTCPWindowTxHasData( &xWindow, ulWindowSize, &ulDelay );

    TEST_ASSERT_TRUE( xReturn );
}


void test_ulTCPWindowTxGet_config_assert( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 400;
    int32_t lPosition = 0;
    TCPSegment_t mockSegment = { 0 };
    TCPSegment_t mockSegment2 = { 0 };
    ListItem_t mockListItem;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    xTCPWindowLoggingLevel = 2;
    xWindow.tx.ulHighestSequenceNumber = 45;
    xWindow.tx.ulCurrentSequenceNumber = xWindow.tx.ulHighestSequenceNumber + 3U;
    mockSegment.lDataLength = 360;
    mockSegment.lMaxLength = 300;
    xWindow.pxHeadSegment = &mockSegment2;
    xWindow.u.bits.bSendFullSize = pdTRUE_UNSIGNED;

    mockSegment2.xQueueItem.pxContainer = NULL;
    mockSegment2.lDataLength = 567;
    mockSegment2.xQueueItem.pxContainer = &xWindow.xPriorityQueue;
    initializeListItem( &mockListItem );
    initializeList( &xWindow.xWaitQueue );

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    /* -> pxTCPWindowTx_GetTXQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> pxTCPWindowTx_GetTXQueue */
    /* -> prvTCPWindowTxHasSpace */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> prvTCPWindowTxHasSpace */
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 3 );
    /* <-pxTCPWindowTx_GetTXQueue */
    /* -->xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment2 );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );

    catch_assert( ulTCPWindowTxGet( &xWindow,
                                    ulWindowSize,
                                    &lPosition ) );

    xTCPWindowLoggingLevel = xBackup;
}

void test_ulTCPWindowTxGet_empty_segment_list( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 23;
    int32_t lPosition = 0;

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    /* -> pxTCPWindowTx_GetTXQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_EQUAL( 0, ulReturn );
}

void test_ulTCPWindowTxGet_empty_wait_queue( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 300;
    int32_t lPosition = 0;
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;

    xWindow.tx.ulHighestSequenceNumber = 45;
    xWindow.tx.ulCurrentSequenceNumber = xWindow.tx.ulHighestSequenceNumber + 3U;
    mockSegment.lDataLength = 360;
    xWindow.pxHeadSegment = &mockSegment;

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    /* -> pxTCPWindowTx_GetTXQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> pxTCPWindowTx_GetTXQueue */
    /* -->prvTCPWindowTxHasSpace */
    /* ---> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -->prvTCPWindowTxHasSpace */
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 50 );

    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_EQUAL( 0, ulReturn );
}

void test_ulTCPWindowTxGet_empty_wait_queue_2( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 300;
    int32_t lPosition = 0;
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;

    xWindow.tx.ulHighestSequenceNumber = 45;
    xWindow.tx.ulCurrentSequenceNumber = xWindow.tx.ulHighestSequenceNumber - 3U;
    mockSegment.lDataLength = 360;
    xWindow.pxHeadSegment = &mockSegment;

    xWindow.xSize.ulTxWindowLength = ( ( xWindow.tx.ulHighestSequenceNumber -
                                         xWindow.tx.ulCurrentSequenceNumber ) +
                                       mockSegment.lDataLength ) - 2U;

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    /* -> pxTCPWindowTx_GetTXQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> pxTCPWindowTx_GetTXQueue */
    /* -->prvTCPWindowTxHasSpace */
    /* ---> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -->prvTCPWindowTxHasSpace */
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 50 );

    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_EQUAL( 0, ulReturn );
}

void test_ulTCPWindowTxGet_empty_wait_queue_3( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 300;
    int32_t lPosition = 0;
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;

    xWindow.tx.ulHighestSequenceNumber = 45;
    xWindow.tx.ulCurrentSequenceNumber = xWindow.tx.ulHighestSequenceNumber - 3U;
    mockSegment.lDataLength = 360;
    xWindow.pxHeadSegment = &mockSegment;

    xWindow.xSize.ulTxWindowLength = ( ( xWindow.tx.ulHighestSequenceNumber -
                                         xWindow.tx.ulCurrentSequenceNumber ) +
                                       mockSegment.lDataLength ) + 2U;

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    /* -> pxTCPWindowTx_GetTXQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> pxTCPWindowTx_GetTXQueue */
    /* -->prvTCPWindowTxHasSpace */
    /* ---> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -->prvTCPWindowTxHasSpace */
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 50 );

    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_EQUAL( 0, ulReturn );
}

void test_ulTCPWindowTxGet_empty_wait_queue_4( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 300;
    int32_t lPosition = 0;
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;

    xWindow.tx.ulHighestSequenceNumber = 45;
    xWindow.tx.ulCurrentSequenceNumber = xWindow.tx.ulHighestSequenceNumber + 3U;
    mockSegment.lDataLength = 360;
    mockSegment.lMaxLength = 400;
    xWindow.pxHeadSegment = &mockSegment;
    xWindow.u.bits.bSendFullSize = pdTRUE_UNSIGNED;

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetTXQueue */
    /* -->prvTCPWindowTxHasSpace */
    /* ---> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -->prvTCPWindowTxHasSpace */

    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_EQUAL( 0, ulReturn );
}

void test_ulTCPWindowTxGet_empty_wait_queue_5( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 400;
    int32_t lPosition = 0;
    TCPSegment_t mockSegment = { 0 };
    TCPSegment_t mockSegment2 = { 0 };
    ListItem_t mockListItem;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    xTCPWindowLoggingLevel = 0;

    xWindow.tx.ulHighestSequenceNumber = 45;
    xWindow.tx.ulCurrentSequenceNumber = xWindow.tx.ulHighestSequenceNumber + 3U;
    mockSegment.lDataLength = 360;
    mockSegment.lMaxLength = 300;
    xWindow.pxHeadSegment = &mockSegment2;
    xWindow.u.bits.bSendFullSize = pdTRUE_UNSIGNED;

    mockSegment2.xQueueItem.pxContainer = NULL;
    mockSegment2.lDataLength = 567;
    initializeListItem( &mockListItem );
    initializeList( &xWindow.xWaitQueue );

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    /* -> pxTCPWindowTx_GetTXQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> pxTCPWindowTx_GetTXQueue */
    /* -> prvTCPWindowTxHasSpace */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> prvTCPWindowTxHasSpace */
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 3 );
    /* <-pxTCPWindowTx_GetTXQueue */
    /* -->xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment2 );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    xTaskGetTickCount_ExpectAndReturn( 32 );

    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_EQUAL( 567, ulReturn );
    TEST_ASSERT_NULL( xWindow.pxHeadSegment );
    xTCPWindowLoggingLevel = xBackup;
}

void test_ulTCPWindowTxGet_empty_wait_queue_6( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 400;
    int32_t lPosition = 0;
    TCPSegment_t mockSegment = { 0 };
    TCPSegment_t mockSegment2 = { 0 };
    ListItem_t mockListItem;

    xWindow.tx.ulHighestSequenceNumber = 45;
    xWindow.tx.ulCurrentSequenceNumber = xWindow.tx.ulHighestSequenceNumber + 3U;
    mockSegment.lDataLength = 360;
    mockSegment.lMaxLength = 300;
    xWindow.pxHeadSegment = &mockSegment;
    xWindow.u.bits.bSendFullSize = pdTRUE_UNSIGNED;

    mockSegment2.xQueueItem.pxContainer = NULL;
    mockSegment2.lDataLength = 567;
    initializeListItem( &mockListItem );
    initializeList( &xWindow.xWaitQueue );

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    /* -> pxTCPWindowTx_GetTXQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> pxTCPWindowTx_GetTXQueue */
    /* -> prvTCPWindowTxHasSpace */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> prvTCPWindowTxHasSpace */
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 3 );
    /* <-pxTCPWindowTx_GetTXQueue */
    /* -->xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment2 );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    xTaskGetTickCount_ExpectAndReturn( 32 );

    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_NOT_NULL( xWindow.pxHeadSegment );
    TEST_ASSERT_EQUAL( 567, ulReturn );
}

void ignore_test_ulTCPWindowTxGet_segment_not_null( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    TCPSegment_t mockSegment2 = { 0 };
    uint32_t ulWindowSize = 23;
    int32_t lPosition = 0;
    ListItem_t mockListItem;

    initializeList( &xWindow.xWaitQueue );

    initializeListItem( &mockListItem );
    initializeListItem( &mockSegment.xQueueItem );
    initializeListItem( &mockSegment2.xQueueItem );

    mockSegment.xQueueItem.pvContainer = NULL;
    mockSegment.u.bits.ucTransmitCount = 7;
    mockSegment.xTransmitTimer.uxBorn = 2;
    xWindow.lSRTT = 0;
    xWindow.usMSS = 10;

    mockSegment2.xQueueItem = mockListItem;
    mockSegment2.xQueueItem.pvContainer = NULL;

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* -->ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 23 );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* -->xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment2 );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* ulTCPWindowTxGet */
    /* -> vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 32 );

    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_EQUAL( 360, ulReturn );
    TEST_ASSERT_EQUAL( 32, mockSegment.xTransmitTimer.uxBorn );
}

void test_ulTCPWindowTxGet_segment_null( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 23;
    int32_t lPosition = 0;

    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;

    mockSegment.xQueueItem.pvContainer = NULL;
    mockSegment.u.bits.ucTransmitCount = 1;
    mockSegment.xTransmitTimer.uxBorn = 2;
    xWindow.lSRTT = 6;
    xWindow.usMSS = 10;

    /* ->xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* ->pxTCPWindowTx_GetWaitQueue */
    /* -->xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* -->ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 2 );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* <ulTCPWindowTxGet */
    /* ->pxTCPWindowTX_GetTxQueue */
    /* -->xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_EQUAL( 0, ulReturn );
    TEST_ASSERT_EQUAL( 2, mockSegment.xTransmitTimer.uxBorn );
}

/* covering more cases in pxTCPWindowTx_GetWaitQueue */
void test_ulTCPWindowTxGet_segment_not_null_2( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 23;
    int32_t lPosition = 0;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    List_t xQueueList;

    initializeList( &xWindow.xWaitQueue );
    initializeListItem( &mockListItem );

    xTCPWindowLoggingLevel = 2;

    mockSegment.xQueueItem.pvContainer = NULL;

    mockSegment.u.bits.ucTransmitCount = 3U;
    mockSegment.xTransmitTimer.uxBorn = 2;
    xWindow.lSRTT = 2;
    xWindow.usMSS = 10;
    xWindow.xSize.ulTxWindowLength = ( xWindow.usMSS * 2 ) + 10;
    xWindow.pxHeadSegment = &mockSegment;

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* -->ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 23000 );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* -->xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* ulTCPWindowTxGet */
    /* -> vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 32 );



    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_EQUAL( 0, ulReturn );
    TEST_ASSERT_EQUAL( 32, mockSegment.xTransmitTimer.uxBorn );

    xTCPWindowLoggingLevel = xBackup;
}

/* covering more cases in ulTCPWindowTxGet */
void test_ulTCPWindowTxGet_segment_not_null_3( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    uint32_t ulWindowSize = 23;
    int32_t lPosition = 0;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    List_t xQueueList;

    xTCPWindowLoggingLevel = 0;

    mockSegment.xQueueItem.pvContainer = NULL;

    mockSegment.u.bits.ucTransmitCount = 3U;
    mockSegment.xTransmitTimer.uxBorn = 2;
    xWindow.lSRTT = 2;
    xWindow.usMSS = 10;
    xWindow.xSize.ulTxWindowLength = ( xWindow.usMSS * 2 ) - 10;
    xWindow.pxHeadSegment = &mockSegment;

    initializeList( &xWindow.xWaitQueue );
    initializeListItem( &mockListItem );

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* --> xTCPWindowPeekHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* -->ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 23000 );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* -->xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> pxTCPWindowTx_GetWaitQueue */
    /* ulTCPWindowTxGet */
    /* -> vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 32 );



    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_EQUAL( 0, ulReturn );
    TEST_ASSERT_EQUAL( 32, mockSegment.xTransmitTimer.uxBorn );
    xTCPWindowLoggingLevel = xBackup;
}

/* covering more cases in ulTCPWindowTxGet */
void test_ulTCPWindowTxGet_segment_not_null_4( void )
{
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    uint32_t ulWindowSize = 23;
    int32_t lPosition = 0;

    ListItem_t mockListItem;
    List_t xQueueList;

    mockSegment.xQueueItem.pvContainer = NULL;

    mockSegment.u.bits.ucTransmitCount = 3U;
    mockSegment.xTransmitTimer.uxBorn = 2;
    xWindow.lSRTT = 2;
    xWindow.usMSS = 10;
    xWindow.xSize.ulTxWindowLength = ( xWindow.usMSS * 2 ) - 10;
    xWindow.pxHeadSegment = &mockSegment;

    initializeList( &xWindow.xWaitQueue );
    initializeListItem( &mockListItem );

    /* -> xTCPWindowGetHead */
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_HEAD_ENTRY_ExpectAnyArgsAndReturn( &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* -> vTCPTimerSet */
    xTaskGetTickCount_ExpectAndReturn( 32 );



    ulReturn = ulTCPWindowTxGet( &xWindow,
                                 ulWindowSize,
                                 &lPosition );
    TEST_ASSERT_EQUAL( 0, ulReturn );
    TEST_ASSERT_EQUAL( 32, mockSegment.xTransmitTimer.uxBorn );
}


void test_ulTCPWindowTxAck_curr_seq_gt_seq( void )
{
    uint32_t ulSequenceNumber = 0;
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };

    xWindow.tx.ulCurrentSequenceNumber = 32;

    ulReturn = ulTCPWindowTxAck( &xWindow, ulSequenceNumber );

    TEST_ASSERT_EQUAL( 0, ulReturn );
}

void test_ulTCPWindowTxAck_curr_seq_lt_seq_no_list_items( void )
{
    uint32_t ulSequenceNumber = 56;
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };

    xWindow.tx.ulCurrentSequenceNumber = 32;
    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xTxSegments.xListEnd );

    ulReturn = ulTCPWindowTxAck( &xWindow, ulSequenceNumber );

    TEST_ASSERT_EQUAL( 0, ulReturn );
}

/* covering code inside prvTCPWindowTxCheckAck */
void test_ulTCPWindowTxAck_curr_seq_lt_seq_2( void )
{
    uint32_t ulSequenceNumber = 56;
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    ListItem_t mockNextListItem;

    xWindow.tx.ulCurrentSequenceNumber = 32;
    mockSegment.ulSequenceNumber = 45;
    mockSegment.u.bits.bAcked = pdFALSE_UNSIGNED;
    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( &mockNextListItem );

    ulReturn = ulTCPWindowTxAck( &xWindow, ulSequenceNumber );

    TEST_ASSERT_EQUAL( 0, ulReturn );
}

/* covering code inside prvTCPWindowTxCheckAck */
void test_ulTCPWindowTxAck_curr_seq_lt_seq_3_continue_loop( void )
{
    uint32_t ulSequenceNumber = 56;
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;

    xWindow.tx.ulCurrentSequenceNumber = 32;
    mockSegment.ulSequenceNumber = 31;
    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xTxSegments.xListEnd );

    ulReturn = ulTCPWindowTxAck( &xWindow, ulSequenceNumber );

    TEST_ASSERT_EQUAL( 0, ulReturn );
}

/* covering code inside prvTCPWindowTxCheckAck */
void test_ulTCPWindowTxAck_curr_seq_lt_seq_4( void )
{
    uint32_t ulSequenceNumber = 56;
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    ListItem_t mockNextListItem;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    xTCPWindowLoggingLevel = 2;
    xWindow.tx.ulCurrentSequenceNumber = 32;
    mockSegment.ulSequenceNumber = 32;
    mockSegment.u.bits.bAcked = pdTRUE_UNSIGNED;
    mockSegment.lDataLength = 2000;
    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( &mockNextListItem );

    ulReturn = ulTCPWindowTxAck( &xWindow, ulSequenceNumber );

    TEST_ASSERT_EQUAL( 2000, ulReturn );

    xTCPWindowLoggingLevel = xBackup;
}

/* covering code inside prvTCPWindowTxCheckAck */
void test_ulTCPWindowTxAck_curr_seq_lt_seq_4_acked_false( void )
{
    uint32_t ulSequenceNumber = 56;
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    ListItem_t mockNextListItem;

    xWindow.tx.ulCurrentSequenceNumber = 32;
    mockSegment.ulSequenceNumber = 32;
    mockSegment.u.bits.bAcked = pdFALSE_UNSIGNED;
    mockSegment.lDataLength = 2000;
    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( &mockNextListItem );

    ulReturn = ulTCPWindowTxAck( &xWindow, ulSequenceNumber );

    TEST_ASSERT_EQUAL( 0, ulReturn );
}

/* covering code inside prvTCPWindowTxCheckAck */
void test_ulTCPWindowTxAck_curr_seq_lt_seq_5_acked_false( void )
{
    uint32_t ulSequenceNumber = 56;
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;

    xWindow.tx.ulCurrentSequenceNumber = 32;
    mockSegment.ulSequenceNumber = 32;
    mockSegment.u.bits.bAcked = pdFALSE_UNSIGNED;
    mockSegment.lDataLength = 20;
    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xTxSegments.xListEnd );

    ulReturn = ulTCPWindowTxAck( &xWindow, ulSequenceNumber );

    TEST_ASSERT_EQUAL( 20, ulReturn );
}

/* covering code inside prvTCPWindowTxCheckAck */
void test_ulTCPWindowTxAck_curr_seq_lt_seq_6_acked_false( void )
{
    uint32_t ulSequenceNumber = 56;
    uint32_t ulReturn;
    TCPWindow_t xWindow = { 0 };
    TCPSegment_t mockSegment = { 0 };
    ListItem_t mockListItem;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    xWindow.tx.ulCurrentSequenceNumber = 32;
    mockSegment.ulSequenceNumber = 32;
    mockSegment.u.bits.bAcked = pdFALSE_UNSIGNED;
    mockSegment.lDataLength = 20;
    xTCPWindowLoggingLevel = 0;

    mockSegment.u.bits.ucTransmitCount = 1U;
    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xTxSegments.xListEnd );

    ulReturn = ulTCPWindowTxAck( &xWindow, ulSequenceNumber );

    TEST_ASSERT_EQUAL( 20, ulReturn );

    xTCPWindowLoggingLevel = xBackup;
}

/* covering code inside prvTCPWindowTxCheckAck */
void ignore_test_ulTCPWindowTxAck_curr_seq_lt_seq_7_acked_false( void )
{
    uint32_t ulSequenceNumber = 56;
    uint32_t ulReturn;
    TCPWindow_t xWindow;
    TCPSegment_t mockSegment;
    ListItem_t mockListItem;

    initializeListItem( &mockListItem );

    xWindow.tx.ulCurrentSequenceNumber = 32;
    mockSegment.u.bits.bAcked = pdFALSE_UNSIGNED;
    mockSegment.lDataLength = 24;

    mockSegment.u.bits.ucTransmitCount = 1U;
    mockSegment.ulSequenceNumber = 32;
    mockListItem.pxContainer = &xWindow.xPriorityQueue;
    mockSegment.xQueueItem = mockListItem;
    mockSegment.xQueueItem.pxContainer = &xWindow.xPriorityQueue;

    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xTxSegments.xListEnd );
    /* -->prvTCPWindowTxCheckAck_CalcSRTT */
    /* --->ulTimerGetAge */
    /* -->prvTCPWindowTxCheckAck_CalcSRTT */
    /* ->prvTCPWindowTxCheckAck */
    xTaskGetTickCount_ExpectAndReturn( 3000 );
    /* -->vTCPWindowFree */
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* ->prvTCPWindowTxCheckAck */
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );

    ulReturn = ulTCPWindowTxAck( &xWindow, ulSequenceNumber );

    TEST_ASSERT_EQUAL( 24, ulReturn );
}

void test_ulTCPWindowTxSack( void )
{
    uint32_t ulAckCount;
    TCPWindow_t xWindow;
    uint32_t ulFirst = 33;
    uint32_t ulLast = 63;
    TCPSegment_t mockSegment;
    ListItem_t mockListItem;

    initializeListItem( &mockListItem );

    xWindow.tx.ulCurrentSequenceNumber = 32;
    xWindow.lSRTT = ipconfigTCP_SRTT_MINIMUM_VALUE_MS - 3;
    mockSegment.u.bits.bAcked = pdFALSE_UNSIGNED;
    mockSegment.lDataLength = 30;

    mockSegment.u.bits.ucTransmitCount = 1U;
    mockSegment.ulSequenceNumber = 33;
    mockListItem.pxContainer = &xWindow.xPriorityQueue;
    mockSegment.xQueueItem = mockListItem;
    mockSegment.xQueueItem.pxContainer = &xWindow.xPriorityQueue;

    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xTxSegments.xListEnd );
    /* -->prvTCPWindowTxCheckAck_CalcSRTT */
    /* --->ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 23 );
    /* -->prvTCPWindowTxCheckAck_CalcSRTT */
    /* ->prvTCPWindowTxCheckAck */
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    /* ulTCPWindowTxSack */
    /* ->prvTCPWindowFastRetransmit */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xWaitQueue.xListEnd );

    ulAckCount = ulTCPWindowTxSack( &xWindow,
                                    ulFirst,
                                    ulLast );
    TEST_ASSERT_EQUAL( 0, ulAckCount );
    TEST_ASSERT_EQUAL( ipconfigTCP_SRTT_MINIMUM_VALUE_MS, xWindow.lSRTT );
}


void test_ulTCPWindowTxSack_prvTCPWindowFastRetransmit_1( void )
{
    uint32_t ulAckCount;
    TCPWindow_t xWindow;
    uint32_t ulFirst = 33;
    uint32_t ulLast = 63;
    TCPSegment_t mockSegment;
    ListItem_t mockListItem;

    initializeListItem( &mockListItem );

    xWindow.tx.ulCurrentSequenceNumber = 32;
    xWindow.lSRTT = ipconfigTCP_SRTT_MINIMUM_VALUE_MS + 30;
    mockSegment.u.bits.bAcked = pdFALSE_UNSIGNED;
    mockSegment.lDataLength = 30;

    mockSegment.u.bits.ucTransmitCount = 1U;
    mockSegment.ulSequenceNumber = 33;
    mockListItem.pxContainer = &xWindow.xPriorityQueue;
    mockSegment.xQueueItem = mockListItem;
    mockSegment.xQueueItem.pxContainer = NULL;
    mockSegment.u.bits.ucDupAckCount = 1U;

    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xTxSegments.xListEnd );
    /* -->prvTCPWindowTxCheckAck_CalcSRTT */
    /* --->ulTimerGetAge */
    xTaskGetTickCount_ExpectAndReturn( 69 );
    /* <--prvTCPWindowTxCheckAck_CalcSRTT */
    /* <-prvTCPWindowTxCheckAck */
    /* ulTCPWindowTxSack */
    /* ->prvTCPWindowFastRetransmit */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* exit the loop */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xWaitQueue.xListEnd );

    ulAckCount = ulTCPWindowTxSack( &xWindow,
                                    ulFirst,
                                    ulLast );
    TEST_ASSERT_EQUAL( 0, ulAckCount );
    TEST_ASSERT_EQUAL( 65, xWindow.lSRTT );
}

void test_ulTCPWindowTxSack_prvTCPWindowFastRetransmit_2( void )
{
    uint32_t ulAckCount;
    TCPWindow_t xWindow;
    uint32_t ulFirst = 33;
    uint32_t ulLast = 63;
    TCPSegment_t mockSegment;
    ListItem_t mockListItem;

    initializeListItem( &mockListItem );

    xWindow.tx.ulCurrentSequenceNumber = 32;
    mockSegment.u.bits.bAcked = pdFALSE_UNSIGNED;
    mockSegment.lDataLength = 30;

    mockSegment.u.bits.ucTransmitCount = 1U;
    mockSegment.ulSequenceNumber = 33;
    mockListItem.pxContainer = &xWindow.xPriorityQueue;
    mockSegment.xQueueItem = mockListItem;
    mockSegment.xQueueItem.pxContainer = NULL;
    mockSegment.u.bits.ucDupAckCount = 1U;

    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xTxSegments.xListEnd );
    /* ulTCPWindowTxSack */
    /* ->prvTCPWindowFastRetransmit */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* exit the loop */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xWaitQueue.xListEnd );

    ulAckCount = ulTCPWindowTxSack( &xWindow,
                                    ulFirst,
                                    ulLast );
    TEST_ASSERT_EQUAL( 0, ulAckCount );
}

void test_ulTCPWindowTxSack_prvTCPWindowFastRetransmit_3( void )
{
    uint32_t ulAckCount;
    TCPWindow_t xWindow;
    uint32_t ulFirst = 33;
    uint32_t ulLast = 63;
    TCPSegment_t mockSegment;
    ListItem_t mockListItem;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    initializeListItem( &mockListItem );

    xTCPWindowLoggingLevel = 3;
    xWindow.tx.ulCurrentSequenceNumber = 32;
    mockSegment.u.bits.bAcked = pdFALSE_UNSIGNED;
    mockSegment.lDataLength = 30;

    mockSegment.u.bits.ucTransmitCount = 1U;
    mockSegment.ulSequenceNumber = 31;
    mockListItem.pxContainer = &xWindow.xPriorityQueue;
    mockSegment.xQueueItem = mockListItem;
    mockSegment.xQueueItem.pxContainer = NULL;
    mockSegment.u.bits.ucDupAckCount = 1U;

    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xTxSegments.xListEnd );
    /* ulTCPWindowTxSack */
    /* ->prvTCPWindowFastRetransmit */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* exit the loop */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xWaitQueue.xListEnd );

    ulAckCount = ulTCPWindowTxSack( &xWindow,
                                    ulFirst,
                                    ulLast );
    TEST_ASSERT_EQUAL( 0, ulAckCount );

    xTCPWindowLoggingLevel = xBackup;
}

void test_ulTCPWindowTxSack_prvTCPWindowFastRetransmit_LoggingGTZero( void )
{
    uint32_t ulAckCount;
    TCPWindow_t xWindow;
    uint32_t ulFirst = 33;
    uint32_t ulLast = 63;
    TCPSegment_t mockSegment;
    ListItem_t mockListItem;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    initializeListItem( &mockListItem );
    initializeList( &xWindow.xPriorityQueue );

    xTCPWindowLoggingLevel = 0;
    xWindow.tx.ulCurrentSequenceNumber = 32;
    mockSegment.u.bits.bAcked = pdFALSE_UNSIGNED;
    mockSegment.lDataLength = 30;

    mockSegment.u.bits.ucTransmitCount = 1U;
    mockSegment.ulSequenceNumber = 31;
    mockListItem.pxContainer = &xWindow.xPriorityQueue;
    mockSegment.xQueueItem = mockListItem;
    mockSegment.xQueueItem.pxContainer = NULL;
    mockSegment.u.bits.ucDupAckCount = 2U;

    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xTxSegments.xListEnd );
    /* ulTCPWindowTxSack */
    /* ->prvTCPWindowFastRetransmit */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* exit the loop */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xWaitQueue.xListEnd );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );

    ulAckCount = ulTCPWindowTxSack( &xWindow,
                                    ulFirst,
                                    ulLast );
    TEST_ASSERT_EQUAL( 0, ulAckCount );

    xTCPWindowLoggingLevel = xBackup;
}

void test_ulTCPWindowTxSack_prvTCPWindowFastRetransmit_4_LoggingLTZero( void )
{
    uint32_t ulAckCount;
    TCPWindow_t xWindow;
    uint32_t ulFirst = 33;
    uint32_t ulLast = 63;
    TCPSegment_t mockSegment;
    ListItem_t mockListItem;
    BaseType_t xBackup = xTCPWindowLoggingLevel;

    xTCPWindowLoggingLevel = -1;

    initializeListItem( &mockListItem );
    initializeList( &xWindow.xPriorityQueue );

    xWindow.tx.ulCurrentSequenceNumber = 32;
    mockSegment.u.bits.bAcked = pdFALSE_UNSIGNED;
    mockSegment.lDataLength = 30;

    mockSegment.u.bits.ucTransmitCount = 1U;
    mockSegment.ulSequenceNumber = 31;
    mockListItem.pxContainer = &xWindow.xPriorityQueue;
    mockSegment.xQueueItem = mockListItem;
    mockSegment.xQueueItem.pxContainer = NULL;
    mockSegment.u.bits.ucDupAckCount = 2U;

    /* ->prvTCPWindowTxCheckAck */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xTxSegments.xListEnd );
    /* ulTCPWindowTxSack */
    /* ->prvTCPWindowFastRetransmit */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &mockListItem );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &mockSegment );
    /* exit the loop */
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) &xWindow.xWaitQueue.xListEnd );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );

    ulAckCount = ulTCPWindowTxSack( &xWindow,
                                    ulFirst,
                                    ulLast );
    TEST_ASSERT_EQUAL( 0, ulAckCount );

    xTCPWindowLoggingLevel = xBackup;
}
