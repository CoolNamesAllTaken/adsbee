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

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_task.h"
#include "mock_queue.h"
#include "mock_portable.h"

#include "FreeRTOS_DNS_Callback.h"

#include "mock_list.h"
#include "mock_Sockets_list_macros.h"

#include "mock_FreeRTOS_DNS_Parser.h"
#include "mock_NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#define LLMNR_ADDRESS     "freertos"
#define GOOD_ADDRESS      "www.freertos.org"
#define BAD_ADDRESS       "this is a bad address"
#define DOTTED_ADDRESS    "192.268.0.1"

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                struct freertos_addrinfo * /* pxAddressInfo */ );

/* ===========================   GLOBAL VARIABLES =========================== */
static int callback_called = 0;

/* The second element is for the flexible array member
 * /* when pvPortMalloc is mocked to return this object.
 */
static DNSCallback_t dnsCallback[ 2 ];

/* ===========================  STATIC FUNCTIONS  =========================== */
static void dns_callback( const char * pcName,
                          void * pvSearchID,
                          struct freertos_addrinfo * pxAddressInfo )
{
    callback_called = 1;
}

/* ============================  TEST FIXTURES  ============================= */

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
    vListInitialise_ExpectAnyArgs();
    vDNSCallbackInitialise();
    callback_called = 0;
    memset( dnsCallback, 0x00, sizeof( dnsCallback ) );
}

/**
 * @brief calls at the end of each test case
 */
void tearDown( void )
{
}

/* =============================  TEST CASES  =============================== */

/**
 * @brief Happy Path identifier passed is not found!
 */
void test_xDNSDoCallback_success_not_equal_identifier( void )
{
    BaseType_t ret;
    ParseSet_t pxSet;
    struct freertos_addrinfo pxAddress;
    DNSMessage_t xDNSMessageHeader;

    pxSet.pxDNSMessageHeader = &xDNSMessageHeader;
    pxSet.pxDNSMessageHeader->usIdentifier = 123;
    char pc_name[] = "test";
    strcpy( pxSet.pcName, pc_name );

    listGET_LIST_ITEM_OWNER_IgnoreAndReturn( ( DNSCallback_t * ) 1234 );
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) 4 ); /* xEnd */
    vTaskSuspendAll_Expect();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 );

    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 12345 );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 4 );

    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    ret = xDNSDoCallback( &pxSet, &pxAddress );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief Happy Path!
 */
void test_xDNSDoCallback_success_equal_identifier( void )
{
    BaseType_t ret;
    ParseSet_t pxSet;
    struct freertos_addrinfo pxAddress;
    DNSMessage_t xDNSMessageHeader;

    pxSet.pxDNSMessageHeader = &xDNSMessageHeader;
    pxSet.pxDNSMessageHeader->usIdentifier = 123;
    char pc_name[] = "test";
    strcpy( pxSet.pcName, pc_name );

    dnsCallback->pCallbackFunction = dns_callback;

    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) 4 );

    vTaskSuspendAll_Expect();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 );

    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 123 );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    vPortFree_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );

    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    ret = xDNSDoCallback( &pxSet, &pxAddress );
    TEST_ASSERT_EQUAL( pdTRUE, ret );
    TEST_ASSERT_EQUAL( 1, callback_called );
}

/**
 * @brief Happy Path!
 */
void test_xDNSDoCallback_success_equal_identifier_set_timer( void )
{
    BaseType_t ret;
    ParseSet_t pxSet;
    struct freertos_addrinfo pxAddress;
    DNSMessage_t xDNSMessageHeader;

    pxSet.pxDNSMessageHeader = &xDNSMessageHeader;
    pxSet.pxDNSMessageHeader->usIdentifier = 123;
    char pc_name[] = "test";
    strcpy( pxSet.pcName, pc_name );
    dnsCallback->pCallbackFunction = dns_callback;

    /* Expectations */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) 4 );
    vTaskSuspendAll_Expect();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 );

    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( 123 );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    vPortFree_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );

    vIPSetDNSTimerEnableState_ExpectAnyArgs();

    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    /* API Call */
    ret = xDNSDoCallback( &pxSet, &pxAddress );

    /* Validations */
    TEST_ASSERT_EQUAL( pdTRUE, ret );
    TEST_ASSERT_EQUAL( 1, callback_called );
}

/**
 * @brief Happy Path!
 */
void test_xDNSSetCallBack_success( void )
{
    void * pvSearchID = NULL;
    BaseType_t xReturn;

    /* Expectations */
    pvPortMalloc_ExpectAnyArgsAndReturn( dnsCallback );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    vTaskSetTimeOutState_ExpectAnyArgs();
    listSET_LIST_ITEM_OWNER_ExpectAnyArgs();
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vTaskSuspendAll_Expect();
    vListInsertEnd_ExpectAnyArgs();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    /* API Call */
    xReturn = xDNSSetCallBack( "hostname", pvSearchID, dns_callback, 56, 123, pdFALSE );

    /* Validations */
    TEST_ASSERT_EQUAL( 0, strcmp( dnsCallback->pcName, "hostname" ) );
    TEST_ASSERT_EQUAL( dns_callback, dnsCallback->pCallbackFunction );
    TEST_ASSERT_EQUAL( pvSearchID, dnsCallback->pvSearchID );
    TEST_ASSERT_EQUAL( 56, dnsCallback->uxRemainingTime );
    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief Happy Path!
 */
void test_xDNSSetCallBack_success_empty_list( void )
{
    void * pvSearchID = NULL;
    BaseType_t xReturn;

    /* Expectations */
    pvPortMalloc_ExpectAnyArgsAndReturn( dnsCallback );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 0 );
    vDNSTimerReload_ExpectAnyArgs();
    vTaskSetTimeOutState_ExpectAnyArgs();
    listSET_LIST_ITEM_OWNER_ExpectAnyArgs();
    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    vTaskSuspendAll_Expect();
    vListInsertEnd_ExpectAnyArgs();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    /* API Call */
    xReturn = xDNSSetCallBack( "hostname", pvSearchID, dns_callback, 56, 123, pdFALSE );

    /* Validations */
    TEST_ASSERT_EQUAL( 0, strcmp( dnsCallback->pcName, "hostname" ) );
    TEST_ASSERT_EQUAL( dns_callback, dnsCallback->pCallbackFunction );
    TEST_ASSERT_EQUAL( pvSearchID, dnsCallback->pvSearchID );
    TEST_ASSERT_EQUAL( 56, dnsCallback->uxRemainingTime );
    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief Memory Allocation failed
 */
void test_xDNSSetCallBack_malloc_failed( void )
{
    void * pvSearchID = NULL;
    BaseType_t xReturn;

    /* Expectations */
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );

    /* API Call */
    xReturn = xDNSSetCallBack( "hostname", pvSearchID, dns_callback, 56, 123, pdFALSE );
    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}


/**
 * @brief Happy path
 */
void test_vDNSCheckCallback_success_search_id_not_null( void )
{
    void * pvSearchID = ( void * ) 456;

    dnsCallback->pvSearchID = pvSearchID;

    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 );
    vListInitialise_ExpectAnyArgs();
    vTaskSuspendAll_Expect();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 16 );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 ); /* end marker */
    uxListRemove_ExpectAnyArgsAndReturn( pdFALSE );
    vPortFree_ExpectAnyArgs();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    vIPSetDNSTimerEnableState_ExpectAnyArgs();

    /* API Call */
    vDNSCheckCallBack( pvSearchID );

    /* Validations */
}

/**
 * @brief Happy path with list non-empty at end.
 */
void test_vDNSCheckCallback_success_search_id_not_null_list_empty( void )
{
    void * pvSearchID = ( void * ) 456;

    dnsCallback->pvSearchID = pvSearchID;

    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 );
    vListInitialise_ExpectAnyArgs();
    vTaskSuspendAll_Expect();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 16 );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 ); /* end marker */
    uxListRemove_ExpectAnyArgsAndReturn( pdFALSE );
    vPortFree_ExpectAnyArgs();
    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );

    /* API Call */
    vDNSCheckCallBack( pvSearchID );

    /* Validations */
}

/**
 * @brief search id null
 */
void test_vDNSCheckCallback_success_search_id_null( void )
{
    void * pvSearchID = ( void * ) 456;

    dnsCallback->pvSearchID = pvSearchID;

    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 );
    vListInitialise_ExpectAnyArgs();
    vTaskSuspendAll_Expect();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 16 );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 ); /* end marker */

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    vIPSetDNSTimerEnableState_ExpectAnyArgs();

    /* API Call */
    vDNSCheckCallBack( NULL );

    /* Validations */
}

/**
 * @brief search id null
 */
void test_vDNSCheckCallback_success_search_id_null_timeout( void )
{
    List_t xTempList;
    void * pvSearchID = ( void * ) 456;

    dnsCallback->pvSearchID = pvSearchID;
    dnsCallback->xIsIPv6 = 0;
    dnsCallback->pCallbackFunction = dns_callback;

    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 );
    vListInitialise_ExpectAnyArgs();
    vTaskSuspendAll_Expect();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 16 );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 ); /* end marker */

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    vListInsertEnd_ExpectAnyArgs();

    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );

    listGET_END_MARKER_ExpectAnyArgsAndReturn( NULL );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 16 );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_NEXT_ExpectAnyArgsAndReturn( NULL ); /* end marker */
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    vPortFree_ExpectAnyArgs();

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    vIPSetDNSTimerEnableState_ExpectAnyArgs();

    /* API Call */
    vDNSCheckCallBack( NULL );

    /* Validations */
    TEST_ASSERT_EQUAL( 1, callback_called );
}

/**
 * @brief search id null same as the above function but calling IPv6
 *        sub-branch
 */
void test_vDNSCheckCallback_success_search_id_null_timeout_IPv6( void )
{
    List_t xTempList;
    void * pvSearchID = ( void * ) 456;

    dnsCallback->pvSearchID = pvSearchID;
    dnsCallback->xIsIPv6 = 1;
    dnsCallback->pCallbackFunction = dns_callback;

    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 );
    vListInitialise_ExpectAnyArgs();
    vTaskSuspendAll_Expect();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 16 );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 ); /* end marker */

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    vListInsertEnd_ExpectAnyArgs();

    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );

    listGET_END_MARKER_ExpectAnyArgsAndReturn( NULL );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 16 );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_NEXT_ExpectAnyArgsAndReturn( NULL ); /* end marker */
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    vPortFree_ExpectAnyArgs();

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    vIPSetDNSTimerEnableState_ExpectAnyArgs();

    /* API Call */
    vDNSCheckCallBack( NULL );

    /* Validations */
    TEST_ASSERT_EQUAL( 1, callback_called );
}

/**
 * @brief search id null same as the above function but hitting a different
 *        sub-branch
 */
void test_vDNSCheckCallback_success_search_id_null_timeout2( void )
{
    void * pvSearchID = ( void * ) 456;
    void * pvSearchID2 = ( void * ) 457;

    dnsCallback->pvSearchID = pvSearchID2;
    dnsCallback->xIsIPv6 = 0;
    dnsCallback->pCallbackFunction = dns_callback;

    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 );
    vListInitialise_ExpectAnyArgs();
    vTaskSuspendAll_Expect();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 16 );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 ); /* end marker */

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    vListInsertEnd_ExpectAnyArgs();

    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );

    listGET_END_MARKER_ExpectAnyArgsAndReturn( NULL );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 16 );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_NEXT_ExpectAnyArgsAndReturn( NULL ); /* end marker */
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    vPortFree_ExpectAnyArgs();

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    vIPSetDNSTimerEnableState_ExpectAnyArgs();

    /* API Call */
    vDNSCheckCallBack( pvSearchID );

    /* Validations */
    TEST_ASSERT_EQUAL( 1, callback_called );
}

/**
 * @brief search id null same as the above function but calling IPv6
 *        sub-branch
 */
void test_vDNSCheckCallback_success_search_id_null_timeout2_IPv6( void )
{
    void * pvSearchID = ( void * ) 456;
    void * pvSearchID2 = ( void * ) 457;

    dnsCallback->pvSearchID = pvSearchID2;
    dnsCallback->xIsIPv6 = 1;
    dnsCallback->pCallbackFunction = dns_callback;

    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 );
    vListInitialise_ExpectAnyArgs();
    vTaskSuspendAll_Expect();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 16 );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 8 ); /* end marker */

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    vListInsertEnd_ExpectAnyArgs();

    xTaskResumeAll_ExpectAndReturn( pdFALSE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );

    listGET_END_MARKER_ExpectAnyArgsAndReturn( NULL );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) 16 );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( dnsCallback );
    listGET_NEXT_ExpectAnyArgsAndReturn( NULL ); /* end marker */
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    vPortFree_ExpectAnyArgs();

    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    vIPSetDNSTimerEnableState_ExpectAnyArgs();

    /* API Call */
    vDNSCheckCallBack( pvSearchID );

    /* Validations */
    TEST_ASSERT_EQUAL( 1, callback_called );
}
