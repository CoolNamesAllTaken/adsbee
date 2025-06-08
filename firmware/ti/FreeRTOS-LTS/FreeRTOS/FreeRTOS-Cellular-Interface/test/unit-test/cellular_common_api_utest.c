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
 * @file cellular_common_api_utest.c
 * @brief Unit tests for functions in cellular_common_api.h.
 */

#include <string.h>
#include <stdbool.h>

#include "unity.h"

#include "cellular_config.h"
#include "cellular_config_defaults.h"

/* Include paths for public enums, structures, and macros. */
#include "cellular_platform.h"
#include "cellular_common_internal.h"
#include "cellular_common_api.h"
#include "cellular_types.h"

#include "mock_cellular_common.h"
#include "mock_cellular_common_portable.h"


#define CELLULAR_URC_HANDLER_TABLE_SIZE                ( sizeof( CellularUrcHandlerTable ) / sizeof( CellularAtParseTokenMap_t ) )
#define CELLULAR_SRC_TOKEN_ERROR_TABLE_SIZE            ( sizeof( CellularSrcTokenErrorTable ) / sizeof( char * ) )
#define CELLULAR_SRC_TOKEN_SUCCESS_TABLE_SIZE          ( sizeof( CellularSrcTokenSuccessTable ) / sizeof( char * ) )
#define CELLULAR_URC_TOKEN_WO_PREFIX_TABLE_SIZE        ( sizeof( CellularUrcTokenWoPrefixTable ) / sizeof( char * ) )
#define CELLULAR_SRC_EXTRA_TOKEN_SUCCESS_TABLE_SIZE    ( sizeof( CellularSrcExtraTokenSuccessTable ) / sizeof( char * ) )

static int32_t queueCreateFail = 0;

CellularAtParseTokenMap_t CellularUrcHandlerTable[] =
{
    { "CEREG",             NULL },
    { "CGREG",             NULL },
    { "CREG",              NULL },
    { "NORMAL POWER DOWN", NULL },
    { "PSM POWER DOWN",    NULL },
    { "QIND",              NULL },
    { "QIOPEN",            NULL },
    { "QIURC",             NULL },
    { "QSIMSTAT",          NULL },
    { "RDY",               NULL }
};

const char * CellularSrcTokenErrorTable[] =
{ "ERROR", "BUSY", "NO CARRIER", "NO ANSWER", "NO DIALTONE", "ABORTED", "+CMS ERROR", "+CME ERROR", "SEND FAIL" };

const char * CellularSrcTokenSuccessTable[] =
{ "OK", "CONNECT", "SEND OK", ">" };

const char * CellularUrcTokenWoPrefixTable[] =
{ "NORMAL POWER DOWN", "PSM POWER DOWN", "RDY" };

const char * CellularSrcExtraTokenSuccessTable[] =
{ "EXTRA_TOKEN_1", "EXTRA_TOKEN_2", "EXTRA_TOKEN_3" };

static CellularTokenTable_t tokenTable =
{
    .pCellularUrcHandlerTable              = CellularUrcHandlerTable,
    .cellularPrefixToParserMapSize         = CELLULAR_URC_HANDLER_TABLE_SIZE,
    .pCellularSrcTokenErrorTable           = CellularSrcTokenErrorTable,
    .cellularSrcTokenErrorTableSize        = CELLULAR_SRC_TOKEN_ERROR_TABLE_SIZE,
    .pCellularSrcTokenSuccessTable         = CellularSrcTokenSuccessTable,
    .cellularSrcTokenSuccessTableSize      = CELLULAR_SRC_TOKEN_SUCCESS_TABLE_SIZE,
    .pCellularUrcTokenWoPrefixTable        = CellularUrcTokenWoPrefixTable,
    .cellularUrcTokenWoPrefixTableSize     = CELLULAR_URC_TOKEN_WO_PREFIX_TABLE_SIZE,
    .pCellularSrcExtraTokenSuccessTable    = CellularSrcExtraTokenSuccessTable,
    .cellularSrcExtraTokenSuccessTableSize = CELLULAR_SRC_EXTRA_TOKEN_SUCCESS_TABLE_SIZE
};

void cellularSocketDataReadyCallback( CellularSocketHandle_t socketHandle,
                                      void * pCallbackContext )
{
    ( void ) socketHandle;
    ( void ) pCallbackContext;
}

void cellularSocketOpenCallback( CellularUrcEvent_t urcEvent,
                                 CellularSocketHandle_t socketHandle,
                                 void * pCallbackContext )
{
    ( void ) urcEvent;
    ( void ) pCallbackContext;
    ( void ) socketHandle;
}

void cellularSocketClosedCallback( CellularSocketHandle_t socketHandle,
                                   void * pCallbackContext )
{
    ( void ) socketHandle;
    ( void ) pCallbackContext;
}

void testCallback( void )
{
}

void cellularUrcNetworkRegistrationCallback( CellularUrcEvent_t urcEvent,
                                             const CellularServiceStatus_t * pServiceStatus,
                                             void * pCallbackContext )
{
    ( void ) urcEvent;
    ( void ) pCallbackContext;
    ( void ) pServiceStatus;
}

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
}

/* Called after each test method. */
void tearDown()
{
}

/* Called at the beginning of the whole suite. */
void suiteSetUp()
{
}

/* Called at the end of the whole suite. */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

/* ========================================================================== */

void MockPlatformMutex_Unlock( PlatformMutex_t * pMutex )
{
    ( void ) pMutex;
}

void MockPlatformMutex_Lock( PlatformMutex_t * pMutex )
{
    ( void ) pMutex;
}

uint16_t MockvQueueDelete( QueueHandle_t queue )
{
    free( queue );
    queue = 0;
    return 1;
}

void MockPlatformMutex_Destroy( PlatformMutex_t * pMutex )
{
    pMutex->created = false;
}

QueueHandle_t MockxQueueCreate( int32_t uxQueueLength,
                                uint32_t uxItemSize )
{
    ( void ) uxQueueLength;
    ( void ) uxItemSize;

    if( queueCreateFail == 0 )
    {
        QueueHandle_t test = malloc( sizeof( struct QueueDefinition ) );
        return test;
    }
    else
    {
        return NULL;
    }
}

bool MockPlatformMutex_Create( PlatformMutex_t * pNewMutex,
                               bool recursive )
{
    ( void ) recursive;
    pNewMutex->created = true;
    return true;
}

static CellularCommInterfaceError_t _prvCommIntfOpen( CellularCommInterfaceReceiveCallback_t receiveCallback,
                                                      void * pUserData,
                                                      CellularCommInterfaceHandle_t * pCommInterfaceHandle )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    ( void ) receiveCallback;
    CellularContext_t * pContext = ( CellularContext_t * ) pUserData;

    ( void ) pCommInterfaceHandle;

    commIntRet = receiveCallback( pContext, NULL );

    return commIntRet;
}

static CellularCommInterfaceError_t _prvCommIntfClose( CellularCommInterfaceHandle_t commInterfaceHandle )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    ( void ) commInterfaceHandle;

    return commIntRet;
}

static CellularCommInterfaceError_t _prvCommIntfSend( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                      const uint8_t * pData,
                                                      uint32_t dataLength,
                                                      uint32_t timeoutMilliseconds,
                                                      uint32_t * pDataSentLength )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    ( void ) commInterfaceHandle;
    ( void ) pData;
    ( void ) dataLength;
    ( void ) timeoutMilliseconds;
    ( void ) pDataSentLength;

    *pDataSentLength = dataLength;

    return commIntRet;
}

static CellularCommInterfaceError_t _prvCommIntfReceive( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                         uint8_t * pBuffer,
                                                         uint32_t bufferLength,
                                                         uint32_t timeoutMilliseconds,
                                                         uint32_t * pDataReceivedLength )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    ( void ) commInterfaceHandle;
    ( void ) pBuffer;
    ( void ) bufferLength;
    ( void ) timeoutMilliseconds;
    ( void ) pDataReceivedLength;

    return commIntRet;
}

static CellularCommInterface_t cellularCommInterface =
{
    .open  = _prvCommIntfOpen,
    .send  = _prvCommIntfSend,
    .recv  = _prvCommIntfReceive,
    .close = _prvCommIntfClose
};


/* ========================================================================== */

/**
 * @brief Cellular_CommonInit - Test the null pCommInterface parameter.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( pCellularHandle == NULL )
 * {
 *     LogError( ( "Cellular_CommonInit pCellularHandle is NULL." ) );
 *     cellularStatus = CELLULAR_INVALID_HANDLE;
 * }
 * @endcode
 * ( pCellularHandle == NULL ) is true.
 */
void test_Cellular_CommonInit_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* API call. */
    cellularStatus = Cellular_CommonInit( NULL, &cellularCommInterface, &tokenTable );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Cellular_CommonInit - Test the null pCommInterface parameter.
 *
 * <b>Coverage</b>
 * @code{c}
 * else if( pCommInterface == NULL )
 * {
 *     LogError( ( "Cellular_CommonInit pCommInterface is NULL." ) );
 *     cellularStatus = CELLULAR_BAD_PARAMETER;
 * }
 * @endcode
 * ( pCommInterface == NULL ) is true.
 */
void test_Cellular_CommonInit_Null_Comm_Interface( void )
{
    struct CellularContext * pHandler;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* API call. */
    cellularStatus = Cellular_CommonInit( &pHandler, NULL, &tokenTable );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Cellular_CommonInit - Test the null pTokenTable parameter.
 *
 * <b>Coverage</b>
 * @code{c}
 * else if( pTokenTable == NULL )
 * {
 *     LogError( ( "Cellular_CommonInit pTokenTable is NULL." ) );
 *     cellularStatus = CELLULAR_BAD_PARAMETER;
 * }
 * @endcode
 * ( pTokenTable == NULL ) is true.
 */
void test_Cellular_CommonInit_Null_Token_Table( void )
{
    struct CellularContext * pHandler;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* API call. */
    cellularStatus = Cellular_CommonInit( &pHandler, &cellularCommInterface, NULL );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Cellular_CommonInit - Test that _Cellular_LibInit returns error.
 *
 * <b>Coverage</b>
 * @code{c}
 * cellularStatus = _Cellular_LibInit( pCellularHandle, pCommInterface, pTokenTable );
 * ...
 * if( cellularStatus == CELLULAR_SUCCESS )
 * {
 *     ...
 * }
 * @endcode
 * ( cellularStatus == CELLULAR_SUCCESS ) is false.
 */
void test_Cellular_CommonInit_Lib_Init_error( void )
{
    struct CellularContext * pHandler;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* Expectation. */
    _Cellular_LibInit_IgnoreAndReturn( CELLULAR_RESOURCE_CREATION_FAIL );

    /* API call. */
    cellularStatus = Cellular_CommonInit( &pHandler, &cellularCommInterface, &tokenTable );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_RESOURCE_CREATION_FAIL, cellularStatus );
}

/**
 * @brief Cellular_CommonInit - Test that Cellular_ModuleInit returns error.
 *
 * <b>Coverage</b>
 * @code{c}
 * cellularStatus = Cellular_ModuleInit( pContext, &pContext->pModuleContext );
 * ...
 * if( cellularStatus != CELLULAR_SUCCESS )
 * {
 *     ( void ) _Cellular_LibCleanup( pContext );
 * }
 * @endcode
 * ( cellularStatus != CELLULAR_SUCCESS ) is true.
 */
void test_Cellular_CommonInit_Module_Init_error( void )
{
    struct CellularContext xCellularContext = { 0 };
    struct CellularContext * pContext;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* Setup. */
    pContext = &xCellularContext;

    /* Expectation. */
    _Cellular_LibInit_IgnoreAndReturn( CELLULAR_SUCCESS );
    Cellular_ModuleInit_ExpectAndReturn( &xCellularContext, &xCellularContext.pModuleContext, CELLULAR_INTERNAL_FAILURE );
    _Cellular_LibCleanup_ExpectAndReturn( &xCellularContext, CELLULAR_SUCCESS );

    /* API call. */
    cellularStatus = Cellular_CommonInit( &pContext, &cellularCommInterface, &tokenTable );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Cellular_CommonInit - Test that Cellular_ModuleEnableUE returns error.
 *
 * <b>Coverage</b>
 * @code{c}
 * cellularStatus = Cellular_ModuleEnableUE( pContext );
 * if( cellularStatus == CELLULAR_SUCCESS )
 * {
 *     cellularStatus = Cellular_ModuleEnableUrc( pContext );
 * }
 * @endcode
 * ( cellularStatus == CELLULAR_SUCCESS ) is false.
 */
void test_Cellular_CommonInit_Module_Enable_UE_error( void )
{
    struct CellularContext xCellularContext = { 0 };
    struct CellularContext * pContext;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* Setup. */
    pContext = &xCellularContext;

    /* Expectation. */
    _Cellular_LibInit_IgnoreAndReturn( CELLULAR_SUCCESS );
    Cellular_ModuleInit_ExpectAndReturn( &xCellularContext, &xCellularContext.pModuleContext, CELLULAR_SUCCESS );
    Cellular_ModuleEnableUE_ExpectAndReturn( &xCellularContext, CELLULAR_INTERNAL_FAILURE );

    Cellular_ModuleCleanUp_ExpectAndReturn( &xCellularContext, CELLULAR_SUCCESS );
    _Cellular_LibCleanup_ExpectAndReturn( &xCellularContext, CELLULAR_SUCCESS );

    /* API call. */
    cellularStatus = Cellular_CommonInit( &pContext, &cellularCommInterface, &tokenTable );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Cellular_CommonInit - Test that Cellular_ModuleEnableUrc returns error.
 *
 * <b>Coverage</b>
 * @code{c}
 * ...
 *     cellularStatus = Cellular_ModuleEnableUrc( pContext );
 * ...
 * if( cellularStatus != CELLULAR_SUCCESS )
 * {
 *     cellularStatus = Cellular_ModuleCleanUp( pContext );
 * }
 * @endcode
 * ( cellularStatus != CELLULAR_SUCCESS ) is true.
 */
void test_Cellular_CommonInit_Module_Enable_URC_error( void )
{
    struct CellularContext xCellularContext = { 0 };
    struct CellularContext * pContext;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* Setup. */
    pContext = &xCellularContext;

    /* Expectation. */
    _Cellular_LibInit_IgnoreAndReturn( CELLULAR_SUCCESS );
    Cellular_ModuleInit_ExpectAndReturn( &xCellularContext, &xCellularContext.pModuleContext, CELLULAR_SUCCESS );
    Cellular_ModuleEnableUE_ExpectAndReturn( &xCellularContext, CELLULAR_SUCCESS );
    Cellular_ModuleEnableUrc_ExpectAndReturn( &xCellularContext, CELLULAR_INTERNAL_FAILURE );

    Cellular_ModuleCleanUp_ExpectAndReturn( &xCellularContext, CELLULAR_SUCCESS );
    _Cellular_LibCleanup_ExpectAndReturn( &xCellularContext, CELLULAR_SUCCESS );

    /* API call. */
    cellularStatus = Cellular_CommonInit( &pContext, &cellularCommInterface, &tokenTable );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonInit.
 */
void test_Cellular_CommonInit_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    struct CellularContext handler;

    _Cellular_LibInit_IgnoreAndReturn( CELLULAR_SUCCESS );

    Cellular_ModuleInit_IgnoreAndReturn( CELLULAR_SUCCESS );

    Cellular_ModuleEnableUE_IgnoreAndReturn( CELLULAR_SUCCESS );

    Cellular_ModuleEnableUrc_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonInit( ( CellularHandle_t * ) &handler, &cellularCommInterface, &tokenTable );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null handler case for Cellular_CommonCleanup.
 */
void test_Cellular_CommonCleanup_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_LibInit_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );

    cellularStatus = Cellular_CommonCleanup( NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonCleanup.
 */
void test_Cellular_CommonCleanup_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t handler = &context;

    Cellular_ModuleCleanUp_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_LibCleanup_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonCleanup( handler );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null handler case for Cellular_CommonRegisterUrcNetworkRegistrationEventCallback.
 */
void test_Cellular_CommonRegisterUrcNetworkRegistrationEventCallback_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );

    cellularStatus = Cellular_CommonRegisterUrcNetworkRegistrationEventCallback( NULL, NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonRegisterUrcNetworkRegistrationEventCallback.
 */
void test_Cellular_CommonRegisterUrcNetworkRegistrationEventCallback_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonRegisterUrcNetworkRegistrationEventCallback( ( CellularHandle_t ) &context, cellularUrcNetworkRegistrationCallback, testCallback );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( context.cbEvents.networkRegistrationCallback, cellularUrcNetworkRegistrationCallback );
    TEST_ASSERT_EQUAL( context.cbEvents.pNetworkRegistrationCallbackContext, testCallback );
}

/**
 * @brief Test that null handler case for Cellular_CommonRegisterUrcPdnEventCallback.
 */
void test_Cellular_CommonRegisterUrcPdnEventCallback_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );

    cellularStatus = Cellular_CommonRegisterUrcPdnEventCallback( NULL, NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonRegisterUrcPdnEventCallback.
 */
void test_Cellular_CommonRegisterUrcPdnEventCallback_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonRegisterUrcPdnEventCallback( ( CellularHandle_t ) &context, NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null handler case for Cellular_CommonRegisterUrcSignalStrengthChangedCallback.
 */
void test_Cellular_CommonRegisterUrcSignalStrengthChangedCallback_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );

    cellularStatus = Cellular_CommonRegisterUrcSignalStrengthChangedCallback( NULL, NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonRegisterUrcSignalStrengthChangedCallback.
 */
void test_Cellular_CommonRegisterUrcSignalStrengthChangedCallback_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonRegisterUrcSignalStrengthChangedCallback( ( CellularHandle_t ) &context, NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null handler case for Cellular_CommonRegisterUrcGenericCallback.
 */
void test_Cellular_CommonRegisterUrcGenericCallback_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );

    cellularStatus = Cellular_CommonRegisterUrcGenericCallback( NULL, NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonRegisterUrcGenericCallback.
 */
void test_Cellular_CommonRegisterUrcGenericCallback_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonRegisterUrcGenericCallback( ( CellularHandle_t ) &context, NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null handler case for Cellular_CommonRegisterModemEventCallback.
 */
void test_Cellular_CommonRegisterModemEventCallback_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );

    cellularStatus = Cellular_CommonRegisterModemEventCallback( NULL, NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonRegisterModemEventCallback.
 */
void test_Cellular_CommonRegisterModemEventCallback_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonRegisterModemEventCallback( ( CellularHandle_t ) &context, NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null handler case for Cellular_CommonATCommandRaw.
 */
void test_Cellular_CommonATCommandRaw_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );

    cellularStatus = Cellular_CommonATCommandRaw( NULL, NULL, NULL, 0, NULL, NULL, 0 );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that null at command payload case for Cellular_CommonATCommandRaw.
 */
void test_Cellular_CommonATCommandRaw_Null_AtCmdPayload( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonATCommandRaw( &context, NULL, NULL, 0, NULL, NULL, 0 );

    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that _Cellular_AtcmdRequestWithCallback return CELLULAR_PKT_STATUS_BAD_REQUEST case for Cellular_CommonATCommandRaw.
 */
void test_Cellular_CommonATCommandRaw_AtCmd_Bad_Request( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    char pPrefix[] = "AtTSest";
    char pData[] = "Test Data";

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_TimeoutAtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_REQUEST );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonATCommandRaw( &context, pPrefix, pData, 0, NULL, NULL, 0 );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonATCommandRaw.
 */
void test_Cellular_CommonATCommandRaw_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    char pPrefix[] = "AtTSest";
    char pData[] = "Test Data";

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_TimeoutAtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonATCommandRaw( &context, pPrefix, pData, 0, NULL, NULL, 0 );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null cellular handler case for Cellular_CommonCreateSocket.
 */
void test_Cellular_CommonCreateSocket_Null_CellularHandler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );

    cellularStatus = Cellular_CommonCreateSocket( NULL, 0, 0, 0, 0, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that null socket handler case for Cellular_CommonCreateSocket.
 */
void test_Cellular_CommonCreateSocket_Null_SocketHandler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonCreateSocket( &context, 0, 0, 0, 0, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that invalid context id case for Cellular_CommonCreateSocket.
 */
void test_Cellular_CommonCreateSocket_Invalid_ContextId( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_BAD_PARAMETER );

    cellularStatus = Cellular_CommonCreateSocket( &context, 0, 0, 0, 0, ( CellularSocketHandle_t * ) &socketHandle );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonCreateSocket.
 */
void test_Cellular_CommonCreateSocket_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_CreateSocketData_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonCreateSocket( &context, 0, 0, 0, 0, ( CellularSocketHandle_t * ) &socketHandle );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null socket handler case for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Null_SocketHandler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, NULL, 0, 0, 0, 0 );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that null parameter case for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_NULL_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;
    uint32_t optionValue = 0;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonSocketSetSockOpt( NULL, &socketHandle, 0, 0, NULL, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle, 0, 0, NULL, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle, 0, 0,
                                                      ( const uint8_t * ) &optionValue, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that option send timeout happy path case for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_SendTimeout_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;
    uint32_t optionValue = 0;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                      CELLULAR_SOCKET_OPTION_SEND_TIMEOUT,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that option send timeout failure path case for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_SendTimeout_Failure_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;
    uint32_t optionValue = 0;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                      CELLULAR_SOCKET_OPTION_SEND_TIMEOUT,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint32_t ) - 1 );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that option recv timeout happy path case for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_RecvTimeout_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;
    uint32_t optionValue = 0;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                      CELLULAR_SOCKET_OPTION_RECV_TIMEOUT,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that option recv timeout failure path case for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_RecvTimeout_Failure_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;
    uint32_t optionValue = 0;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                      CELLULAR_SOCKET_OPTION_RECV_TIMEOUT,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint32_t ) - 1 );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that option pdn context id happy path case for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_PdnContextId_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;
    uint32_t optionValue = 0;

    socketHandle.socketState = SOCKETSTATE_ALLOCATED;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                      CELLULAR_SOCKET_OPTION_PDN_CONTEXT_ID,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint8_t ) );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that option pdn context id failure path case for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_PdnContextId_Failure_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;
    uint32_t optionValue = 0;

    socketHandle.socketState = SOCKETSTATE_CONNECTING;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                      CELLULAR_SOCKET_OPTION_PDN_CONTEXT_ID,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint8_t ) );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that option pdn context id failure path case with wrong size for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_PdnContextId_WrongSize_Failure_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;
    uint32_t optionValue = 0;

    socketHandle.socketState = SOCKETSTATE_ALLOCATED;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                      CELLULAR_SOCKET_OPTION_PDN_CONTEXT_ID,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that option pdn context id failure path case for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_Unsupported_Failure_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;
    uint32_t optionValue = 0;

    socketHandle.socketState = SOCKETSTATE_CONNECTING;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                      CELLULAR_SOCKET_OPTION_SET_LOCAL_PORT + 1,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( CELLULAR_UNSUPPORTED, cellularStatus );
}

/**
 * @brief Test that option pdn context id failure path case for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_UnsupportedOption_Failure_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;
    uint32_t optionValue = 0;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_IP,
                                                      CELLULAR_SOCKET_OPTION_SEND_TIMEOUT,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( CELLULAR_UNSUPPORTED, cellularStatus );
}

/**
 * @brief Test that null handler case for Cellular_CommonSocketRegisterDataReadyCallback.
 */
void test_Cellular_CommonSocketRegisterDataReadyCallback_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );

    cellularStatus = Cellular_CommonSocketRegisterDataReadyCallback( NULL, NULL,
                                                                     NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that null socketHandle case for Cellular_CommonSocketRegisterDataReadyCallback.
 */
void test_Cellular_CommonSocketRegisterDataReadyCallback_Null_socketHandle( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketRegisterDataReadyCallback( &context, NULL,
                                                                     NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonSocketRegisterDataReadyCallback.
 */
void test_Cellular_CommonSocketRegisterDataReadyCallback_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketRegisterDataReadyCallback( &context, &socketHandle,
                                                                     cellularSocketDataReadyCallback,
                                                                     testCallback );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( socketHandle.dataReadyCallback, cellularSocketDataReadyCallback );
    TEST_ASSERT_EQUAL( socketHandle.pDataReadyCallbackContext, testCallback );
}

/**
 * @brief Test that null handler case for Cellular_CommonSocketRegisterSocketOpenCallback.
 */
void test_Cellular_CommonSocketRegisterSocketOpenCallback_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );

    cellularStatus = Cellular_CommonSocketRegisterSocketOpenCallback( NULL, NULL,
                                                                      NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that null socketHandle case for Cellular_CommonSocketRegisterSocketOpenCallback.
 */
void test_Cellular_CommonSocketRegisterSocketOpenCallback_Null_socketHandle( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketRegisterSocketOpenCallback( &context, NULL,
                                                                      NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonSocketRegisterSocketOpenCallback.
 */
void test_Cellular_CommonSocketRegisterSocketOpenCallback_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketRegisterSocketOpenCallback( &context, &socketHandle,
                                                                      cellularSocketOpenCallback,
                                                                      testCallback );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( socketHandle.openCallback, cellularSocketOpenCallback );
    TEST_ASSERT_EQUAL( socketHandle.pOpenCallbackContext, testCallback );
}

/**
 * @brief Test that null handler case for Cellular_CommonSocketRegisterClosedCallback.
 */
void test_Cellular_CommonSocketRegisterClosedCallback_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );

    cellularStatus = Cellular_CommonSocketRegisterClosedCallback( NULL, NULL,
                                                                  NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that null socketHandle case for Cellular_CommonSocketRegisterClosedCallback.
 */
void test_Cellular_CommonSocketRegisterClosedCallback_Null_socketHandle( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketRegisterClosedCallback( &context, NULL,
                                                                  NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for Cellular_CommonSocketRegisterClosedCallback.
 */
void test_Cellular_CommonSocketRegisterClosedCallback_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketRegisterClosedCallback( &context, &socketHandle,
                                                                  cellularSocketClosedCallback,
                                                                  testCallback );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( socketHandle.closedCallback, cellularSocketClosedCallback );
    TEST_ASSERT_EQUAL( socketHandle.pClosedCallbackContext, testCallback );
}

/**
 * @brief Test that option set local port happy path case for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_SetLocalPort_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle = { 0 };
    uint16_t optionValue = 12345;

    socketHandle.socketState = SOCKETSTATE_ALLOCATED;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                      CELLULAR_SOCKET_OPTION_SET_LOCAL_PORT,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint16_t ) );

    TEST_ASSERT_EQUAL( optionValue, socketHandle.localPort );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that option set local port at wrong socket state for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_SetLocalPort_Failure_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle = { 0 };
    uint16_t optionValue = 12345;

    socketHandle.socketState = SOCKETSTATE_CONNECTING;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                      CELLULAR_SOCKET_OPTION_SET_LOCAL_PORT,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint16_t ) );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
    TEST_ASSERT_EQUAL( 0, socketHandle.localPort );
}

/**
 * @brief Test that option set local port failure path case with wrong size for Cellular_CommonSocketSetSockOpt.
 */
void test_Cellular_CommonSocketSetSockOpt_Option_SetLocalPort_WrongSize_Failure_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    struct CellularSocketContext socketHandle = { 0 };
    uint16_t optionValue = 12345;

    socketHandle.socketState = SOCKETSTATE_ALLOCATED;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonSocketSetSockOpt( &context, &socketHandle,
                                                      CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                      CELLULAR_SOCKET_OPTION_SET_LOCAL_PORT,
                                                      ( const uint8_t * ) &optionValue, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
    TEST_ASSERT_EQUAL( 0, socketHandle.localPort );
}
