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
 * @file cellular_common_utest.c
 * @brief Unit tests for functions in cellular_common.h.
 */
#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include <limits.h>

#include "unity.h"

#include "cellular_config.h"
#include "cellular_config_defaults.h"

/* Include paths for public enums, structures, and macros. */
#include "cellular_platform.h"
#include "cellular_common_internal.h"
#include "cellular_types.h"

#include "mock_cellular_pkthandler_internal.h"
#include "mock_cellular_pktio_internal.h"

#define SIGNAL_QUALITY_CSQ_UNKNOWN                     ( 99 )
#define SIGNAL_QUALITY_CSQ_RSSI_MIN                    ( 0 )
#define SIGNAL_QUALITY_CSQ_RSSI_MAX                    ( 31 )
#define SIGNAL_QUALITY_CSQ_BER_MIN                     ( 0 )
#define SIGNAL_QUALITY_CSQ_BER_MAX                     ( 7 )
#define SIGNAL_QUALITY_CSQ_RSSI_BASE                   ( -113 )
#define SIGNAL_QUALITY_CSQ_RSSI_STEP                   ( 2 )

#define CELLULAR_URC_HANDLER_TABLE_SIZE                ( sizeof( CellularUrcHandlerTable ) / sizeof( CellularAtParseTokenMap_t ) )
#define CELLULAR_SRC_TOKEN_ERROR_TABLE_SIZE            ( sizeof( CellularSrcTokenErrorTable ) / sizeof( char * ) )
#define CELLULAR_SRC_TOKEN_SUCCESS_TABLE_SIZE          ( sizeof( CellularSrcTokenSuccessTable ) / sizeof( char * ) )
#define CELLULAR_URC_TOKEN_WO_PREFIX_TABLE_SIZE        ( sizeof( CellularUrcTokenWoPrefixTable ) / sizeof( char * ) )
#define CELLULAR_SRC_EXTRA_TOKEN_SUCCESS_TABLE_SIZE    ( sizeof( CellularSrcExtraTokenSuccessTable ) / sizeof( char * ) )

/**
 * @brief Parameters in Signal Bars Look up table for measuring Signal Bars.
 */
typedef struct signalBarsTable
{
    int8_t upperThreshold;
    uint8_t bars;
} signalBarsTable_t;

static int mallocAllocFail = 0;

static int mockPlatformMutexCreateFlag = 0;

static int eventData = 0;

static char * pData;

CellularHandle_t gCellularHandle = NULL;

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

/* Look up table is maintained here as global scope within this file instead of
 * block scope to help developers to convert BER value. */
/* coverity[misra_c_2012_rule_8_9_violation] */
static const uint16_t rxEqualValueToBerTable[] =
{
    14,  /* Assumed value 0.14%. */
    28,  /* Assumed value 0.28%.*/
    57,  /* Assumed value 0.57%. */
    113, /* Assumed value 1.13%. */
    226, /* Assumed value 2.26%. */
    453, /* Assumed value 4.53%. */
    905, /* Assumed value 9.05%. */
    1810 /* Assumed value 18.10%. */
};

/* Look up Table for Mapping Signal Bars with RSSI value in dBm of GSM Signal.
 * The upper RSSI threshold is maintained in decreasing order to return the signal Bars. */

/* Look up table is maintained here as global scope within this file instead of
 * block scope to help developers to quickly change the RSRP Upper thresholds
 * for respective Bars. */
/* coverity[misra_c_2012_rule_8_9_violation] */
static const signalBarsTable_t gsmSignalBarsTable[] =
{
    { -104, 1 },
    { -98,  2 },
    { -89,  3 },
    { -80,  4 },
    { 0,    5 },
};

/* Look up Table for Mapping Signal Bars with RSRP value in dBm of LTE CAT M1 Signal.
 * The upper RSRP threshold is maintained in decreasing order to return the signal Bars. */

/* Look up table is maintained here as global scope within this file instead of
 * block scope to help developers to quickly change the RSRP Upper thresholds
 * for respective Bars. */
/* coverity[misra_c_2012_rule_8_9_violation] */
static const signalBarsTable_t lteCATMSignalBarsTable[] =
{
    { -115, 1 },
    { -105, 2 },
    { -95,  3 },
    { -85,  4 },
    { 0,    5 },
};

/* Look up Table for Mapping Signal Bars with RSRP value in dBm of LTE CAT NB1 Signal.
 * The upper RSRP threshold is maintained in decreasing order to return the signal Bars. */

/* Look up table is maintained here as global scope within this file instead of
 * block scope to help developers to quickly change the RSRP Upper thresholds
 * for respective Bars. */
/* coverity[misra_c_2012_rule_8_9_violation] */
static const signalBarsTable_t lteNBIotSignalBarsTable[] =
{
    { -115, 1 },
    { -105, 2 },
    { -95,  3 },
    { -85,  4 },
    { 0,    5 },
};

static CellularCommInterfaceError_t _prvCommIntfOpen( CellularCommInterfaceReceiveCallback_t receiveCallback,
                                                      void * pUserData,
                                                      CellularCommInterfaceHandle_t * pCommInterfaceHandle );

static CellularCommInterfaceError_t _prvCommIntfSend( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                      const uint8_t * pData,
                                                      uint32_t dataLength,
                                                      uint32_t timeoutMilliseconds,
                                                      uint32_t * pDataSentLength );

static CellularCommInterfaceError_t _prvCommIntfReceive( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                         uint8_t * pBuffer,
                                                         uint32_t bufferLength,
                                                         uint32_t timeoutMilliseconds,
                                                         uint32_t * pDataReceivedLength );

static CellularCommInterfaceError_t _prvCommIntfClose( CellularCommInterfaceHandle_t commInterfaceHandle );

static CellularCommInterface_t CellularCommInterface;
/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    mallocAllocFail = 0;
    eventData = 0;
    mockPlatformMutexCreateFlag = 0;
    CellularCommInterface.open = _prvCommIntfOpen;
    CellularCommInterface.send = _prvCommIntfSend;
    CellularCommInterface.recv = _prvCommIntfReceive;
    CellularCommInterface.close = _prvCommIntfClose;
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

void dummyTaskENTER_CRITICAL( void )
{
}

void dummyTaskEXIT_CRITICAL( void )
{
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

void cellularUrcNetworkRegistrationCallback( CellularUrcEvent_t urcEvent,
                                             const CellularServiceStatus_t * pServiceStatus,
                                             void * pCallbackContext )
{
    ( void ) pServiceStatus;
    ( void ) pCallbackContext;
    eventData = urcEvent;
}

void cellularUrcPdnEventCallback( CellularUrcEvent_t urcEvent,
                                  uint8_t contextId,
                                  void * pCallbackContext )
{
    ( void ) contextId;
    ( void ) pCallbackContext;
    eventData = urcEvent;
}

void cellularUrcSignalStrengthChangedCallback( CellularUrcEvent_t urcEvent,
                                               const CellularSignalInfo_t * pSignalInfo,
                                               void * pCallbackContext )
{
    ( void ) pSignalInfo;
    ( void ) pCallbackContext;
    eventData = urcEvent;
}

void cellularUrcGenericCallback( const char * pRawData,
                                 void * pCallbackContext )
{
    int len;

    ( void ) pCallbackContext;

    if( strlen( pRawData ) > 0 )
    {
        len = strlen( pRawData ) + 1;
        pData = ( char * ) malloc( sizeof( char ) * len );
        strcpy( pData, pRawData );
    }
}

void cellularModemEventCallback( CellularModemEvent_t modemEvent,
                                 void * pCallbackContext )
{
    ( void ) pCallbackContext;
    eventData = modemEvent;
}

CellularPktStatus_t cellularUndefinedRespCallback( void * pCallbackContext,
                                                   const char * pLine )
{
    ( void ) pLine;
    ( void ) pCallbackContext;
    return CELLULAR_PKT_STATUS_OK;
}

void * mock_malloc( size_t size )
{
    if( mallocAllocFail == 1 )
    {
        return NULL;
    }

    return malloc( size );
}

bool MockPlatformMutex_Create( PlatformMutex_t * pNewMutex,
                               bool recursive )
{
    bool ret = false;

    ( void ) recursive;

    if( ( mockPlatformMutexCreateFlag & 0xFF ) > 0 )
    {
        ret = true;
    }

    mockPlatformMutexCreateFlag = mockPlatformMutexCreateFlag >> 8;
    pNewMutex->created = ret;
    return ret;
}

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


static CellularPktStatus_t prvDummyInputBufferCallback( void * pInputBufferCallbackContext,
                                                        char * pBuffer,
                                                        uint32_t bufferLength,
                                                        uint32_t * pBufferLengthHandled )
{
    ( void ) pInputBufferCallbackContext;
    ( void ) pBuffer;
    ( void ) bufferLength;
    ( void ) pBufferLengthHandled;

    return CELLULAR_PKT_STATUS_OK;
}

/* ========================================================================== */

/**
 * @brief Test that null context case for _Cellular_CheckLibraryStatus.
 */
void test__Cellular_CheckLibraryStatus_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_CheckLibraryStatus( NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that library not open case for _Cellular_CheckLibraryStatus.
 */
void test__Cellular_CheckLibraryStatus_Library_Not_Open( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    cellularStatus = _Cellular_CheckLibraryStatus( &context );

    TEST_ASSERT_EQUAL( CELLULAR_LIBRARY_NOT_OPEN, cellularStatus );
}

/**
 * @brief Test that library shutdown case for _Cellular_CheckLibraryStatus.
 */
void test__Cellular_CheckLibraryStatus_Library_Shutdown( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.bLibOpened = true;
    context.bLibShutdown = true;
    cellularStatus = _Cellular_CheckLibraryStatus( &context );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that library closing case for _Cellular_CheckLibraryStatus.
 */
void test__Cellular_CheckLibraryStatus_Library_Closing( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.bLibOpened = true;
    context.bLibClosing = true;
    cellularStatus = _Cellular_CheckLibraryStatus( &context );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that library happy path case for _Cellular_CheckLibraryStatus.
 */
void test__Cellular_CheckLibraryStatus_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.bLibOpened = true;
    cellularStatus = _Cellular_CheckLibraryStatus( &context );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that each status case for _Cellular_TranslatePktStatus.
 */
void test__Cellular_TranslatePktStatus_Each_Case( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_TranslatePktStatus( CELLULAR_PKT_STATUS_OK );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );

    cellularStatus = _Cellular_TranslatePktStatus( CELLULAR_PKT_STATUS_TIMED_OUT );
    TEST_ASSERT_EQUAL( CELLULAR_TIMEOUT, cellularStatus );

    cellularStatus = _Cellular_TranslatePktStatus( CELLULAR_PKT_STATUS_FAILURE );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that each status case for _Cellular_TranslateAtCoreStatus.
 */
void test__Cellular_TranslateAtCoreStatus_Each_Case( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    pktStatus = _Cellular_TranslateAtCoreStatus( CELLULAR_AT_SUCCESS );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    pktStatus = _Cellular_TranslateAtCoreStatus( CELLULAR_AT_BAD_PARAMETER );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );

    pktStatus = _Cellular_TranslateAtCoreStatus( CELLULAR_AT_NO_MEMORY );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );
}

/**
 * @brief Test that memory allocation failure case for _Cellular_CreateSocketData.
 */
void test__Cellular_CreateSocketData_Mem_Alloc_Fail( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;
    CellularSocketHandle_t socketHandle;

    mallocAllocFail = 1;
    memset( &context, 0, sizeof( CellularContext_t ) );
    cellularStatus = _Cellular_CreateSocketData( &context, 0, CELLULAR_SOCKET_DOMAIN_AF_INET,
                                                 CELLULAR_SOCKET_TYPE_DGRAM,
                                                 CELLULAR_SOCKET_PROTOCOL_TCP,
                                                 &socketHandle );
    TEST_ASSERT_EQUAL( CELLULAR_NO_MEMORY, cellularStatus );
}

/**
 * @brief Test that no socket data entry case for _Cellular_CreateSocketData.
 */
void test__Cellular_CreateSocketData_No_Socket_Data_Entry_Fail( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;
    CellularSocketHandle_t socketHandle;
    uint32_t i = 0;

    memset( &context, 0, sizeof( CellularContext_t ) );

    for( i = 0; i < CELLULAR_NUM_SOCKET_MAX; i++ )
    {
        context.pSocketData[ i ] = malloc( sizeof( CellularSocketContext_t ) );
    }

    cellularStatus = _Cellular_CreateSocketData( &context, 0, CELLULAR_SOCKET_DOMAIN_AF_INET,
                                                 CELLULAR_SOCKET_TYPE_DGRAM,
                                                 CELLULAR_SOCKET_PROTOCOL_TCP,
                                                 &socketHandle );
    TEST_ASSERT_EQUAL( CELLULAR_NO_MEMORY, cellularStatus );
}

/**
 * @brief Test that happy path case for _Cellular_CreateSocketData.
 */
void test__Cellular_CreateSocketData_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;
    CellularSocketHandle_t socketHandle;

    memset( &context, 0, sizeof( CellularContext_t ) );
    cellularStatus = _Cellular_CreateSocketData( &context, 0, CELLULAR_SOCKET_DOMAIN_AF_INET,
                                                 CELLULAR_SOCKET_TYPE_DGRAM,
                                                 CELLULAR_SOCKET_PROTOCOL_TCP,
                                                 &socketHandle );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null context case for _Cellular_RemoveSocketData.
 */
void test__Cellular_RemoveSocketData_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularSocketContext_t socketContext;
    CellularSocketHandle_t socketHandle = &socketContext;

    cellularStatus = _Cellular_RemoveSocketData( NULL,
                                                 socketHandle );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that no match socketHandle case for _Cellular_RemoveSocketData.
 */
void test__Cellular_RemoveSocketData_No_Match_SocketHandle( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;
    CellularSocketContext_t socketContext;
    CellularSocketHandle_t socketHandle = &socketContext;
    uint32_t i = 0;

    memset( &context, 0, sizeof( CellularContext_t ) );

    for( i = 0; i < CELLULAR_NUM_SOCKET_MAX; i++ )
    {
        context.pSocketData[ i ] = malloc( sizeof( CellularSocketContext_t ) );
    }

    cellularStatus = _Cellular_RemoveSocketData( &context,
                                                 socketHandle );

    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that happy path case for _Cellular_RemoveSocketData.
 */
void test__Cellular_RemoveSocketData_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;
    CellularSocketHandle_t socketHandle;
    int i = rand() % CELLULAR_NUM_SOCKET_MAX;

    memset( &context, 0, sizeof( CellularContext_t ) );
    socketHandle = malloc( sizeof( CellularSocketContext_t ) );
    context.pSocketData[ i ] = socketHandle;

    cellularStatus = _Cellular_RemoveSocketData( &context,
                                                 socketHandle );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null context case for _Cellular_IsValidSocket.
 */
void test__Cellular_IsValidSocket_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_IsValidSocket( NULL,
                                              0 );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that bad socket Index parameter case for _Cellular_IsValidSocket.
 */
void test__Cellular_IsValidSocket_Bad_SocketIndex_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    cellularStatus = _Cellular_IsValidSocket( &context,
                                              CELLULAR_NUM_SOCKET_MAX );

    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that bad socket parameter case for _Cellular_IsValidSocket.
 */
void test__Cellular_IsValidSocket_Bad_Socket_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    cellularStatus = _Cellular_IsValidSocket( &context,
                                              0 );

    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that happy path case for _Cellular_IsValidSocket.
 */
void test__Cellular_IsValidSocket_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;
    int i = rand() % CELLULAR_NUM_SOCKET_MAX;

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pSocketData[ i ] = malloc( sizeof( CellularSocketContext_t ) );
    cellularStatus = _Cellular_IsValidSocket( &context,
                                              i );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    free( context.pSocketData[ i ] );
}

/**
 * @brief Test that out of upper bound contextId case for _Cellular_IsValidPdn.
 */
void test__Cellular_IsValidPdn_Bad_Upper_Bound_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_IsValidPdn( CELLULAR_PDN_CONTEXT_ID_MAX + 1 );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that out of lower bound contextId case for _Cellular_IsValidPdn.
 */
void test__Cellular_IsValidPdn_Bad_Lower_Bound_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_IsValidPdn( CELLULAR_PDN_CONTEXT_ID_MIN - 1 );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that happy path case for _Cellular_IsValidPdn.
 */
void test__Cellular_IsValidPdn_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    int i = rand() % CELLULAR_PDN_CONTEXT_ID_MAX;

    i = i > 0 ? i : i + 1;

    cellularStatus = _Cellular_IsValidPdn( i );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that Rssi Value case for _Cellular_ConvertCsqSignalRssi.
 */
void test__Cellular_ConvertCsqSignalRssi_Bad_Rssi_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_ConvertCsqSignalRssi( 0, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that Csq Rssi case for _Cellular_ConvertCsqSignalRssi.
 */
void test__Cellular_ConvertCsqSignalRssi_Bad_CsqRssi_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    int16_t rssiValue;

    cellularStatus = _Cellular_ConvertCsqSignalRssi( SIGNAL_QUALITY_CSQ_RSSI_MAX + 1, &rssiValue );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    cellularStatus = _Cellular_ConvertCsqSignalRssi( SIGNAL_QUALITY_CSQ_RSSI_MIN - 1, &rssiValue );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that CSQ_UNKNOWN case for _Cellular_ConvertCsqSignalRssi.
 */
void test__Cellular_ConvertCsqSignalRssi_CSQ_UNKNOWN( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    int16_t rssiValue;

    cellularStatus = _Cellular_ConvertCsqSignalRssi( SIGNAL_QUALITY_CSQ_UNKNOWN, &rssiValue );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_SIGNAL_VALUE, rssiValue );
}

/**
 * @brief Test that happy path case for _Cellular_ConvertCsqSignalRssi.
 */
void test__Cellular_ConvertCsqSignalRssi_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    int16_t rssiValue;
    int16_t csqRssi = SIGNAL_QUALITY_CSQ_RSSI_MAX - 1;

    cellularStatus = _Cellular_ConvertCsqSignalRssi( SIGNAL_QUALITY_CSQ_RSSI_MAX - 1, &rssiValue );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( SIGNAL_QUALITY_CSQ_RSSI_BASE + ( csqRssi * SIGNAL_QUALITY_CSQ_RSSI_STEP ), rssiValue );
}

/**
 * @brief Test that Ber Value null case for _Cellular_ConvertCsqSignalBer.
 */
void test__Cellular_ConvertCsqSignalBer_Bad_BerValue_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_ConvertCsqSignalBer( 0, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that Ber Value case for _Cellular_ConvertCsqSignalBer.
 */
void test__Cellular_ConvertCsqSignalBer_Bad_CsqRssi_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    int16_t berValue;

    cellularStatus = _Cellular_ConvertCsqSignalBer( SIGNAL_QUALITY_CSQ_BER_MAX + 1, &berValue );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    cellularStatus = _Cellular_ConvertCsqSignalBer( SIGNAL_QUALITY_CSQ_BER_MIN - 1, &berValue );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that invalid csqBer case for _Cellular_ConvertCsqSignalBer.
 */
void test__Cellular_ConvertCsqSignalBer_Invalid_CsqBer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    int16_t berValue;

    cellularStatus = _Cellular_ConvertCsqSignalBer( SIGNAL_QUALITY_CSQ_UNKNOWN, &berValue );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_SIGNAL_VALUE, berValue );
}

/**
 * @brief Test that happy path case for _Cellular_ConvertCsqSignalBer.
 */
void test__Cellular_ConvertCsqSignalBer_Happy( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    int16_t berValue;
    int csqBer = rand() % SIGNAL_QUALITY_CSQ_BER_MAX;

    cellularStatus = _Cellular_ConvertCsqSignalBer( csqBer, &berValue );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( rxEqualValueToBerTable[ csqBer ], berValue );
}

/**
 * @brief Test that null context case for _Cellular_GetModuleContext.
 */
void test__Cellular_GetModuleContext_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_GetModuleContext( NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for _Cellular_GetModuleContext.
 */
void test__Cellular_GetModuleContext_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;
    int32_t moduleContext;
    int32_t * pModuleContext;

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pModuleContext = &moduleContext;
    cellularStatus = _Cellular_GetModuleContext( &context, ( void ** ) &pModuleContext );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( pModuleContext, context.pModuleContext );
}

/**
 * @brief Test that null signal info case for _Cellular_ComputeSignalBars.
 */
void test__Cellular_ComputeSignalBars_Null_SignalInfo( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_ComputeSignalBars( 0, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that unknown rat (Radio Access Technologies case for _Cellular_ComputeSignalBars.
 */
void test__Cellular_ComputeSignalBars_Unknow_Rat( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularSignalInfo_t signalInfo;

    cellularStatus = _Cellular_ComputeSignalBars( CELLULAR_RAT_WCDMA, &signalInfo );

    TEST_ASSERT_EQUAL( CELLULAR_UNKNOWN, cellularStatus );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_SIGNAL_BAR_VALUE, signalInfo.bars );
}

/**
 * @brief Test that greater rat (Radio Access Technologies case for _Cellular_ComputeSignalBars.
 */
void test__Cellular_ComputeSignalBars_Greater_Than_Bar( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularSignalInfo_t signalInfo;
    signalBarsTable_t bigSignalBars = { 1, 0 };

    signalInfo.rssi = bigSignalBars.upperThreshold;
    cellularStatus = _Cellular_ComputeSignalBars( CELLULAR_RAT_GSM, &signalInfo );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_SIGNAL_BAR_VALUE, signalInfo.bars );
}

/**
 * @brief Test that GSM happy path case for _Cellular_ComputeSignalBars.
 */
void test__Cellular_ComputeSignalBars_GSM_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularSignalInfo_t signalInfo;

    signalInfo.rssi = gsmSignalBarsTable[ 0 ].upperThreshold;
    cellularStatus = _Cellular_ComputeSignalBars( CELLULAR_RAT_GSM, &signalInfo );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( gsmSignalBarsTable[ 0 ].bars, signalInfo.bars );
}

/**
 * @brief Test that EDGE happy path case for _Cellular_ComputeSignalBars.
 */
void test__Cellular_ComputeSignalBars_EDGE_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularSignalInfo_t signalInfo;

    signalInfo.rssi = gsmSignalBarsTable[ 0 ].upperThreshold;
    cellularStatus = _Cellular_ComputeSignalBars( CELLULAR_RAT_EDGE, &signalInfo );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( gsmSignalBarsTable[ 0 ].bars, signalInfo.bars );
}

/**
 * @brief Test that LTE happy path case for _Cellular_ComputeSignalBars.
 */
void test__Cellular_ComputeSignalBars_LTE_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularSignalInfo_t signalInfo;

    signalInfo.rsrp = lteCATMSignalBarsTable[ 0 ].upperThreshold;
    cellularStatus = _Cellular_ComputeSignalBars( CELLULAR_RAT_LTE, &signalInfo );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( lteCATMSignalBarsTable[ 0 ].bars, signalInfo.bars );
}

/**
 * @brief Test that CATM1 happy path case for _Cellular_ComputeSignalBars.
 */
void test__Cellular_ComputeSignalBars_CATM1_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularSignalInfo_t signalInfo;

    signalInfo.rsrp = lteCATMSignalBarsTable[ 0 ].upperThreshold;
    cellularStatus = _Cellular_ComputeSignalBars( CELLULAR_RAT_CATM1, &signalInfo );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( lteCATMSignalBarsTable[ 0 ].bars, signalInfo.bars );
}

/**
 * @brief Test that NBIOT happy path case for _Cellular_ComputeSignalBars.
 */
void test__Cellular_ComputeSignalBars_NBIOT_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularSignalInfo_t signalInfo;

    signalInfo.rsrp = lteNBIotSignalBarsTable[ 0 ].upperThreshold;
    cellularStatus = _Cellular_ComputeSignalBars( CELLULAR_RAT_NBIOT, &signalInfo );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( lteNBIotSignalBarsTable[ 0 ].bars, signalInfo.bars );
}

/**
 * @brief Test that null context case for _Cellular_GetCurrentRat.
 */
void test__Cellular_GetCurrentRat_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_GetCurrentRat( NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that null Rat case for _Cellular_GetCurrentRat.
 */
void test__Cellular_GetCurrentRat_Null_Rat( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.bLibOpened = true;

    cellularStatus = _Cellular_GetCurrentRat( &context, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that happy path case for _Cellular_GetCurrentRat.
 */
void test__Cellular_GetCurrentRat_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;
    CellularRat_t rat;

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.bLibOpened = true;
    context.libAtData.rat = CELLULAR_RAT_WCDMA;

    cellularStatus = _Cellular_GetCurrentRat( &context, &rat );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( CELLULAR_RAT_WCDMA, rat );
}

/**
 * @brief Test that null parameter case for _Cellular_NetworkRegistrationCallback.
 */
void test__Cellular_NetworkRegistrationCallback_Null_Parameter( void )
{
    CellularContext_t context;

    _Cellular_NetworkRegistrationCallback( NULL, CELLULAR_URC_SOCKET_OPENED, NULL );

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.cbEvents.networkRegistrationCallback = NULL;
    _Cellular_NetworkRegistrationCallback( &context, CELLULAR_URC_SOCKET_OPENED, NULL );
}

/**
 * @brief Test that happy path case for _Cellular_NetworkRegistrationCallback.
 */
void test__Cellular_NetworkRegistrationCallback_Happy_Path( void )
{
    CellularContext_t context;

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.cbEvents.networkRegistrationCallback = cellularUrcNetworkRegistrationCallback;
    _Cellular_NetworkRegistrationCallback( &context, CELLULAR_URC_SOCKET_OPENED, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_URC_SOCKET_OPENED, eventData );
}

/**
 * @brief Test that null parameter case for _Cellular_PdnEventCallback.
 */
void test__Cellular_PdnEventCallback_Null_Parameter( void )
{
    CellularContext_t context;

    _Cellular_PdnEventCallback( NULL, CELLULAR_URC_SOCKET_OPENED, 0U );

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.cbEvents.pdnEventCallback = NULL;
    _Cellular_PdnEventCallback( &context, CELLULAR_URC_SOCKET_OPENED, 0U );
}

/**
 * @brief Test that happy path case for _Cellular_PdnEventCallback.
 */
void test__Cellular_PdnEventCallback_Happy_Path( void )
{
    CellularContext_t context;

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.cbEvents.pdnEventCallback = cellularUrcPdnEventCallback;
    _Cellular_PdnEventCallback( &context, CELLULAR_URC_SOCKET_OPENED, 0U );

    TEST_ASSERT_EQUAL( CELLULAR_URC_SOCKET_OPENED, eventData );
}

/**
 * @brief Test that null parameter case for _Cellular_SignalStrengthChangedCallback.
 */
void test__Cellular_SignalStrengthChangedCallback_Null_Parameter( void )
{
    CellularContext_t context;

    _Cellular_SignalStrengthChangedCallback( NULL, CELLULAR_URC_SOCKET_OPENED, NULL );

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.cbEvents.signalStrengthChangedCallback = NULL;
    _Cellular_SignalStrengthChangedCallback( &context, CELLULAR_URC_SOCKET_OPENED, NULL );
}

/**
 * @brief Test that happy path case for _Cellular_SignalStrengthChangedCallback.
 */
void test__Cellular_SignalStrengthChangedCallback_Happy_Path( void )
{
    CellularContext_t context;

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.cbEvents.signalStrengthChangedCallback = cellularUrcSignalStrengthChangedCallback;
    _Cellular_SignalStrengthChangedCallback( &context, CELLULAR_URC_SOCKET_OPENED, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_URC_SOCKET_OPENED, eventData );
}

/**
 * @brief Test that null parameter case for _Cellular_GenericCallback.
 */
void test__Cellular_GenericCallback_Null_Parameter( void )
{
    CellularContext_t context;
    const char pRawData[] = "cellularUrcGenericCallback test.";

    _Cellular_GenericCallback( NULL, pRawData );

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.cbEvents.genericCallback = NULL;
    _Cellular_GenericCallback( &context, pRawData );
}

/**
 * @brief Test that happy path case for _Cellular_GenericCallback.
 */
void test__Cellular_GenericCallback_Happy_Path( void )
{
    CellularContext_t context;
    const char pRawData[] = "cellularUrcGenericCallback test.";

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.cbEvents.genericCallback = cellularUrcGenericCallback;
    _Cellular_GenericCallback( &context, pRawData );

    TEST_ASSERT_EQUAL( strcmp( pRawData, pData ), 0 );
    free( pData );
}

/**
 * @brief Test that null parameter case for _Cellular_ModemEventCallback.
 */

void test__Cellular_ModemEventCallback_Null_Parameter( void )
{
    CellularContext_t context;

    _Cellular_ModemEventCallback( NULL, CELLULAR_MODEM_EVENT_POWERED_DOWN );

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.cbEvents.modemEventCallback = NULL;
    _Cellular_ModemEventCallback( &context, CELLULAR_MODEM_EVENT_POWERED_DOWN );
}

/**
 * @brief Test that happy path case for _Cellular_ModemEventCallback.
 */
void test__Cellular_ModemEventCallback_Happy_Path( void )
{
    CellularContext_t context;

    memset( &context, 0, sizeof( struct CellularContext ) );
    context.cbEvents.modemEventCallback = cellularModemEventCallback;
    _Cellular_ModemEventCallback( &context, CELLULAR_MODEM_EVENT_POWERED_DOWN );

    TEST_ASSERT_EQUAL( CELLULAR_MODEM_EVENT_POWERED_DOWN, eventData );
}

/**
 * @brief Test that null context case for _Cellular_GetSocketData.
 */
void test__Cellular_GetSocketData_Null_Context( void )
{
    CellularSocketContext_t * pSocketData = NULL;

    pSocketData = _Cellular_GetSocketData( NULL, 0 );
    TEST_ASSERT_EQUAL( NULL, pSocketData );
}

/**
 * @brief Test that out of range socket id case for _Cellular_GetSocketData.
 */
void test__Cellular_GetSocketData_Upper_Bound_SocketId( void )
{
    CellularSocketContext_t * pSocketData = NULL;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    pSocketData = _Cellular_GetSocketData( &context, CELLULAR_NUM_SOCKET_MAX );
    TEST_ASSERT_EQUAL( NULL, pSocketData );
}

/**
 * @brief Test that null socket data case for _Cellular_GetSocketData.
 */
void test__Cellular_GetSocketData_Null_SocketData( void )
{
    CellularSocketContext_t * pSocketData = NULL;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    pSocketData = _Cellular_GetSocketData( &context, 0 );
    TEST_ASSERT_EQUAL( NULL, pSocketData );
}

/**
 * @brief Test that happy path case for _Cellular_GetSocketData.
 */
void test__Cellular_GetSocketData_Happy_Path( void )
{
    CellularSocketContext_t * pSocketData = NULL;
    CellularContext_t context;
    uint32_t i = rand() % CELLULAR_NUM_SOCKET_MAX;

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pSocketData[ i ] = malloc( sizeof( CellularSocketContext_t ) );

    pSocketData = _Cellular_GetSocketData( &context, i );
    TEST_ASSERT_EQUAL( context.pSocketData[ i ], pSocketData );
    free( context.pSocketData[ i ] );
}

/**
 * @brief Test that null context case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_LibInit( NULL, NULL, NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that null comm interface member case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_Null_CommInterface_Member( void )
{
    CellularHandle_t CellularHandle = NULL;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_LibInit( &CellularHandle, NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    CellularCommInterface.recv = NULL;
    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    CellularCommInterface.send = NULL;
    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    CellularCommInterface.close = NULL;
    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    CellularCommInterface.open = NULL;
    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that null token table case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_Null_Tabletoken_Member( void )
{
    CellularHandle_t CellularHandle = NULL;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularTokenTable_t tokenTableNoUrcTable =
    {
        .pCellularUrcHandlerTable      = NULL,
        .cellularPrefixToParserMapSize = CELLULAR_URC_HANDLER_TABLE_SIZE,
    };

    CellularTokenTable_t tokenTableNoErrorTable =
    {
        .pCellularUrcHandlerTable       = CellularUrcHandlerTable,
        .cellularPrefixToParserMapSize  = CELLULAR_URC_HANDLER_TABLE_SIZE,
        .pCellularSrcTokenErrorTable    = NULL,
        .cellularSrcTokenErrorTableSize = CELLULAR_SRC_TOKEN_ERROR_TABLE_SIZE
    };

    CellularTokenTable_t tokenTableNoSuccessTable =
    {
        .pCellularUrcHandlerTable         = CellularUrcHandlerTable,
        .cellularPrefixToParserMapSize    = CELLULAR_URC_HANDLER_TABLE_SIZE,
        .pCellularSrcTokenErrorTable      = CellularSrcTokenErrorTable,
        .cellularSrcTokenErrorTableSize   = CELLULAR_SRC_TOKEN_ERROR_TABLE_SIZE,
        .pCellularSrcTokenSuccessTable    = NULL,
        .cellularSrcTokenSuccessTableSize = CELLULAR_SRC_TOKEN_SUCCESS_TABLE_SIZE
    };

    CellularTokenTable_t tokenTableNoWoPrefixTable =
    {
        .pCellularUrcHandlerTable          = CellularUrcHandlerTable,
        .cellularPrefixToParserMapSize     = CELLULAR_URC_HANDLER_TABLE_SIZE,
        .pCellularSrcTokenErrorTable       = CellularSrcTokenErrorTable,
        .cellularSrcTokenErrorTableSize    = CELLULAR_SRC_TOKEN_ERROR_TABLE_SIZE,
        .pCellularSrcTokenSuccessTable     = CellularSrcTokenSuccessTable,
        .cellularSrcTokenSuccessTableSize  = CELLULAR_SRC_TOKEN_SUCCESS_TABLE_SIZE,
        .pCellularUrcTokenWoPrefixTable    = NULL,
        .cellularUrcTokenWoPrefixTableSize = CELLULAR_URC_TOKEN_WO_PREFIX_TABLE_SIZE
    };

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTableNoUrcTable );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTableNoErrorTable );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTableNoSuccessTable );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTableNoWoPrefixTable );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that memory allocation failure case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_Memory_Allocation_Failure( void )
{
    CellularHandle_t CellularHandle = NULL;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    mallocAllocFail = 1;

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTable );

    TEST_ASSERT_EQUAL( CELLULAR_NO_MEMORY, cellularStatus );
}

/**
 * @brief Test that CreateLibStatusMutex failure case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_CreateLibStatusMutex_Failure( void )
{
    CellularHandle_t CellularHandle = NULL;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTable );

    TEST_ASSERT_EQUAL( CELLULAR_RESOURCE_CREATION_FAIL, cellularStatus );
}

/**
 * @brief Test that _Cellular_CreateAtDataMutex failure case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_Cellular_CreateAtDataMutex_Failure( void )
{
    CellularHandle_t CellularHandle = NULL;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* Mock CreateLibStatusMutex work. */
    mockPlatformMutexCreateFlag = 1;

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTable );

    TEST_ASSERT_EQUAL( CELLULAR_RESOURCE_CREATION_FAIL, cellularStatus );
}

/**
 * @brief Test that _Cellular_CreatePktRequestMutex failure case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_Cellular_CreatePktRequestMutex_Failure( void )
{
    CellularHandle_t CellularHandle = NULL;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* Mock CreateLibStatusMutex and _Cellular_CreateAtDataMutex work. */
    mockPlatformMutexCreateFlag = 0x0101;
    _Cellular_CreatePktRequestMutex_IgnoreAndReturn( false );
    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTable );

    TEST_ASSERT_EQUAL( CELLULAR_RESOURCE_CREATION_FAIL, cellularStatus );
}

/**
 * @brief Test that _Cellular_CreatePktResponseMutex failure case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_Cellular_CreatePktResponseMutex_Failure( void )
{
    CellularHandle_t CellularHandle = NULL;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* Mock CreateLibStatusMutex, _Cellular_CreateAtDataMutex and _Cellular_CreatePktRequestMutex work. */
    mockPlatformMutexCreateFlag = 0x0101;
    _Cellular_CreatePktRequestMutex_IgnoreAndReturn( true );
    _Cellular_CreatePktResponseMutex_IgnoreAndReturn( false );
    _Cellular_DestroyPktResponseMutex_Ignore();
    _Cellular_DestroyPktRequestMutex_Ignore();

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTable );

    TEST_ASSERT_EQUAL( CELLULAR_RESOURCE_CREATION_FAIL, cellularStatus );
}

/**
 * @brief Test that pkio init failure case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_PkioInit_Failure( void )
{
    CellularHandle_t CellularHandle = NULL;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* Mock CreateLibStatusMutex, _Cellular_CreateAtDataMutex and _Cellular_CreatePktRequestMutex work. */
    mockPlatformMutexCreateFlag = 0x0101;
    _Cellular_CreatePktRequestMutex_IgnoreAndReturn( true );
    _Cellular_CreatePktResponseMutex_IgnoreAndReturn( true );
    _Cellular_AtParseInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_PktHandlerInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_PktioInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT );
    _Cellular_PktioShutdown_Ignore();
    _Cellular_PktHandlerCleanup_Ignore();
    _Cellular_DestroyPktResponseMutex_Ignore();
    _Cellular_DestroyPktRequestMutex_Ignore();

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTable );

    TEST_ASSERT_EQUAL( CELLULAR_TIMEOUT, cellularStatus );
}

/**
 * @brief Test that happy path case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_Happy_Path( void )
{
    CellularHandle_t CellularHandle = NULL;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* Mock CreateLibStatusMutex, _Cellular_CreateAtDataMutex and _Cellular_CreatePktRequestMutex work. */
    mockPlatformMutexCreateFlag = 0x0101;
    _Cellular_CreatePktRequestMutex_IgnoreAndReturn( true );
    _Cellular_CreatePktResponseMutex_IgnoreAndReturn( true );
    _Cellular_AtParseInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_PktHandlerInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_PktioInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTable );
    gCellularHandle = CellularHandle;
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null context case for _Cellular_LibCleanup.
 */
void test__Cellular_LibCleanup_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = _Cellular_LibCleanup( NULL );

    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for _Cellular_LibCleanup.
 */
void test__Cellular_LibCleanup_Happy_Path( void )
{
    CellularContext_t * pContext = ( CellularContext_t * ) gCellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    int i = rand() % CELLULAR_NUM_SOCKET_MAX;
    CellularSocketContext_t * pSocketData = ( CellularSocketContext_t * ) malloc( sizeof( CellularSocketContext_t ) );

    pContext->pSocketData[ i ] = pSocketData;

    _Cellular_PktioShutdown_Ignore();
    _Cellular_PktHandlerCleanup_Ignore();
    _Cellular_DestroyPktRequestMutex_Ignore();
    _Cellular_DestroyPktResponseMutex_Ignore();

    cellularStatus = _Cellular_LibCleanup( pContext );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that PktHandlerInit failure case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_PktHandlerInit_Fail( void )
{
    CellularHandle_t CellularHandle = NULL;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* Mock CreateLibStatusMutex, _Cellular_CreateAtDataMutex and _Cellular_CreatePktRequestMutex work. */
    mockPlatformMutexCreateFlag = 0x0101;
    _Cellular_CreatePktRequestMutex_IgnoreAndReturn( true );
    _Cellular_CreatePktResponseMutex_IgnoreAndReturn( true );
    _Cellular_AtParseInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_PktHandlerInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_DestroyPktResponseMutex_Ignore();
    _Cellular_DestroyPktRequestMutex_Ignore();

    cellularStatus = _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTable );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that no pktio shutdown case for _Cellular_LibCleanup.
 */
void test__Cellular_LibCleanup_No_Pktio_Shutdown( void )
{
    CellularContext_t * pContext = ( CellularContext_t * ) malloc( sizeof( struct CellularContext ) );
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    int i = rand() % CELLULAR_NUM_SOCKET_MAX;
    CellularSocketContext_t * pSocketData = ( CellularSocketContext_t * ) malloc( sizeof( CellularSocketContext_t ) );

    pContext->pSocketData[ i ] = pSocketData;
    pContext->bLibOpened = false;

    _Cellular_PktioShutdown_Ignore();
    _Cellular_PktHandlerCleanup_Ignore();
    _Cellular_DestroyPktRequestMutex_Ignore();
    _Cellular_DestroyPktResponseMutex_Ignore();

    cellularStatus = _Cellular_LibCleanup( pContext );

    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case for _shutdownCallback.
 */
void test__shutdownCallback_Happy_Path( void )
{
    CellularHandle_t CellularHandle = NULL;
    CellularContext_t * pContext;

    /* Mock CreateLibStatusMutex, _Cellular_CreateAtDataMutex and _Cellular_CreatePktRequestMutex work. */
    mockPlatformMutexCreateFlag = 0x0101;
    _Cellular_CreatePktRequestMutex_IgnoreAndReturn( true );
    _Cellular_CreatePktResponseMutex_IgnoreAndReturn( true );
    _Cellular_AtParseInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_PktHandlerInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_PktioInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    ( void ) _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTable );
    pContext = ( CellularContext_t * ) CellularHandle;
    pContext->pPktioShutdownCB( pContext );
    TEST_ASSERT_EQUAL( true, pContext->bLibShutdown );
}

/**
 * @brief Test that happy path case for _Cellular_AtcmdRequestWithCallback.
 */
void test__Cellular_AtcmdRequestWithCallback_Happy_Path( void )
{
    CellularAtReq_t atReqGetResult = { 0 };
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    _Cellular_PktHandler_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    pktStatus = _Cellular_AtcmdRequestWithCallback( &context, atReqGetResult );

    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test that double allocate context case for _Cellular_LibInit.
 */
void test__Cellular_LibInit_PktHandlerInit_Double_Allocate_Context( void )
{
    CellularHandle_t CellularHandle = NULL;

    /* Mock CreateLibStatusMutex, _Cellular_CreateAtDataMutex and _Cellular_CreatePktRequestMutex work. */
    mockPlatformMutexCreateFlag = 0x0101;
    _Cellular_CreatePktRequestMutex_IgnoreAndReturn( true );
    _Cellular_CreatePktResponseMutex_IgnoreAndReturn( true );
    _Cellular_AtParseInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_PktHandlerInit_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTable );
    CellularHandle = NULL;
    _Cellular_LibInit( &CellularHandle, &CellularCommInterface, &tokenTable );
}

/**
 * @brief Test that null parameter case for _Cellular_RegisterUndefinedRespCallback.
 */
void test__Cellular_RegisterUndefinedRespCallback_Null_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    int32_t customDefinedContext;

    /* Pass NULL cellular context pointer to _Cellular_RegisterUndefinedRespCallback. */
    cellularStatus = _Cellular_RegisterUndefinedRespCallback( NULL, cellularUndefinedRespCallback, &customDefinedContext );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case for _Cellular_RegisterUndefinedRespCallback.
 */
void test__Cellular_RegisterUndefinedRespCallback_Happy_Path( void )
{
    CellularContext_t context;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    int32_t customDefinedContext;

    /* Register the cellular undefined response callback. */
    cellularStatus = _Cellular_RegisterUndefinedRespCallback( &context, cellularUndefinedRespCallback, &customDefinedContext );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL_PTR( cellularUndefinedRespCallback, context.undefinedRespCallback );
    TEST_ASSERT_EQUAL_PTR( &customDefinedContext, context.pUndefinedRespCBContext );

    /* unregister the cellular undefined response callback. */
    cellularStatus = _Cellular_RegisterUndefinedRespCallback( &context, NULL, &customDefinedContext );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_NULL( context.undefinedRespCallback );
    /* Undefined callback context is cleared if the undefined callback is NULL. */
    TEST_ASSERT_NULL( context.pUndefinedRespCBContext );

    /* Register the cellular undefined response callback without callback context. */
    cellularStatus = _Cellular_RegisterUndefinedRespCallback( &context, cellularUndefinedRespCallback, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL_PTR( cellularUndefinedRespCallback, context.undefinedRespCallback );
    TEST_ASSERT_NULL( context.pUndefinedRespCBContext );

    /* unregister the cellular undefined response callback without callback context. */
    cellularStatus = _Cellular_RegisterUndefinedRespCallback( &context, NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_NULL( context.undefinedRespCallback );
    TEST_ASSERT_NULL( context.pUndefinedRespCBContext );
}

/**
 * @brief _Cellular_RegisterInputBufferCallback - parameter null context.
 * pContext parameter is NULL. Verify the return value.
 */
void test__Cellular_RegisterInputBufferCallback_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* API call. */
    cellularStatus = _Cellular_RegisterInputBufferCallback( NULL, NULL, NULL );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief _Cellular_RegisterInputBufferCallback - parameter NULL callback.
 * inputBufferCallback parameter is NULL. Verify the member variable is updated.
 */
void test__Cellular_RegisterInputBufferCallback_Null_Callback( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t cellularContext;
    uint32_t inputBufferCallbackContext;

    /* Setup internal variable. */
    memset( &cellularContext, 0, sizeof( CellularContext_t ) );
    cellularContext.inputBufferCallback = prvDummyInputBufferCallback;
    cellularContext.pInputBufferCallbackContext = &inputBufferCallbackContext;

    /* API call. */
    cellularStatus = _Cellular_RegisterInputBufferCallback( &cellularContext, NULL, &inputBufferCallbackContext );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( NULL, cellularContext.inputBufferCallback );
    /* The callback context will be cleaned when inputBufferCallback is NULL. */
    TEST_ASSERT_EQUAL( NULL, cellularContext.pInputBufferCallbackContext );
}

/**
 * @brief _Cellular_RegisterInputBufferCallback - Setup the URC data callback.
 * Verify the URC data callback and callback context are set correctly.
 */
void test__Cellular_RegisterInputBufferCallback_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t cellularContext;
    uint32_t inputBufferCallbackContext;

    /* Setup internal variable. */
    memset( &cellularContext, 0, sizeof( CellularContext_t ) );
    cellularContext.inputBufferCallback = NULL;

    /* API call. */
    cellularStatus = _Cellular_RegisterInputBufferCallback( &cellularContext, prvDummyInputBufferCallback, &inputBufferCallbackContext );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
    TEST_ASSERT_EQUAL( prvDummyInputBufferCallback, cellularContext.inputBufferCallback );
    TEST_ASSERT_EQUAL( &inputBufferCallbackContext, cellularContext.pInputBufferCallbackContext );
}
