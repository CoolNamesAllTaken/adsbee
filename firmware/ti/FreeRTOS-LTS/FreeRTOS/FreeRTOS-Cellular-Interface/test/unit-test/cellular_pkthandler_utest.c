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
 * @file cellular_pkthandler_utest.c
 * @brief Unit tests for functions in cellular_pkthandler_internal.h.
 */

#include <stdio.h>
#include <string.h>
#include <stdbool.h>

#include "unity.h"

#include "cellular_config.h"
#include "cellular_config_defaults.h"

/* Include paths for public enums, structures, and macros. */
#include "cellular_platform.h"
#include "cellular_common_internal.h"
#include "cellular_pkthandler_internal.h"
#include "cellular_types.h"

#include "mock_cellular_at_core.h"
#include "mock_cellular_common.h"
#include "mock_cellular_pktio_internal.h"

#define CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_RESP    "+QIRD: 32\r123243154354364576587utrhfgdghfg"
#define CELLULAR_URC_TOKEN_STRING_INPUT                 "RDY"
#define CELLULAR_URC_TOKEN_STRING_INPUT_START_PLUS      "+RDY"
#define CELLULAR_URC_TOKEN_STRING_INPUT_WITH_PAYLOAD    "+RDY:START"
#define CELLULAR_URC_TOKEN_STRING_GREATER_INPUT         "RDYY"
#define CELLULAR_URC_TOKEN_STRING_SMALLER_INPUT         "RD"
#define CELLULAR_PLUS_TOKEN_ONLY_STRING                 "+"
#define CELLULAR_SAMPLE_PREFIX_STRING_LARGE_INPUT       "+CPIN:Story for Littel Red Riding Hood: Once upon a time there was a dear little girl who was loved by every one who looked at her, but most of all by her grandmother, and there was nothing that she would not have given to the child. Once she gave her a little cap of red velvet, which suited her so well that she would never wear anything else. So she was always called Little Red Riding Hood."
#define CELLULAR_AT_CMD_TYPICAL_MAX_SIZE                ( 32U )

#define CELLULAR_AT_UNDEFINED_STRING_RESP               "undefined_string"

static uint16_t queueData = CELLULAR_PKT_STATUS_BAD_PARAM;
static int32_t queueReturnFail = 0;
static int32_t queueCreateFail = 0;
static int32_t pktRespCBReturn = 0;
static bool passCompareString = false;
static char * pCompareString = NULL;
static int32_t undefinedCallbackContext = 0;
static uint32_t lastDelayTimeMs = 0U;

void cellularAtParseTokenHandler( CellularContext_t * pContext,
                                  char * pInputStr );

CellularAtParseTokenMap_t CellularUrcHandlerTable[] =
{
    { "CEREG",             cellularAtParseTokenHandler },
    { "CGREG",             cellularAtParseTokenHandler },
    { "CREG",              cellularAtParseTokenHandler },
    { "NORMAL POWER DOWN", cellularAtParseTokenHandler },
    { "PSM POWER DOWN",    cellularAtParseTokenHandler },
    { "QIND",              cellularAtParseTokenHandler },
    { "QIOPEN",            cellularAtParseTokenHandler },
    { "QIURC",             cellularAtParseTokenHandler },
    { "RDY",               cellularAtParseTokenHandler },
    { "RDY",               cellularAtParseTokenHandler }
};
const uint32_t CellularUrcHandlerTableSize = sizeof( CellularUrcHandlerTable ) / sizeof( CellularAtParseTokenMap_t );

CellularAtParseTokenMap_t CellularUrcHandlerTableWoParseFunc[] =
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
const uint32_t CellularUrcHandlerTableWoParseFuncSize = sizeof( CellularUrcHandlerTableWoParseFunc ) / sizeof( CellularAtParseTokenMap_t );

CellularAtParseTokenMap_t CellularUrcHandlerTableSortFailCase[] =
{
    { "NORMAL POWER DOWN", NULL },
    { "CEREG",             NULL },
    { "CERE",              NULL },
    { "CEREG",             NULL },
    { "PSM POWER DOWN",    NULL },
    { "QIND",              NULL },
    { "QIOPEN",            NULL },
    { "QIURC",             NULL },
    { "QSIMSTAT",          NULL },
    { "RDY",               NULL }
};
const uint32_t CellularUrcHandlerTableSortFailCaseSize = sizeof( CellularUrcHandlerTableSortFailCase ) / sizeof( CellularAtParseTokenMap_t );

CellularTokenTable_t tokenTable =
{
    .pCellularUrcHandlerTable              = CellularUrcHandlerTable,
    .cellularPrefixToParserMapSize         = CellularUrcHandlerTableSize,
    .pCellularSrcTokenErrorTable           = NULL,
    .cellularSrcTokenErrorTableSize        = 0,
    .pCellularSrcTokenSuccessTable         = NULL,
    .cellularSrcTokenSuccessTableSize      = 0,
    .pCellularUrcTokenWoPrefixTable        = NULL,
    .cellularUrcTokenWoPrefixTableSize     = 0,
    .pCellularSrcExtraTokenSuccessTable    = NULL,
    .cellularSrcExtraTokenSuccessTableSize = 0
};

CellularTokenTable_t tokenTableWoParseFunc =
{
    .pCellularUrcHandlerTable              = CellularUrcHandlerTableWoParseFunc,
    .cellularPrefixToParserMapSize         = CellularUrcHandlerTableWoParseFuncSize,
    .pCellularSrcTokenErrorTable           = NULL,
    .cellularSrcTokenErrorTableSize        = 0,
    .pCellularSrcTokenSuccessTable         = NULL,
    .cellularSrcTokenSuccessTableSize      = 0,
    .pCellularUrcTokenWoPrefixTable        = NULL,
    .cellularUrcTokenWoPrefixTableSize     = 0,
    .pCellularSrcExtraTokenSuccessTable    = NULL,
    .cellularSrcExtraTokenSuccessTableSize = 0
};

CellularTokenTable_t tokenTableSortFailCase =
{
    .pCellularUrcHandlerTable              = CellularUrcHandlerTableSortFailCase,
    .cellularPrefixToParserMapSize         = CellularUrcHandlerTableSortFailCaseSize,
    .pCellularSrcTokenErrorTable           = NULL,
    .cellularSrcTokenErrorTableSize        = 0,
    .pCellularSrcTokenSuccessTable         = NULL,
    .cellularSrcTokenSuccessTableSize      = 0,
    .pCellularUrcTokenWoPrefixTable        = NULL,
    .cellularUrcTokenWoPrefixTableSize     = 0,
    .pCellularSrcExtraTokenSuccessTable    = NULL,
    .cellularSrcExtraTokenSuccessTableSize = 0
};

CellularTokenTable_t tokenTableWoMapSize =
{
    .pCellularUrcHandlerTable              = CellularUrcHandlerTableSortFailCase,
    .cellularPrefixToParserMapSize         = 0,
    .pCellularSrcTokenErrorTable           = NULL,
    .cellularSrcTokenErrorTableSize        = 0,
    .pCellularSrcTokenSuccessTable         = NULL,
    .cellularSrcTokenSuccessTableSize      = 0,
    .pCellularUrcTokenWoPrefixTable        = NULL,
    .cellularUrcTokenWoPrefixTableSize     = 0,
    .pCellularSrcExtraTokenSuccessTable    = NULL,
    .cellularSrcExtraTokenSuccessTableSize = 0
};

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    queueData = 0;
    queueReturnFail = 0;
    pktRespCBReturn = 0;
    lastDelayTimeMs = 0U;
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

void dummyDelay( uint32_t milliseconds )
{
    lastDelayTimeMs = milliseconds;
}

void * mock_malloc( size_t size )
{
    return ( void * ) malloc( size );
}

static CellularPktStatus_t pktRespCB( CellularContext_t * pContext,
                                      const CellularATCommandResponse_t * pAtResp,
                                      void * pData,
                                      uint16_t dataLen )
{
    CellularPktStatus_t pktStatus = pktRespCBReturn;

    ( void ) pContext;
    ( void ) pAtResp;
    ( void ) pData;
    ( void ) dataLen;

    return pktStatus;
}

bool MockPlatformMutex_Create( PlatformMutex_t * pNewMutex,
                               bool recursive )
{
    ( void ) recursive;

    pNewMutex->created = true;
    return true;
}

void MockPlatformMutex_Lock( PlatformMutex_t * pMutex )
{
    ( void ) pMutex;
}

void MockPlatformMutex_Unlock( PlatformMutex_t * pMutex )
{
    ( void ) pMutex;
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

BaseType_t MockxQueueSend( QueueHandle_t queue,
                           void * data,
                           uint32_t time )
{
    ( void ) queue;
    ( void ) time;

    queueData = *( ( uint16_t * ) data );

    if( queueReturnFail == 0 )
    {
        return true;
    }
    else
    {
        queueData = false;
        return false;
    }
}

/* This function mock the API xQueueReceive, by reading the byte value of the queueReturnFail.
 * The first byte value of queueReturnFail means the return value when xQueueReceive called at first time, and
 * the second byte value of queueReturnFail means the return value when xQueueReceive called, and etc.
 */
BaseType_t MockxQueueReceive( QueueHandle_t queue,
                              void * data,
                              uint32_t time )
{
    ( void ) queue;
    ( void ) time;

    if( ( queueReturnFail & 0xFF ) == 0 )
    {
        *( int32_t * ) data = ( queueData & 0xFF );

        if( ( queueData >> 8 ) > 0 )
        {
            queueData = queueData >> 8;
        }

        if( ( queueReturnFail >> 8 ) > 0 )
        {
            queueReturnFail = queueReturnFail >> 8;
        }

        return true;
    }
    else
    {
        return false;
    }
}

void MockPlatformMutex_Destroy( PlatformMutex_t * pMutex )
{
    pMutex->created = false;
}


uint16_t MockvQueueDelete( QueueHandle_t queue )
{
    free( queue );
    queue = NULL;
    return 1;
}

CellularATError_t Cellular_ATIsPrefixPresent( const char * pString,
                                              bool * pResult )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;

    TEST_ASSERT( pString != NULL );
    TEST_ASSERT( pResult != NULL );

    if( strcmp( pString, CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_RESP ) == 0 )
    {
        *pResult = true;
    }
    else if( strcmp( pString, CELLULAR_PLUS_TOKEN_ONLY_STRING ) == 0 )
    {
        *pResult = true;
    }
    else if( strcmp( pString, CELLULAR_URC_TOKEN_STRING_INPUT_WITH_PAYLOAD ) == 0 )
    {
        *pResult = true;
    }
    else if( strcmp( pString, CELLULAR_URC_TOKEN_STRING_INPUT_START_PLUS ) == 0 )
    {
        *pResult = false;
    }
    else
    {
        *pResult = false;
    }

    return atStatus;
}

CellularATError_t _CMOCK_Cellular_ATStrDup_CALLBACK( char ** ppDst,
                                                     const char * pSrc,
                                                     int cmock_num_calls )
{
    char * p = NULL;
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    const char * pTempSrc = pSrc;

    ( void ) cmock_num_calls;

    if( ( ppDst == NULL ) || ( pTempSrc == NULL ) || ( strnlen( pTempSrc, CELLULAR_AT_MAX_STRING_SIZE ) >= CELLULAR_AT_MAX_STRING_SIZE ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        *ppDst = ( char * ) Platform_Malloc( sizeof( char ) * ( strlen( pTempSrc ) + 1U ) );

        if( *ppDst != NULL )
        {
            p = *ppDst;

            while( *pTempSrc != '\0' )
            {
                *p = *pTempSrc;
                p++;
                pTempSrc++;
            }

            *p = '\0';
        }
    }

    return atStatus;
}

static void _CMOCK_Cellular_Generic_CALLBACK( const CellularContext_t * pContext,
                                              const char * pRawData,
                                              int cmock_num_calls )
{
    ( void ) pRawData;
    ( void ) pContext;
    ( void ) cmock_num_calls;

    if( strcmp( pCompareString, pRawData ) == 0 )
    {
        passCompareString = true;
    }
}

/* Empty callback function for test. */
void cellularAtParseTokenHandler( CellularContext_t * pContext,
                                  char * pInputStr )
{
    ( void ) pContext;
    ( void ) pInputStr;

    if( strcmp( pCompareString, pInputStr ) == 0 )
    {
        passCompareString = true;
    }
}

static char * getStringAfterColon( char * pInputStr )
{
    char * ret = memchr( pInputStr, ':', strlen( pInputStr ) );

    return ret ? ret + 1 : pInputStr + strlen( pInputStr );
}

static CellularPktStatus_t undefinedRespCallback( void * pCallbackContext,
                                                  const char * pLine )
{
    CellularPktStatus_t undefineReturnStatus = CELLULAR_PKT_STATUS_OK;

    /* Verify pCallbackContext. */
    TEST_ASSERT_EQUAL_PTR( &undefinedCallbackContext, pCallbackContext );

    /* Verify pLine. */
    if( strcmp( CELLULAR_AT_UNDEFINED_STRING_RESP, pLine ) == 0 )
    {
        *( ( int32_t * ) pCallbackContext ) = 1;
        undefineReturnStatus = CELLULAR_PKT_STATUS_OK;
    }
    else
    {
        *( ( int32_t * ) pCallbackContext ) = 0;
        undefineReturnStatus = CELLULAR_PKT_STATUS_FAILURE;
    }

    return undefineReturnStatus;
}


/* ========================================================================== */

/**
 * @brief Test that invalid parameter for _Cellular_PktHandlerCleanup.
 */
void test__Cellular_PktHandlerCleanup_Invalid_Parameter( void )
{
    CellularContext_t context;

    _Cellular_PktHandlerCleanup( NULL );

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pktRespQueue = NULL;
    _Cellular_PktHandlerCleanup( &context );
}

/**
 * @brief Test that happy path for _Cellular_PktHandlerCleanup.
 */
void test__Cellular_PktHandlerCleanup_Happy_Path( void )
{
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pktRespQueue = xQueueCreate( 1, sizeof( CellularPktStatus_t ) );

    _Cellular_PktHandlerCleanup( &context );

    TEST_ASSERT_EQUAL( NULL, context.pktRespQueue );
}

/**
 * @brief Test that null context case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_NULL_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    pktStatus = _Cellular_HandlePacket( NULL, AT_SOLICITED, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that null buffer AT_SOLICITED case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_Null_Buffer_AT_SOLICITED( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );

    pktStatus = _Cellular_HandlePacket( &context, AT_SOLICITED, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test that AT_SOLICITED false At Resp failure case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_AT_SOLICITED_False_AtResp_Failure( void )
{
    CellularContext_t context;
    CellularATCommandLine_t testATCmdLine;
    CellularATCommandResponse_t atResp;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );
    testATCmdLine.pLine = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_RESP;
    testATCmdLine.pNext = NULL;
    atResp.pItm = &testATCmdLine;
    atResp.status = false;

    pktStatus = _Cellular_HandlePacket( &context, AT_SOLICITED, ( void * ) &atResp );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );

    context.pktRespCB = pktRespCB;
    pktStatus = _Cellular_HandlePacket( &context, AT_SOLICITED, ( void * ) &atResp );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );
}

/**
 * @brief Test that AT_SOLICITED xQueueSend failure case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_AT_SOLICITED_xQueueSend_Failure( void )
{
    CellularContext_t context;
    CellularATCommandLine_t testATCmdLine;
    CellularATCommandResponse_t atResp;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );
    testATCmdLine.pLine = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_RESP;
    testATCmdLine.pNext = NULL;
    atResp.pItm = &testATCmdLine;
    atResp.status = true;

    queueReturnFail = 1;
    pktStatus = _Cellular_HandlePacket( &context, AT_SOLICITED, ( void * ) &atResp );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );
    TEST_ASSERT_EQUAL( false, queueData );
}

/**
 * @brief Test that happy path case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_AT_SOLICITED_Happy_Path( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandLine_t testATCmdLine;
    CellularATCommandResponse_t atResp;

    testATCmdLine.pLine = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_RESP;
    testATCmdLine.pNext = NULL;
    atResp.pItm = &testATCmdLine;
    atResp.status = true;

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pktRespCB = pktRespCB;

    pktStatus = _Cellular_HandlePacket( &context, AT_SOLICITED, ( void * ) &atResp );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, queueData );
}

/**
 * @brief Test that null param AT_UNSOLICITED case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_Null_PARAM_AT_UNSOLICITED( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );

    pktStatus = _Cellular_HandlePacket( &context, AT_UNSOLICITED, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test that start with + but no token string case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_AT_UNSOLICITED_Start_Plus_No_Token_String( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );
    Cellular_ATStrDup_StubWithCallback( _CMOCK_Cellular_ATStrDup_CALLBACK );

    pktStatus = _Cellular_HandlePacket( &context, AT_UNSOLICITED, CELLULAR_PLUS_TOKEN_ONLY_STRING );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_REQUEST, pktStatus );
}

/**
 * @brief Test that too large string case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_AT_UNSOLICITED_Too_Large_String( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );
    Cellular_ATStrDup_StubWithCallback( _CMOCK_Cellular_ATStrDup_CALLBACK );

    pktStatus = _Cellular_HandlePacket( &context, AT_UNSOLICITED, CELLULAR_SAMPLE_PREFIX_STRING_LARGE_INPUT );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );
}

/**
 * @brief Test that NULL parse function AT_UNSOLICITED case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_AT_UNSOLICITED_Null_Parse_Function( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTableWoParseFunc, sizeof( CellularTokenTable_t ) );
    Cellular_ATStrDup_StubWithCallback( _CMOCK_Cellular_ATStrDup_CALLBACK );

    pktStatus = _Cellular_HandlePacket( &context, AT_UNSOLICITED, CELLULAR_URC_TOKEN_STRING_INPUT );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );
}

/**
 * @brief Test that happy path case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_AT_UNSOLICITED_Happy_Path( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    Cellular_ATStrDup_StubWithCallback( _CMOCK_Cellular_ATStrDup_CALLBACK );

    /* set for cellularAtParseTokenHandler function */
    passCompareString = false;
    pCompareString = getStringAfterColon( CELLULAR_URC_TOKEN_STRING_INPUT_WITH_PAYLOAD );

    pktStatus = _Cellular_HandlePacket( &context, AT_UNSOLICITED, CELLULAR_URC_TOKEN_STRING_INPUT_WITH_PAYLOAD );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
    TEST_ASSERT_EQUAL( true, passCompareString );
}

/**
 * @brief Test input string without payload for _Cellular_HandlePacket.
 *
 * URC input string "+RDY" should be regarded as URC without prefix.
 * If there is a handler function registered in the table, the handler function is
 * called with pInputStr point to "+RDY" string.
 */
void test__Cellular_HandlePacket_AT_UNSOLICITED_Input_String_without_payload( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtParseTokenMap_t cellularTestUrcHandlerTable[] =
    {
        /* Use the URC string instead of the URC prefix in the mapping table. */
        { CELLULAR_URC_TOKEN_STRING_INPUT_START_PLUS, cellularAtParseTokenHandler }
    };

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.tokenTable.pCellularUrcHandlerTable = cellularTestUrcHandlerTable;
    context.tokenTable.cellularPrefixToParserMapSize = 1;

    Cellular_ATStrDup_StubWithCallback( _CMOCK_Cellular_ATStrDup_CALLBACK );

    /* set for cellularAtParseTokenHandler function */
    passCompareString = false;
    pCompareString = CELLULAR_URC_TOKEN_STRING_INPUT_START_PLUS;

    pktStatus = _Cellular_HandlePacket( &context, AT_UNSOLICITED, CELLULAR_URC_TOKEN_STRING_INPUT_START_PLUS );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* passCompareString is set to true in cellularAtParseTokenHandler if pCompareString
     * equals to parameter pInputStr. */
    TEST_ASSERT_EQUAL( true, passCompareString );
}

/**
 * @brief Test that handle input string greater than urc token case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_AT_UNSOLICITED_Input_String_Greater_Than_Urc_Token_Path( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Test the greater string size in comparison function. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    Cellular_ATStrDup_StubWithCallback( _CMOCK_Cellular_ATStrDup_CALLBACK );

    /* set for generic callback function */
    passCompareString = false;
    pCompareString = CELLULAR_URC_TOKEN_STRING_GREATER_INPUT;
    _Cellular_GenericCallback_Stub( _CMOCK_Cellular_Generic_CALLBACK );

    pktStatus = _Cellular_HandlePacket( &context, AT_UNSOLICITED, CELLULAR_URC_TOKEN_STRING_GREATER_INPUT );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
    TEST_ASSERT_EQUAL( true, passCompareString );
}

/**
 * @brief Test that handle input string less than urc token case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_AT_UNSOLICITED_Input_String_Less_Than_Urc_Token_Path( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Test the smaller string size in comparison function. */
    Cellular_ATStrDup_StubWithCallback( _CMOCK_Cellular_ATStrDup_CALLBACK );

    /* set for generic callback function */
    passCompareString = false;
    pCompareString = CELLULAR_URC_TOKEN_STRING_SMALLER_INPUT;
    _Cellular_GenericCallback_Stub( _CMOCK_Cellular_Generic_CALLBACK );

    pktStatus = _Cellular_HandlePacket( &context, AT_UNSOLICITED, CELLULAR_URC_TOKEN_STRING_SMALLER_INPUT );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
    TEST_ASSERT_EQUAL( true, passCompareString );
}

/**
 * @brief Test that null buffer invalid message type case for _Cellular_HandlePacket.
 */
void test__Cellular_HandlePacket_Wrong_RespType( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Send invalid message type. */
    pktStatus = _Cellular_HandlePacket( &context, AT_UNDEFINED + 1, CELLULAR_URC_TOKEN_STRING_SMALLER_INPUT );

    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test _Cellular_HandlePacket function with AT_UNDEFINED message type.
 *
 * AT_UNDEFINED message type is received. A callback function handles the message
 * without problem. CELLULAR_PKT_STATUS_OK should be returned.
 */
void test__Cellular_HandlePacket_AT_UNDEFINED_with_undefined_callback_okay( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char undefinedCallbackStr[] = CELLULAR_AT_UNDEFINED_STRING_RESP;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Set undefined response callback. */
    undefinedCallbackContext = 0;
    context.undefinedRespCallback = undefinedRespCallback;
    context.pUndefinedRespCBContext = &undefinedCallbackContext;

    /* Send AT_UNDEFINED message. */
    pktStatus = _Cellular_HandlePacket( &context, AT_UNDEFINED, undefinedCallbackStr );

    /* CELLULAR_PKT_STATUS_OK should be returned, since it is handled. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* Verify undefinedRespCallback is called and the expected string is received. */
    TEST_ASSERT_EQUAL_INT32( 1, undefinedCallbackContext );
}

/**
 * @brief Test _Cellular_HandlePacket function with AT_UNDEFINED message type.
 *
 * AT_UNDEFINED message type is received. A callback function handles the message
 * but fail to recognized the undefined response. CELLULAR_PKT_STATUS_INVALID_DATA
 * should be returned.
 */
void test__Cellular_HandlePacket_AT_UNDEFINED_with_undefined_callback_fail( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char undefinedCallbackStr[] = "RandomString";

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Set undefined response callback. */
    undefinedCallbackContext = 1;
    context.undefinedRespCallback = undefinedRespCallback;
    context.pUndefinedRespCBContext = &undefinedCallbackContext;

    /* Send AT_UNDEFINED message. */
    pktStatus = _Cellular_HandlePacket( &context, AT_UNDEFINED, undefinedCallbackStr );

    /* CELLULAR_PKT_STATUS_INVALID_DATA should be returned. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_DATA, pktStatus );

    /* Verify undefinedRespCallback is called and the expected string is received. */
    TEST_ASSERT_EQUAL_INT32( 0, undefinedCallbackContext );
}

/**
 * @brief Test _Cellular_HandlePacket function with AT_UNDEFINED message type.
 *
 * AT_UNDEFINED message type is received. No callback function is registered to handle
 * the undefined message. CELLULAR_PKT_STATUS_INVALID_DATA should be returned.
 */
void test__Cellular_HandlePacket_AT_UNDEFINED_without_undefined_callback( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char undefinedCallbackStr[] = CELLULAR_AT_UNDEFINED_STRING_RESP;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Send AT_UNDEFINED message. */
    pktStatus = _Cellular_HandlePacket( &context, AT_UNDEFINED, undefinedCallbackStr );

    /* CELLULAR_PKT_STATUS_INVALID_DATA should be returned. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_DATA, pktStatus );
}

/**
 * @brief Test that URC with colon for _Cellular_HandlePacket when token is not in the token table.
 */
void test__Cellular_HandlePacket_AT_UNSOLICITED_Input_String_With_Colon_Not_In_Urc_Token_Path( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTableWoParseFunc, sizeof( CellularTokenTable_t ) );
    Cellular_ATStrDup_StubWithCallback( _CMOCK_Cellular_ATStrDup_CALLBACK );

    /* set for generic callback function */
    passCompareString = false;
    pCompareString = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_RESP;
    _Cellular_GenericCallback_Stub( _CMOCK_Cellular_Generic_CALLBACK );

    pktStatus = _Cellular_HandlePacket( &context, AT_UNSOLICITED, CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_RESP );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
    TEST_ASSERT_EQUAL( true, passCompareString );
}

/**
 * @brief Test that null Context case for _Cellular_PktHandler_AtcmdRequestWithCallback.
 */
void test__Cellular_PktHandler_AtcmdRequestWithCallback_NULL_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReq;

    memset( &atReq, 0, sizeof( CellularAtReq_t ) );

    pktStatus = _Cellular_PktHandler_AtcmdRequestWithCallback( NULL, atReq, PACKET_REQ_TIMEOUT_MS );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that null atReq case for _Cellular_PktHandler_AtcmdRequestWithCallback.
 */
void test__Cellular_PktHandler_AtcmdRequestWithCallback_NULL_atReq( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReq;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    memset( &atReq, 0, sizeof( CellularAtReq_t ) );
    pktStatus = _Cellular_PktHandler_AtcmdRequestWithCallback( &context, atReq, PACKET_REQ_TIMEOUT_MS );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_REQUEST, pktStatus );
}

/**
 * @brief Test that _Cellular_PktioSendAtCmd return fail case for _Cellular_PktHandler_AtcmdRequestWithCallback.
 */
void test__Cellular_PktHandler_AtcmdRequestWithCallback__Cellular_PktioSendAtCmd_Return_Fail( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetMccMnc =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );
    pktStatus = _Cellular_PktHandler_AtcmdRequestWithCallback( &context, atReqGetMccMnc, PACKET_REQ_TIMEOUT_MS );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test that _Cellular_PktioSendAtCmd return OK case for _Cellular_PktHandler_AtcmdRequestWithCallback.
 */
void test__Cellular_PktHandler_AtcmdRequestWithCallback__Cellular_PktioSendAtCmd_Return_OK( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetMccMnc =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    /* xQueueReceive true, and the data is CELLULAR_PKT_STATUS_OK. */
    queueData = CELLULAR_PKT_STATUS_OK;
    pktStatus = _Cellular_PktHandler_AtcmdRequestWithCallback( &context, atReqGetMccMnc, PACKET_REQ_TIMEOUT_MS );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test that return expected rsp code from xQueueReceive for _Cellular_AtcmdRequestWithCallback.
 */
void test__Cellular_AtcmdRequestWithCallback__Cellular_PktioSendAtCmd_Return_Expected_RspCode_From_xQueueReceive( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetMccMnc =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* xQueueReceive true, and the data is CELLULAR_PKT_STATUS_BAD_PARAM. */
    queueData = CELLULAR_PKT_STATUS_BAD_PARAM;
    pktStatus = _Cellular_PktHandler_AtcmdRequestWithCallback( &context, atReqGetMccMnc, PACKET_REQ_TIMEOUT_MS );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test that _Cellular_PktioSendAtCmd return OK case for _Cellular_PktHandler_AtcmdRequestWithCallback.
 */
void test__Cellular_PktHandler_AtcmdRequestWithCallback_xQueueReceive_Return_Fail( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetMccMnc =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    /* xQueueReceive failed. */
    queueReturnFail = 1;
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    pktStatus = _Cellular_PktHandler_AtcmdRequestWithCallback( &context, atReqGetMccMnc, PACKET_REQ_TIMEOUT_MS );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_TIMED_OUT, pktStatus );
}

/**
 * @brief Test that null Context case for _Cellular_TimeoutAtcmdDataRecvRequestWithCallback.
 */
void test__Cellular_TimeoutAtcmdDataRecvRequestWithCallback_NULL_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReq;

    memset( &atReq, 0, sizeof( CellularAtReq_t ) );

    pktStatus = _Cellular_TimeoutAtcmdDataRecvRequestWithCallback( NULL, atReq, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that null atReq case for _Cellular_TimeoutAtcmdDataRecvRequestWithCallback.
 */
void test__Cellular_TimeoutAtcmdDataRecvRequestWithCallback_NULL_atReq( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReq;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    memset( &atReq, 0, sizeof( CellularAtReq_t ) );

    pktStatus = _Cellular_TimeoutAtcmdDataRecvRequestWithCallback( &context, atReq, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_REQUEST, pktStatus );
}

/**
 * @brief Test that null Context case for _Cellular_AtcmdDataSend.
 */
void test__Cellular_AtcmdDataSend_NULL_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    const char dataBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    uint32_t sentDataLength = 0;
    CellularAtDataReq_t atDataReq =
    {
        ( const uint8_t * ) dataBuf,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE,
        &sentDataLength,
        NULL,
        0
    };

    CellularAtReq_t atReq;

    memset( &atReq, 0, sizeof( CellularAtReq_t ) );

    pktStatus = _Cellular_AtcmdDataSend( NULL, atReq, atDataReq, NULL, NULL, 0, 0, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that null req case for _Cellular_AtcmdDataSend.
 */
void test__Cellular_AtcmdDataSend_Null_Req( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtDataReq_t atDataReq;
    CellularAtReq_t atReq =
    {
        NULL,
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    pktStatus = _Cellular_AtcmdDataSend( &context, atReq, atDataReq, NULL, NULL, 0, 0, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_REQUEST, pktStatus );
}

/**
 * @brief Test that happy path case for _Cellular_AtcmdDataSend.
 */
void test__Cellular_AtcmdDataSend_Happy_Path( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char dataBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    char pEndPattern[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    uint32_t sentDataLength = 0;
    CellularAtDataReq_t atDataReq =
    {
        ( const uint8_t * ) dataBuf,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE,
        &sentDataLength,
        ( const uint8_t * ) pEndPattern,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE
    };

    CellularAtReq_t atReq =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    /* xQueueReceive true, and the data is CELLULAR_PKT_STATUS_OK. */
    queueData = CELLULAR_PKT_STATUS_OK;
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    queueData = CELLULAR_PKT_STATUS_OK;
    pktStatus = _Cellular_AtcmdDataSend( &context, atReq, atDataReq, NULL, NULL, 0, 0, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test that happy path case for _Cellular_AtcmdDataSend.
 */
void test__Cellular_AtcmdDataSend_data_send_delay( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char dataBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    uint32_t sentDataLength = 0;
    CellularAtDataReq_t atDataReq =
    {
        ( const uint8_t * ) dataBuf,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE,
        &sentDataLength,
        NULL,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE
    };

    CellularAtReq_t atReq =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* xQueueReceive true, and the data is CELLULAR_PKT_STATUS_OK. */
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    queueData = CELLULAR_PKT_STATUS_OK;

    /* Send data with data send delay 100ms. */
    pktStatus = _Cellular_AtcmdDataSend( &context, atReq, atDataReq, NULL, NULL, 0, 0, 100U );
    TEST_ASSERT_EQUAL( 100U, lastDelayTimeMs );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test that Test dataReq.pData or dataReq.pSentDataLength null case for _Cellular_AtcmdDataSend.
 */
void test__Cellular_AtcmdDataSend_call__Cellular_DataSendWithTimeoutDelayRaw_DataReq_Null_Parameter_Failure( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char dataBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    char pEndPattern[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    uint32_t sentDataLength = 0;
    CellularAtDataReq_t atDataReqNullParam =
    {
        NULL,
        0,
        NULL,
        NULL,
        0
    };

    CellularAtDataReq_t atDataReqNullSendLength =
    {
        ( const uint8_t * ) dataBuf,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE,
        NULL,
        ( const uint8_t * ) pEndPattern,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE
    };

    CellularAtDataReq_t atDataReqNullEndPattern =
    {
        ( const uint8_t * ) dataBuf,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE,
        &sentDataLength,
        NULL,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE
    };

    CellularAtReq_t atReq =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    /* xQueueReceive true, and the data is CELLULAR_PKT_STATUS_OK. */
    queueData = CELLULAR_PKT_STATUS_OK;
    /* Test dataReq.pData or dataReq.pSentDataLength case. */
    pktStatus = _Cellular_AtcmdDataSend( &context, atReq, atDataReqNullParam, NULL, NULL, 0, 0, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_REQUEST, pktStatus );

    pktStatus = _Cellular_AtcmdDataSend( &context, atReq, atDataReqNullSendLength, NULL, NULL, 0, 0, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_REQUEST, pktStatus );

    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    /* xQueueReceive true, and the data is CELLULAR_PKT_STATUS_OK. */
    queueData = CELLULAR_PKT_STATUS_OK;
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    queueData = CELLULAR_PKT_STATUS_OK;
    pktStatus = _Cellular_AtcmdDataSend( &context, atReq, atDataReqNullEndPattern, NULL, NULL, 0, 0, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test that unexpected unexpected size failure case for _Cellular_AtcmdDataSend.
 */
void test__Cellular_AtcmdDataSend_call__Cellular_DataSendWithTimeoutDelayRaw_Unexpected_DataReq_Size_Failure( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char dataBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    char pEndPattern[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    uint32_t sentDataLength = 0;
    CellularAtDataReq_t atDataReq =
    {
        ( const uint8_t * ) dataBuf,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE,
        &sentDataLength,
        ( const uint8_t * ) pEndPattern,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE
    };

    CellularAtReq_t atReq =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Test return unexpected dataReq.pSentDataLength size from _Cellular_PktioSendData. */
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    /* xQueueReceive true, and the data is CELLULAR_PKT_STATUS_OK. */
    queueData = CELLULAR_PKT_STATUS_OK;
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE - 2 );
    pktStatus = _Cellular_AtcmdDataSend( &context, atReq, atDataReq, NULL, NULL, 0, 0, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_SEND_ERROR, pktStatus );
}

/**
 * @brief Test that return unexpected sendEndPatternLen size failure case for _Cellular_AtcmdDataSend.
 */
void test__Cellular_AtcmdDataSend_call__Cellular_DataSendWithTimeoutDelayRaw_Unexpected_SendEndPatternLen_Size_Failure( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char dataBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    char pEndPattern[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    uint32_t sentDataLength = 0;
    CellularAtDataReq_t atDataReq =
    {
        ( const uint8_t * ) dataBuf,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE,
        &sentDataLength,
        ( const uint8_t * ) pEndPattern,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE
    };

    CellularAtReq_t atReq =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Test return unexpected sendEndPatternLen size from _Cellular_PktioSendData. */
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    /* xQueueReceive true, and the data is CELLULAR_PKT_STATUS_OK. */
    queueData = CELLULAR_PKT_STATUS_OK;
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE - 2 );
    pktStatus = _Cellular_AtcmdDataSend( &context, atReq, atDataReq, NULL, NULL, 0, 0, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_SEND_ERROR, pktStatus );
}

/**
 * @brief Test xQueueReceive return ok, but the data is not CELLULAR_PKT_STATUS_OK failure case for _Cellular_AtcmdDataSend.
 */
void test__Cellular_AtcmdDataSend_call__Cellular_DataSendWithTimeoutDelayRaw_Failure( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char dataBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    char pEndPattern[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    uint32_t sentDataLength = 0;
    CellularAtDataReq_t atDataReq =
    {
        ( const uint8_t * ) dataBuf,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE,
        &sentDataLength,
        ( const uint8_t * ) pEndPattern,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE
    };

    CellularAtReq_t atReq =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Test xQueueReceive return ok, but the data is not CELLULAR_PKT_STATUS_OK. */
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    /* xQueueReceive true, and the data is CELLULAR_PKT_STATUS_OK. */
    queueData = CELLULAR_PKT_STATUS_OK;
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    queueData = queueData | ( CELLULAR_PKT_STATUS_BAD_PARAM << 8 );
    pktStatus = _Cellular_AtcmdDataSend( &context, atReq, atDataReq, NULL, NULL, 0, 0, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test that xQueueReceive return false failure case for _Cellular_AtcmdDataSend.
 */
void test__Cellular_AtcmdDataSend_call__Cellular_DataSendWithTimeoutDelayRaw_xQueueReceive_Return_False_Failure( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char dataBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    char pEndPattern[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    uint32_t sentDataLength = 0;
    CellularAtDataReq_t atDataReq =
    {
        ( const uint8_t * ) dataBuf,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE,
        &sentDataLength,
        ( const uint8_t * ) pEndPattern,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE
    };

    CellularAtReq_t atReq =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    /* xQueueReceive true, and the data is CELLULAR_PKT_STATUS_OK. */
    queueData = CELLULAR_PKT_STATUS_OK;
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    queueReturnFail = queueReturnFail | ( 1 << 8 );
    pktStatus = _Cellular_AtcmdDataSend( &context, atReq, atDataReq, NULL, NULL, 0, 0, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_TIMED_OUT, pktStatus );
}

/**
 * @brief Test that null context case for _Cellular_TimeoutAtcmdDataSendSuccessToken.
 */
void test__Cellular_TimeoutAtcmdDataSendSuccessToken_Null_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtDataReq_t atDataReq;
    CellularAtReq_t atReq;

    pktStatus = _Cellular_TimeoutAtcmdDataSendSuccessToken( NULL, atReq, atDataReq, 0, 0, NULL, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that null req case for _Cellular_TimeoutAtcmdDataSendSuccessToken.
 */
void test__Cellular_TimeoutAtcmdDataSendSuccessToken_Null_Req( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtDataReq_t atDataReq;
    CellularAtReq_t atReq =
    {
        NULL,
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    pktStatus = _Cellular_TimeoutAtcmdDataSendSuccessToken( &context, atReq, atDataReq, 0, 0, NULL, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_REQUEST, pktStatus );
}

/**
 * @brief Test that happy path case for _Cellular_TimeoutAtcmdDataSendSuccessToken.
 */
void test__Cellular_TimeoutAtcmdDataSendSuccessToken_Happy_Path( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char dataBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    char pEndPattern[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    uint32_t sentDataLength = 0;
    CellularAtDataReq_t atDataReq =
    {
        ( const uint8_t * ) dataBuf,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE,
        &sentDataLength,
        ( const uint8_t * ) pEndPattern,
        CELLULAR_AT_CMD_TYPICAL_MAX_SIZE
    };

    CellularAtReq_t atReq =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    queueData = CELLULAR_PKT_STATUS_OK;
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    _Cellular_PktioSendData_IgnoreAndReturn( CELLULAR_AT_CMD_TYPICAL_MAX_SIZE );
    queueData = queueData | ( CELLULAR_PKT_STATUS_OK << 8 );
    pktStatus = _Cellular_TimeoutAtcmdDataSendSuccessToken( &context, atReq, atDataReq, 0, 0, NULL, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}


/**
 * @brief Test that null param case for _Cellular_TimeoutAtcmdDataSendRequestWithCallback.
 */
void test__Cellular_TimeoutAtcmdDataSendRequestWithCallback_Null_Param( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReq;
    CellularAtDataReq_t atDataReqNullParam;

    pktStatus = _Cellular_TimeoutAtcmdDataSendRequestWithCallback( NULL, atReq, atDataReqNullParam, 0, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that null context case for _Cellular_PktHandlerInit.
 */
void test__Cellular_PktHandlerInit_Null_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    pktStatus = _Cellular_PktHandlerInit( NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );
}

/**
 * @brief Test that happy path case for _Cellular_PktHandlerInit.
 */
void test__Cellular_PktHandlerInit_Happy_Path( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    pktStatus = _Cellular_PktHandlerInit( &context );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test that null pktRespQueue case for _Cellular_PktHandlerInit.
 */
void test__Cellular_PktHandlerInit_Null_pktRespQueue( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Flag to set creating queue failure. */
    queueCreateFail = 1;
    pktStatus = _Cellular_PktHandlerInit( &context );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );
}

/**
 * @brief Test that happy path case for _Cellular_CreatePktRequestMutex.
 */
void test__Cellular_CreatePktRequestMutex_Null_Parameter( void )
{
    bool ret = true;

    ret = _Cellular_CreatePktRequestMutex( NULL );
    TEST_ASSERT_EQUAL( false, ret );
}

/**
 * @brief Test that happy path case for _Cellular_CreatePktRequestMutex.
 */
void test__Cellular_CreatePktRequestMutex_Happy_Path( void )
{
    bool ret = false;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    ret = _Cellular_CreatePktRequestMutex( &context );
    TEST_ASSERT_EQUAL( true, ret );
}

/**
 * @brief Test that null parameter case for _Cellular_CreatePktResponseMutex.
 */
void test__Cellular_CreatePktResponseMutex_Null_Parameter( void )
{
    bool ret = true;

    ret = _Cellular_CreatePktResponseMutex( NULL );
    TEST_ASSERT_EQUAL( false, ret );
}

/**
 * @brief Test that happy path case for _Cellular_CreatePktResponseMutex.
 */
void test__Cellular_CreatePktResponseMutex_Happy_Path( void )
{
    bool ret = false;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    ret = _Cellular_CreatePktResponseMutex( &context );
    TEST_ASSERT_EQUAL( true, ret );
}

/**
 * @brief Test that null parameter case for _Cellular_DestroyPktRequestMutex.
 */
void test__Cellular_DestroyPktRequestMutex_Null_Parameter( void )
{
    CellularContext_t context;

    _Cellular_CreatePktResponseMutex( &context );
    _Cellular_DestroyPktRequestMutex( NULL );
    TEST_ASSERT_EQUAL( false, context.pktRequestMutex.created );
}

/**
 * @brief Test that happy path case for _Cellular_DestroyPktRequestMutex.
 */
void test__Cellular_DestroyPktRequestMutex_Happy_Path( void )
{
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CreatePktRequestMutex( &context );
    _Cellular_DestroyPktRequestMutex( &context );
    TEST_ASSERT_EQUAL( false, context.pktRequestMutex.created );
}

/**
 * @brief Test that null parameter case for _Cellular_DestroyPktResponseMutex.
 */
void test__Cellular_DestroyPktResponseMutex_Null_Parameter( void )
{
    CellularContext_t context;

    _Cellular_CreatePktResponseMutex( &context );
    _Cellular_DestroyPktResponseMutex( NULL );
    TEST_ASSERT_EQUAL( true, context.PktRespMutex.created );
}

/**
 * @brief Test that happy path case for _Cellular_DestroyPktResponseMutex.
 */
void test__Cellular_DestroyPktResponseMutex_Happy_Path( void )
{
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CreatePktResponseMutex( &context );
    _Cellular_DestroyPktResponseMutex( &context );
    TEST_ASSERT_EQUAL( false, context.PktRespMutex.created );
}

/**
 * @brief Test that null context case for _Cellular_AtParseInit.
 */
void test__Cellular_AtParseInit_Null_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    pktStatus = _Cellular_AtParseInit( NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that happy path case for _Cellular_AtParseInit.
 */
void test__Cellular_AtParseInit_Happy_Path( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTableWoParseFunc, sizeof( CellularTokenTable_t ) );
    pktStatus = _Cellular_AtParseInit( &context );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}


/**
 * @brief Test that sort fail case case for _Cellular_AtParseInit.
 */
void test__Cellular_AtParseInit_Check_Sort_Fail( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTableSortFailCase, sizeof( CellularTokenTable_t ) );
    pktStatus = _Cellular_AtParseInit( &context );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test that token table fail case case for _Cellular_AtParseInit.
 */
void test__Cellular_AtParseInit_Check_TokenTable_Fail( void )
{
    CellularContext_t context;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    memset( &context, 0, sizeof( CellularContext_t ) );
    pktStatus = _Cellular_AtParseInit( &context );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );

    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTableWoMapSize, sizeof( CellularTokenTable_t ) );
    pktStatus = _Cellular_AtParseInit( &context );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );

    memset( &context, 0, sizeof( CellularContext_t ) );
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    pktStatus = _Cellular_AtParseInit( &context );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test that null Context case for _Cellular_AtcmdRequestSuccessToken.
 */
void test__Cellular_AtcmdRequestSuccessToken_NULL_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReq;
    const char * successTokenTable[] = { "1, CONNECT CLOSE" };

    memset( &atReq, 0, sizeof( CellularAtReq_t ) );

    pktStatus = _Cellular_AtcmdRequestSuccessToken( NULL, atReq, PACKET_REQ_TIMEOUT_MS, successTokenTable, 1 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that null atReq case for _Cellular_AtcmdRequestSuccessToken.
 */
void test__Cellular_AtcmdRequestSuccessToken_NULL_pCellularSrcTokenSuccessTable( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReq;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    memset( &atReq, 0, sizeof( CellularAtReq_t ) );
    pktStatus = _Cellular_AtcmdRequestSuccessToken( &context, atReq, PACKET_REQ_TIMEOUT_MS, NULL, 1 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test that _Cellular_PktioSendAtCmd return OK case for _Cellular_PktHandler_AtcmdRequestWithCallback.
 */
void test__Cellular_AtcmdRequestSuccessToken_Cellular_PktioSendAtCmd_Return_OK( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetMccMnc =
    {
        "AT+COPS?",
        CELLULAR_AT_WITH_PREFIX,
        "+COPS",
        NULL,
        NULL,
        sizeof( int32_t ),
    };
    CellularContext_t context = { 0 };
    const char * successTokenTable[] = { "1, CONNECT CLOSE" };

    _Cellular_PktioSendAtCmd_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* xQueueReceive true, and the data is CELLULAR_PKT_STATUS_OK. */
    queueData = CELLULAR_PKT_STATUS_OK;
    pktStatus = _Cellular_AtcmdRequestSuccessToken( &context, atReqGetMccMnc, PACKET_REQ_TIMEOUT_MS, successTokenTable, 1 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}
