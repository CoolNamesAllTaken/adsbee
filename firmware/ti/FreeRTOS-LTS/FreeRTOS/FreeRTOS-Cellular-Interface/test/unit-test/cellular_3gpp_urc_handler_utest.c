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
 * @file cellular_3gpp_urc_handler.c
 * @brief Unit tests for functions in cellular_common_internal.h.
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

#include "mock_cellular_at_core.h"
#include "mock_cellular_common.h"

static int parseRegStatusCase = 0;
static int parseLacTacInRegCase = 0;
static int parseCellIdInRegCase = 0;
static int parseRatInfoInRegCase = 0;
static int parseRejectTypeInRegCase = 0;
static int parseRejectCauseInRegCase = 0;
static int returnNULL = 0;
static int atoiFailure = 0;
/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    parseRegStatusCase = 0;
    parseLacTacInRegCase = 0;
    parseCellIdInRegCase = 0;
    parseRatInfoInRegCase = 0;
    parseRejectTypeInRegCase = 0;
    parseRejectCauseInRegCase = 0;
    returnNULL = 0;
    atoiFailure = 0;
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
    ( void ) milliseconds;
}

void * mock_malloc( size_t size )
{
    return malloc( size );
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

void MockPlatformMutex_Unlock( PlatformMutex_t * pMutex )
{
    ( void ) pMutex;
}

void MockPlatformMutex_Lock( PlatformMutex_t * pMutex )
{
    ( void ) pMutex;
}

CellularATError_t Mock_Cellular_ATStrtoi_Callback( const char * pStr,
                                                   int32_t base,
                                                   int32_t * pResult,
                                                   int cmockNumCalls )
{
    ( void ) base;
    ( void ) cmockNumCalls;

    *pResult = atoi( pStr );

    if( atoiFailure == 1 )
    {
        return CELLULAR_AT_ERROR;
    }
    else
    {
        return CELLULAR_AT_SUCCESS;
    }
}

void handleNextTok_parseRegStatusCase( char ** ppTokOutput,
                                       int32_t parseRegStatusCase )
{
    if( parseRegStatusCase == 1 )
    {
        char pTestString[] = "10";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRegStatusCase == 2 )
    {
        char pTestString[] = "5";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRegStatusCase == 3 )
    {
        char pTestString[] = "3";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRegStatusCase == 4 )
    {
        char pTestString[] = "8";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRegStatusCase == 5 )
    {
        char pTestString[] = "-3";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
}

void handleNextTok_parseRatInfoInRegCase( char ** ppTokOutput,
                                          int32_t parseRatInfoInRegCase )
{
    if( parseRatInfoInRegCase == 1 )
    {
        char pTestString[] = "10";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRatInfoInRegCase == 2 )
    {
        char pTestString[] = "7";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRatInfoInRegCase == 3 )
    {
        char pTestString[] = "1";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRatInfoInRegCase == 4 )
    {
        char pTestString[] = "3";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRatInfoInRegCase == 5 )
    {
        char pTestString[] = "8";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRatInfoInRegCase == 6 )
    {
        char pTestString[] = "9";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
}

void handleNextTok_parseRejectTypeInRegCase( char ** ppTokOutput,
                                             int32_t parseRejectTypeInRegCase )
{
    if( parseRejectTypeInRegCase == 1 )
    {
        char pTestString[] = "256";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRejectTypeInRegCase == 2 )
    {
        char pTestString[] = "3";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRejectTypeInRegCase == 3 )
    {
        char pTestString[] = "-3";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
}

void handleNextTok_parseRejectCauseInRegCase( char ** ppTokOutput,
                                              int32_t parseRejectCauseInRegCase )
{
    if( parseRejectCauseInRegCase == 1 )
    {
        char pTestString[] = "256";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRejectCauseInRegCase == 2 )
    {
        char pTestString[] = "3";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
    else if( parseRejectCauseInRegCase == 3 )
    {
        char pTestString[] = "-3";
        *ppTokOutput = malloc( sizeof( pTestString ) );
        memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
    }
}

CellularATError_t Mock_Cellular_ATGetNextTok_Callback( char ** ppString,
                                                       char ** ppTokOutput,
                                                       int cmockNumCalls )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char pFitNum[] = "1";

    ( void ) ppString;

    if( *ppTokOutput )
    {
        free( *ppTokOutput );
        *ppTokOutput = NULL;
    }

    if( cmockNumCalls < 7 )
    {
        if( cmockNumCalls == 1 )
        {
            if( parseRegStatusCase > 0 )
            {
                handleNextTok_parseRegStatusCase( ppTokOutput, parseRegStatusCase );
            }
            else
            {
                *ppTokOutput = malloc( sizeof( pFitNum ) );
                memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
            }
        }
        else if( cmockNumCalls == 2 )
        {
            if( parseLacTacInRegCase == 1 )
            {
                char pTestString[] = "65536";
                *ppTokOutput = malloc( sizeof( pTestString ) );
                memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
            }
            else if( parseLacTacInRegCase == 2 )
            {
                char pTestString[] = "-3";
                *ppTokOutput = malloc( sizeof( pTestString ) );
                memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
            }
            else
            {
                *ppTokOutput = malloc( sizeof( pFitNum ) );
                memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
            }
        }
        else if( cmockNumCalls == 3 )
        {
            if( parseCellIdInRegCase == 1 )
            {
                char pTestString[] = "-10";
                *ppTokOutput = malloc( sizeof( pTestString ) );
                memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
            }
            else
            {
                *ppTokOutput = malloc( sizeof( pFitNum ) );
                memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
            }
        }
        else if( cmockNumCalls == 4 )
        {
            if( parseRatInfoInRegCase > 0 )
            {
                handleNextTok_parseRatInfoInRegCase( ppTokOutput, parseRatInfoInRegCase );
            }
            else
            {
                char pTestString[] = "0";
                *ppTokOutput = malloc( sizeof( pTestString ) );
                memcpy( *ppTokOutput, pTestString, sizeof( pTestString ) );
            }
        }
        else if( cmockNumCalls == 5 )
        {
            if( parseRejectTypeInRegCase > 0 )
            {
                handleNextTok_parseRejectTypeInRegCase( ppTokOutput, parseRejectTypeInRegCase );
            }
            else
            {
                *ppTokOutput = malloc( sizeof( pFitNum ) );
                memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
            }
        }
        else if( cmockNumCalls == 6 )
        {
            if( parseRejectCauseInRegCase > 0 )
            {
                handleNextTok_parseRejectCauseInRegCase( ppTokOutput, parseRejectCauseInRegCase );
            }
            else
            {
                *ppTokOutput = malloc( sizeof( pFitNum ) );
                memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
            }
        }
        else
        {
            if( returnNULL != 0 )
            {
                /* Do nothing to return NULL token. */
            }
            else
            {
                *ppTokOutput = malloc( sizeof( pFitNum ) );
                memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
            }
        }
    }
    else
    {
        atCoreStatus = CELLULAR_AT_ERROR;
    }

    return atCoreStatus;
}

CellularPktStatus_t Mock__Cellular_TranslateAtCoreStatus_Callback( CellularATError_t status,
                                                                   int cmockNumCalls )
{
    CellularPktStatus_t pktStatus;

    ( void ) cmockNumCalls;

    switch( status )
    {
        case CELLULAR_AT_SUCCESS:
            pktStatus = CELLULAR_PKT_STATUS_OK;
            break;

        case CELLULAR_AT_BAD_PARAMETER:
            pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
            break;

        case CELLULAR_AT_NO_MEMORY:
        case CELLULAR_AT_UNSUPPORTED:
        case CELLULAR_AT_MODEM_ERROR:
        case CELLULAR_AT_ERROR:
        case CELLULAR_AT_UNKNOWN:
        default:
            pktStatus = CELLULAR_PKT_STATUS_FAILURE;
            break;
    }

    return pktStatus;
}

void cellularUrcNetworkRegistrationCallback( CellularUrcEvent_t urcEvent,
                                             const CellularServiceStatus_t * pServiceStatus,
                                             void * pCallbackContext )
{
    ( void ) urcEvent;
    ( void ) pServiceStatus;
    ( void ) pCallbackContext;
}

/* ========================================================================== */

/**
 * @brief Test that any NULL handler case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_FAILURE.
 */
void test_Cellular_ParseRegStatus_Null_Handler( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;

    packetStatus = _Cellular_ParseRegStatus( NULL, NULL, false, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, packetStatus );
}

/**
 * @brief Test that any NULL RegPayload case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_BAD_PARAM.
 */
void test_Cellular_ParseRegStatus_Null_RegPayload( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    packetStatus = _Cellular_ParseRegStatus( &context, NULL, false, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, packetStatus );
}

/**
 * @brief Test that reject type/case for REGISTRATION_STATUS_REGISTRATION_DENIED to return CELLULAR_PKT_STATUS_OK.
 */
void test_Cellular_ParseRegStatus_CELLULAR_REG_POS_REJ_TYPE_Cause_Registration_Denied( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.libAtData.csRegStatus = REGISTRATION_STATUS_REGISTRATION_DENIED;
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );
    parseRegStatusCase = 3;
    parseRatInfoInRegCase = 3;
    packetStatus = _Cellular_ParseRegStatus( &context, "+CREG: 2", false, CELLULAR_REG_TYPE_CREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, packetStatus );
}

/**
 * @brief Test that CELLULAR_REG_POS_RAT invalid value case to return CELLULAR_PKT_STATUS_OK.
 */
void test_Cellular_ParseRegStatus_CELLULAR_REG_POS_RAT_Invalid_Value( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );
    parseRatInfoInRegCase = 3;
    packetStatus = _Cellular_ParseRegStatus( &context, "+CREG: 2", false, CELLULAR_REG_TYPE_CREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, packetStatus );
}

/**
 * @brief Test that register out of upper bound range case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_FAILURE.
 */
void test_Cellular_ParseRegStatus_Regs_OutOfUpperBoundRange( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );
    parseRegStatusCase = 1;
    parseLacTacInRegCase = 1;
    parseCellIdInRegCase = 1;
    parseRatInfoInRegCase = 1;
    parseRejectTypeInRegCase = 1;
    parseRejectCauseInRegCase = 1;
    packetStatus = _Cellular_ParseRegStatus( &context, "+CEREG: 2", false, CELLULAR_REG_TYPE_CEREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, packetStatus );
}

/**
 * @brief Test that register out of lower bound range case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_FAILURE.
 */
void test_Cellular_ParseRegStatus_Regs_OutOfLowerBoundRange( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );
    parseRegStatusCase = 5;
    parseLacTacInRegCase = 2;
    parseCellIdInRegCase = 1;
    /* CELLULAR_RAT_EDGE case. */
    parseRatInfoInRegCase = 4;
    parseRejectTypeInRegCase = 3;
    parseRejectCauseInRegCase = 3;
    packetStatus = _Cellular_ParseRegStatus( &context, "+CEREG: 2", false, CELLULAR_REG_TYPE_CEREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, packetStatus );
}

/**
 * @brief Test that atoi fail case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_FAILURE.
 */
void test_Cellular_ParseRegStatus_Regs_Atoi_Fail( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );
    parseRegStatusCase = 1;
    parseLacTacInRegCase = 1;
    parseCellIdInRegCase = 1;
    parseRejectTypeInRegCase = 1;
    parseRejectCauseInRegCase = 3;
    atoiFailure = 1;
    packetStatus = _Cellular_ParseRegStatus( &context, "+CEREG: 2", false, CELLULAR_REG_TYPE_CEREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, packetStatus );
}

/**
 * @brief Test that CELLULAR_RAT_CATM1 case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_OK.
 */
void test_Cellular_ParseRegStatus_CELLULAR_RAT_CATM1( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );
    /* CELLULAR_RAT_CATM1 case. */
    parseRatInfoInRegCase = 5;
    packetStatus = _Cellular_ParseRegStatus( &context, "+CEREG: 2", false, CELLULAR_REG_TYPE_CEREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, packetStatus );
}

/**
 * @brief Test that CELLULAR_REG_POS_RAT CELLULAR_RAT_LTE case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_OK.
 */
void test_Cellular_ParseRegStatus_CELLULAR_REG_POS_RAT_Status_CELLULAR_RAT_LTE( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );
    parseRatInfoInRegCase = 2;
    packetStatus = _Cellular_ParseRegStatus( &context, "+CEREG: 2", false, CELLULAR_REG_TYPE_CEREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, packetStatus );
}

/**
 * @brief Test that CELLULAR_REG_TYPE_CEREG clear atlib data case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_OK.
 */
void test_Cellular_ParseRegStatus_CELLULAR_REG_TYPE_CEREG_Status_Clear_AtLib_Data( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );
    parseRegStatusCase = 4;
    parseRatInfoInRegCase = 6;
    packetStatus = _Cellular_ParseRegStatus( &context, "+CEREG: 2", false, CELLULAR_REG_TYPE_CEREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, packetStatus );
}

/**
 * @brief Test that CELLULAR_REG_TYPE_CEREG status registration denied case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_OK.
 */
void test_Cellular_ParseRegStatus_CELLULAR_REG_TYPE_CEREG_Status_Registration_Denied( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );
    parseRegStatusCase = 3;
    packetStatus = _Cellular_ParseRegStatus( &context, "+CEREG: 2", false, CELLULAR_REG_TYPE_CEREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, packetStatus );
}

/**
 * @brief Test that CELLULAR_REG_TYPE_CEREG status registration roaming case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_OK.
 */
void test_Cellular_ParseRegStatus_CELLULAR_REG_TYPE_CEREG_Status_Registration_Roaming( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );
    parseRegStatusCase = 2;
    packetStatus = _Cellular_ParseRegStatus( &context, "+CEREG: 2", false, CELLULAR_REG_TYPE_CEREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, packetStatus );
}

/**
 * @brief Test that CELLULAR_REG_TYPE_CEREG happy path case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_OK.
 */
void test_Cellular_ParseRegStatus_CELLULAR_REG_TYPE_CEREG_Happy_Path( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.cbEvents.networkRegistrationCallback = cellularUrcNetworkRegistrationCallback;
    _Cellular_NetworkRegistrationCallback_Ignore();
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );
    returnNULL = 1;
    packetStatus = _Cellular_ParseRegStatus( &context, "+CEREG: 2", false, CELLULAR_REG_TYPE_CEREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, packetStatus );
}

/**
 * @brief Test that CELLULAR_REG_TYPE_CREG happy path case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_OK.
 */
void test_Cellular_ParseRegStatus_CELLULAR_REG_TYPE_CREG_Happy_Path( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.cbEvents.networkRegistrationCallback = cellularUrcNetworkRegistrationCallback;
    _Cellular_NetworkRegistrationCallback_Ignore();
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );

    packetStatus = _Cellular_ParseRegStatus( &context, "+CREG: 2", false, CELLULAR_REG_TYPE_CREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, packetStatus );
}

/**
 * @brief Test that CELLULAR_REG_TYPE_CGREG happy path case _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_OK.
 */
void test_Cellular_ParseRegStatus_CELLULAR_REG_TYPE_CGREG_Happy_Path( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.cbEvents.networkRegistrationCallback = cellularUrcNetworkRegistrationCallback;
    _Cellular_NetworkRegistrationCallback_Ignore();
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );

    packetStatus = _Cellular_ParseRegStatus( &context, "+CGREG: 2", false, CELLULAR_REG_TYPE_CGREG );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, packetStatus );
}

/**
 * @brief Test that CELLULAR_REG_TYPE_UNKNOWN case for _Cellular_ParseRegStatus to return CELLULAR_PKT_STATUS_OK.
 *
 */
void test_Cellular_ParseRegStatus_CELLULAR_REG_TYPE_UNKNOWN( void )
{
    CellularPktStatus_t packetStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Callback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi_Callback );
    _Cellular_TranslateAtCoreStatus_StubWithCallback( Mock__Cellular_TranslateAtCoreStatus_Callback );

    packetStatus = _Cellular_ParseRegStatus( &context, "123456789", false, CELLULAR_REG_TYPE_UNKNOWN );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, packetStatus );
}

/**
 * @brief Test that failure path case case Cellular_CommonUrcProcessCreg to return CELLULAR_PKT_STATUS_FAILURE.
 */
void test_Cellular_CommonUrcProcessCreg_AtCmd_Failure_Path( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_NetworkRegistrationCallback_Ignore();
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_ERROR, CELLULAR_PKT_STATUS_FAILURE );

    pktStatus = Cellular_CommonUrcProcessCreg( &context, "+QIURC: \"pdpdeact\",1" );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );
}

/**
 * @brief Test that null context case case Cellular_CommonUrcProcessCreg to return CELLULAR_PKT_STATUS_INVALID_HANDLE.
 */
void test_Cellular_CommonUrcProcessCreg_Null_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    pktStatus = Cellular_CommonUrcProcessCreg( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that failure path case case Cellular_CommonUrcProcessCgreg to return CELLULAR_PKT_STATUS_FAILURE.
 */
void test_Cellular_CommonUrcProcessCgreg_AtCmd_Failure_Path( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_NetworkRegistrationCallback_Ignore();
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_ERROR, CELLULAR_PKT_STATUS_FAILURE );
    pktStatus = Cellular_CommonUrcProcessCgreg( &context, "+QIURC: \"pdpdeact\",1" );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );
}

/**
 * @brief Test that null context case case Cellular_CommonUrcProcessCgreg to return CELLULAR_PKT_STATUS_INVALID_HANDLE.
 */
void test_Cellular_CommonUrcProcessCgreg_Null_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    pktStatus = Cellular_CommonUrcProcessCgreg( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that happy path case case Cellular_CommonUrcProcessCereg to return CELLULAR_PKT_STATUS_FAILURE.
 */
void test_Cellular_CommonUrcProcessCereg_AtCmd_Failure_Path( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_NetworkRegistrationCallback_Ignore();
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_ERROR, CELLULAR_PKT_STATUS_FAILURE );

    pktStatus = Cellular_CommonUrcProcessCereg( &context, "+QIURC: \"pdpdeact\",1" );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );
}

/**
 * @brief Test that null context case case Cellular_CommonUrcProcessCereg to return CELLULAR_PKT_STATUS_INVALID_HANDLE.
 */
void test_Cellular_CommonUrcProcessCereg_Null_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    pktStatus = Cellular_CommonUrcProcessCereg( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}
