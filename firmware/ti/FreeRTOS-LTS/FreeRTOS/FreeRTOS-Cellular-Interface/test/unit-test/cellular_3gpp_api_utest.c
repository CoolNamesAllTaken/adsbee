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
 * @file cellular_3gpp_api_utest.c
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
#include "mock_cellular_at_core.h"


/**
 * @brief Cellular sample prefix string input.
 */
#define CELLULAR_SAMPLE_PREFIX_STRING_INPUT                        "+CPIN:READY"

/**
 * @brief Cellular sample network registration URC not registered.
 */
#define CELLULAR_SAMPLE_NETWORK_REGISTRATION_RESPONSE              "+CREG: 2,2"

/**
 * @brief Cellular sample network registration URC not registered.
 */
#define CELLULAR_SAMPLE_NETWORK_REGISTRATION_URC_NOT_REGISTERED    "+CREG: 2"

/**
 * @brief Cellular sample network registration URC registered.
 */
#define CELLULAR_SAMPLE_NETWORK_REGISTRATION_URC_REGISTERED        "+CREG: 1,\"FFFE\",\"341B50D\", 8"

/**
 * @brief Cellular sample prefix string output.
 */
#define CELLULAR_SAMPLE_PREFIX_STRING_OUTPUT                       "READY"

/**
 * @brief operator information.
 */
typedef struct cellularOperatorInfo
{
    CellularPlmnInfo_t plmnInfo;                             /* Device registered PLMN info (MCC and MNC).  */
    CellularRat_t rat;                                       /* Device registered Radio Access Technology (Cat-M, Cat-NB, GPRS etc).  */
    CellularNetworkRegistrationMode_t networkRegMode;        /* Network Registered mode of the device (Manual, Auto etc).   */
    CellularOperatorNameFormat_t operatorNameFormat;         /* Format of registered network operator name. */
    char operatorName[ CELLULAR_NETWORK_NAME_MAX_SIZE + 1 ]; /* Registered network operator name. */
} cellularOperatorInfo_t;

typedef enum parseTimeConditionState
{
    PARSE_TIME_FIRST_CALL_FAILURE_CONDITION = 6,
    PARSE_TIME_SECOND_CALL_FAILURE_CONDITION = 7,
    PARSE_TIME_THIRD_CALL_FAILURE_CONDITION = 8,
    PARSE_TIME_FOURTH_CALL_FAILURE_CONDITION = 9,
    PARSE_TIME_FIFTH_CALL_FAILURE_CONDITION = 10,
    PARSE_TIME_SIXTH_CALL_FAILURE_CONDITION = 11
} parseTimeConditionState_t;

static int cbCondition = 0;
static int parseRegFailureCase = 0;
static int parseNetworkTimeFailureCase = 0;
static int parseNetworkNameFailureCase = 0;
static int cpsms_pos_mode_error = 0;
static int recvFuncGetHplmnCase = 0;
static int parseHplmn_test = 0;
static int simLockStateTestCase = 0;
static int psmSettingsCheckTimerValue = 0;
static int psmSettingsTimerIndex = -1;
static int psmSettingsTimerError = 0;
static int psmSettingsActiveTimerValue = 0;
static int parseEidrxTokenOutOfRange = 0;
static int mallocAllocFail = 0;
static int nullTokenFirst = 0;
static int checkCrsmReadStatusCase = 0;
static int negativeNumberCase = 0;
static int commonCase = 0;
static int wrongDataLength = 0;

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    cbCondition = 0;
    parseRegFailureCase = 0;
    parseNetworkTimeFailureCase = 0;
    parseNetworkNameFailureCase = 0;
    cpsms_pos_mode_error = 0;
    recvFuncGetHplmnCase = 0;
    parseHplmn_test = 0;
    simLockStateTestCase = 0;
    psmSettingsCheckTimerValue = 0;
    psmSettingsTimerIndex = -1;
    psmSettingsTimerError = 0;
    psmSettingsActiveTimerValue = 0;
    parseEidrxTokenOutOfRange = 0;
    mallocAllocFail = 0;
    nullTokenFirst = 0;
    checkCrsmReadStatusCase = 0;
    negativeNumberCase = 0;
    commonCase = 0;
    wrongDataLength = 0;
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

bool MockPlatformMutex_Create( PlatformMutex_t * pNewMutex,
                               bool recursive )
{
    ( void ) pNewMutex;
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

CellularPktStatus_t Mock_AtcmdRequestWithCallback( CellularContext_t * pContext,
                                                   CellularAtReq_t atReq,
                                                   int cmock_num_calls )
{
    cellularOperatorInfo_t * pOperatorInfo;

    ( void ) pContext;

    if( cmock_num_calls == 0 )
    {
        /* AT+COPS=3,2 call. */
    }
    else if( cmock_num_calls == 1 )
    {
        /* AT+COPS? call. */
        pOperatorInfo = ( cellularOperatorInfo_t * ) atReq.pData;
        pOperatorInfo->rat = CELLULAR_RAT_INVALID;
    }
    else
    {
        TEST_FAIL_MESSAGE( "Unexpected Mock_AtcmdRequestWithCallback call" );
    }

    return CELLULAR_PKT_STATUS_OK;
}

static void _saveData( char * pLine,
                       CellularATCommandResponse_t * pResp,
                       uint32_t dataLen )
{
    CellularATCommandLine_t * pNew = NULL, * pTemp = NULL;

    ( void ) dataLen;

    pNew = ( CellularATCommandLine_t * ) malloc( sizeof( CellularATCommandLine_t ) );
    /* coverity[misra_c_2012_rule_10_5_violation] */
    configASSERT( ( int32_t ) ( pNew != NULL ) );

    /* Reuse the pktio buffer instead of allocate. */
    pNew->pLine = pLine;
    pNew->pNext = NULL;

    if( pResp->pItm == NULL )
    {
        pResp->pItm = pNew;
    }
    else
    {
        pTemp = pResp->pItm;

        while( pTemp->pNext != NULL )
        {
            pTemp = pTemp->pNext;
        }

        pTemp->pNext = pNew;
    }
}

CellularPktStatus_t handleCommonCallback( CellularContext_t * pContext,
                                          CellularAtReq_t atReq )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    /* null context */
    if( cbCondition == 0 )
    {
        pktStatus = atReq.respCallback( NULL, NULL, NULL, 0 );
    }
    /* AtResp */
    else if( cbCondition == 1 )
    {
        /* null AtResp */
        if( commonCase == 0 )
        {
            pktStatus = atReq.respCallback( pContext, NULL, NULL, 0 );
        }
        /* null AtResp item */
        else if( commonCase == 1 )
        {
            pktStatus = atReq.respCallback( pContext, &atResp, NULL, 0 );
        }
        /* null AtResp item line */
        else if( commonCase == 2 )
        {
            char * pLine = NULL;

            _saveData( pLine, &atResp, sizeof( pLine ) );
            pktStatus = atReq.respCallback( pContext, &atResp, NULL, 0 );
        }
    }
    /* null data pointer */
    else if( cbCondition == 2 )
    {
        /* null data pointer */
        if( commonCase == 0 )
        {
            char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, NULL, 0 );
        }
        /* wrong data length */
        else if( commonCase == 1 )
        {
            char pData[ 2 ];
            char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, wrongDataLength );
        }
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime( CellularContext_t * pContext,
                                                                                    CellularAtReq_t atReq,
                                                                                    int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    char pData[ 20 ];

    ( void ) cmock_num_calls;

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cbCondition < 3 )
    {
        pktStatus = handleCommonCallback( pContext, atReq );
    }
    else if( ( cbCondition == 3 ) || ( cbCondition == 4 ) )
    {
        char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

        _saveData( pLine, &atResp, strlen( pLine ) + 1 );
        pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
    }
    else if( cbCondition == 5 )
    {
        if( commonCase == 0 )
        {
            char pLine[] = "-0519−00402";

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
        }
        else if( commonCase == 1 )
        {
            char pLine[] = "255";

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
        }
    }
    else if( cbCondition >= 6 )
    {
        char pLine[] = "+255";

        _saveData( pLine, &atResp, strlen( pLine ) + 1 );
        pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
    }

    return pktStatus;
}

CellularATError_t Mock_Cellular_ATStrtoi( const char * pStr,
                                          int32_t base,
                                          int32_t * pResult,
                                          int cmock_num_calls )
{
    ( void ) base;

    if( cbCondition < PARSE_TIME_FIRST_CALL_FAILURE_CONDITION )
    {
        *pResult = atoi( pStr );
    }
    else
    {
        if( cbCondition == PARSE_TIME_FIRST_CALL_FAILURE_CONDITION )
        {
            if( cmock_num_calls == 1 )
            {
                if( negativeNumberCase == 1 )
                {
                    *pResult = atoi( "-255" );
                }
                else
                {
                    *pResult = atoi( "+655350" );
                }
            }
            else
            {
                *pResult = atoi( pStr );
            }
        }
        else if( cbCondition == PARSE_TIME_SECOND_CALL_FAILURE_CONDITION )
        {
            if( cmock_num_calls == 2 )
            {
                if( negativeNumberCase == 1 )
                {
                    *pResult = atoi( "-255" );
                }
                else
                {
                    *pResult = atoi( "+655350" );
                }
            }
            else
            {
                *pResult = atoi( pStr );
            }
        }
        else if( cbCondition == PARSE_TIME_THIRD_CALL_FAILURE_CONDITION )
        {
            if( cmock_num_calls == 3 )
            {
                if( negativeNumberCase == 1 )
                {
                    *pResult = atoi( "-255" );
                }
                else
                {
                    *pResult = atoi( "+655350" );
                }
            }
            else
            {
                *pResult = atoi( pStr );
            }
        }
        else if( cbCondition == PARSE_TIME_FOURTH_CALL_FAILURE_CONDITION )
        {
            if( cmock_num_calls == 4 )
            {
                if( negativeNumberCase == 1 )
                {
                    *pResult = atoi( "-255" );
                }
                else
                {
                    *pResult = atoi( "+655350" );
                }
            }
            else
            {
                *pResult = atoi( pStr );
            }
        }
        else if( cbCondition == PARSE_TIME_FIFTH_CALL_FAILURE_CONDITION )
        {
            if( cmock_num_calls == 5 )
            {
                if( negativeNumberCase == 1 )
                {
                    *pResult = atoi( "-255" );
                }
                else
                {
                    *pResult = atoi( "+655350" );
                }
            }
            else
            {
                *pResult = atoi( pStr );
            }
        }
        else if( cbCondition == PARSE_TIME_SIXTH_CALL_FAILURE_CONDITION )
        {
            if( cmock_num_calls == 6 )
            {
                if( negativeNumberCase == 1 )
                {
                    *pResult = atoi( "-255" );
                }
                else
                {
                    *pResult = atoi( "+655350" );
                }
            }
            else
            {
                *pResult = atoi( pStr );
            }
        }
    }

    return CELLULAR_AT_SUCCESS;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetFirmwareVersion( CellularContext_t * pContext,
                                                                                                  CellularAtReq_t atReq,
                                                                                                  int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    char pData[ CELLULAR_FW_VERSION_MAX_SIZE + 1 ];

    ( void ) cmock_num_calls;

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cbCondition < 3 )
    {
        pktStatus = handleCommonCallback( pContext, atReq );
    }
    else if( cbCondition == 3 )
    {
        char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

        _saveData( pLine, &atResp, strlen( pLine ) + 1 );
        pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetImei( CellularContext_t * pContext,
                                                                                       CellularAtReq_t atReq,
                                                                                       int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    char pData[ CELLULAR_IMEI_MAX_SIZE + 1 ];

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cmock_num_calls > 0 )
    {
        if( cbCondition < 3 )
        {
            pktStatus = handleCommonCallback( pContext, atReq );
        }
        else if( cbCondition == 3 )
        {
            char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
        }
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetModelId( CellularContext_t * pContext,
                                                                                CellularAtReq_t atReq,
                                                                                int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    char pData[ CELLULAR_MODEL_ID_MAX_SIZE + 1 ];

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cmock_num_calls > 1 )
    {
        if( cbCondition < 3 )
        {
            pktStatus = handleCommonCallback( pContext, atReq );
        }
        else if( cbCondition == 3 )
        {
            char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
        }
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetManufactureId( CellularContext_t * pContext,
                                                                                      CellularAtReq_t atReq,
                                                                                      int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    char pData[ CELLULAR_MANUFACTURE_ID_MAX_SIZE + 1 ];

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cmock_num_calls > 2 )
    {
        if( cbCondition < 3 )
        {
            pktStatus = handleCommonCallback( pContext, atReq );
        }
        else if( cbCondition == 3 )
        {
            char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
        }
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg( CellularContext_t * pContext,
                                                                                   CellularAtReq_t atReq,
                                                                                   int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    char pData[ sizeof( CellularNetworkRegType_t ) ];

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cmock_num_calls < 1 )
    {
        if( cbCondition < 3 )
        {
            pktStatus = handleCommonCallback( pContext, atReq );
        }
        else if( cbCondition == 3 )
        {
            char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
        }
        else if( cbCondition == 4 )
        {
            char pLine[] = CELLULAR_SAMPLE_NETWORK_REGISTRATION_URC_NOT_REGISTERED;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
        }
        else if( cbCondition == 5 )
        {
            char pLine[] = CELLULAR_SAMPLE_NETWORK_REGISTRATION_URC_REGISTERED;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
        }
        else if( cbCondition == 6 )
        {
            char pLine[] = CELLULAR_SAMPLE_NETWORK_REGISTRATION_RESPONSE;
            char pLine2[] = CELLULAR_SAMPLE_NETWORK_REGISTRATION_URC_REGISTERED;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            _saveData( pLine2, &atResp, strlen( pLine2 ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, sizeof( pData ) );
        }
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc( CellularContext_t * pContext,
                                                                                  CellularAtReq_t atReq,
                                                                                  int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    cellularOperatorInfo_t cellularOperatorInfo;

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );
    memset( &cellularOperatorInfo, 0, sizeof( cellularOperatorInfo_t ) );

    if( cmock_num_calls == 0 )
    {
        /* AT+COPS=3,2 call. */
    }
    else if( cmock_num_calls == 1 )
    {
        /* AT+COPS? call. */
        if( cbCondition < 3 )
        {
            pktStatus = handleCommonCallback( pContext, atReq );
        }
        else if( cbCondition == 3 )
        {
            char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );

            if( parseNetworkNameFailureCase == 2 )
            {
                cellularOperatorInfo.operatorNameFormat = OPERATOR_NAME_FORMAT_LONG;
                pktStatus = atReq.respCallback( pContext, &atResp, &cellularOperatorInfo, sizeof( cellularOperatorInfo_t ) );
            }
            else if( parseNetworkNameFailureCase == 3 )
            {
                cellularOperatorInfo.operatorNameFormat = OPERATOR_NAME_FORMAT_NUMERIC;
                pktStatus = atReq.respCallback( pContext, &atResp, &cellularOperatorInfo, sizeof( cellularOperatorInfo_t ) );
            }
            else
            {
                pktStatus = atReq.respCallback( pContext, &atResp, &cellularOperatorInfo, sizeof( cellularOperatorInfo_t ) );
            }
        }
    }
    else
    {
        TEST_FAIL_MESSAGE( "Unexpected Mock_AtcmdRequestWithCallback call" );
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings( CellularContext_t * pContext,
                                                                                               CellularAtReq_t atReq,
                                                                                               int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    CellularEidrxSettingsList_t cellularEidrxSettingsList;

    ( void ) cmock_num_calls;
    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cbCondition < 3 )
    {
        pktStatus = handleCommonCallback( pContext, atReq );
    }
    else if( cbCondition == 3 )
    {
        char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;
        char pLine2[] = "+CEDRXS: 0";

        _saveData( pLine, &atResp, strlen( pLine ) + 1 );
        _saveData( pLine2, &atResp, sizeof( pLine2 ) );
        pktStatus = atReq.respCallback( pContext, &atResp, &cellularEidrxSettingsList, sizeof( CELLULAR_EDRX_LIST_MAX_SIZE ) );
    }
    else if( cbCondition == 4 )
    {
        char pLine[] = "+CEDRXS:";
        char pLine2[] = "+CEDRXS: 0";
        _saveData( pLine, &atResp, sizeof( pLine ) );
        _saveData( pLine2, &atResp, sizeof( pLine2 ) );
        pktStatus = atReq.respCallback( pContext, &atResp, &cellularEidrxSettingsList, sizeof( CELLULAR_EDRX_LIST_MAX_SIZE ) );
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings( CellularContext_t * pContext,
                                                                                    CellularAtReq_t atReq,
                                                                                    int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    CellularPsmSettings_t cellularPsmSettings;

    ( void ) cmock_num_calls;
    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cbCondition < 3 )
    {
        pktStatus = handleCommonCallback( pContext, atReq );
    }
    else if( cbCondition == 3 )
    {
        char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

        _saveData( pLine, &atResp, strlen( pLine ) + 1 );
        memset( &cellularPsmSettings, 0, sizeof( CellularPsmSettings_t ) );
        pktStatus = atReq.respCallback( pContext, &atResp, &cellularPsmSettings, sizeof( CellularPsmSettings_t ) );

        if( psmSettingsCheckTimerValue == 1 )
        {
            uint32_t ulTimeValueSeconds = 0U;

            if( psmSettingsTimerIndex == 0 )
            {
                ulTimeValueSeconds = psmSettingsActiveTimerValue * 2U;
            }
            else if( psmSettingsTimerIndex == 1 )
            {
                ulTimeValueSeconds = psmSettingsActiveTimerValue * 60U;
            }
            else if( psmSettingsTimerIndex == 2 )
            {
                ulTimeValueSeconds = psmSettingsActiveTimerValue * 6 * 60U;
            }
            else if( psmSettingsTimerIndex == 7 )
            {
                ulTimeValueSeconds = 0xFFFFFFFFU;
            }
            else
            {
                ulTimeValueSeconds = 0U;
            }

            TEST_ASSERT_EQUAL_INT( ulTimeValueSeconds, cellularPsmSettings.activeTimeValue );
        }
    }
    else if( cbCondition == 4 )
    {
        char pLine[] = "+CEDRXS: 0";

        _saveData( pLine, &atResp, sizeof( pLine ) );
        pktStatus = atReq.respCallback( pContext, &atResp, &cellularPsmSettings, sizeof( CellularPsmSettings_t ) );
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetIccid( CellularContext_t * pContext,
                                                                              CellularAtReq_t atReq,
                                                                              int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    char pData[ strlen( CELLULAR_SAMPLE_PREFIX_STRING_INPUT ) + 1 ];

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cmock_num_calls == 2 )
    {
        if( cbCondition < 3 )
        {
            pktStatus = handleCommonCallback( pContext, atReq );
        }
        else if( cbCondition == 3 )
        {
            char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, CELLULAR_ICCID_MAX_SIZE + 1 );
        }
        else if( cbCondition == 4 )
        {
            char pLine[] = "This is testing string for greater than 20.";

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, CELLULAR_ICCID_MAX_SIZE + 1 );
        }
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetImsi( CellularContext_t * pContext,
                                                                             CellularAtReq_t atReq,
                                                                             int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    char pData[ strlen( CELLULAR_SAMPLE_PREFIX_STRING_INPUT ) + 1 ];

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cmock_num_calls == 0 )
    {
        if( cbCondition < 3 )
        {
            pktStatus = handleCommonCallback( pContext, atReq );
        }
        else if( cbCondition == 3 )
        {
            char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, CELLULAR_IMSI_MAX_SIZE + 1 );
        }
        else if( cbCondition == 4 )
        {
            char pLine[] = "This is the testing long string.";

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, pData, CELLULAR_IMSI_MAX_SIZE + 1 );
        }
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn( CellularContext_t * pContext,
                                                                              CellularAtReq_t atReq,
                                                                              int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    CellularPlmnInfo_t cellularPlmnInfo;

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cmock_num_calls == 1 )
    {
        if( cbCondition < 3 )
        {
            pktStatus = handleCommonCallback( pContext, atReq );
        }
        else if( cbCondition == 3 )
        {
            char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

            _saveData( pLine, &atResp, strlen( pLine ) + 1 );
            pktStatus = atReq.respCallback( pContext, &atResp, &cellularPlmnInfo, sizeof( CellularPlmnInfo_t ) );
        }
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_RecvFuncIpAddress( CellularContext_t * pContext,
                                                                               CellularAtReq_t atReq,
                                                                               int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    CellularEidrxSettingsList_t cellularEidrxSettingsList;

    ( void ) cmock_num_calls;

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cbCondition < 3 )
    {
        pktStatus = handleCommonCallback( pContext, atReq );
    }
    else if( cbCondition == 3 )
    {
        char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

        _saveData( pLine, &atResp, strlen( pLine ) + 1 );
        pktStatus = atReq.respCallback( pContext, &atResp, &cellularEidrxSettingsList, sizeof( CELLULAR_EDRX_LIST_MAX_SIZE ) );
    }
    else if( cbCondition == 4 )
    {
        char pLine[] = "+CEDRXS: 0";

        _saveData( pLine, &atResp, sizeof( pLine ) );
        pktStatus = atReq.respCallback( pContext, &atResp, &cellularEidrxSettingsList, sizeof( CELLULAR_EDRX_LIST_MAX_SIZE ) );
    }
    else if( cbCondition == 5 )
    {
        char pLine = '\0';

        _saveData( &pLine, &atResp, sizeof( pLine ) );
        pktStatus = atReq.respCallback( pContext, &atResp, &cellularEidrxSettingsList, sizeof( CELLULAR_EDRX_LIST_MAX_SIZE ) );
    }

    return pktStatus;
}

CellularPktStatus_t Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus( CellularContext_t * pContext,
                                                                                      CellularAtReq_t atReq,
                                                                                      int cmock_num_calls )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATCommandResponse_t atResp;
    CellularSimCardLockState_t cellularSimCardLockState;

    ( void ) cmock_num_calls;

    memset( &atResp, 0, sizeof( CellularATCommandResponse_t ) );

    if( cbCondition < 3 )
    {
        pktStatus = handleCommonCallback( pContext, atReq );
    }
    else if( cbCondition == 3 )
    {
        char pLine[] = CELLULAR_SAMPLE_PREFIX_STRING_INPUT;

        _saveData( pLine, &atResp, strlen( pLine ) + 1 );
        pktStatus = atReq.respCallback( pContext, &atResp, &cellularSimCardLockState, sizeof( CellularSimCardLockState_t ) );
    }
    else if( cbCondition == 4 )
    {
        char pLine[] = "+CEDRXS: 0";

        _saveData( pLine, &atResp, sizeof( pLine ) );
        pktStatus = atReq.respCallback( pContext, &atResp, &cellularSimCardLockState, sizeof( CellularSimCardLockState_t ) );
    }

    return pktStatus;
}

void handle_simLockStateTestCase( char ** ppTokOutput,
                                  int simLockStateTestCase )
{
    switch( simLockStateTestCase )
    {
        case 1:
            *ppTokOutput = malloc( strlen( "READY" ) + 1 );
            strcpy( *ppTokOutput, "READY" );
            break;

        case 2:
            *ppTokOutput = malloc( strlen( "SIM PIN" ) + 1 );
            strcpy( *ppTokOutput, "SIM PIN" );
            break;

        case 3:
            *ppTokOutput = malloc( strlen( "SIM PUK" ) + 1 );
            strcpy( *ppTokOutput, "SIM PUK" );
            break;

        case 4:
            *ppTokOutput = malloc( strlen( "SIM PIN2" ) + 1 );
            strcpy( *ppTokOutput, "SIM PIN2" );
            break;

        case 5:
            *ppTokOutput = malloc( strlen( "SIM PUK2" ) + 1 );
            strcpy( *ppTokOutput, "SIM PUK2" );
            break;

        case 6:
            *ppTokOutput = malloc( strlen( "PH-NET PIN" ) + 1 );
            strcpy( *ppTokOutput, "PH-NET PIN" );
            break;

        case 7:
            *ppTokOutput = malloc( strlen( "PH-NET PUK" ) + 1 );
            strcpy( *ppTokOutput, "PH-NET PUK" );
            break;

        case 8:
            *ppTokOutput = malloc( strlen( "PH-NETSUB PIN" ) + 1 );
            strcpy( *ppTokOutput, "PH-NETSUB PIN" );
            break;

        case 9:
            *ppTokOutput = malloc( strlen( "PH-NETSUB PUK" ) + 1 );
            strcpy( *ppTokOutput, "PH-NETSUB PUK" );
            break;

        case 10:
            *ppTokOutput = malloc( strlen( "PH-SP PIN" ) + 1 );
            strcpy( *ppTokOutput, "PH-SP PIN" );
            break;

        case 11:
            *ppTokOutput = malloc( strlen( "PH-SP PUK" ) + 1 );
            strcpy( *ppTokOutput, "PH-SP PUK" );
            break;

        case 12:
            *ppTokOutput = malloc( strlen( "PH-CORP PIN" ) + 1 );
            strcpy( *ppTokOutput, "PH-CORP PIN" );
            break;

        case 13:
            *ppTokOutput = malloc( strlen( "PH-CORP PUK" ) + 1 );
            strcpy( *ppTokOutput, "PH-CORP PUK" );
            break;

        case 14:
            *ppTokOutput = malloc( strlen( "123456789" ) + 1 );
            strcpy( *ppTokOutput, "123456789" );

        default:
            break;
    }
}

CellularATError_t Mock_simLockStateTestCase_ATGetNextTok_Calback( char ** ppString,
                                                                  char ** ppTokOutput,
                                                                  int cmock_num_calls )
{
    char pFitNum[] = "1";
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    ( void ) ppString;
    ( void ) cmock_num_calls;

    if( *ppTokOutput )
    {
        free( *ppTokOutput );
        *ppTokOutput = NULL;
    }

    if( simLockStateTestCase > 0 )
    {
        handle_simLockStateTestCase( ppTokOutput, simLockStateTestCase );
    }
    else
    {
        *ppTokOutput = malloc( sizeof( pFitNum ) );
        memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
    }

    return atCoreStatus;
}

CellularATError_t Mock_parseNetworkNameFailureCase_ATGetNextTok_Calback( char ** ppString,
                                                                         char ** ppTokOutput,
                                                                         int cmock_num_calls )
{
    char pFitNum[] = "1";
    char pOutOfNameFormat[] = "3";
    char pMcc[] = "2";
    char pNumericNum[] = "123456";
    char pBigNum[] = "32";
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    ( void ) ppString;

    if( *ppTokOutput )
    {
        free( *ppTokOutput );
        *ppTokOutput = NULL;
    }

    if( cmock_num_calls == 0 )
    {
        char pFitNum[] = "1";
        *ppTokOutput = malloc( sizeof( pFitNum ) );
        memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
    }
    else if( cmock_num_calls == 1 )
    {
        if( ( parseNetworkNameFailureCase == 3 ) ||
            ( parseNetworkNameFailureCase == 5 ) )
        {
            *ppTokOutput = malloc( sizeof( pMcc ) );
            memcpy( *ppTokOutput, pMcc, sizeof( pMcc ) );
        }
        else if( parseNetworkNameFailureCase == 4 )
        {
            *ppTokOutput = malloc( sizeof( pOutOfNameFormat ) );
            memcpy( *ppTokOutput, pOutOfNameFormat, sizeof( pOutOfNameFormat ) );
        }
        else
        {
            *ppTokOutput = malloc( sizeof( pFitNum ) );
            memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
        }
    }
    else if( cmock_num_calls == 2 )
    {
        /* null data pointer. */
        if( parseNetworkNameFailureCase == 1 )
        {
            *ppTokOutput = NULL;
        }
        /* OPERATOR_NAME_FORMAT_SHORT. */
        else if( parseNetworkNameFailureCase == 2 )
        {
            *ppTokOutput = malloc( sizeof( pFitNum ) );
            memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
        }
        /* OPERATOR_NAME_FORMAT_NUMERIC. */
        else if( parseNetworkNameFailureCase == 3 )
        {
            if( commonCase == 0 )
            {
                *ppTokOutput = malloc( sizeof( pNumericNum ) );
                memcpy( *ppTokOutput, pNumericNum, sizeof( pNumericNum ) );
            }
            else if( commonCase == 1 )
            {
                char pNumericNumCaseII[] = "12345";
                *ppTokOutput = malloc( sizeof( pNumericNumCaseII ) );
                memcpy( *ppTokOutput, pNumericNumCaseII, sizeof( pNumericNumCaseII ) );
            }
        }
        /* OPERATOR_NAME_FORMAT_NUMERIC wrong length. */
        else if( parseNetworkNameFailureCase == 5 )
        {
            *ppTokOutput = malloc( sizeof( pBigNum ) );
            memcpy( *ppTokOutput, pBigNum, sizeof( pBigNum ) );
        }
        else
        {
            *ppTokOutput = malloc( sizeof( pFitNum ) );
            memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
        }
    }
    else if( cmock_num_calls == 3 )
    {
        if( parseNetworkNameFailureCase == 7 )
        {
            *ppTokOutput = malloc( sizeof( pBigNum ) );
            memcpy( *ppTokOutput, pBigNum, sizeof( pBigNum ) );
        }
        else if( parseNetworkNameFailureCase == 8 )
        {
            char pTmp[] = "8";
            *ppTokOutput = malloc( sizeof( pTmp ) );
            memcpy( *ppTokOutput, pTmp, sizeof( pTmp ) );
        }
        else if( parseNetworkNameFailureCase == 9 )
        {
            char pTmp[] = "-8";
            *ppTokOutput = malloc( sizeof( pTmp ) );
            memcpy( *ppTokOutput, pTmp, sizeof( pTmp ) );
        }
    }

    if( ( parseNetworkNameFailureCase == 6 ) ||
        ( parseNetworkNameFailureCase == 1 ) )
    {
        atCoreStatus = CELLULAR_AT_SUCCESS;
    }

    return atCoreStatus;
}

CellularATError_t Mock_recvFuncGetHplmnCase_ATGetNextTok_Calback( char ** ppString,
                                                                  char ** ppTokOutput,
                                                                  int cmock_num_calls )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char pFitNum[] = "1";

    ( void ) ppString;

    if( *ppTokOutput )
    {
        free( *ppTokOutput );
        *ppTokOutput = NULL;
    }

    if( cmock_num_calls == 0 )
    {
        if( recvFuncGetHplmnCase == 1 )
        {
            char pSts[] = "11";
            *ppTokOutput = malloc( sizeof( pSts ) );
            memcpy( *ppTokOutput, pSts, sizeof( pSts ) );
        }
        else if( checkCrsmReadStatusCase == 1 )
        {
            char pSts[] = "145";
            *ppTokOutput = malloc( sizeof( pSts ) );
            memcpy( *ppTokOutput, pSts, sizeof( pSts ) );
        }
        else if( checkCrsmReadStatusCase == 2 )
        {
            char pSts[] = "146";
            *ppTokOutput = malloc( sizeof( pSts ) );
            memcpy( *ppTokOutput, pSts, sizeof( pSts ) );
        }
        else
        {
            char pSts[] = "144";
            *ppTokOutput = malloc( sizeof( pSts ) );
            memcpy( *ppTokOutput, pSts, sizeof( pSts ) );
        }
    }
    else if( cmock_num_calls == 1 )
    {
        if( ( recvFuncGetHplmnCase == 2 ) )
        {
            *ppTokOutput = NULL;
        }
        else if( recvFuncGetHplmnCase == 3 )
        {
            char pSts[] = "64";
            *ppTokOutput = malloc( sizeof( pSts ) );
            memcpy( *ppTokOutput, pSts, sizeof( pSts ) );
        }
        else if( recvFuncGetHplmnCase > 3 )
        {
            char pSts[] = "4";
            *ppTokOutput = malloc( sizeof( pSts ) );
            memcpy( *ppTokOutput, pSts, sizeof( pSts ) );
        }
    }
    else if( cmock_num_calls == 2 )
    {
        if( recvFuncGetHplmnCase == 0 )
        {
            if( parseHplmn_test == 0 )
            {
                char pSts[] = "This is testing string.";
                *ppTokOutput = malloc( sizeof( pSts ) );
                memcpy( *ppTokOutput, pSts, sizeof( pSts ) );
            }
            else
            {
                char pSts[] = "01Ftesting string.";
                *ppTokOutput = malloc( sizeof( pSts ) );
                memcpy( *ppTokOutput, pSts, sizeof( pSts ) );
            }
        }
        else if( recvFuncGetHplmnCase == 4 )
        {
            *ppTokOutput = NULL;
        }
        else if( recvFuncGetHplmnCase == 6 )
        {
            char pSts[] = "This is testing string.";
            *ppTokOutput = malloc( sizeof( pSts ) );
            memcpy( *ppTokOutput, pSts, sizeof( pSts ) );
        }
        else if( recvFuncGetHplmnCase == 7 )
        {
            char pSts[] = "0xF2345678";
            *ppTokOutput = malloc( sizeof( pSts ) );
            memcpy( *ppTokOutput, pSts, sizeof( pSts ) );
        }
        else if( recvFuncGetHplmnCase == 8 )
        {
            char pSts[] = "FFFFFFFFFFF";
            *ppTokOutput = malloc( sizeof( pSts ) );
            memcpy( *ppTokOutput, pSts, sizeof( pSts ) );
        }
        else
        {
            *ppTokOutput = malloc( sizeof( pFitNum ) );
            memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
        }
    }

    if( ( recvFuncGetHplmnCase == 4 ) ||
        ( recvFuncGetHplmnCase == 2 ) )
    {
        atCoreStatus = CELLULAR_AT_SUCCESS;
    }

    return atCoreStatus;
}

CellularATError_t Mock_Cellular_ATGetNextTok_Calback( char ** ppString,
                                                      char ** ppTokOutput,
                                                      int cmock_num_calls )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char pFitNum[] = "1";
    char pBigNum[] = "32";
    char pNumericNum[] = "123456";
    char pNegativeNum[] = "-3";
    char pPositiveNum[] = "256";
    int len = 10;

    ( void ) ppString;

    if( *ppTokOutput )
    {
        free( *ppTokOutput );
        *ppTokOutput = NULL;
    }

    if( cmock_num_calls == 0 )
    {
        if( parseEidrxTokenOutOfRange == 1 )
        {
            *ppTokOutput = malloc( sizeof( pPositiveNum ) );
            memcpy( *ppTokOutput, pPositiveNum, sizeof( pPositiveNum ) );
        }
        else if( parseEidrxTokenOutOfRange == 2 )
        {
            *ppTokOutput = malloc( sizeof( pNegativeNum ) );
            memcpy( *ppTokOutput, pNegativeNum, sizeof( pNegativeNum ) );
        }
        else if( parseRegFailureCase == 1 )
        {
            *ppTokOutput = malloc( sizeof( pBigNum ) );
            memcpy( *ppTokOutput, pBigNum, sizeof( pBigNum ) );
        }
        else if( cpsms_pos_mode_error == 1 )
        {
            *ppTokOutput = malloc( sizeof( pNumericNum ) );
            memcpy( *ppTokOutput, pNumericNum, sizeof( pNumericNum ) );
        }
        else if( cpsms_pos_mode_error == 2 )
        {
            *ppTokOutput = malloc( sizeof( pNegativeNum ) );
            memcpy( *ppTokOutput, pNegativeNum, sizeof( pNegativeNum ) );
        }
        else
        {
            *ppTokOutput = malloc( sizeof( pFitNum ) );
            memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
        }
    }
    else if( cmock_num_calls == 1 )
    {
        if( parseEidrxTokenOutOfRange == 1 )
        {
            *ppTokOutput = malloc( sizeof( pPositiveNum ) );
            memcpy( *ppTokOutput, pPositiveNum, sizeof( pPositiveNum ) );
        }
        else if( parseEidrxTokenOutOfRange == 2 )
        {
            *ppTokOutput = malloc( sizeof( pNegativeNum ) );
            memcpy( *ppTokOutput, pNegativeNum, sizeof( pNegativeNum ) );
        }
        /* null data pointer. */
        else if( parseNetworkTimeFailureCase == 1 )
        {
            *ppTokOutput = NULL;
        }
        /* big number case or _parseCopsNetworkNameToken parse error case. */
        else if( parseNetworkTimeFailureCase == 2 )
        {
            if( commonCase == 0 )
            {
                *ppTokOutput = malloc( sizeof( pBigNum ) );
                memcpy( *ppTokOutput, pBigNum, sizeof( pBigNum ) );
            }
            else
            {
                *ppTokOutput = malloc( sizeof( pNegativeNum ) );
                memcpy( *ppTokOutput, pNegativeNum, sizeof( pNegativeNum ) );
            }
        }
        else
        {
            *ppTokOutput = malloc( sizeof( pFitNum ) );
            memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
        }
    }
    else if( cmock_num_calls == 2 )
    {
        if( parseEidrxTokenOutOfRange == 1 )
        {
            nullTokenFirst = 1;
        }
        else
        {
            *ppTokOutput = malloc( sizeof( pFitNum ) );
            memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
        }
    }
    else if( cmock_num_calls < 7 )
    {
        if( cmock_num_calls == 3 )
        {
            if( psmSettingsTimerIndex >= 0 )
            {
                int t3412TimerInx = ( psmSettingsTimerIndex << 5U );

                if( psmSettingsTimerError == 1 )
                {
                    t3412TimerInx = 0 - t3412TimerInx;
                }

                *ppTokOutput = malloc( len );
                snprintf( *ppTokOutput, len, "%d", t3412TimerInx );
            }
            else
            {
                *ppTokOutput = malloc( sizeof( pFitNum ) );
                memcpy( *ppTokOutput, pFitNum, sizeof( pFitNum ) );
            }
        }
        else
        {
            if( ( cmock_num_calls == 4 ) && ( psmSettingsTimerIndex >= 0 ) )
            {
                int t3324TimerInx = ( psmSettingsTimerIndex << 5U );

                if( psmSettingsTimerError == 1 )
                {
                    t3324TimerInx = 0 - t3324TimerInx;
                }

                *ppTokOutput = malloc( len );
                snprintf( *ppTokOutput, len, "%d", t3324TimerInx | psmSettingsActiveTimerValue );
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

    if( nullTokenFirst == 1 )
    {
        *ppTokOutput = NULL;
        atCoreStatus = CELLULAR_AT_SUCCESS;
    }
    else if( *ppTokOutput == NULL )
    {
        atCoreStatus = CELLULAR_AT_ERROR;
    }

    if( parseNetworkTimeFailureCase == 1 )
    {
        atCoreStatus = CELLULAR_AT_SUCCESS;
    }

    return atCoreStatus;
}

void * mock_malloc( size_t size )
{
    if( mallocAllocFail == 1 )
    {
        return NULL;
    }

    return malloc( size );
}

/* ========================================================================== */

/**
 * @brief Test that any NULL handler case Cellular_CommonGetEidrxSettings to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonGetEidrxSettings_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonGetEidrxSettings( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that any NULL EidrxSettingsList case Cellular_CommonGetEidrxSettings to return CELLULAR_BAD_PARAMETER.
 */
void test_Cellular_CommonGetEidrxSettings_Null_EidrxSettings( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that at command failure case Cellular_CommonGetEidrxSettings to return CELLULAR_TIMEOUT.
 */
void test_Cellular_CommonGetEidrxSettings_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT, CELLULAR_TIMEOUT );
    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_TIMEOUT, cellularStatus );
}

/**
 * @brief Test that null context case in callback function _Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetEidrxSettings_Cb_Cellular_RecvFuncGetEidrxSettings_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null item line case in callback function _Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetEidrxSettings_Cb_Cellular_RecvFuncGetEidrxSettings_Null_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that wrong data length case in callback function _Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetEidrxSettings_Cb_Cellular_RecvFuncGetEidrxSettings_Wrong_Data_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 2;
    commonCase = 1;
    wrongDataLength = CELLULAR_EDRX_LIST_MAX_SIZE + 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null item case in callback function _Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetEidrxSettings_Cb_Cellular_RecvFuncGetEidrxSettings_Null_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command failure case in callback function _Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetEidrxSettings_Cb__Cellular_RecvFuncGetEidrxSettings_Null_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 1;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null data pointer case in callback function Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetEidrxSettings_Cb_Cellular_RecvFuncGetEidrxSettings_Null_Data_Pointer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that error packet status in loop in callback function Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetEidrxSettings_Cb_Cellular_RecvFuncGetEidrxSettings_Error_PacketSTatus_InLoop( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_ERROR );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that input line case in callback function Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetEidrxSettings_Cb_Cellular_RecvFuncGetEidrxSettings_Input_Line_Case( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 4;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that CELLULAR_CEDRXS_POS_ACT case in callback function Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetEidrxSettings_Cb_Cellular_RecvFuncGetEidrxSettings_CEDRXS_POS_ACT_OutOfRange( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    parseEidrxTokenOutOfRange = 1;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that out of lower bound range case in callback function Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetEidrxSettings_Cb_Cellular_RecvFuncGetEidrxSettings_OutOfLowerBound_Range( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    parseEidrxTokenOutOfRange = 2;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that atoi failure case in parseEidrxToken called by callback function Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetEidrxSettings_Cb_Cellular_RecvFuncGetEidrxSettings_Atoi_Failed_In_parseEidrxToken( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case in callback function Cellular_RecvFuncGetEidrxSettings
 * for Cellular_CommonGetEidrxSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetEidrxSettings_Cb_Cellular_RecvFuncGetEidrxSettings_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_Cellular_RecvFuncGetEidrxSettings );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonGetEidrxSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetEidrxSettings_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettingsList_t eidrxSettingsList;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetEidrxSettings( cellularHandle, &eidrxSettingsList );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that any NULL handler case Cellular_CommonSetEidrxSettings to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonSetEidrxSettings_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonSetEidrxSettings( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that any NULL EidrxSettingsList case Cellular_CommonSetEidrxSettings to return CELLULAR_BAD_PARAMETER.
 */
void test_Cellular_CommonSetEidrxSettings_Null_EidrxSettings( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonSetEidrxSettings( cellularHandle, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that at command failure case Cellular_CommonSetEidrxSettings to return CELLULAR_TIMEOUT.
 */
void test_Cellular_CommonSetEidrxSettings_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettings_t eidrxSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT, CELLULAR_TIMEOUT );
    cellularStatus = Cellular_CommonSetEidrxSettings( cellularHandle, &eidrxSettings );
    TEST_ASSERT_EQUAL( CELLULAR_TIMEOUT, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonSetEidrxSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonSetEidrxSettings_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularEidrxSettings_t eidrxSettings;

    eidrxSettings.requestedEdrxValue = 0xF;
    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonSetEidrxSettings( cellularHandle, &eidrxSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );

    eidrxSettings.requestedEdrxValue = 0x0;
    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonSetEidrxSettings( cellularHandle, &eidrxSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that NULL handler case Cellular_CommonRfOn to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonRfOn_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonRfOn( NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonRfOn to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonRfOn_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonRfOn( cellularHandle );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that NULL handler case Cellular_CommonRfOff to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonRfOff_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonRfOff( NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonRfOff to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonRfOff_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonRfOff( cellularHandle );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that NULL handler case Cellular_CommonGetRegisteredNetwork to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that bad parameter case Cellular_CommonGetRegisteredNetwork to return CELLULAR_BAD_PARAMETER.
 */
void test_Cellular_CommonGetRegisteredNetwork_Bad_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that bad parameter case Cellular_CommonGetRegisteredNetwork to return CELLULAR_NO_MEMORY.
 */
void test_Cellular_CommonGetRegisteredNetwork_No_Memory( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    mallocAllocFail = 1;
    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_NO_MEMORY, cellularStatus );
}

/**
 * @brief Test that set to numeric format failed.
 *
 * <b>Coverage</b>
 * @code{c}
 * static CellularError_t atcmdUpdateMccMnc( CellularContext_t * pContext,
 *                                           cellularOperatorInfo_t * pOperatorInfo )
 * {
 *     ...
 *     atCopsRequest.pAtCmd = "AT+COPS=3,2",
 *     atCopsRequest.atCmdType = CELLULAR_AT_NO_RESULT,
 *     pktStatus =  _Cellular_AtcmdRequestWithCallback( pContext, atCopsRequest );
 *
 *     if( pktStatus == CELLULAR_PKT_STATUS_OK )
 *     {
 *         ...
 *     }
 * }
 * @endcode
 * ( pktStatus == CELLULAR_PKT_STATUS_OK ) is false.
 */
void test_Cellular_CommonGetRegisteredNetwork_Set_Numeric_Format_Fail( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that invalid rat case Cellular_CommonGetRegisteredNetwork to return CELLULAR_UNKNOWN.
 */
void test_Cellular_CommonGetRegisteredNetwork_Invalid_Rat( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_UNKNOWN, cellularStatus );
}

/**
 * @brief Test that null context case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command response case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_Null_AtCmd_Resp( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 1;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command response item case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_Null_AtCmd_Resp_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command response item line case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_Null_AtCmd_Resp_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command response case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_Null_Data_Pointer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 2;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that wrong data length case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_Wrong_Data_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 2;
    commonCase = 1;
    wrongDataLength = sizeof( cellularOperatorInfo_t ) + 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that at command failure case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    Cellular_ATGetNextTok_IgnoreAndReturn( CELLULAR_AT_ERROR );

    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_ERROR, CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that atoi failure case in _parseCopsRegModeToken called by callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc__parseCopsRegModeToken_Atoi_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_ERROR );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that atoi failure case in _parseCopsNetworkNameFormatToken called by callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc__parseCopsNetworkNameFormatToken_Atoi_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseCopsNetworkNameFormatToken */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_ERROR );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that atoi failure case in _parseCopsRatToken called by callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc__parseCopsRatToken_Atoi_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseCopsNetworkNameFormatToken */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseCopsRatToken */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_ERROR );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    Cellular_ATGetNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    Cellular_ATGetNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /*_parseCopsNetworkNameFormatToken*/
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    Cellular_ATGetNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCopsNetworkNameToken */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    Cellular_ATGetNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCopsRatToken */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseCopsRegModeToken too big number case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsRegModeToken_Big_Num_Error( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseRegFailureCase = 1;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_ERROR, CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsRegModeToken negative number case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsRegModeToken_Negative_Number( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseEidrxTokenOutOfRange = 2;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_ERROR, CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsNetworkNameFormatToken null pointer case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsNetworkNameFormatToken_Null_Pointer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkTimeFailureCase = 1;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsNetworkNameFormatToken big number case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsNetworkNameFormatToken_Big_Number( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkTimeFailureCase = 2;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsNetworkNameFormatToken out of lower bound case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsNetworkNameFormatToken_OutOfLowerBound( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkTimeFailureCase = 2;
    commonCase = 1;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsNetworkNameToken null pointer case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsNetworkNameToken_Null_Pointer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkNameFailureCase = 1;
    Cellular_ATGetNextTok_StubWithCallback( Mock_parseNetworkNameFailureCase_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsNetworkNameToken name format long case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsNetworkNameToken_Name_Format_Long( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkNameFailureCase = 2;
    Cellular_ATGetNextTok_StubWithCallback( Mock_parseNetworkNameFailureCase_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsNetworkNameToken name format numeric case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsNetworkNameToken_Name_Format_Numeric( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkNameFailureCase = 3;
    Cellular_ATGetNextTok_StubWithCallback( Mock_parseNetworkNameFailureCase_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsNetworkNameToken name format numeric case II in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsNetworkNameToken_Name_Format_Numeric_CaseII( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkNameFailureCase = 3;
    commonCase = 1;
    Cellular_ATGetNextTok_StubWithCallback( Mock_parseNetworkNameFailureCase_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsNetworkNameToken name format numeric wrong length case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsNetworkNameToken_Name_Format_Numeric_Wrong_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkNameFailureCase = 5;
    Cellular_ATGetNextTok_StubWithCallback( Mock_parseNetworkNameFailureCase_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsNetworkNameToken name format numeric parse error case in callback
 * function _Cellular_RecvFuncUpdateMccMnc for Cellular_CommonGetRegisteredNetwork to return
 * CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsNetworkNameToken_Parse_Error( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkNameFailureCase = 4;
    Cellular_ATGetNextTok_StubWithCallback( Mock_parseNetworkNameFailureCase_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsRatToken null token case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsRatToken_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkNameFailureCase = 6;
    Cellular_ATGetNextTok_StubWithCallback( Mock_parseNetworkNameFailureCase_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsRatToken token out of range case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsRatToken_Token_OutOfRange( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkNameFailureCase = 7;
    Cellular_ATGetNextTok_StubWithCallback( Mock_parseNetworkNameFailureCase_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsRatToken token out of lower bound case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsRatToken_Token_OutOfLowerBound( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkNameFailureCase = 9;
    Cellular_ATGetNextTok_StubWithCallback( Mock_parseNetworkNameFailureCase_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that at command failure case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsRatToken_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_ERROR );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseCopsRatToken happy path case in callback function _Cellular_RecvFuncUpdateMccMnc
 * for Cellular_CommonGetRegisteredNetwork to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetRegisteredNetwork_Cb__Cellular_RecvFuncUpdateMccMnc_parseCopsRatToken_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncUpdateMccMnc );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    /* _parseCops */
    parseNetworkNameFailureCase = 8;
    Cellular_ATGetNextTok_StubWithCallback( Mock_parseNetworkNameFailureCase_ATGetNextTok_Calback );
    /* _parseCopsRegModeToken */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonGetRegisteredNetwork to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetRegisteredNetwork_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPlmnInfo_t networkInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetRegisteredNetwork( cellularHandle, &networkInfo );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that NULL handler case Cellular_CommonGetServiceStatus to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonGetServiceStatus_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonGetServiceStatus( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that bad parameter case Cellular_CommonGetServiceStatus to return CELLULAR_BAD_PARAMETER.
 */
void test_Cellular_CommonGetServiceStatus_Bad_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetServiceStatus( cellularHandle, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that null context case in callback function _Cellular_RecvFuncGetNetworkReg
 * for Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Cb__Cellular_RecvFuncGetNetworkReg_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularServiceStatus_t serviceStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    /* called by atcmdUpdateMccMnc. */
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetServiceStatus( cellularHandle, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null data pointer case in callback function _Cellular_RecvFuncGetNetworkReg
 * for Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Cb__Cellular_RecvFuncGetNetworkReg_Null_Data_Pointer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularServiceStatus_t serviceStatus;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.libAtData.psRegStatus = 5;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    cbCondition = 2;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    /* called by atcmdUpdateMccMnc. */
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetServiceStatus( ( CellularHandle_t ) &context, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that wrong data length case in callback function _Cellular_RecvFuncGetNetworkReg
 * for Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Cb__Cellular_RecvFuncGetNetworkReg_Wrong_Data_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularServiceStatus_t serviceStatus;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.libAtData.psRegStatus = 5;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    cbCondition = 2;
    commonCase = 1;
    wrongDataLength = sizeof( CellularNetworkRegType_t ) + 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    /* called by atcmdUpdateMccMnc. */
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetServiceStatus( ( CellularHandle_t ) &context, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null at command response in callback function _Cellular_RecvFuncGetNetworkReg
 * for Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Cb__Cellular_RecvFuncGetNetworkReg_Null_AtCmd_Resp( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularServiceStatus_t serviceStatus;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.libAtData.psRegStatus = 1;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    cbCondition = 1;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    /* called by atcmdUpdateMccMnc. */
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );


    cellularStatus = Cellular_CommonGetServiceStatus( ( CellularHandle_t ) &context, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null at command item response in callback function _Cellular_RecvFuncGetNetworkReg
 * for Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Cb__Cellular_RecvFuncGetNetworkReg_Null_AtCmd_Resp_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularServiceStatus_t serviceStatus;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.libAtData.psRegStatus = 1;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    /* called by atcmdUpdateMccMnc. */
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );


    cellularStatus = Cellular_CommonGetServiceStatus( ( CellularHandle_t ) &context, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null at command item line response in callback function _Cellular_RecvFuncGetNetworkReg
 * for Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Cb__Cellular_RecvFuncGetNetworkReg_Null_AtCmd_Resp_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularServiceStatus_t serviceStatus;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.libAtData.psRegStatus = 1;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    /* called by atcmdUpdateMccMnc. */
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );


    cellularStatus = Cellular_CommonGetServiceStatus( ( CellularHandle_t ) &context, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path in callback function _Cellular_RecvFuncGetNetworkReg at command failure
 * for Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Cb__Cellular_RecvFuncGetNetworkReg_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularServiceStatus_t serviceStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );

    /* called by atcmdUpdateMccMnc. */
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetServiceStatus( cellularHandle, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path in callback function _Cellular_RecvFuncGetNetworkReg
 * for Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Cb__Cellular_RecvFuncGetNetworkReg_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularServiceStatus_t serviceStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    /* _Cellular_ParseRegStatus */
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_BAD_PARAMETER );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_NetworkRegistrationCallback_Ignore();

    /* called by atcmdUpdateMccMnc. */
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetServiceStatus( cellularHandle, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that_Cellular_ParseRegStatus return error in callback function _Cellular_RecvFuncGetNetworkReg
 * for Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Cb__Cellular_RecvFuncGetNetworkReg_Parse_Error( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularServiceStatus_t serviceStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    cbCondition = 6;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    /* Return error in _Cellular_ParseRegStatus. */
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_BAD_PARAMETER );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE );
    _Cellular_NetworkRegistrationCallback_Ignore();

    /* called by atcmdUpdateMccMnc. */
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* The serviceStatus is updated and verified in cellular_3gpp_urc_handler.c test cases. */
    cellularStatus = Cellular_CommonGetServiceStatus( cellularHandle, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that network not registered URC is received in callback function
 * _Cellular_RecvFuncGetNetworkReg for Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Cb__Cellular_RecvFuncGetNetworkReg_URC_not_registered( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularServiceStatus_t serviceStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for +CREG:2. */
    cbCondition = 4;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE );

    /* _Cellular_ParseRegStatus */
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_BAD_PARAMETER );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE );
    _Cellular_NetworkRegistrationCallback_Ignore();

    /* called by atcmdUpdateMccMnc. */
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* The serviceStatus is updated and verified in cellular_3gpp_urc_handler.c test cases. */
    cellularStatus = Cellular_CommonGetServiceStatus( cellularHandle, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that network registered URC is received in callback function
 * _Cellular_RecvFuncGetNetworkReg for Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Cb__Cellular_RecvFuncGetNetworkReg_URC_registered( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularServiceStatus_t serviceStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for +CREG:2. */
    cbCondition = 5;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkReg );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* _Cellular_ParseRegStatus */
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_BAD_PARAMETER );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_NetworkRegistrationCallback_Ignore();

    /* called by atcmdUpdateMccMnc. */
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* The serviceStatus is updated and verified in cellular_3gpp_urc_handler.c test cases. */
    cellularStatus = Cellular_CommonGetServiceStatus( cellularHandle, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that wrong psRegStatus case Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Wrong_psRegStatus( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularServiceStatus_t serviceStatus;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.libAtData.psRegStatus = 1;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CGREG. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    /* called by atcmdUpdateMccMnc. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetServiceStatus( ( CellularHandle_t ) &context, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );

    context.libAtData.psRegStatus = 5;
    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CGREG. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    /* called by atcmdUpdateMccMnc. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetServiceStatus( ( CellularHandle_t ) &context, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonGetServiceStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetServiceStatus_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularServiceStatus_t serviceStatus;

    memset( &context, 0, sizeof( CellularContext_t ) );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CREG. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CGREG. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    /* called by atcmdQueryRegStatus -> queryNetworkStatus for CGREG -> queryNetworkStatus for CEREG. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    /* called by atcmdUpdateMccMnc. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetServiceStatus( cellularHandle, &serviceStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that NULL handler case Cellular_CommonGetNetworkTime to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonGetNetworkTime_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonGetNetworkTime( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that bad parameter case Cellular_CommonGetNetworkTime to return CELLULAR_BAD_PARAMETER.
 */
void test_Cellular_CommonGetNetworkTime_Bad_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that retrieve network time failure case Cellular_CommonGetNetworkTime to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetNetworkTime_Retrieve_Network_Time_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT, CELLULAR_TIMEOUT );

    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_TIMEOUT, cellularStatus );
}

/**
 * @brief Test that null context case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* Null context condition. */
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command response case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Null_AtCmd( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* Null at command response case condition. */
    cbCondition = 1;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command response item case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Null_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* Null at command response item case condition. */
    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command response item line case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Null_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* Null at command response item line case condition. */
    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null data pointer case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Null_Data( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 2;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null data length case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Null_Data_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 2;
    commonCase = 1;
    wrongDataLength = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseTimeZoneInfo at command failure case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeZone_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_BAD_PARAMETER );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseTimeZoneInCCLKResponse atoi return failure case I in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeZone_InCCLKResp_Atoi_Failure_Case_I( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = 5;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseTimeZoneInCCLKResponse atoi return failure case II in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeZone_InCCLKResp_Atoi_Failure_Case_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = 5;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseTimeZoneInCCLKResponse atoi return failure case III in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeZone_InCCLKResp_Atoi_Failure_Case_III( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = 5;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseTimeZoneInCCLKResponse negative case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeZone_InCCLKResp_Negative( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = 5;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseTimeZoneInCCLKResponse negative case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeZone_InCCLKResp_Parse_Sign_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse sign failure case condition. */
    cbCondition = 5;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseTimeZoneInCCLKResponse atoi return failure case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeZone_InCCLKResp_Atoi_Return_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse sign failure case condition. */
    cbCondition = 6;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that at command failure case in _parseTimeZoneInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeZoneInfo_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse sign failure case condition. */
    cbCondition = 5;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_ERROR );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseYearMonthDayInCCLKResponse year atoi return number failure case I in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_YearMonthDAy_CCLKResp_Year_Atoi_Return_Number_Failure_I( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_FIRST_CALL_FAILURE_CONDITION;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseYearMonthDayInCCLKResponse year atoi return number failure case II in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_YearMonthDAy_CCLKResp_Year_Atoi_Return_Number_Failure_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_FIRST_CALL_FAILURE_CONDITION;
    negativeNumberCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseYearMonthDayInCCLKResponse year atoi failure case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_YearMonthDAy_CCLKResp_Year_Atoi_Return_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_FIRST_CALL_FAILURE_CONDITION;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_BAD_PARAMETER );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseYearMonthDayInCCLKResponse month atoi return number failure case I in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_YearMonthDAy_CCLKResp_Month_Return_Number_Failure_I( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_SECOND_CALL_FAILURE_CONDITION;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseYearMonthDayInCCLKResponse month atoi return number failure case II in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_YearMonthDAy_CCLKResp_Month_Return_Number_Failure_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_SECOND_CALL_FAILURE_CONDITION;
    negativeNumberCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseYearMonthDayInCCLKResponse month atoi failure case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_YearMonthDAy_CCLKResp_Month_Atoi_Return_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_FIRST_CALL_FAILURE_CONDITION;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_BAD_PARAMETER );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseYearMonthDayInCCLKResponse day atoi return number failure case I in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_YearMonthDAy_CCLKResp_Day_Atoi_Return_Number_Failure_I( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_THIRD_CALL_FAILURE_CONDITION;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseYearMonthDayInCCLKResponse day atoi return number failure case II in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_YearMonthDAy_CCLKResp_Day_Atoi_Return_Number_Failure_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_THIRD_CALL_FAILURE_CONDITION;
    negativeNumberCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseYearMonthDayInCCLKResponse day atoi failure case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_YearMonthDAy_CCLKResp_Day_Atoi_Return_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_FIRST_CALL_FAILURE_CONDITION;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_BAD_PARAMETER );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseTimeInCCLKResponse hour atoi return number failure case I in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeInCCLKResp_Hour_Atoi_Return_Number_Failure_I( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_FOURTH_CALL_FAILURE_CONDITION;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseTimeInCCLKResponse hour atoi return number failure case II in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeInCCLKResp_Hour_Atoi_Return_Number_Failure_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_FOURTH_CALL_FAILURE_CONDITION;
    negativeNumberCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseTimeInCCLKResponse minute atoi return number failure case I in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeInCCLKResp_Minute_Atoi_Return_Number_Failure_I( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_FIFTH_CALL_FAILURE_CONDITION;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseTimeInCCLKResponse minute atoi return number failure case II in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeInCCLKResp_Minute_Atoi_Return_Number_Failure_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_FIFTH_CALL_FAILURE_CONDITION;
    negativeNumberCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseTimeInCCLKResponse minute atoi return failure case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeInCCLKResp_Minute_Atoi_Return_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_FIFTH_CALL_FAILURE_CONDITION;

    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_ERROR );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that _parseTimeInCCLKResponse second atoi return failure case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeInCCLKResp_Second_Atoi_Return_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_FIFTH_CALL_FAILURE_CONDITION;

    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_ERROR );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that _parseTimeInCCLKResponse second atoi return number failure case I in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeInCCLKResp_Second_Atoi_Return_Number_Failure_I( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_SIXTH_CALL_FAILURE_CONDITION;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that _parseTimeInCCLKResponse second atoi return number failure case II in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Parse_TimeInCCLKResp_Second_Atoi_Return_Number_Failure_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* parse time failure case condition. */
    cbCondition = PARSE_TIME_SIXTH_CALL_FAILURE_CONDITION;
    negativeNumberCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that at command failure case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* happy path case condition. */
    cbCondition = 4;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_BAD_PARAMETER );
    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_BAD_PARAMETER, CELLULAR_PKT_STATUS_BAD_PARAM );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}


/**
 * @brief Test that happy path case in _Cellular_RecvFuncGetNetworkTime to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetNetworkTime_RecvFuncCallback_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* happy path case condition. */
    cbCondition = 4;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetNetworkTime );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* Enter _parseTimeZoneInfo. */
    Cellular_ATRemoveOutermostDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeZoneInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseYearMonthDayInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    /* _parseTimeInCCLKResponse */
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    Cellular_ATGetSpecificNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonGetNetworkTime to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetNetworkTime_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularTime_t networkTime;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    cellularStatus = Cellular_CommonGetNetworkTime( cellularHandle, &networkTime );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that NULL handler case Cellular_CommonGetModemInfo to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonGetModemInfo_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonGetModemInfo( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that bad parameter case Cellular_CommonGetModemInfo to return CELLULAR_BAD_PARAMETER.
 */
void test_Cellular_CommonGetModemInfo_Bad_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that get firmware version failure case Cellular_CommonGetModemInfo to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetModemInfo_Get_FW_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion CELLULAR_PKT_STATUS_BAD_PARAM failure*/
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    /* atReqGetImei */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetModelId */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetManufactureId */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get firmware version callback function null context failure
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_FW_Callback__Cellular_RecvFuncGetFirmwareVersion_Null_Context_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion */
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetFirmwareVersion );

    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get firmware version callback function null
 * at command response failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_FW_Callback__Cellular_RecvFuncGetFirmwareVersion_Null_AtResp_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion */
    cbCondition = 1;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetFirmwareVersion );

    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get firmware version callback function null
 * at command response item failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_FW_Callback__Cellular_RecvFuncGetFirmwareVersion_Null_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion */
    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetFirmwareVersion );

    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get firmware version callback function null
 * at command response item line failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_FW_Callback__Cellular_RecvFuncGetFirmwareVersion_Null_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion */
    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetFirmwareVersion );

    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get firmware version callback function null data pointer
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_FW_Callback__Cellular_RecvFuncGetFirmwareVersion_Null_Data_Pointer_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion */
    cbCondition = 2;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetFirmwareVersion );

    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get firmware version callback function wrong data length
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_FW_Callback__Cellular_RecvFuncGetFirmwareVersion_Wrong_Data_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion */
    cbCondition = 2;
    commonCase = 1;
    wrongDataLength = CELLULAR_FW_VERSION_MAX_SIZE + 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetFirmwareVersion );

    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get firmware version callback function at command failure
 * case I Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_FW_Callback__Cellular_RecvFuncGetFirmwareVersion_AtCmd_Failure_Case_I( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetFirmwareVersion );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get firmware version callback function at command failure
 * case II Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_FW_Callback__Cellular_RecvFuncGetFirmwareVersion_AtCmd_Failure_Case_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetFirmwareVersion );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveTrailingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get firmware version callback function happy path
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_FW_Callback__Cellular_RecvFuncGetFirmwareVersion_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetFirmwareVersion );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveTrailingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that get imei version callback function null context failure
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetImei_Null_Context_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImei */
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetImei );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get imei version callback function null at command
 * response failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetImei_Null_AtResp_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImei */
    cbCondition = 1;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetImei );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get imei version callback function null at command
 * response item failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetImei_Null_AtResp_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImei */
    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetImei );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get imei version callback function null at command
 * response item line failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetImei_Null_AtResp_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImei */
    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetImei );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get imei version callback function null data pointer
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetImei_Null_Data_Pointer_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetImei */
    cbCondition = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetImei );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get imei version callback function at command failure
 * case I Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetImei_AtCmd_Failure_Case_I( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetImei */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetImei );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get imei version callback function at command failure
 * case II Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetImei_AtCmd_Failure_Case_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetImei */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetImei );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get imei version callback function happy path
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetImei_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetImei */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular__Cellular_RecvFuncGetImei );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that get imei failure case Cellular_CommonGetModemInfo to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetModemInfo_Get_IMEI_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion CELLULAR_PKT_STATUS_BAD_PARAM failure*/
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetImei */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    /* atReqGetModelId */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetManufactureId */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get model id callback function null context failure
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetModelId_Null_Context_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetModelId */
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetModelId );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get model id callback function null at command
 * response failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetModelId_Null_AtResp_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetModelId */
    cbCondition = 1;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetModelId );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get model id callback function null at command
 * response item failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetModelId_Null_AtResp_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetModelId */
    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetModelId );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get model id callback function null at command
 * response item line failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetModelId_Null_AtResp_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetModelId */
    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetModelId );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get model id callback function null data pointer
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetModelId_Null_Data_Pointer_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetModelId */
    cbCondition = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetModelId );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get model id callback function at command failure
 * case I Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetModelId_AtCmd_Failure_Case_I( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetModelId */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetModelId );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get model id callback function at command failure
 * case II Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetModelId_AtCmd_Failure_Case_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetModelId */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetModelId );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveTrailingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get model id callback function happy path
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetModelId_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetModelId */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetModelId );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveTrailingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that get model id failure case Cellular_CommonGetModemInfo to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetModemInfo_Get_ModelId_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion CELLULAR_PKT_STATUS_BAD_PARAM failure*/
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetImei */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetModelId */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    /* atReqGetManufactureId */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get manufacture id callback function null context failure
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetManufactureId_Null_Context_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetManufactureId */
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetManufactureId );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get manufacture id callback function null at command
 * response failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetManufactureId_Null_AtResp_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetManufactureId */
    cbCondition = 1;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetManufactureId );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get manufacture id callback function null at command
 * response item failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetManufactureId_Null_AtResp_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetManufactureId */
    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetManufactureId );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get manufacture id callback function null at command
 * response item line failure case Cellular_CommonGetModemInfo
 * to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetManufactureId_Null_AtResp_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetManufactureId */
    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetManufactureId );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get manufacture id callback function null data pointer
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetManufactureId_Null_Data_Pointer_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetManufactureId */
    cbCondition = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetManufactureId );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get manufacture id callback function at command
 * case I Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetManufactureId_AtCmd_Failure_Case_I( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetManufactureId */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetManufactureId );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get manufacture id callback function at command
 * case II Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetManufactureId_AtCmd_Failure_Case_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetManufactureId */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetManufactureId );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveTrailingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that get manufacture id callback function happy path
 * case Cellular_CommonGetModemInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetModemInfo_Get_Imei_Callback__Cellular_RecvFuncGetManufactureId_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    /* atReqGetManufactureId */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetManufactureId );
    Cellular_ATRemoveLeadingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveTrailingWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that get manufacture id failure case Cellular_CommonGetModemInfo to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetModemInfo_Get_ManufactureId_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion CELLULAR_PKT_STATUS_BAD_PARAM failure*/
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetImei */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetModelId */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetManufactureId */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonGetModemInfo to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetModemInfo_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularModemInfo_t modemInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetFirmwareVersion */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetImei */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetModelId */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetManufactureId */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = Cellular_CommonGetModemInfo( cellularHandle, &modemInfo );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that NULL handler case Cellular_CommonGetIPAddress to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonGetIPAddress_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonGetIPAddress( NULL, 0, NULL, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that bad parameter case Cellular_CommonGetIPAddress to return CELLULAR_BAD_PARAMETER.
 */
void test_Cellular_CommonGetIPAddress_Bad_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, NULL, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, 0 );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that at command failure case Cellular_CommonGetIPAddress to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetIPAddress_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );

    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null context case in callback function _Cellular_RecvFuncIpAddress
 * for Cellular_CommonGetIPAddress to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetIPAddress_Cb_Cellular_RecvFuncIpAddress_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncIpAddress );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command failure case in callback function _Cellular_RecvFuncIpAddress
 * for Cellular_CommonGetIPAddress to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetIPAddress_Cb_Cellular_RecvFuncIpAddress_Null_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 1;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncIpAddress );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command item case in callback function _Cellular_RecvFuncIpAddress
 * for Cellular_CommonGetIPAddress to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetIPAddress_Cb_Cellular_RecvFuncIpAddress_Null_AtCmd_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncIpAddress );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command item line case in callback function _Cellular_RecvFuncIpAddress
 * for Cellular_CommonGetIPAddress to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetIPAddress_Cb_Cellular_RecvFuncIpAddress_Null_AtCmd_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncIpAddress );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null data pointer case in callback function _Cellular_RecvFuncIpAddress
 * for Cellular_CommonGetIPAddress to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetIPAddress_Cb_Cellular_RecvFuncIpAddress_Null_Data_Pointer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 2;
    commonCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncIpAddress );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that wrong data length case in callback function _Cellular_RecvFuncIpAddress
 * for Cellular_CommonGetIPAddress to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetIPAddress_Cb_Cellular_RecvFuncIpAddress_Wrong_Data_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 2;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncIpAddress );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that at command failure case in callback function _Cellular_RecvFuncIpAddress
 * for Cellular_CommonGetIPAddress to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetIPAddress_Cb_Cellular_RecvFuncIpAddress_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncIpAddress );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_ERROR );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path case in callback function _Cellular_RecvFuncIpAddress
 * for Cellular_CommonGetIPAddress to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetIPAddress_Cb_Cellular_RecvFuncIpAddress_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncIpAddress );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case in callback function _Cellular_RecvFuncIpAddress
 * for Cellular_CommonGetIPAddress to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetIPAddress_Cb_Cellular_RecvFuncIpAddress_Happy_Path_CGPADDR( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 5;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncIpAddress );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case in callback function _Cellular_RecvFuncIpAddress
 * for Cellular_CommonGetIPAddress to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetIPAddress_Cb_Cellular_RecvFuncIpAddress_Null_Input_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 4;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncIpAddress );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonGetIPAddress to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetIPAddress_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    char pBuffer[ 10 ];

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = Cellular_CommonGetIPAddress( cellularHandle, 0, pBuffer, sizeof( pBuffer ) );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that bad parameter case Cellular_CommonSetPdnConfig to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonSetPdnConfig_Bad_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    cellularStatus = Cellular_CommonSetPdnConfig( NULL, 0, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that bad pdn context type case Cellular_CommonSetPdnConfig to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonSetPdnConfig_Bad_Pdn_Context_Type( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPdnConfig_t pdnConfig;

    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = Cellular_CommonSetPdnConfig( cellularHandle, 0, &pdnConfig );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that at command failure case Cellular_CommonSetPdnConfig to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonSetPdnConfig_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPdnConfig_t pdnConfig;

    pdnConfig.pdnContextType = CELLULAR_PDN_CONTEXT_IPV4;

    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );
    cellularStatus = Cellular_CommonSetPdnConfig( cellularHandle, 0, &pdnConfig );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path ipv6 case Cellular_CommonSetPdnConfig to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonSetPdnConfig_IPV6_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPdnConfig_t pdnConfig;

    pdnConfig.pdnContextType = CELLULAR_PDN_CONTEXT_IPV6;

    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = Cellular_CommonSetPdnConfig( cellularHandle, 0, &pdnConfig );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path ipv4v6 case Cellular_CommonSetPdnConfig to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonSetPdnConfig_IPV4V6_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPdnConfig_t pdnConfig;

    pdnConfig.pdnContextType = CELLULAR_PDN_CONTEXT_IPV4V6;

    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = Cellular_CommonSetPdnConfig( cellularHandle, 0, &pdnConfig );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that NULL handler case Cellular_CommonGetSimCardLockStatus to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonGetSimCardLockStatus( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that bad parameter case Cellular_CommonGetSimCardLockStatus to return CELLULAR_BAD_PARAMETER.
 */
void test_Cellular_CommonGetSimCardLockStatus_Bad_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that null context case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command failure case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_Null_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null data pointer case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_Null_Data_Pointer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that wrong data length case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_Wrong_Data_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 2;
    commonCase = 1;
    wrongDataLength = sizeof( CellularSimCardLockState_t ) + 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null item case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_Null_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null item line case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_Null_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that at command failure case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_BAD_PARAMETER );
    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_BAD_PARAMETER, CELLULAR_PKT_STATUS_BAD_PARAM );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that SimLockState READY case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_READY( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 1;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState SIM_PIN case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_SIM_PIN( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 2;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState SIM_PUK case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_SIM_PUK( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 3;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState SIM_PIN2 case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_SIM_PIN2( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 4;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState SIM_PUK2 case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_SIM_PUK2( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 5;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState PH_NET_PIN case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_PH_NET_PIN( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 6;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState PH_NET_PUK case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_PH_NET_PUK( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 7;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState PH_NETSUB_PIN case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_PH_NETSUB_PIN( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 8;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState PH_NETSUB_PUK case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_PH_NETSUB_PUK( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 9;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState PH_SP_PIN case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_PH_SP_PIN( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 10;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState PH_SP_PUK case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_PH_SP_PUK( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 11;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState PH_CORP_PIN case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_PH_CORP_PIN( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 12;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState PH_CORP_PUK case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_PH_CORP_PUK( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 13;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that SimLockState Unknown case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_SimLockState_Unknown( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    simLockStateTestCase = 14;
    Cellular_ATGetNextTok_StubWithCallback( Mock_simLockStateTestCase_ATGetNextTok_Calback );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case in callback function _Cellular_RecvFuncGetSimLockStatus
 * for Cellular_CommonGetSimCardLockStatus to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardLockStatus_Cb_Cellular_RecvFuncGetSimLockStatus_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetSimLockStatus );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonGetSimCardLockStatus to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetSimCardLockStatus_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardStatus_t simCardStatus;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_OK, CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetSimCardLockStatus( cellularHandle, &simCardStatus );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that NULL handler case Cellular_CommonGetSimCardInfo to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonGetSimCardInfo_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonGetSimCardInfo( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that bad parameter case Cellular_CommonGetSimCardInfo to return CELLULAR_BAD_PARAMETER.
 */
void test_Cellular_CommonGetSimCardInfo_Bad_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that at command failure case Cellular_CommonGetSimCardInfo to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetSimCardInfo_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetHplmn case. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetIccid case. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT, CELLULAR_TIMEOUT );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_TIMEOUT, cellularStatus );
}

/**
 * @brief Test that null context case in callback function _Cellular_RecvFuncGetIccid
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetIccid_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetIccid );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command failure case in callback function _Cellular_RecvFuncGetIccid
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetIccid_Null_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    cbCondition = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetIccid );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null data pointer case in callback function _Cellular_RecvFuncGetIccid
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetIccid_Null_Data_Pointer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetIccid );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path case in callback function _Cellular_RecvFuncGetIccid
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetIccid_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetIccid );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that at command failure case in callback function _Cellular_RecvFuncGetIccid
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetIccid_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetIccid );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_ERROR, CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that too long string case in callback function _Cellular_RecvFuncGetIccid
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetIccid_Too_Long_String( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 4;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetIccid );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null item case in callback function _Cellular_RecvFuncGetIccid
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetIccid_Null_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetIccid );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null item line case in callback function _Cellular_RecvFuncGetIccid
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetIccid_Null_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetIccid );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that wrong data length case in callback function _Cellular_RecvFuncGetIccid
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetIccid_Wrong_Data_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cbCondition = 2;
    commonCase = 1;
    wrongDataLength = CELLULAR_ICCID_MAX_SIZE + 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetIccid );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null context case in callback function _Cellular_RecvFuncGetImsi
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetImsi_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetImsi );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command failure case in callback function _Cellular_RecvFuncGetImsi
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetImsi_Null_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    cbCondition = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetImsi );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null data pointer case in callback function _Cellular_RecvFuncGetImsi
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetImsi_Null_Data_Pointer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    cbCondition = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetImsi );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that wrong data length case in callback function _Cellular_RecvFuncGetImsi
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetImsi_Wrong_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    cbCondition = 2;
    commonCase = 1;
    wrongDataLength = CELLULAR_IMSI_MAX_SIZE + 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetImsi );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null item case in callback function _Cellular_RecvFuncGetImsi
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetImsi_Null_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetImsi );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null item line case in callback function _Cellular_RecvFuncGetImsi
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetImsi_Null_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetImsi );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that string too long case in callback function _Cellular_RecvFuncGetImsi
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetImsi_String_Too_Long( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    cbCondition = 4;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetImsi );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_ERROR, CELLULAR_PKT_STATUS_FAILURE );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that at command failure case in callback function _Cellular_RecvFuncGetImsi
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetImsi_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetImsi );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_ERROR, CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path case in callback function _Cellular_RecvFuncGetImsi
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetImsi_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetImsi );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_ExpectAndReturn( CELLULAR_AT_SUCCESS, CELLULAR_PKT_STATUS_OK );

    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null context case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_INVALID_HANDLE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command failure case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_Null_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null data pointer case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_Null_Data_Pointer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that wrong data length case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_Wrong_Data_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 2;
    commonCase = 1;
    wrongDataLength = sizeof( CellularPlmnInfo_t ) + 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null item case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_Null_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null item line case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_Null_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that at command failure error case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_ERROR );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that checkCrsmReadStatus error case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_checkCrsmReadStatus_Error( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_IgnoreAndReturn( CELLULAR_AT_SUCCESS );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that checkCrsmReadStatus illegal token case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_checkCrsmReadStatus_illegal_Token_Error( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    recvFuncGetHplmnCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_recvFuncGetHplmnCase_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseHplmn null token case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_parseHplmn_Null_Token( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    recvFuncGetHplmnCase = 4;
    checkCrsmReadStatusCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_recvFuncGetHplmnCase_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseHplmn data length less than CRSM_HPLMN_RAT_LENGTH case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_parseHplmn_Wrong_Data_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    recvFuncGetHplmnCase = 5;
    checkCrsmReadStatusCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_recvFuncGetHplmnCase_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseHplmn data equal to FFFFFF CRSM_HPLMN_RAT_LENGTH case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_parseHplmn_Wrong_Data( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    recvFuncGetHplmnCase = 8;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_recvFuncGetHplmnCase_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseHplmn happy path case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_parseHplmn_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    recvFuncGetHplmnCase = 6;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_recvFuncGetHplmnCase_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _parseHplmn happy path case II in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_parseHplmn_Happy_Path_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    recvFuncGetHplmnCase = 7;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_recvFuncGetHplmnCase_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that CrsmMemoryStatus false memoryStatus case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_CrsmMemoryStatus_False_Memory_Status( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    recvFuncGetHplmnCase = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_recvFuncGetHplmnCase_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that _checkCrsmMemoryStatus false memoryStatus case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_checkCrsmMemoryStatus_False_Memory_Status( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    recvFuncGetHplmnCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_recvFuncGetHplmnCase_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path case in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    recvFuncGetHplmnCase = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_recvFuncGetHplmnCase_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path case II in callback function _Cellular_RecvFuncGetHplmn
 * for Cellular_CommonGetSimCardInfo to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetSimCardInfo_Cb_Cellular_RecvFuncGetHplmn_Happy_Path_Case_II( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetHplmn case. */
    cbCondition = 3;
    recvFuncGetHplmnCase = 0;
    parseHplmn_test = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetHplmn );
    Cellular_ATRemoveAllWhiteSpaces_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_recvFuncGetHplmnCase_ATGetNextTok_Calback );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonGetSimCardInfo to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetSimCardInfo_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularSimCardInfo_t simCardInfo;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    /* atReqGetImsi case. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetHplmn case. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    /* atReqGetIccid case. */
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = Cellular_CommonGetSimCardInfo( cellularHandle, &simCardInfo );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that NULL handler case Cellular_CommonSetPsmSettings to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonSetPsmSettings_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonSetPsmSettings( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that bad parameter case Cellular_CommonSetPsmSettings to return CELLULAR_BAD_PARAMETER.
 */
void test_Cellular_CommonSetPsmSettings_Bad_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonSetPsmSettings( cellularHandle, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that at command failure case Cellular_CommonSetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonSetPsmSettings_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    psmSettings.periodicRauValue = 0x0;
    psmSettings.gprsReadyTimer = 0x9B;
    psmSettings.periodicTauValue = 0xfc;
    psmSettings.activeTimeValue = 0x1;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT, CELLULAR_TIMEOUT );

    cellularStatus = Cellular_CommonSetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_TIMEOUT, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonSetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonSetPsmSettings_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    psmSettings.periodicRauValue = 0x0;
    psmSettings.gprsReadyTimer = 0x99;
    psmSettings.periodicTauValue = 0x4;
    psmSettings.activeTimeValue = 0x0;
    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = Cellular_CommonSetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that NULL handler case Cellular_CommonGetPsmSettings to return CELLULAR_INVALID_HANDLE.
 */
void test_Cellular_CommonGetPsmSettings_Null_Handler( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_INVALID_HANDLE );
    cellularStatus = Cellular_CommonGetPsmSettings( NULL, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_INVALID_HANDLE, cellularStatus );
}

/**
 * @brief Test that bad parameter case Cellular_CommonGetPsmSettings to return CELLULAR_BAD_PARAMETER.
 */
void test_Cellular_CommonGetPsmSettings_Bad_Parameter( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_BAD_PARAMETER, cellularStatus );
}

/**
 * @brief Test that at command failure case Cellular_CommonGetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetPsmSettings_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    psmSettings.periodicRauValue = 0;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_TIMED_OUT, CELLULAR_TIMEOUT );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_TIMEOUT, cellularStatus );
}

/**
 * @brief Test that null context case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Null_Context( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;


    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 0;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_FAILURE, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null at command failure case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Null_AtCmd_Failure( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;


    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null atResp item line case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Null_AtResp_Item_Line( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 1;
    commonCase = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that wrong data length case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Wrong_Data_Length( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 2;
    commonCase = 1;
    wrongDataLength = sizeof( CellularPsmSettings_t ) + 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that atResp item null case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Null_AtResp_Item( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 1;
    commonCase = 1;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that null data pointer case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Null_Data_Pointer( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;


    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 2;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    _Cellular_TranslatePktStatus_ExpectAndReturn( CELLULAR_PKT_STATUS_BAD_PARAM, CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that Cellular_ATRemovePrefix error case in Cellular_CommonGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_AtCmd_Error_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;


    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_BAD_PARAMETER );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    cpsms_pos_mode_error = 1;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that null token first error case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Null_Token_First( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    nullTokenFirst = 1;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that CPSMS_POS_MODE error case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_CPSMS_AtStrtoi_Error_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    cpsms_pos_mode_error = 1;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_IgnoreAndReturn( CELLULAR_AT_ERROR );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_FAILURE );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_INTERNAL_FAILURE );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_INTERNAL_FAILURE, cellularStatus );
}

/**
 * @brief Test that CPSMS_POS_MODE error case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_CPSMS_Error_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    cpsms_pos_mode_error = 1;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that CPSMS_POS_MODE negative number error case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_INTERNAL_FAILURE.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_CPSMS_Negative_Number_Error_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );

    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    cpsms_pos_mode_error = 2;
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Happy_Path_Idx_0( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    psmSettingsCheckTimerValue = 1;
    psmSettingsTimerIndex = 0;
    psmSettingsActiveTimerValue = 2;
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Happy_Path_Idx_1( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    psmSettingsCheckTimerValue = 1;
    psmSettingsTimerIndex = 1;
    psmSettingsActiveTimerValue = 2;
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path timer index is 2 case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Happy_Path_Idx_2( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    psmSettingsCheckTimerValue = 1;
    psmSettingsTimerIndex = 2;
    psmSettingsActiveTimerValue = 2;
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path timer index is 3 case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Happy_Path_Idx_3( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    psmSettingsCheckTimerValue = 1;
    psmSettingsTimerIndex = 3;
    psmSettingsActiveTimerValue = 2;
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path timer index is 4 case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Happy_Path_Idx_4( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    psmSettingsCheckTimerValue = 1;
    psmSettingsTimerIndex = 4;
    psmSettingsActiveTimerValue = 2;
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path timer index is 5 case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Happy_Path_Idx_5( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    psmSettingsCheckTimerValue = 1;
    psmSettingsTimerIndex = 5;
    psmSettingsActiveTimerValue = 2;
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path timer index is 6 case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Happy_Path_Idx_6( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    psmSettingsCheckTimerValue = 1;
    psmSettingsTimerIndex = 6;
    psmSettingsActiveTimerValue = 2;
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path timer index is 7 case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Happy_Path_Idx_7( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    psmSettingsCheckTimerValue = 1;
    psmSettingsTimerIndex = 7;
    psmSettingsActiveTimerValue = 2;
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that timer error return case in callback function _Cellular_RecvFuncGetPsmSettings
 * for Cellular_CommonGetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetPsmSettings_Cb_Cellular_RecvFuncGetPsmSettings_Timer_Error_Return( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );
    _Cellular_IsValidPdn_IgnoreAndReturn( CELLULAR_SUCCESS );
    cbCondition = 3;
    _Cellular_AtcmdRequestWithCallback_StubWithCallback( Mock_AtcmdRequestWithCallback__Cellular_RecvFuncGetPsmSettings );
    psmSettingsTimerIndex = 2;
    psmSettingsTimerError = 1;
    Cellular_ATRemovePrefix_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATRemoveAllDoubleQuote_IgnoreAndReturn( CELLULAR_AT_SUCCESS );
    Cellular_ATGetNextTok_StubWithCallback( Mock_Cellular_ATGetNextTok_Calback );
    Cellular_ATStrtoi_StubWithCallback( Mock_Cellular_ATStrtoi );

    _Cellular_TranslateAtCoreStatus_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );
    _Cellular_TranslatePktStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}

/**
 * @brief Test that happy path case Cellular_CommonGetPsmSettings to return CELLULAR_SUCCESS.
 */
void test_Cellular_CommonGetPsmSettings_Happy_Path( void )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    CellularHandle_t cellularHandle = &context;
    CellularPsmSettings_t psmSettings;

    _Cellular_CheckLibraryStatus_IgnoreAndReturn( CELLULAR_SUCCESS );

    _Cellular_AtcmdRequestWithCallback_IgnoreAndReturn( CELLULAR_PKT_STATUS_OK );

    cellularStatus = Cellular_CommonGetPsmSettings( cellularHandle, &psmSettings );
    TEST_ASSERT_EQUAL( CELLULAR_SUCCESS, cellularStatus );
}
