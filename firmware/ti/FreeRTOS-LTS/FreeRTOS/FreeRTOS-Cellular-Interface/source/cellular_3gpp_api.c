/*
 * FreeRTOS-Cellular-Interface v1.4.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @brief FreeRTOS Cellular Library API implementation with 3GPP AT command.
 */

/* Standard includes. */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "cellular_platform.h"

#ifndef CELLULAR_DO_NOT_USE_CUSTOM_CONFIG
    /* Include custom config file before other headers. */
    #include "cellular_config.h"
#endif
#include "cellular_config_defaults.h"
#include "cellular_internal.h"
#include "cellular_common_internal.h"
#include "cellular_common_api.h"
#include "cellular_at_core.h"
#include "cellular_types.h"

/*-----------------------------------------------------------*/

#define CELLULAR_CEDRXS_POS_ACT             ( 0U )
#define CELLULAR_CEDRXS_POS_VALUE           ( 1U )
#define CELLULAR_CEDRXS_MAX_ENTRY           ( 4U )

#define CELLULAR_AT_CMD_TYPICAL_MAX_SIZE    ( 32U )

#define PDN_ACT_PACKET_REQ_TIMEOUT_MS       ( 150000UL )

#define INVALID_PDN_INDEX                   ( 0xFFU )

/* Length of HPLMN including RAT. */
#define CRSM_HPLMN_RAT_LENGTH               ( 9U )

#define PRINTF_BINARY_PATTERN_INT4          "%c%c%c%c"
#define PRINTF_BYTE_TO_BINARY_INT4( i )          \
    ( ( ( ( i ) & 0x08U ) != 0U ) ? '1' : '0' ), \
    ( ( ( ( i ) & 0x04U ) != 0U ) ? '1' : '0' ), \
    ( ( ( ( i ) & 0x02U ) != 0U ) ? '1' : '0' ), \
    ( ( ( ( i ) & 0x01U ) != 0U ) ? '1' : '0' )

#define PRINTF_BINARY_PATTERN_INT8 \
    PRINTF_BINARY_PATTERN_INT4 PRINTF_BINARY_PATTERN_INT4
#define PRINTF_BYTE_TO_BINARY_INT8( i ) \
    PRINTF_BYTE_TO_BINARY_INT4( ( i ) >> 4 ), PRINTF_BYTE_TO_BINARY_INT4( i )

#define CPSMS_POS_MODE           ( 0U )
#define CPSMS_POS_RAU            ( 1U )
#define CPSMS_POS_RDY_TIMER      ( 2U )
#define CPSMS_POS_TAU            ( 3U )
#define CPSMS_POS_ACTIVE_TIME    ( 4U )

#define T3324_TIMER_UNIT( x )     ( ( uint32_t ) ( ( ( x ) & 0x000000E0U ) >> 5U ) ) /* Bits 6, 7, 8. */
#define T3324_TIMER_VALUE( x )    ( ( uint32_t ) ( ( x ) & 0x0000001FU ) )
#define T3324_TIMER_DEACTIVATED         ( 0xFFFFFFFFU )

#define T3324_TIMER_UNIT_2SECONDS       ( 0U )
#define T3324_TIMER_UNIT_1MINUTE        ( 1U )
#define T3324_TIMER_UNIT_DECIHOURS      ( 2U )
#define T3324_TIMER_UNIT_DEACTIVATED    ( 7U )

#define T3412_TIMER_UNIT( x )     ( ( uint32_t ) ( ( ( x ) & 0x000000E0U ) >> 5U ) ) /* Bits 6, 7, 8. */
#define T3412_TIMER_VALUE( x )    ( ( uint32_t ) ( ( x ) & 0x0000001FU ) )
#define T3412_TIMER_DEACTIVATED               ( 0xFFFFFFFFU )

#define T3412_TIMER_UNIT_10MINUTES            ( 0U )
#define T3412_TIMER_UNIT_1HOURS               ( 1U )
#define T3412_TIMER_UNIT_10HOURS              ( 2U )
#define T3412_TIMER_UNIT_2SECONDS             ( 3U )
#define T3412_TIMER_UNIT_30SECONDS            ( 4U )
#define T3412_TIMER_UNIT_1MINUTES             ( 5U )
#define T3412_TIMER_UNIT_DEACTIVATED          ( 7U )

#define CELLULAR_PDN_CONTEXT_TYPE_MAX_SIZE    ( 7U ) /* The length of "IPV4V6" + 1. */

/*-----------------------------------------------------------*/

/**
 * @ingroup cellular_datatypes_structs
 * @brief operator information.
 */
typedef struct cellularOperatorInfo
{
    CellularPlmnInfo_t plmnInfo;                             /**<  Device registered PLMN info (MCC and MNC).  */
    CellularRat_t rat;                                       /**<  Device registered Radio Access Technology (Cat-M, Cat-NB, GPRS etc).  */
    CellularNetworkRegistrationMode_t networkRegMode;        /**<  Network Registered mode of the device (Manual, Auto etc).   */
    CellularOperatorNameFormat_t operatorNameFormat;         /**<  Format of registered network operator name. */
    char operatorName[ CELLULAR_NETWORK_NAME_MAX_SIZE + 1 ]; /**<  Registered network operator name. */
} cellularOperatorInfo_t;

/*-----------------------------------------------------------*/

static CellularPktStatus_t _parseTimeZoneInCCLKResponse( char ** ppToken,
                                                         bool * pTimeZoneSignNegative,
                                                         const char * pTimeZoneResp,
                                                         CellularTime_t * pTimeInfo );
static CellularPktStatus_t _parseYearMonthDayInCCLKResponse( char ** ppToken,
                                                             char ** ppTimeZoneResp,
                                                             CellularTime_t * pTimeInfo );
static CellularPktStatus_t _parseTimeInCCLKResponse( char ** ppToken,
                                                     bool timeZoneSignNegative,
                                                     char ** ppTimeZoneResp,
                                                     CellularTime_t * pTimeInfo );
static CellularPktStatus_t _parseTimeZoneInfo( char * pTimeZoneResp,
                                               CellularTime_t * pTimeInfo );
static CellularPktStatus_t _Cellular_RecvFuncGetNetworkTime( CellularContext_t * pContext,
                                                             const CellularATCommandResponse_t * pAtResp,
                                                             void * pData,
                                                             uint16_t dataLen );
static CellularPktStatus_t _Cellular_RecvFuncGetFirmwareVersion( CellularContext_t * pContext,
                                                                 const CellularATCommandResponse_t * pAtResp,
                                                                 void * pData,
                                                                 uint16_t dataLen );
static CellularPktStatus_t _Cellular_RecvFuncGetImei( CellularContext_t * pContext,
                                                      const CellularATCommandResponse_t * pAtResp,
                                                      void * pData,
                                                      uint16_t dataLen );
static CellularPktStatus_t _Cellular_RecvFuncGetModelId( CellularContext_t * pContext,
                                                         const CellularATCommandResponse_t * pAtResp,
                                                         void * pData,
                                                         uint16_t dataLen );
static CellularPktStatus_t _Cellular_RecvFuncGetManufactureId( CellularContext_t * pContext,
                                                               const CellularATCommandResponse_t * pAtResp,
                                                               void * pData,
                                                               uint16_t dataLen );
static bool regResponseIsUrc( char * pRegLine );
static CellularPktStatus_t _Cellular_RecvFuncGetNetworkReg( CellularContext_t * pContext,
                                                            const CellularATCommandResponse_t * pAtResp,
                                                            void * pData,
                                                            uint16_t dataLen );
static CellularError_t queryNetworkStatus( CellularContext_t * pContext,
                                           const char * pCommand,
                                           const char * pPrefix,
                                           CellularNetworkRegType_t regType );
static bool _parseCopsRegModeToken( char * pToken,
                                    cellularOperatorInfo_t * pOperatorInfo );
static bool _parseCopsNetworkNameFormatToken( const char * pToken,
                                              cellularOperatorInfo_t * pOperatorInfo );
static bool _parseCopsNetworkNameToken( const char * pToken,
                                        cellularOperatorInfo_t * pOperatorInfo );
static bool _parseCopsRatToken( const char * pToken,
                                cellularOperatorInfo_t * pOperatorInfo );
static CellularATError_t _parseCops( char * pCopsResponse,
                                     cellularOperatorInfo_t * pOperatorInfo );
static CellularPktStatus_t _Cellular_RecvFuncUpdateMccMnc( CellularContext_t * pContext,
                                                           const CellularATCommandResponse_t * pAtResp,
                                                           void * pData,
                                                           uint16_t dataLen );
static CellularPktStatus_t _Cellular_RecvFuncIpAddress( CellularContext_t * pContext,
                                                        const CellularATCommandResponse_t * pAtResp,
                                                        void * pData,
                                                        uint16_t dataLen );
static CellularATError_t parseEidrxToken( char * pToken,
                                          uint8_t tokenIndex,
                                          CellularEidrxSettingsList_t * pEidrxSettingsList,
                                          uint8_t count );
static CellularATError_t parseEidrxLine( char * pInputLine,
                                         uint8_t count,
                                         CellularEidrxSettingsList_t * pEidrxSettingsList );
static CellularPktStatus_t _Cellular_RecvFuncGetEidrxSettings( CellularContext_t * pContext,
                                                               const CellularATCommandResponse_t * pAtResp,
                                                               void * pData,
                                                               uint16_t dataLen );
static CellularError_t atcmdUpdateMccMnc( CellularContext_t * pContext,
                                          cellularOperatorInfo_t * pOperatorInfo );
static CellularError_t atcmdQueryRegStatus( CellularContext_t * pContext,
                                            CellularServiceStatus_t * pServiceStatus );
static CellularATError_t parseT3412TimerValue( char * pToken,
                                               uint32_t * pTimerValueSeconds );
static CellularATError_t parseT3324TimerValue( char * pToken,
                                               uint32_t * pTimerValueSeconds );
static CellularSimCardLockState_t _getSimLockState( char * pToken );
static CellularPktStatus_t _Cellular_RecvFuncGetSimLockStatus( CellularContext_t * pContext,
                                                               const CellularATCommandResponse_t * pAtResp,
                                                               void * pData,
                                                               uint16_t dataLen );
static bool _checkCrsmMemoryStatus( const char * pToken );
static bool _checkCrsmReadStatus( const char * pToken );
static bool _parseHplmn( char * pToken,
                         void * pData );
static CellularPktStatus_t _Cellular_RecvFuncGetHplmn( CellularContext_t * pContext,
                                                       const CellularATCommandResponse_t * pAtResp,
                                                       void * pData,
                                                       uint16_t dataLen );
#if ( CELLULAR_CONFIG_USE_CCID_COMMAND == 1 )
    static CellularPktStatus_t _Cellular_RecvFuncGetIccid( CellularContext_t * pContext,
                                                           const CellularATCommandResponse_t * pAtResp,
                                                           void * pData,
                                                           uint16_t dataLen );
#endif
static CellularPktStatus_t _Cellular_RecvFuncGetImsi( CellularContext_t * pContext,
                                                      const CellularATCommandResponse_t * pAtResp,
                                                      void * pData,
                                                      uint16_t dataLen );
static uint32_t appendBinaryPattern( char * cmdBuf,
                                     uint32_t cmdLen,
                                     uint32_t value,
                                     bool endOfString );
static CellularATError_t parseCpsmsMode( char * pToken,
                                         CellularPsmSettings_t * pPsmSettings );
static CellularATError_t parseGetPsmToken( char * pToken,
                                           uint8_t tokenIndex,
                                           CellularPsmSettings_t * pPsmSettings );
static CellularPktStatus_t _Cellular_RecvFuncGetPsmSettings( CellularContext_t * pContext,
                                                             const CellularATCommandResponse_t * pAtResp,
                                                             void * pData,
                                                             uint16_t dataLen );

/*-----------------------------------------------------------*/

static CellularPktStatus_t _parseTimeZoneInCCLKResponse( char ** ppToken,
                                                         bool * pTimeZoneSignNegative,
                                                         const char * pTimeZoneResp,
                                                         CellularTime_t * pTimeInfo )
{
    int32_t tempValue = 0;
    CellularATError_t atCoreStatus = CELLULAR_AT_ERROR;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    /* Get Time Zone info. */
    *ppToken = strstr( pTimeZoneResp, "+" );

    if( *ppToken == NULL )
    {
        *ppToken = strstr( pTimeZoneResp, "-" );

        if( *ppToken != NULL )
        {
            /* Setting the timeZoneNegative value to 1 for processing seconds later. */
            *pTimeZoneSignNegative = true;
        }
    }

    if( *ppToken != NULL )
    {
        atCoreStatus = Cellular_ATStrtoi( *ppToken, 10, &tempValue );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            pTimeInfo->timeZone = tempValue;
        }
        else
        {
            LogError( ( "Error in Processing TimeZone Information. Token %s", *ppToken ) );
        }
    }

    pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _parseYearMonthDayInCCLKResponse( char ** ppToken,
                                                             char ** ppTimeZoneResp,
                                                             CellularTime_t * pTimeInfo )
{
    int32_t tempValue = 0;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    atCoreStatus = Cellular_ATStrtoi( *ppToken, 10, &tempValue );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        if( ( tempValue >= 0 ) && ( tempValue <= ( int32_t ) UINT16_MAX ) )
        {
            pTimeInfo->year = ( uint16_t ) tempValue;
        }
        else
        {
            LogError( ( "Error in Processing Year. Token %s", *ppToken ) );
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        /* Getting the next token to process month in the CCLK AT response. */
        atCoreStatus = Cellular_ATGetSpecificNextTok( ppTimeZoneResp, "/", ppToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATStrtoi( *ppToken, 10, &tempValue );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( ( tempValue >= 0 ) &&
                ( tempValue <= ( int32_t ) UINT8_MAX ) )
            {
                pTimeInfo->month = ( uint8_t ) tempValue;
            }
            else
            {
                LogError( ( "Error in Processing month. Token %s", *ppToken ) );
                atCoreStatus = CELLULAR_AT_ERROR;
            }
        }
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        /* Getting the next token to process date in the CCLK AT response. */
        atCoreStatus = Cellular_ATGetSpecificNextTok( ppTimeZoneResp, ",", ppToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATStrtoi( *ppToken, 10, &tempValue );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( ( tempValue >= 0 ) && ( tempValue <= ( int32_t ) UINT8_MAX ) )
            {
                pTimeInfo->day = ( uint8_t ) tempValue;
            }
            else
            {
                LogError( ( "Error in Processing Day. token %s", *ppToken ) );
                atCoreStatus = CELLULAR_AT_ERROR;
            }
        }
    }

    pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _parseTimeInCCLKResponse( char ** ppToken,
                                                     bool timeZoneSignNegative,
                                                     char ** ppTimeZoneResp,
                                                     CellularTime_t * pTimeInfo )
{
    int32_t tempValue = 0;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    atCoreStatus = Cellular_ATStrtoi( *ppToken, 10, &tempValue );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        if( ( tempValue >= 0 ) && ( tempValue <= ( int32_t ) UINT8_MAX ) )
        {
            pTimeInfo->hour = ( uint8_t ) tempValue;
        }
        else
        {
            LogError( ( "Error in Processing Hour. token %s", *ppToken ) );
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        /* Getting the next Token to process Minute in the CCLK AT Response. */
        atCoreStatus = Cellular_ATGetSpecificNextTok( ppTimeZoneResp, ":", ppToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATStrtoi( *ppToken, 10, &tempValue );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( ( tempValue >= 0 ) && ( tempValue <= ( int32_t ) UINT8_MAX ) )
            {
                pTimeInfo->minute = ( uint8_t ) tempValue;
            }
            else
            {
                LogError( ( "Error in Processing minute. Token %s", *ppToken ) );
                atCoreStatus = CELLULAR_AT_ERROR;
            }
        }
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        /* Getting the next token to process Second in the CCLK AT Response.
         * Get the next token based on the signedness of the Timezone. */
        if( !timeZoneSignNegative )
        {
            atCoreStatus = Cellular_ATGetSpecificNextTok( ppTimeZoneResp, "+", ppToken );
        }
        else
        {
            atCoreStatus = Cellular_ATGetSpecificNextTok( ppTimeZoneResp, "-", ppToken );
        }
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATStrtoi( *ppToken, 10, &tempValue );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( ( tempValue >= 0 ) && ( tempValue <= ( int32_t ) UINT8_MAX ) )
            {
                pTimeInfo->second = ( uint8_t ) tempValue;
            }
            else
            {
                LogError( ( "Error in Processing Second. Token %s", *ppToken ) );
                atCoreStatus = CELLULAR_AT_ERROR;
            }
        }
    }

    pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _parseTimeZoneInfo( char * pTimeZoneResp,
                                               CellularTime_t * pTimeInfo )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pToken = NULL;
    bool timeZoneSignNegative = false;
    char * pTempTimeZoneResp = NULL;

    pTempTimeZoneResp = pTimeZoneResp;
    ( void ) memset( pTimeInfo, 0, sizeof( CellularTime_t ) );
    atCoreStatus = Cellular_ATRemoveOutermostDoubleQuote( &pTempTimeZoneResp );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        pktStatus = _parseTimeZoneInCCLKResponse( &pToken, &timeZoneSignNegative,
                                                  pTempTimeZoneResp, pTimeInfo );
    }

    if( pktStatus == CELLULAR_PKT_STATUS_OK )
    {
        /* Getting the next token to process year in the CCLK AT response. */
        atCoreStatus = Cellular_ATGetSpecificNextTok( &pTempTimeZoneResp, "/", &pToken );
    }

    if( ( atCoreStatus == CELLULAR_AT_SUCCESS ) && ( pktStatus == CELLULAR_PKT_STATUS_OK ) )
    {
        pktStatus = _parseYearMonthDayInCCLKResponse( &pToken,
                                                      &pTempTimeZoneResp, pTimeInfo );
    }

    if( pktStatus == CELLULAR_PKT_STATUS_OK )
    {
        /* Getting the next token to process hour in the CCLK AT response. */
        atCoreStatus = Cellular_ATGetSpecificNextTok( &pTempTimeZoneResp, ":", &pToken );
    }

    if( ( atCoreStatus == CELLULAR_AT_SUCCESS ) && ( pktStatus == CELLULAR_PKT_STATUS_OK ) )
    {
        pktStatus = _parseTimeInCCLKResponse( &pToken, timeZoneSignNegative,
                                              &pTempTimeZoneResp, pTimeInfo );
    }

    if( pktStatus == CELLULAR_PKT_STATUS_OK )
    {
        LogDebug( ( "TimeZoneInfo: Timezone %d Year %d Month %d day %d,", ( int ) pTimeInfo->timeZone,
                    pTimeInfo->year,
                    pTimeInfo->month,
                    pTimeInfo->day ) );

        LogDebug( ( "Hour %d Minute %d Second %d",
                    pTimeInfo->hour,
                    pTimeInfo->minute,
                    pTimeInfo->second ) );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetNetworkTime( CellularContext_t * pContext,
                                                             const CellularATCommandResponse_t * pAtResp,
                                                             void * pData,
                                                             uint16_t dataLen )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pRespLine = NULL;

    if( pContext == NULL )
    {
        LogError( ( "GetNetworkTime: pContext is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetNetworkTime: Response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pData == NULL ) || ( dataLen == 0u ) )
    {
        LogError( ( "GetNetworkTime: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pRespLine = pAtResp->pItm->pLine;
        atCoreStatus = Cellular_ATRemovePrefix( &pRespLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemoveAllWhiteSpaces( pRespLine );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            pktStatus = _parseTimeZoneInfo( pRespLine, ( CellularTime_t * ) pData );
        }
        else
        {
            pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetFirmwareVersion( CellularContext_t * pContext,
                                                                 const CellularATCommandResponse_t * pAtResp,
                                                                 void * pData,
                                                                 uint16_t dataLen )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pRespLine = NULL;

    if( pContext == NULL )
    {
        LogError( ( "GetFirmwareVersion: pContext is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetFirmwareVersion: Response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pData == NULL ) || ( dataLen != ( CELLULAR_FW_VERSION_MAX_SIZE + 1U ) ) )
    {
        LogError( ( "GetFirmwareVersion: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pRespLine = pAtResp->pItm->pLine;
        atCoreStatus = Cellular_ATRemoveLeadingWhiteSpaces( &pRespLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemoveTrailingWhiteSpaces( pRespLine );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            ( void ) strncpy( ( char * ) pData, pRespLine, CELLULAR_FW_VERSION_MAX_SIZE );
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetImei( CellularContext_t * pContext,
                                                      const CellularATCommandResponse_t * pAtResp,
                                                      void * pData,
                                                      uint16_t dataLen )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pRespLine = NULL;

    if( pContext == NULL )
    {
        LogError( ( "GetImei: pContext is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetImei: Response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pData == NULL ) || ( dataLen != ( CELLULAR_IMEI_MAX_SIZE + 1U ) ) )
    {
        LogError( ( "GetImei: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pRespLine = pAtResp->pItm->pLine;
        atCoreStatus = Cellular_ATRemoveLeadingWhiteSpaces( &pRespLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemoveAllWhiteSpaces( pRespLine );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            ( void ) strncpy( ( char * ) pData, pRespLine, CELLULAR_IMEI_MAX_SIZE );
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetModelId( CellularContext_t * pContext,
                                                         const CellularATCommandResponse_t * pAtResp,
                                                         void * pData,
                                                         uint16_t dataLen )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pRespLine = NULL;

    if( pContext == NULL )
    {
        LogError( ( "GetModelId: pContext is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetModelId: Response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pData == NULL ) || ( dataLen != ( CELLULAR_MODEL_ID_MAX_SIZE + 1U ) ) )
    {
        LogError( ( "GetModelId: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pRespLine = pAtResp->pItm->pLine;
        atCoreStatus = Cellular_ATRemoveLeadingWhiteSpaces( &pRespLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemoveTrailingWhiteSpaces( pRespLine );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            ( void ) strncpy( ( char * ) pData, pRespLine, CELLULAR_MODEL_ID_MAX_SIZE );
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetManufactureId( CellularContext_t * pContext,
                                                               const CellularATCommandResponse_t * pAtResp,
                                                               void * pData,
                                                               uint16_t dataLen )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pRespLine = NULL;

    if( pContext == NULL )
    {
        LogError( ( "GetManufactureId: pContext is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetManufactureId: Response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pData == NULL ) || ( dataLen != ( CELLULAR_MANUFACTURE_ID_MAX_SIZE + 1U ) ) )
    {
        LogError( ( "GetManufactureId: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pRespLine = pAtResp->pItm->pLine;
        atCoreStatus = Cellular_ATRemoveLeadingWhiteSpaces( &pRespLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemoveTrailingWhiteSpaces( pRespLine );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            ( void ) strncpy( ( char * ) pData, pRespLine, CELLULAR_MANUFACTURE_ID_MAX_SIZE );
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/


static bool regResponseIsUrc( char * pRegLine )
{
    bool isUrcResponse = false;
    char * pSeparator = NULL;

    /* CREG, CEREG, CGREG has the same prefix for AT command response and URC.
     * There will be cases that the URC code is regarded as AT command response.
     * The response content can be used to distinguish them.
     *
     * Take AT+CREG for example, CREG has the following response format.
     * Read response : +CREG: <n>,<stat>[,<lac>,<ci>[,<AcTStatus>]]
     * URC : +CREG: <stat>[,[<lac>],[<ci>][,[<AcTStatus>][,<cause_type>, <reject_cause>]]]
     *
     * Not registered searching response:
     * Read response : +CREG: 2,2
     * URC : +CREG: 2
     *
     * Registered, home network response
     * Read response : +CREG: 2,1,"FFFE","341B50D",8
     * URC : +CREG: 1,"FFFE","341B50D", 8
     */
    pSeparator = strstr( pRegLine, "," );

    if( pSeparator == NULL )
    {
        /* Not registered searching response case. */
        isUrcResponse = true;
    }
    else if( pSeparator[ 1 ] == '"' )
    {
        /* Registered case, the second token start with '"' */
        isUrcResponse = true;
    }
    else
    {
        isUrcResponse = false;
    }

    return isUrcResponse;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetNetworkReg( CellularContext_t * pContext,
                                                            const CellularATCommandResponse_t * pAtResp,
                                                            void * pData,
                                                            uint16_t dataLen )
{
    char * pPregLine = NULL;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    CellularNetworkRegType_t regType = CELLULAR_REG_TYPE_UNKNOWN;
    CellularATCommandLine_t * pCommandLine = NULL;

    if( pContext == NULL )
    {
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "_Cellular_RecvFuncGetPsreg: response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pData == NULL ) || ( dataLen != sizeof( CellularNetworkRegType_t ) ) )
    {
        LogError( ( "_Cellular_RecvFuncGetPsreg: ppData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pCommandLine = pAtResp->pItm;
        regType = *( ( CellularNetworkRegType_t * ) pData );

        while( ( pCommandLine != NULL ) && ( pktStatus == CELLULAR_PKT_STATUS_OK ) )
        {
            pPregLine = pCommandLine->pLine;

            /* Assumption is that the data is null terminated so we don't need the dataLen. */
            _Cellular_LockAtDataMutex( pContext );

            if( regResponseIsUrc( pPregLine ) == true )
            {
                /* Remove the prefix for URC handler. */
                atCoreStatus = Cellular_ATRemovePrefix( &pPregLine );
                pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );

                if( pktStatus == CELLULAR_PKT_STATUS_OK )
                {
                    pktStatus = _Cellular_ParseRegStatus( pContext, pPregLine, true, regType );
                }
            }
            else
            {
                pktStatus = _Cellular_ParseRegStatus( pContext, pPregLine, false, regType );
            }

            _Cellular_UnlockAtDataMutex( pContext );
            pCommandLine = pCommandLine->pNext;
        }

        LogDebug( ( "atcmd network register status %d pktStatus:%d", regType, pktStatus ) );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularError_t queryNetworkStatus( CellularContext_t * pContext,
                                           const char * pCommand,
                                           const char * pPrefix,
                                           CellularNetworkRegType_t regType )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularNetworkRegType_t recvRegType = regType;
    CellularAtReq_t atReqGetResult = { 0 };

    CELLULAR_CONFIG_ASSERT( pContext != NULL );
    atReqGetResult.pAtCmd = pCommand;
    atReqGetResult.atCmdType = CELLULAR_AT_MULTI_WITH_PREFIX;
    atReqGetResult.pAtRspPrefix = pPrefix;
    atReqGetResult.respCallback = _Cellular_RecvFuncGetNetworkReg;
    atReqGetResult.pData = &recvRegType;
    atReqGetResult.dataLen = ( uint16_t ) sizeof( CellularNetworkRegType_t );

    pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetResult );
    cellularStatus = _Cellular_TranslatePktStatus( pktStatus );

    return cellularStatus;
}

/*-----------------------------------------------------------*/

static bool _parseCopsRegModeToken( char * pToken,
                                    cellularOperatorInfo_t * pOperatorInfo )
{
    bool parseStatus = true;
    int32_t var = 0;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    if( pToken == NULL )
    {
        LogError( ( "_parseCopsRegMode: Input Parameter NULL" ) );
        parseStatus = false;
    }
    else
    {
        atCoreStatus = Cellular_ATStrtoi( pToken, 10, &var );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( ( var >= 0 ) && ( var < ( int32_t ) REGISTRATION_MODE_MAX ) )
            {
                /* MISRA Ref 10.5.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-105 */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                pOperatorInfo->networkRegMode = ( CellularNetworkRegistrationMode_t ) var;
            }
            else
            {
                LogError( ( "_parseCopsRegMode: Error in processing Network Registration mode. Token %s", pToken ) );
                parseStatus = false;
            }
        }
    }

    return parseStatus;
}

/*-----------------------------------------------------------*/

static bool _parseCopsNetworkNameFormatToken( const char * pToken,
                                              cellularOperatorInfo_t * pOperatorInfo )
{
    bool parseStatus = true;
    int32_t var = 0;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    if( pToken == NULL )
    {
        LogError( ( "_parseCopsNetworkNameFormat: Input Parameter NULL" ) );
        parseStatus = false;
    }
    else
    {
        atCoreStatus = Cellular_ATStrtoi( pToken, 10, &var );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( ( var >= 0 ) &&
                ( var < ( int32_t ) OPERATOR_NAME_FORMAT_MAX ) )
            {
                /* MISRA Ref 10.5.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-105 */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                pOperatorInfo->operatorNameFormat = ( CellularOperatorNameFormat_t ) var;
            }
            else
            {
                LogError( ( "_parseCopsNetworkNameFormat: Error in processing Network Registration mode. Token %s", pToken ) );
                parseStatus = false;
            }
        }
    }

    return parseStatus;
}

/*-----------------------------------------------------------*/

static bool _parseCopsNetworkNameToken( const char * pToken,
                                        cellularOperatorInfo_t * pOperatorInfo )
{
    bool parseStatus = true;
    uint32_t mccMncLen = 0U;

    if( pToken == NULL )
    {
        LogError( ( "_parseCopsNetworkName: Input Parameter NULL" ) );
        parseStatus = false;
    }
    else
    {
        if( ( pOperatorInfo->operatorNameFormat == OPERATOR_NAME_FORMAT_LONG ) ||
            ( pOperatorInfo->operatorNameFormat == OPERATOR_NAME_FORMAT_SHORT ) )
        {
            ( void ) strncpy( pOperatorInfo->operatorName, pToken, CELLULAR_NETWORK_NAME_MAX_SIZE );
        }
        else if( pOperatorInfo->operatorNameFormat == OPERATOR_NAME_FORMAT_NUMERIC )
        {
            mccMncLen = ( uint32_t ) strlen( pToken );

            if( ( mccMncLen == ( CELLULAR_MCC_MAX_SIZE + CELLULAR_MNC_MAX_SIZE ) ) ||
                ( mccMncLen == ( CELLULAR_MCC_MAX_SIZE + CELLULAR_MNC_MAX_SIZE - 1U ) ) )
            {
                ( void ) strncpy( pOperatorInfo->plmnInfo.mcc, pToken, CELLULAR_MCC_MAX_SIZE );
                pOperatorInfo->plmnInfo.mcc[ CELLULAR_MCC_MAX_SIZE ] = '\0';
                ( void ) strncpy( pOperatorInfo->plmnInfo.mnc, &( pToken[ CELLULAR_MCC_MAX_SIZE ] ),
                                  ( uint32_t ) ( mccMncLen - CELLULAR_MCC_MAX_SIZE + 1u ) );
                pOperatorInfo->plmnInfo.mnc[ CELLULAR_MNC_MAX_SIZE ] = '\0';
            }
            else
            {
                LogError( ( "_parseCopsNetworkName: Error in processing Network MCC MNC: Length not Valid" ) );
                parseStatus = false;
            }
        }
        else
        {
            LogError( ( "Error in processing Operator Name: Format Unknown" ) );
            parseStatus = false;
        }
    }

    return parseStatus;
}

/*-----------------------------------------------------------*/

static bool _parseCopsRatToken( const char * pToken,
                                cellularOperatorInfo_t * pOperatorInfo )
{
    bool parseStatus = true;
    int32_t var = 0;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    if( pToken == NULL )
    {
        LogError( ( "_parseCopsNetworkName: Input Parameter NULL" ) );
        parseStatus = false;
    }
    else
    {
        atCoreStatus = Cellular_ATStrtoi( pToken, 10, &var );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( ( var < ( int32_t ) CELLULAR_RAT_MAX ) && ( var >= 0 ) )
            {
                /* MISRA Ref 10.5.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-105 */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                pOperatorInfo->rat = ( CellularRat_t ) var;
            }
            else
            {
                LogError( ( "_parseCopsNetworkName: Error in processing RAT. Token %s", pToken ) );
                parseStatus = false;
            }
        }
    }

    return parseStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t _parseCops( char * pCopsResponse,
                                     cellularOperatorInfo_t * pOperatorInfo )
{
    char * pToken = NULL;
    char * pTempCopsResponse = pCopsResponse;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    bool parseStatus = false;

    /* Getting next token from COPS response. */
    atCoreStatus = Cellular_ATGetNextTok( &pTempCopsResponse, &pToken );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        parseStatus = _parseCopsRegModeToken( pToken, pOperatorInfo );

        if( parseStatus == false )
        {
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATGetNextTok( &pTempCopsResponse, &pToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        parseStatus = _parseCopsNetworkNameFormatToken( pToken, pOperatorInfo );

        if( parseStatus == false )
        {
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATGetNextTok( &pTempCopsResponse, &pToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        parseStatus = _parseCopsNetworkNameToken( pToken, pOperatorInfo );

        if( parseStatus == false )
        {
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATGetNextTok( &pTempCopsResponse, &pToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        parseStatus = _parseCopsRatToken( pToken, pOperatorInfo );

        if( parseStatus == false )
        {
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncUpdateMccMnc( CellularContext_t * pContext,
                                                           const CellularATCommandResponse_t * pAtResp,
                                                           void * pData,
                                                           uint16_t dataLen )
{
    char * pCopsResponse = NULL;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    cellularOperatorInfo_t * pOperatorInfo = NULL;

    if( pContext == NULL )
    {
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "UpdateMccMnc: Response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pData == NULL ) || ( dataLen != sizeof( cellularOperatorInfo_t ) ) )
    {
        LogError( ( "UpdateMccMnc: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else
    {
        pCopsResponse = pAtResp->pItm->pLine;
        pOperatorInfo = ( cellularOperatorInfo_t * ) pData;

        /* Remove COPS Prefix. */
        atCoreStatus = Cellular_ATRemovePrefix( &pCopsResponse );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            /* Removing all the Quotes from the COPS response. */
            atCoreStatus = Cellular_ATRemoveAllDoubleQuote( pCopsResponse );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            /* Removing all Space from the COPS response. */
            atCoreStatus = Cellular_ATRemoveAllWhiteSpaces( pCopsResponse );
        }

        /* parse all the data from cops. */
        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = _parseCops( pCopsResponse, pOperatorInfo );
        }

        if( atCoreStatus == CELLULAR_AT_ERROR )
        {
            LogError( ( "ERROR: COPS %s", pCopsResponse ) );
            pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncIpAddress( CellularContext_t * pContext,
                                                        const CellularATCommandResponse_t * pAtResp,
                                                        void * pData,
                                                        uint16_t dataLen )
{
    char * pInputLine = NULL, * pToken = NULL;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    if( pContext == NULL )
    {
        LogError( ( "Recv IP address: Invalid context" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "Recv IP address: response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pData == NULL ) || ( dataLen == 0U ) )
    {
        LogError( ( "Recv IP address: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pInputLine = pAtResp->pItm->pLine;
        atCoreStatus = Cellular_ATRemovePrefix( &pInputLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pInputLine, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            LogDebug( ( "Recv IP address: Context id: %s, Address %s", pToken, pInputLine ) );

            if( pInputLine[ 0 ] != '\0' )
            {
                ( void ) strncpy( pData, pInputLine, dataLen );
            }
            else
            {
                /* This is the case "+CGPADDR: <cid>". Return empty string. */
                ( void ) memset( pData, 0, dataLen );
            }
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t parseEidrxToken( char * pToken,
                                          uint8_t tokenIndex,
                                          CellularEidrxSettingsList_t * pEidrxSettingsList,
                                          uint8_t count )
{
    int32_t tempValue = 0;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    switch( tokenIndex )
    {
        case CELLULAR_CEDRXS_POS_ACT:
            atCoreStatus = Cellular_ATStrtoi( pToken, 10, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= 0 ) &&
                    ( tempValue <= ( int32_t ) UINT8_MAX ) )
                {
                    pEidrxSettingsList->eidrxList[ count ].rat = ( uint8_t ) tempValue;
                }
                else
                {
                    LogError( ( "Error in processing RAT value. Token %s", pToken ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }

            break;

        case CELLULAR_CEDRXS_POS_VALUE:
            atCoreStatus = Cellular_ATStrtoi( pToken, 2, &tempValue );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                if( ( tempValue >= 0 ) &&
                    ( tempValue <= ( int32_t ) UINT8_MAX ) )
                {
                    pEidrxSettingsList->eidrxList[ count ].requestedEdrxValue = ( uint8_t ) tempValue;
                }
                else
                {
                    LogError( ( "Error in processing Requested Edrx value. Token %s", pToken ) );
                    atCoreStatus = CELLULAR_AT_ERROR;
                }
            }

            break;

        default:
            LogError( ( "Unknown Parameter Position in AT+CEDRXS Response" ) );
            atCoreStatus = CELLULAR_AT_ERROR;
            break;
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t parseEidrxLine( char * pInputLine,
                                         uint8_t count,
                                         CellularEidrxSettingsList_t * pEidrxSettingsList )
{
    char * pToken = NULL;
    char * pLocalInputLine = pInputLine;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    uint8_t tokenIndex = 0;

    atCoreStatus = Cellular_ATRemovePrefix( &pLocalInputLine );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATRemoveAllDoubleQuote( pLocalInputLine );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        atCoreStatus = Cellular_ATGetNextTok( &pLocalInputLine, &pToken );
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        tokenIndex = 0;

        while( pToken != NULL )
        {
            if( parseEidrxToken( pToken, tokenIndex, pEidrxSettingsList, count ) != CELLULAR_AT_SUCCESS )
            {
                LogInfo( ( "parseEidrxToken %s index %d failed", pToken, tokenIndex ) );
            }

            tokenIndex++;

            if( Cellular_ATGetNextTok( &pLocalInputLine, &pToken ) != CELLULAR_AT_SUCCESS )
            {
                break;
            }
        }
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        LogDebug( ( "GetEidrx setting[%d]: RAT: %d, Value: 0x%x",
                    count, pEidrxSettingsList->eidrxList[ count ].rat,
                    pEidrxSettingsList->eidrxList[ count ].requestedEdrxValue ) );
    }
    else
    {
        LogError( ( "GetEidrx: Parsing Error encountered, atCoreStatus: %d", atCoreStatus ) );
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetEidrxSettings( CellularContext_t * pContext,
                                                               const CellularATCommandResponse_t * pAtResp,
                                                               void * pData,
                                                               uint16_t dataLen )
{
    char * pInputLine = NULL;
    uint8_t count = 0;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    CellularEidrxSettingsList_t * pEidrxSettingsList = NULL;
    const CellularATCommandLine_t * pCommnadItem = NULL;

    if( pContext == NULL )
    {
        LogError( ( "GetEidrxSettings: Invalid context" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetEidrxSettings: Response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pData == NULL ) || ( dataLen != CELLULAR_EDRX_LIST_MAX_SIZE ) )
    {
        LogError( ( "GetEidrxSettings: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pEidrxSettingsList = ( CellularEidrxSettingsList_t * ) pData;
        pCommnadItem = pAtResp->pItm;

        while( ( pCommnadItem != NULL ) && ( pktStatus == CELLULAR_PKT_STATUS_OK ) )
        {
            pInputLine = pCommnadItem->pLine;

            if( ( strcmp( "+CEDRXS: 0", pInputLine ) == 0 ) ||
                ( strcmp( "+CEDRXS:", pInputLine ) == 0 ) )
            {
                LogDebug( ( "GetEidrx: empty EDRXS setting %s", pInputLine ) );
            }
            else
            {
                atCoreStatus = parseEidrxLine( pInputLine, count, pEidrxSettingsList );
                pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );

                if( pktStatus == CELLULAR_PKT_STATUS_OK )
                {
                    count++;
                }
            }

            pCommnadItem = pCommnadItem->pNext;
            pEidrxSettingsList->count = count;
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularError_t atcmdUpdateMccMnc( CellularContext_t * pContext,
                                          cellularOperatorInfo_t * pOperatorInfo )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus;
    CellularAtReq_t atCopsRequest = { 0 };

    /* Set the response to numeric format. */
    atCopsRequest.pAtCmd = "AT+COPS=3,2";
    atCopsRequest.atCmdType = CELLULAR_AT_NO_RESULT;
    pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atCopsRequest );

    if( pktStatus == CELLULAR_PKT_STATUS_OK )
    {
        /* Acquire the MCC and MNC information. */
        atCopsRequest.pAtCmd = "AT+COPS?";
        atCopsRequest.atCmdType = CELLULAR_AT_WITH_PREFIX;
        atCopsRequest.pAtRspPrefix = "+COPS";
        atCopsRequest.respCallback = _Cellular_RecvFuncUpdateMccMnc;
        atCopsRequest.pData = pOperatorInfo;
        atCopsRequest.dataLen = ( uint16_t ) sizeof( cellularOperatorInfo_t );
        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atCopsRequest );
    }

    cellularStatus = _Cellular_TranslatePktStatus( pktStatus );

    return cellularStatus;
}

/*-----------------------------------------------------------*/

static CellularError_t atcmdQueryRegStatus( CellularContext_t * pContext,
                                            CellularServiceStatus_t * pServiceStatus )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    const cellularAtData_t * pLibAtData = NULL;
    CellularNetworkRegistrationStatus_t psRegStatus = REGISTRATION_STATUS_UNKNOWN;

    CELLULAR_CONFIG_ASSERT( pContext != NULL );

    cellularStatus = queryNetworkStatus( pContext, "AT+CREG?", "+CREG", CELLULAR_REG_TYPE_CREG );

    #ifndef CELLULAR_MODEM_NO_GSM_NETWORK
        /* Added below +CGREG support as some modems also support GSM/EDGE network. */
        if( cellularStatus == CELLULAR_SUCCESS )
        {
            /* Ignore the network status query return value with CGREG. Some modem
             * may not support EDGE or GSM. In this case, psRegStatus is not stored
             * in libAtData. CEREG will be used to query the ps network status. */
            ( void ) queryNetworkStatus( pContext, "AT+CGREG?", "+CGREG", CELLULAR_REG_TYPE_CGREG );
        }

        /* Check if modem acquired GPRS Registration. */
        /* Query CEREG only if the modem did not already acquire PS registration. */
        _Cellular_LockAtDataMutex( pContext );
        psRegStatus = pContext->libAtData.psRegStatus;
        _Cellular_UnlockAtDataMutex( pContext );
    #endif /* ifndef CELLULAR_MODEM_NO_GSM_NETWORK */

    #ifndef CELLULAR_MODEM_NO_EPS_NETWORK
        if( ( cellularStatus == CELLULAR_SUCCESS ) &&
            ( psRegStatus != REGISTRATION_STATUS_REGISTERED_HOME ) &&
            ( psRegStatus != REGISTRATION_STATUS_ROAMING_REGISTERED ) )
        {
            cellularStatus = queryNetworkStatus( pContext, "AT+CEREG?", "+CEREG", CELLULAR_REG_TYPE_CEREG );
        }
    #endif

    /* Get the service status from lib AT data. */
    if( cellularStatus == CELLULAR_SUCCESS )
    {
        pLibAtData = &( pContext->libAtData );
        _Cellular_LockAtDataMutex( pContext );
        pServiceStatus->rat = pLibAtData->rat;
        pServiceStatus->csRegistrationStatus = pLibAtData->csRegStatus;
        pServiceStatus->psRegistrationStatus = pLibAtData->psRegStatus;
        pServiceStatus->csRejectionCause = pLibAtData->csRejCause;
        pServiceStatus->csRejectionType = pLibAtData->csRejectType;
        pServiceStatus->psRejectionCause = pLibAtData->psRejCause;
        pServiceStatus->psRejectionType = pLibAtData->psRejectType;
        _Cellular_UnlockAtDataMutex( pContext );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t parseT3412TimerValue( char * pToken,
                                               uint32_t * pTimerValueSeconds )
{
    int32_t tempValue = 0;
    uint32_t tokenValue = 0;
    uint32_t timerUnitIndex = 0;
    uint32_t timerValue = 0;
    CellularATError_t atCoreStatus = Cellular_ATStrtoi( pToken, 2, &tempValue );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        if( tempValue < 0 )
        {
            LogError( ( "Error in processing Periodic Processing Active time value. Token %s", pToken ) );
            atCoreStatus = CELLULAR_AT_ERROR;
        }
        else
        {
            tokenValue = ( uint32_t ) tempValue;
        }
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        timerUnitIndex = T3412_TIMER_UNIT( tokenValue );
        timerValue = T3412_TIMER_VALUE( tokenValue );

        /* Parse the time unit. */
        switch( timerUnitIndex )
        {
            case T3412_TIMER_UNIT_10MINUTES:
                *pTimerValueSeconds = timerValue * ( 10U * 60U );
                break;

            case T3412_TIMER_UNIT_1HOURS:
                *pTimerValueSeconds = timerValue * ( 1U * 60U * 60U );
                break;

            case T3412_TIMER_UNIT_10HOURS:
                *pTimerValueSeconds = timerValue * ( 10U * 60U * 60U );
                break;

            case T3412_TIMER_UNIT_2SECONDS:
                *pTimerValueSeconds = timerValue * 2U;
                break;

            case T3412_TIMER_UNIT_30SECONDS:
                *pTimerValueSeconds = timerValue * 30U;
                break;

            case T3412_TIMER_UNIT_1MINUTES:
                *pTimerValueSeconds = timerValue * 60U;
                break;

            case T3412_TIMER_UNIT_DEACTIVATED:
                *pTimerValueSeconds = T3412_TIMER_DEACTIVATED;
                break;

            default:
                LogError( ( "Invalid T3412 timer unit index" ) );
                atCoreStatus = CELLULAR_AT_ERROR;
                break;
        }
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t parseT3324TimerValue( char * pToken,
                                               uint32_t * pTimerValueSeconds )
{
    int32_t tempValue = 0;
    uint32_t tokenValue = 0;
    uint32_t timerUnitIndex = 0;
    uint32_t timerValue = 0;
    CellularATError_t atCoreStatus = Cellular_ATStrtoi( pToken, 2, &tempValue );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        if( tempValue < 0 )
        {
            LogError( ( "Error in processing Periodic Processing Active time value. Token %s", pToken ) );
            atCoreStatus = CELLULAR_AT_ERROR;
        }
        else
        {
            tokenValue = ( uint32_t ) tempValue;
        }
    }

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        timerUnitIndex = T3324_TIMER_UNIT( tokenValue );
        timerValue = T3324_TIMER_VALUE( tokenValue );

        /* Parse the time unit. */
        switch( timerUnitIndex )
        {
            case T3324_TIMER_UNIT_2SECONDS:
                *pTimerValueSeconds = timerValue * 2U;
                break;

            case T3324_TIMER_UNIT_1MINUTE:
                *pTimerValueSeconds = timerValue * 60U;
                break;

            case T3324_TIMER_UNIT_DECIHOURS:
                *pTimerValueSeconds = timerValue * ( 6U * 60U );
                break;

            case T3324_TIMER_UNIT_DEACTIVATED:
                *pTimerValueSeconds = T3324_TIMER_DEACTIVATED;
                break;

            default:
                LogError( ( "Invalid T3324 timer unit index" ) );
                atCoreStatus = CELLULAR_AT_ERROR;
                break;
        }
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonGetEidrxSettings( CellularHandle_t cellularHandle,
                                                 CellularEidrxSettingsList_t * pEidrxSettingsList )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetEidrx = { 0 };

    atReqGetEidrx.pAtCmd = "AT+CEDRXS?";
    atReqGetEidrx.atCmdType = CELLULAR_AT_MULTI_WITH_PREFIX;
    atReqGetEidrx.pAtRspPrefix = "+CEDRXS";
    atReqGetEidrx.respCallback = _Cellular_RecvFuncGetEidrxSettings;
    atReqGetEidrx.pData = pEidrxSettingsList;
    atReqGetEidrx.dataLen = CELLULAR_EDRX_LIST_MAX_SIZE;

    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pEidrxSettingsList == NULL )
    {
        LogError( ( "Cellular_CommonGetEidrxSettings : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        ( void ) memset( pEidrxSettingsList, 0, sizeof( CellularEidrxSettingsList_t ) );
        /* Query the pEidrxSettings from the network. */
        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetEidrx );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_GetEidrxSettings: couldn't retrieve Eidrx settings" ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonSetEidrxSettings( CellularHandle_t cellularHandle,
                                                 const CellularEidrxSettings_t * pEidrxSettings )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { '\0' };
    CellularAtReq_t atReqSetEidrx = { 0 };

    atReqSetEidrx.pAtCmd = cmdBuf;
    atReqSetEidrx.atCmdType = CELLULAR_AT_NO_RESULT;
    atReqSetEidrx.pAtRspPrefix = NULL;
    atReqSetEidrx.respCallback = NULL;
    atReqSetEidrx.pData = NULL;
    atReqSetEidrx.dataLen = 0;

    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pEidrxSettings == NULL )
    {
        LogError( ( "Cellular_CommonSetEidrxSettings : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        /* Form the AT command. */

        /* MISRA Ref 21.6.1 [Use of snprintf] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-216 */
        /* coverity[misra_c_2012_rule_21_6_violation]. */
        ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_MAX_SIZE, "%s%d,%d,\"" PRINTF_BINARY_PATTERN_INT4 "\"",
                           "AT+CEDRXS=",
                           pEidrxSettings->mode,
                           pEidrxSettings->rat,
                           PRINTF_BYTE_TO_BINARY_INT4( pEidrxSettings->requestedEdrxValue ) );
        LogDebug( ( "Eidrx setting: %s ", cmdBuf ) );
        /* Query the PSMsettings from the network. */
        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqSetEidrx );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "_Cellular_SetEidrxSettings: couldn't set Eidrx settings" ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonRfOn( CellularHandle_t cellularHandle )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus;
    CellularPktStatus_t pktStatus;
    CellularAtReq_t atReq = { 0 };

    atReq.pAtCmd = "AT+CFUN=1";
    atReq.atCmdType = CELLULAR_AT_NO_RESULT;
    atReq.pAtRspPrefix = NULL;
    atReq.respCallback = NULL;
    atReq.pData = NULL;
    atReq.dataLen = 0;

    /* Make sure library is open. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReq );
        cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonRfOff( CellularHandle_t cellularHandle )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus;
    CellularPktStatus_t pktStatus;
    CellularAtReq_t atReq = { 0 };

    atReq.pAtCmd = "AT+CFUN=4";
    atReq.atCmdType = CELLULAR_AT_NO_RESULT;
    atReq.pAtRspPrefix = NULL;
    atReq.respCallback = NULL;
    atReq.pData = NULL;
    atReq.dataLen = 0;

    /* Make sure library is open. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReq );
        cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonGetRegisteredNetwork( CellularHandle_t cellularHandle,
                                                     CellularPlmnInfo_t * pNetworkInfo )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    cellularOperatorInfo_t * pOperatorInfo = ( cellularOperatorInfo_t * ) Platform_Malloc( sizeof( cellularOperatorInfo_t ) );

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pNetworkInfo == NULL )
    {
        LogError( ( "Cellular_CommonGetRegisteredNetwork : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else if( pOperatorInfo == NULL )
    {
        LogError( ( "Cellular_CommonGetRegisteredNetwork : Bad parameter" ) );
        cellularStatus = CELLULAR_NO_MEMORY;
    }
    else
    {
        ( void ) memset( pOperatorInfo, 0, sizeof( cellularOperatorInfo_t ) );
        cellularStatus = atcmdUpdateMccMnc( pContext, pOperatorInfo );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        if( pOperatorInfo->rat != CELLULAR_RAT_INVALID )
        {
            ( void ) memcpy( pNetworkInfo->mcc, pOperatorInfo->plmnInfo.mcc, CELLULAR_MCC_MAX_SIZE );
            pNetworkInfo->mcc[ CELLULAR_MCC_MAX_SIZE ] = '\0';
            ( void ) memcpy( pNetworkInfo->mnc, pOperatorInfo->plmnInfo.mnc, CELLULAR_MNC_MAX_SIZE );
            pNetworkInfo->mnc[ CELLULAR_MNC_MAX_SIZE ] = '\0';
        }
        else
        {
            cellularStatus = CELLULAR_UNKNOWN;
        }
    }

    Platform_Free( pOperatorInfo );

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonGetServiceStatus( CellularHandle_t cellularHandle,
                                                 CellularServiceStatus_t * pServiceStatus )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    cellularOperatorInfo_t operatorInfo;

    ( void ) memset( &operatorInfo, 0, sizeof( cellularOperatorInfo_t ) );

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pServiceStatus == NULL )
    {
        LogError( ( "Cellular_CommonGetServiceStatus : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        /* Always query and update the cellular Lib AT data. */
        ( void ) atcmdQueryRegStatus( pContext, pServiceStatus );
        ( void ) atcmdUpdateMccMnc( pContext, &operatorInfo );

        /* Service status data from operator info. */
        pServiceStatus->networkRegistrationMode = operatorInfo.networkRegMode;
        pServiceStatus->plmnInfo = operatorInfo.plmnInfo;
        ( void ) strncpy( pServiceStatus->operatorName, operatorInfo.operatorName, CELLULAR_NETWORK_NAME_MAX_SIZE );
        pServiceStatus->operatorNameFormat = operatorInfo.operatorNameFormat;

        LogDebug( ( "SrvStatus: rat %d cs %d, ps %d, mode %d, csRejType %d,",
                    pServiceStatus->rat,
                    pServiceStatus->csRegistrationStatus,
                    pServiceStatus->psRegistrationStatus,
                    pServiceStatus->networkRegistrationMode,
                    pServiceStatus->csRejectionType ) );

        LogDebug( ( "csRej %d, psRejType %d, psRej %d, plmn %s%s",
                    pServiceStatus->csRejectionCause,
                    pServiceStatus->psRejectionType,
                    pServiceStatus->psRejectionCause,
                    pServiceStatus->plmnInfo.mcc,
                    pServiceStatus->plmnInfo.mnc ) );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonGetNetworkTime( CellularHandle_t cellularHandle,
                                               CellularTime_t * pNetworkTime )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetNetworkTime = { 0 };

    atReqGetNetworkTime.pAtCmd = "AT+CCLK?";
    atReqGetNetworkTime.atCmdType = CELLULAR_AT_WITH_PREFIX;
    atReqGetNetworkTime.pAtRspPrefix = "+CCLK";
    atReqGetNetworkTime.respCallback = _Cellular_RecvFuncGetNetworkTime;
    atReqGetNetworkTime.pData = pNetworkTime;
    atReqGetNetworkTime.dataLen = ( uint16_t ) sizeof( CellularTime_t );

    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pNetworkTime == NULL )
    {
        LogError( ( "Cellular_CommonGetNetworkTime : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetNetworkTime );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_GetNetworkTime: couldn't retrieve Network Time" ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonGetModemInfo( CellularHandle_t cellularHandle,
                                             CellularModemInfo_t * pModemInfo )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetFirmwareVersion = { 0 };
    CellularAtReq_t atReqGetImei = { 0 };
    CellularAtReq_t atReqGetModelId = { 0 };
    CellularAtReq_t atReqGetManufactureId = { 0 };

    atReqGetFirmwareVersion.pAtCmd = "AT+CGMR";
    atReqGetFirmwareVersion.atCmdType = CELLULAR_AT_WO_PREFIX;
    atReqGetFirmwareVersion.pAtRspPrefix = NULL;
    atReqGetFirmwareVersion.respCallback = _Cellular_RecvFuncGetFirmwareVersion;
    atReqGetFirmwareVersion.pData = pModemInfo->firmwareVersion;
    atReqGetFirmwareVersion.dataLen = CELLULAR_FW_VERSION_MAX_SIZE + 1U;

    atReqGetImei.pAtCmd = "AT+CGSN";
    atReqGetImei.atCmdType = CELLULAR_AT_WO_PREFIX;
    atReqGetImei.pAtRspPrefix = NULL;
    atReqGetImei.respCallback = _Cellular_RecvFuncGetImei;
    atReqGetImei.pData = pModemInfo->imei;
    atReqGetImei.dataLen = CELLULAR_IMEI_MAX_SIZE + 1U;

    atReqGetModelId.pAtCmd = "AT+CGMM";
    atReqGetModelId.atCmdType = CELLULAR_AT_WO_PREFIX;
    atReqGetModelId.pAtRspPrefix = NULL;
    atReqGetModelId.respCallback = _Cellular_RecvFuncGetModelId;
    atReqGetModelId.pData = pModemInfo->modelId;
    atReqGetModelId.dataLen = CELLULAR_MODEL_ID_MAX_SIZE + 1U;

    atReqGetManufactureId.pAtCmd = "AT+CGMI";
    atReqGetManufactureId.atCmdType = CELLULAR_AT_WO_PREFIX;
    atReqGetManufactureId.pAtRspPrefix = NULL;
    atReqGetManufactureId.respCallback = _Cellular_RecvFuncGetManufactureId;
    atReqGetManufactureId.pData = pModemInfo->manufactureId;
    atReqGetManufactureId.dataLen = CELLULAR_MANUFACTURE_ID_MAX_SIZE + 1U;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pModemInfo == NULL )
    {
        LogError( ( "Cellular_CommonGetModemInfo : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        ( void ) memset( pModemInfo, 0, sizeof( CellularModemInfo_t ) );
        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetFirmwareVersion );

        if( pktStatus == CELLULAR_PKT_STATUS_OK )
        {
            pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetImei );
        }

        if( pktStatus == CELLULAR_PKT_STATUS_OK )
        {
            pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetModelId );
        }

        if( pktStatus == CELLULAR_PKT_STATUS_OK )
        {
            pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetManufactureId );
        }

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
        else
        {
            LogDebug( ( "ModemInfo: hwVer:%s, fwVer:%s, serialNum:%s, IMEI:%s, manufactureId:%s, modelId:%s ",
                        pModemInfo->hardwareVersion, pModemInfo->firmwareVersion, pModemInfo->serialNumber, pModemInfo->imei,
                        pModemInfo->manufactureId, pModemInfo->modelId ) );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonGetIPAddress( CellularHandle_t cellularHandle,
                                             uint8_t contextId,
                                             char * pBuffer,
                                             uint32_t bufferLength )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_TYPICAL_MAX_SIZE ] = { '\0' };
    CellularAtReq_t atReqGetIp = { 0 };

    atReqGetIp.pAtCmd = cmdBuf;
    atReqGetIp.atCmdType = CELLULAR_AT_WITH_PREFIX;
    atReqGetIp.pAtRspPrefix = "+CGPADDR";
    atReqGetIp.respCallback = _Cellular_RecvFuncIpAddress;
    atReqGetIp.pData = pBuffer;
    atReqGetIp.dataLen = ( uint16_t ) bufferLength;

    /* Make sure the library is open. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( ( pBuffer == NULL ) || ( bufferLength == 0U ) )
    {
        LogError( ( "_Cellular_GetIPAddress: pBuffer is invalid or bufferLength is wrong" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        cellularStatus = _Cellular_IsValidPdn( contextId );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Form the AT command. */


        /* MISRA Ref 21.6.1 [Use of snprintf] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-216 */
        /* coverity[misra_c_2012_rule_21_6_violation]. */
        ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_TYPICAL_MAX_SIZE, "%s%d", "AT+CGPADDR=", contextId );

        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetIp );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "_Cellular_GetIPAddress: couldn't retrieve the IP, cmdBuf:%s, pktStatus: %d", cmdBuf, pktStatus ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

void _Cellular_DestroyAtDataMutex( CellularContext_t * pContext )
{
    CELLULAR_CONFIG_ASSERT( pContext != NULL );

    PlatformMutex_Destroy( &( pContext->libAtDataMutex ) );
}

/*-----------------------------------------------------------*/

bool _Cellular_CreateAtDataMutex( CellularContext_t * pContext )
{
    bool status = false;

    CELLULAR_CONFIG_ASSERT( pContext != NULL );

    status = PlatformMutex_Create( &( pContext->libAtDataMutex ), false );

    return status;
}

/*-----------------------------------------------------------*/

void _Cellular_LockAtDataMutex( CellularContext_t * pContext )
{
    CELLULAR_CONFIG_ASSERT( pContext != NULL );

    PlatformMutex_Lock( &( pContext->libAtDataMutex ) );
}

/*-----------------------------------------------------------*/

void _Cellular_UnlockAtDataMutex( CellularContext_t * pContext )
{
    CELLULAR_CONFIG_ASSERT( pContext != NULL );

    PlatformMutex_Unlock( &( pContext->libAtDataMutex ) );
}

/*-----------------------------------------------------------*/

/* mode 0: Clean everything.
 * mode 1: Only clean the fields for creg/cgreg=0 URC. */
void _Cellular_InitAtData( CellularContext_t * pContext,
                           uint32_t mode )
{
    cellularAtData_t * pLibAtData = NULL;

    CELLULAR_CONFIG_ASSERT( pContext != NULL );

    pLibAtData = &( pContext->libAtData );

    if( mode == 0u )
    {
        ( void ) memset( pLibAtData, 0, sizeof( cellularAtData_t ) );
        pLibAtData->csRegStatus = REGISTRATION_STATUS_NOT_REGISTERED_SEARCHING;
        pLibAtData->psRegStatus = REGISTRATION_STATUS_NOT_REGISTERED_SEARCHING;
    }

    pLibAtData->lac = 0xFFFFU;
    pLibAtData->cellId = 0xFFFFFFFFU;
    pLibAtData->rat = CELLULAR_RAT_INVALID;
    pLibAtData->rac = 0xFF;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonSetPdnConfig( CellularHandle_t cellularHandle,
                                             uint8_t contextId,
                                             const CellularPdnConfig_t * pPdnConfig )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { '\0' };
    char pPdpTypeStr[ CELLULAR_PDN_CONTEXT_TYPE_MAX_SIZE ] = { '\0' };
    CellularAtReq_t atReqSetPdn = { 0 };

    atReqSetPdn.pAtCmd = cmdBuf;
    atReqSetPdn.atCmdType = CELLULAR_AT_NO_RESULT;
    atReqSetPdn.pAtRspPrefix = NULL;
    atReqSetPdn.respCallback = NULL;
    atReqSetPdn.pData = NULL;
    atReqSetPdn.dataLen = 0;

    if( pPdnConfig == NULL )
    {
        LogError( ( "Cellular_CommonSetPdnConfig: Input parameter is NULL" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        switch( pPdnConfig->pdnContextType )
        {
            case CELLULAR_PDN_CONTEXT_IPV4:
                ( void ) strncpy( pPdpTypeStr, "IP", 3U ); /* 3U is the length of "IP" + '\0'. */
                break;

            case CELLULAR_PDN_CONTEXT_IPV6:
                ( void ) strncpy( pPdpTypeStr, "IPV6", 5U ); /* 5U is the length of "IPV6" + '\0'. */
                break;

            case CELLULAR_PDN_CONTEXT_IPV4V6:
                ( void ) strncpy( pPdpTypeStr, "IPV4V6", 7U ); /* 7U is the length of "IPV4V6" + '\0'. */
                break;

            default:
                LogError( ( "Cellular_CommonSetPdnConfig: Invalid pdn context type %d",
                            CELLULAR_PDN_CONTEXT_IPV4V6 ) );
                cellularStatus = CELLULAR_BAD_PARAMETER;
                break;
        }
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        cellularStatus = _Cellular_IsValidPdn( contextId );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Make sure the library is open. */
        cellularStatus = _Cellular_CheckLibraryStatus( pContext );
    }

    if( cellularStatus == CELLULAR_SUCCESS )
    {
        /* Form the AT command. */

        /* MISRA Ref 21.6.1 [Use of snprintf] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-216 */
        /* coverity[misra_c_2012_rule_21_6_violation]. */
        ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_MAX_SIZE, "%s%d,\"%s\",\"%s\"",
                           "AT+CGDCONT=",
                           contextId,
                           pPdpTypeStr,
                           pPdnConfig->apnName );
        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqSetPdn );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_CommonSetPdnConfig: can't set PDN, cmdBuf:%s, PktRet: %d", cmdBuf, pktStatus ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

static CellularSimCardLockState_t _getSimLockState( char * pToken )
{
    CellularSimCardLockState_t tempState = CELLULAR_SIM_CARD_LOCK_UNKNOWN;

    if( pToken != NULL )
    {
        if( strcmp( pToken, "READY" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_READY;
        }
        else if( strcmp( pToken, "SIM PIN" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_PIN;
        }
        else if( strcmp( pToken, "SIM PUK" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_PUK;
        }
        else if( strcmp( pToken, "SIM PIN2" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_PIN2;
        }
        else if( strcmp( pToken, "SIM PUK2" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_PUK2;
        }
        else if( strcmp( pToken, "PH-NET PIN" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_PH_NET_PIN;
        }
        else if( strcmp( pToken, "PH-NET PUK" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_PH_NET_PUK;
        }
        else if( strcmp( pToken, "PH-NETSUB PIN" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_PH_NETSUB_PIN;
        }
        else if( strcmp( pToken, "PH-NETSUB PUK" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_PH_NETSUB_PUK;
        }
        else if( strcmp( pToken, "PH-SP PIN" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_SP_PIN;
        }
        else if( strcmp( pToken, "PH-SP PUK" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_SP_PUK;
        }
        else if( strcmp( pToken, "PH-CORP PIN" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_CORP_PIN;
        }
        else if( strcmp( pToken, "PH-CORP PUK" ) == 0 )
        {
            tempState = CELLULAR_SIM_CARD_CORP_PUK;
        }
        else
        {
            LogError( ( "Unknown SIM Lock State %s", pToken ) );
        }
    }

    return tempState;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetSimLockStatus( CellularContext_t * pContext,
                                                               const CellularATCommandResponse_t * pAtResp,
                                                               void * pData,
                                                               uint16_t dataLen )
{
    char * pToken = NULL, * pInputStr = NULL;
    CellularSimCardLockState_t * pSimLockState = NULL;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    if( pContext == NULL )
    {
        LogError( ( "_Cellular_RecvFuncGetSimLockStatus: pContext is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "_Cellular_RecvFuncGetSimLockStatus: Response pData is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pData == NULL ) || ( dataLen != sizeof( CellularSimCardLockState_t ) ) )
    {
        LogError( ( "_Cellular_RecvFuncGetSimLockStatus: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pInputStr = pAtResp->pItm->pLine;
        pSimLockState = ( CellularSimCardLockState_t * ) pData;
    }

    if( pktStatus == CELLULAR_PKT_STATUS_OK )
    {
        atCoreStatus = Cellular_ATRemoveAllWhiteSpaces( pInputStr );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemovePrefix( &pInputStr );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pInputStr, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            LogDebug( ( "SIM Lock State: %s", pToken ) );
            *pSimLockState = _getSimLockState( pToken );
        }

        if( atCoreStatus != CELLULAR_AT_SUCCESS )
        {
            pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static bool _checkCrsmMemoryStatus( const char * pToken )
{
    bool memoryStatus = true;

    if( pToken == NULL )
    {
        LogError( ( "Input Parameter NULL" ) );
        memoryStatus = false;
    }

    if( memoryStatus == true )
    {
        /* Checking the value sw2 in AT command response for memory problem during CRSM read.
         * Refer 3GPP Spec TS 51.011 Section 9.4. */
        if( strcmp( pToken, "64" ) == 0 ) /* '40' memory problem. */
        {
            LogError( ( "_checkCrsmMemoryStatus: Error in Processing HPLMN: CRSM Memory Error" ) );
            memoryStatus = false;
        }
    }

    return memoryStatus;
}

/*-----------------------------------------------------------*/

static bool _checkCrsmReadStatus( const char * pToken )
{
    bool readStatus = true;

    if( pToken == NULL )
    {
        LogError( ( "Input Parameter NULL" ) );
        readStatus = false;
    }

    if( readStatus == true )
    {
        /* Checking the parameter sw1 in AT command response for successful CRSM read.
         * Refer 3GPP Spec TS 51.011 Section 9.4. */
        if( ( strcmp( pToken, "144" ) != 0 ) && /* '90' normal ending of the command. */
            ( strcmp( pToken, "145" ) != 0 ) && /* '91' normal ending of the command, with extra information. */
            ( strcmp( pToken, "146" ) != 0 ) )  /* '92' command successful but after using an internal update retry routine 'X' times. */
        {
            LogError( ( "_checkCrsmReadStatus: Error in Processing HPLMN: CRSM Read Error" ) );
            readStatus = false;
        }
    }

    return readStatus;
}

/*-----------------------------------------------------------*/

static bool _parseHplmn( char * pToken,
                         void * pData )
{
    bool parseStatus = true;
    CellularPlmnInfo_t * plmn = ( CellularPlmnInfo_t * ) pData;

    if( pToken == NULL )
    {
        LogError( ( "_parseHplmn: pToken is NULL or pData is NULL" ) );
        parseStatus = false;
    }
    else if( ( strlen( pToken ) < ( CRSM_HPLMN_RAT_LENGTH ) ) || ( strncmp( pToken, "FFFFFF", 6 ) == 0 ) )
    {
        LogError( ( "_parseHplmn: Error in processing HPLMN invalid token %s", pToken ) );
        parseStatus = false;
    }
    else
    {
        /* Returning only the very first HPLMN present in EFHPLMNwACT in SIM.
         * EF-HPLMNwACT can contain a maximum of 10 HPLMN entries in decreasing order of priority.
         * In this implementation, returning the very first HPLMN is the PLMN priority list. */
        /* Refer TS 51.011 Section 10.3.37 for encoding. */
        plmn->mcc[ 0 ] = pToken[ 1 ];
        plmn->mcc[ 1 ] = pToken[ 0 ];
        plmn->mcc[ 2 ] = pToken[ 3 ];
        plmn->mnc[ 0 ] = pToken[ 5 ];
        plmn->mnc[ 1 ] = pToken[ 4 ];

        if( pToken[ 2 ] != 'F' )
        {
            plmn->mnc[ 2 ] = pToken[ 2 ];
            plmn->mnc[ 3 ] = '\0';
        }
        else
        {
            plmn->mnc[ 2 ] = '\0';
        }
    }

    return parseStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetHplmn( CellularContext_t * pContext,
                                                       const CellularATCommandResponse_t * pAtResp,
                                                       void * pData,
                                                       uint16_t dataLen )
{
    bool parseStatus = true;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pCrsmResponse = NULL, * pToken = NULL;

    if( pContext == NULL )
    {
        LogError( ( "GetHplmn: pContext is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetHplmn: Response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pData == NULL ) || ( dataLen != sizeof( CellularPlmnInfo_t ) ) )
    {
        LogError( ( "GetHplmn: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pCrsmResponse = pAtResp->pItm->pLine;
        atCoreStatus = Cellular_ATRemoveAllWhiteSpaces( pCrsmResponse );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            /* Removing the CRSM prefix in AT Response. */
            atCoreStatus = Cellular_ATRemovePrefix( &pCrsmResponse );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            /* Removing All quotes in the AT Response. */
            atCoreStatus = Cellular_ATRemoveAllDoubleQuote( pCrsmResponse );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            /* Getting the next token separated by comma in At Response. */
            atCoreStatus = Cellular_ATGetNextTok( &pCrsmResponse, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            parseStatus = _checkCrsmReadStatus( pToken );

            if( parseStatus == false )
            {
                atCoreStatus = CELLULAR_AT_ERROR;
            }
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pCrsmResponse, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            parseStatus = _checkCrsmMemoryStatus( pToken );

            if( parseStatus == false )
            {
                atCoreStatus = CELLULAR_AT_ERROR;
            }
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pCrsmResponse, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            parseStatus = _parseHplmn( pToken, pData );

            if( parseStatus == false )
            {
                atCoreStatus = CELLULAR_AT_ERROR;
            }
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

#if ( CELLULAR_CONFIG_USE_CCID_COMMAND == 1 )
    static CellularPktStatus_t _Cellular_RecvFuncGetIccid( CellularContext_t * pContext,
                                                           const CellularATCommandResponse_t * pAtResp,
                                                           void * pData,
                                                           uint16_t dataLen )
    {
        CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
        CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
        char * pRespLine = NULL;

        if( pContext == NULL )
        {
            LogError( ( "getIccid: pContext is invalid" ) );
            pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
        }
        else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) ||
                 ( pAtResp->pItm->pLine == NULL ) )
        {
            LogError( ( "getIccid: Response is invalid" ) );
            pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
        }
        else if( ( pData == NULL ) || ( dataLen != ( CELLULAR_ICCID_MAX_SIZE + 1U ) ) )
        {
            LogError( ( "getIccid: pData is invalid or dataLen is wrong" ) );
            pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
        }
        else
        {
            pRespLine = pAtResp->pItm->pLine;
            atCoreStatus = Cellular_ATRemoveAllWhiteSpaces( pRespLine );

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                /* Removing QCCID Prefix in AT Response. */
                atCoreStatus = Cellular_ATRemovePrefix( &pRespLine );
            }

            if( atCoreStatus == CELLULAR_AT_SUCCESS )
            {
                /* Storing the ICCID value in the AT Response. */
                if( strlen( pRespLine ) < ( ( size_t ) CELLULAR_ICCID_MAX_SIZE + 1U ) )
                {
                    ( void ) strncpy( pData, pRespLine, dataLen );
                }
                else
                {
                    atCoreStatus = CELLULAR_AT_BAD_PARAMETER;
                }
            }

            pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
        }

        return pktStatus;
    }
#endif /* if ( CELLULAR_CONFIG_USE_CCID_COMMAND == 1 ) */

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetImsi( CellularContext_t * pContext,
                                                      const CellularATCommandResponse_t * pAtResp,
                                                      void * pData,
                                                      uint16_t dataLen )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    char * pRespLine = NULL;

    if( pContext == NULL )
    {
        LogError( ( "getImsi: pContext is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "getImsi: Response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pData == NULL ) || ( dataLen != ( CELLULAR_IMSI_MAX_SIZE + 1U ) ) )
    {
        LogError( ( "getImsi: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pRespLine = pAtResp->pItm->pLine;

        /* Removing all the Spaces in the AT Response. */
        atCoreStatus = Cellular_ATRemoveAllWhiteSpaces( pRespLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            if( strlen( pRespLine ) < ( CELLULAR_IMSI_MAX_SIZE + 1U ) )
            {
                ( void ) strncpy( ( char * ) pData, pRespLine, dataLen );
            }
            else
            {
                atCoreStatus = CELLULAR_AT_ERROR;
            }
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonGetSimCardLockStatus( CellularHandle_t cellularHandle,
                                                     CellularSimCardStatus_t * pSimCardStatus )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetSimLockStatus;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pSimCardStatus == NULL )
    {
        LogError( ( "Cellular_CommonGetSimCardLockStatus : Bad paremeter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        /* Initialize the sim state and the sim lock state. */
        pSimCardStatus->simCardLockState = CELLULAR_SIM_CARD_LOCK_UNKNOWN;

        atReqGetSimLockStatus.pAtCmd = "AT+CPIN?";
        atReqGetSimLockStatus.atCmdType = CELLULAR_AT_WITH_PREFIX;
        atReqGetSimLockStatus.pAtRspPrefix = "+CPIN";
        atReqGetSimLockStatus.respCallback = _Cellular_RecvFuncGetSimLockStatus;
        atReqGetSimLockStatus.pData = &( pSimCardStatus->simCardLockState );
        atReqGetSimLockStatus.dataLen = ( uint16_t ) sizeof( CellularSimCardLockState_t );

        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetSimLockStatus );

        cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        LogDebug( ( "_Cellular_GetSimStatus, Sim Insert State[%d], Lock State[%d]",
                    pSimCardStatus->simCardState, pSimCardStatus->simCardLockState ) );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonGetSimCardInfo( CellularHandle_t cellularHandle,
                                               CellularSimCardInfo_t * pSimCardInfo )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetImsi = { 0 };
    CellularAtReq_t atReqGetHplmn = { 0 };

    #if ( CELLULAR_CONFIG_USE_CCID_COMMAND == 1 )
    CellularAtReq_t atReqGetIccid = { 0 };

    /* Use non-stanard 3GPP AT command "AT+CCID" for ICCID information. */
    atReqGetIccid.pAtCmd = "AT+CCID";
    atReqGetIccid.atCmdType = CELLULAR_AT_WITH_PREFIX;
    atReqGetIccid.pAtRspPrefix = "+CCID";
    atReqGetIccid.respCallback = _Cellular_RecvFuncGetIccid;
    atReqGetIccid.pData = pSimCardInfo->iccid;
    atReqGetIccid.dataLen = CELLULAR_ICCID_MAX_SIZE + 1U;
    #endif

    atReqGetImsi.pAtCmd = "AT+CIMI";
    atReqGetImsi.atCmdType = CELLULAR_AT_WO_PREFIX;
    atReqGetImsi.pAtRspPrefix = NULL;
    atReqGetImsi.respCallback = _Cellular_RecvFuncGetImsi;
    atReqGetImsi.pData = pSimCardInfo->imsi;
    atReqGetImsi.dataLen = CELLULAR_IMSI_MAX_SIZE + 1U;

    atReqGetHplmn.pAtCmd = "AT+CRSM=176,28514,0,0,0"; /* READ BINARY command. HPLMN Selector with Access Technology( 6F62 ). */
    atReqGetHplmn.atCmdType = CELLULAR_AT_WITH_PREFIX;
    atReqGetHplmn.pAtRspPrefix = "+CRSM";
    atReqGetHplmn.respCallback = _Cellular_RecvFuncGetHplmn;
    atReqGetHplmn.pData = &( pSimCardInfo->plmn );
    atReqGetHplmn.dataLen = ( uint16_t ) sizeof( CellularPlmnInfo_t );

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pSimCardInfo == NULL )
    {
        LogError( ( "Cellular_CommonGetSimCardInfo : Bad paremeter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        ( void ) memset( pSimCardInfo, 0, sizeof( CellularSimCardInfo_t ) );
        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetImsi );

        if( pktStatus == CELLULAR_PKT_STATUS_OK )
        {
            pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetHplmn );
        }

        #if ( CELLULAR_CONFIG_USE_CCID_COMMAND == 1 )
            if( pktStatus == CELLULAR_PKT_STATUS_OK )
            {
                pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetIccid );
            }
        #endif

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
        else
        {
            LogDebug( ( "SimInfo updated: IMSI:%s, Hplmn:%s%s, ICCID:%s",
                        pSimCardInfo->imsi, pSimCardInfo->plmn.mcc, pSimCardInfo->plmn.mnc,
                        pSimCardInfo->iccid ) );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

static uint32_t appendBinaryPattern( char * cmdBuf,
                                     uint32_t cmdLen,
                                     uint32_t value,
                                     bool endOfString )
{
    uint32_t retLen = 0;

    if( value != 0U )
    {
        /* MISRA Ref 21.6.1 [Use of snprintf] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-216 */
        /* coverity[misra_c_2012_rule_21_6_violation]. */
        ( void ) snprintf( cmdBuf, cmdLen, "\"" PRINTF_BINARY_PATTERN_INT8 "\"%c",
                           PRINTF_BYTE_TO_BINARY_INT8( value ), endOfString ? '\0' : ',' );
    }
    else
    {
        /* MISRA Ref 21.6.1 [Use of snprintf] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-216 */
        /* coverity[misra_c_2012_rule_21_6_violation]. */
        ( void ) snprintf( cmdBuf, cmdLen, "%c", endOfString ? '\0' : ',' );
    }

    retLen = ( uint32_t ) strlen( cmdBuf );

    return retLen;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonSetPsmSettings( CellularHandle_t cellularHandle,
                                               const CellularPsmSettings_t * pPsmSettings )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char cmdBuf[ CELLULAR_AT_CMD_MAX_SIZE ] = { '\0' };
    uint32_t cmdBufLen = 0;
    CellularAtReq_t atReqSetPsm = { 0 };

    atReqSetPsm.pAtCmd = cmdBuf;
    atReqSetPsm.atCmdType = CELLULAR_AT_NO_RESULT;
    atReqSetPsm.pAtRspPrefix = NULL;
    atReqSetPsm.respCallback = NULL;
    atReqSetPsm.pData = NULL;
    atReqSetPsm.dataLen = 0;

    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pPsmSettings == NULL )
    {
        LogError( ( "Cellular_CommonSetPsmSettings : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        /* Form the AT command. */

        /* MISRA Ref 21.6.1 [Use of snprintf] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-216 */
        /* coverity[misra_c_2012_rule_21_6_violation]. */
        ( void ) snprintf( cmdBuf, CELLULAR_AT_CMD_MAX_SIZE, "AT+CPSMS=%d,", pPsmSettings->mode );
        cmdBufLen = ( uint32_t ) strlen( cmdBuf );
        cmdBufLen = cmdBufLen + appendBinaryPattern( &( cmdBuf[ cmdBufLen ] ), ( CELLULAR_AT_CMD_MAX_SIZE - cmdBufLen ),
                                                     pPsmSettings->periodicRauValue, false );
        cmdBufLen = cmdBufLen + appendBinaryPattern( &( cmdBuf[ cmdBufLen ] ), ( CELLULAR_AT_CMD_MAX_SIZE - cmdBufLen ),
                                                     pPsmSettings->gprsReadyTimer, false );
        cmdBufLen = cmdBufLen + appendBinaryPattern( &( cmdBuf[ cmdBufLen ] ), ( CELLULAR_AT_CMD_MAX_SIZE - cmdBufLen ),
                                                     pPsmSettings->periodicTauValue, false );
        ( void ) appendBinaryPattern( &( cmdBuf[ cmdBufLen ] ), ( CELLULAR_AT_CMD_MAX_SIZE - cmdBufLen ),
                                      pPsmSettings->activeTimeValue, true );

        LogDebug( ( "PSM setting: %s ", cmdBuf ) );

        /* Query the PSMsettings from the network. */
        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqSetPsm );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_SetPsmSettings: couldn't set PSM settings" ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t parseCpsmsMode( char * pToken,
                                         CellularPsmSettings_t * pPsmSettings )
{
    int32_t tempValue = 0;
    CellularATError_t atCoreStatus = Cellular_ATStrtoi( pToken, 2, &tempValue );

    if( atCoreStatus == CELLULAR_AT_SUCCESS )
    {
        if( ( tempValue >= 0 ) && ( tempValue <= ( int32_t ) UINT8_MAX ) )
        {
            pPsmSettings->mode = ( uint8_t ) tempValue;
        }
        else
        {
            LogError( ( "Error in processing mode. Token %s", pToken ) );
            atCoreStatus = CELLULAR_AT_ERROR;
        }
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

static CellularATError_t parseGetPsmToken( char * pToken,
                                           uint8_t tokenIndex,
                                           CellularPsmSettings_t * pPsmSettings )
{
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;

    switch( tokenIndex )
    {
        case CPSMS_POS_MODE:
            atCoreStatus = parseCpsmsMode( pToken, pPsmSettings );
            break;

        case CPSMS_POS_RAU:
            atCoreStatus = parseT3412TimerValue( pToken, &( pPsmSettings->periodicRauValue ) );
            break;

        case CPSMS_POS_RDY_TIMER:
            atCoreStatus = parseT3324TimerValue( pToken, &( pPsmSettings->gprsReadyTimer ) );
            break;

        case CPSMS_POS_TAU:
            atCoreStatus = parseT3412TimerValue( pToken, &( pPsmSettings->periodicTauValue ) );
            break;

        case CPSMS_POS_ACTIVE_TIME:
            atCoreStatus = parseT3324TimerValue( pToken, &( pPsmSettings->activeTimeValue ) );
            break;

        default:
            LogError( ( "Unknown Parameter Position in AT+QPSMS Response" ) );
            atCoreStatus = CELLULAR_AT_ERROR;
            break;
    }

    return atCoreStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_RecvFuncGetPsmSettings( CellularContext_t * pContext,
                                                             const CellularATCommandResponse_t * pAtResp,
                                                             void * pData,
                                                             uint16_t dataLen )
{
    char * pInputLine = NULL, * pToken = NULL;
    uint8_t tokenIndex = 0;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularATError_t atCoreStatus = CELLULAR_AT_SUCCESS;
    CellularPsmSettings_t * pPsmSettings = NULL;

    if( pContext == NULL )
    {
        LogError( ( "GetPsmSettings: pContext is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( ( pAtResp == NULL ) || ( pAtResp->pItm == NULL ) || ( pAtResp->pItm->pLine == NULL ) )
    {
        LogError( ( "GetPsmSettings: Response is invalid" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else if( ( pData == NULL ) || ( dataLen != sizeof( CellularPsmSettings_t ) ) )
    {
        LogError( ( "GetPsmSettings: pData is invalid or dataLen is wrong" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        pInputLine = pAtResp->pItm->pLine;
        pPsmSettings = ( CellularPsmSettings_t * ) pData;
        atCoreStatus = Cellular_ATRemovePrefix( &pInputLine );

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATRemoveAllDoubleQuote( pInputLine );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            atCoreStatus = Cellular_ATGetNextTok( &pInputLine, &pToken );
        }

        if( atCoreStatus == CELLULAR_AT_SUCCESS )
        {
            tokenIndex = 0;

            while( pToken != NULL )
            {
                atCoreStatus = parseGetPsmToken( pToken, tokenIndex, pPsmSettings );

                if( atCoreStatus != CELLULAR_AT_SUCCESS )
                {
                    LogInfo( ( "parseGetPsmToken %s index %d failed", pToken, tokenIndex ) );
                }

                tokenIndex++;

                if( Cellular_ATGetNextTok( &pInputLine, &pToken ) != CELLULAR_AT_SUCCESS )
                {
                    break;
                }
            }
        }

        pktStatus = _Cellular_TranslateAtCoreStatus( atCoreStatus );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonGetPsmSettings( CellularHandle_t cellularHandle,
                                               CellularPsmSettings_t * pPsmSettings )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetPsm = { 0 };

    atReqGetPsm.pAtCmd = "AT+CPSMS?";
    atReqGetPsm.atCmdType = CELLULAR_AT_WITH_PREFIX;
    atReqGetPsm.pAtRspPrefix = "+CPSMS";
    atReqGetPsm.respCallback = _Cellular_RecvFuncGetPsmSettings;
    atReqGetPsm.pData = pPsmSettings;
    atReqGetPsm.dataLen = ( uint16_t ) sizeof( CellularPsmSettings_t );

    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pPsmSettings == NULL )
    {
        LogError( ( "Cellular_CommonGetPsmSettings : Bad parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        /* Initialize the data. */
        ( void ) memset( pPsmSettings, 0, sizeof( CellularPsmSettings_t ) );
        pPsmSettings->mode = 0xFF;

        /* Query the PSMsettings from the network. */
        pktStatus = _Cellular_AtcmdRequestWithCallback( pContext, atReqGetPsm );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Cellular_GetPsmSettings: couldn't retrieve PSM settings" ) );
            cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/
