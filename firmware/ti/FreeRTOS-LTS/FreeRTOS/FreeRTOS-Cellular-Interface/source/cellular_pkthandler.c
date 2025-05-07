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
 * @brief FreeRTOS Cellular Library common packet handler functions to dispatch packet.
 */

#ifndef CELLULAR_DO_NOT_USE_CUSTOM_CONFIG
    /* Include custom config file before other headers. */
    #include "cellular_config.h"
#endif
#include "cellular_config_defaults.h"

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

#include "cellular_platform.h"
#include "cellular_internal.h"
#include "cellular_pkthandler_internal.h"
#include "cellular_pktio_internal.h"
#include "cellular_types.h"
#include "cellular_common_internal.h"

/*-----------------------------------------------------------*/

#ifndef MIN
    #define MIN( a, b )    ( ( ( a ) < ( b ) ) ? ( a ) : ( b ) )
#endif

/* Windows simulator implementation. */
#if defined( _WIN32 ) || defined( _WIN64 )
    #define strtok_r    strtok_s
#endif

/*-----------------------------------------------------------*/

static CellularPktStatus_t _convertAndQueueRespPacket( CellularContext_t * pContext,
                                                       const void * pBuf );
static CellularPktStatus_t _processUrcPacket( CellularContext_t * pContext,
                                              const char * pBuf );
static CellularPktStatus_t _Cellular_AtcmdRequestTimeoutWithCallbackRaw( CellularContext_t * pContext,
                                                                         CellularAtReq_t atReq,
                                                                         uint32_t timeoutMS );
static CellularPktStatus_t _Cellular_DataSendWithTimeoutDelayRaw( CellularContext_t * pContext,
                                                                  CellularAtDataReq_t dataReq,
                                                                  uint32_t timeoutMs );
static void _Cellular_PktHandlerAcquirePktRequestMutex( CellularContext_t * pContext );
static void _Cellular_PktHandlerReleasePktRequestMutex( CellularContext_t * pContext );
static int32_t _searchCompareFunc( const void * pInputToken,
                                   const void * pBase );
static int32_t _sortCompareFunc( const void * pElem1Ptr,
                                 const void * pElem2Ptr );
static CellularPktStatus_t _atParseGetHandler( CellularContext_t * pContext,
                                               const char * pTokenPtr,
                                               char * pSavePtr );
static CellularPktStatus_t _handleUndefinedMessage( CellularContext_t * pContext,
                                                    const char * pLine );

/*-----------------------------------------------------------*/

static CellularPktStatus_t _convertAndQueueRespPacket( CellularContext_t * pContext,
                                                       const void * pBuf )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    const CellularATCommandResponse_t * pAtResp = NULL;

    /* pBuf is checked in _Cellular_HandlePacket. */
    pAtResp = ( const CellularATCommandResponse_t * ) pBuf;

    if( pAtResp->status == false )
    {
        /* The modem returns error code to indicate that the command failed. */
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }

    if( ( pContext->pktRespCB != NULL ) && ( pktStatus == CELLULAR_PKT_STATUS_OK ) )
    {
        pktStatus = pContext->pktRespCB( pContext,
                                         ( const CellularATCommandResponse_t * ) pBuf,
                                         pContext->pPktUsrData,
                                         pContext->PktUsrDataLen );
    }

    /* Notify calling thread, Not blocking immediately comes back if the queue is full. */
    if( PlatformQueue_Send( pContext->pktRespQueue, ( void * ) &pktStatus, ( PlatformTickType_t ) 0 ) != platformPASS )
    {
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
        LogError( ( "_convertAndQueueRespPacket: Got a response when the Resp Q is full!!" ) );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief copy the URC log in the buffer to a heap memory and process it.
 */
static CellularPktStatus_t _processUrcPacket( CellularContext_t * pContext,
                                              const char * pBuf )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    bool inputWithPrefix = false;
    char * pInputLine = NULL;
    char * pSavePtr = NULL, * pTokenPtr = NULL;
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;

    /* pBuf is checked in _Cellular_HandlePacket. */
    atStatus = Cellular_ATStrDup( &pInputLine, pBuf );

    if( atStatus != CELLULAR_AT_SUCCESS )
    {
        /* Fail to allocate memory. */
        LogError( ( "Failed to allocate memory for URC [%s]", pBuf ) );
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else
    {
        LogDebug( ( "Next URC token to parse [%s]", pInputLine ) );

        /* Check if prefix exist in the input string. The pInputLine is checked in Cellular_ATStrDup. */
        ( void ) Cellular_ATIsPrefixPresent( pInputLine, &inputWithPrefix );

        if( inputWithPrefix == true )
        {
            /* Cellular_ATIsPrefixPresent check the prefix string is valid and start with
             * leading char. ":" is also checked in Cellular_ATIsPrefixPresent. Remove
             * the leading char and split the string into the following substrings :
             * pInputLine = "+" pTokenPtr + ":" + pSavePtr. */
            pSavePtr = &( pInputLine[ 1 ] );
            pTokenPtr = strtok_r( pSavePtr, ":", &pSavePtr );

            if( pTokenPtr == NULL )
            {
                LogError( ( "_Cellular_AtParse : input string error, start with \"+\" but no token %s", pInputLine ) );
                pktStatus = CELLULAR_PKT_STATUS_BAD_REQUEST;
            }
            else
            {
                pktStatus = _atParseGetHandler( pContext, pTokenPtr, pSavePtr );
            }
        }
        else
        {
            /* This is the input without prefix case. Nothing need to be done for this case.
             * There are some special cases. For example, "+URC" the string without  ":" should
             * be regarded as URC without prefix. */
            pktStatus = _atParseGetHandler( pContext, pInputLine, pInputLine );
        }

        if( pktStatus == CELLULAR_PKT_STATUS_PREFIX_MISMATCH )
        {
            /* No URC callback function available, check for generic callback. */
            LogDebug( ( "No URC Callback func avail %s, now trying generic URC Callback", pTokenPtr ) );

            if( inputWithPrefix == true )
            {
                /* inputWithPrefix is true means the string starts with '+'.
                 * Restore string to "+pTokenPtr:pSavePtr" for callback function. */
                pSavePtr[ -1 ] = ':';
            }

            _Cellular_GenericCallback( pContext, pInputLine );
            pktStatus = CELLULAR_PKT_STATUS_OK;
        }

        /* Free the allocated pInputLine. */
        Platform_Free( pInputLine );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/
static CellularPktStatus_t _Cellular_AtcmdRequestTimeoutWithCallbackRaw( CellularContext_t * pContext,
                                                                         CellularAtReq_t atReq,
                                                                         uint32_t timeoutMS )
{
    CellularPktStatus_t respCode = CELLULAR_PKT_STATUS_OK;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    PlatformBaseType_t qRet = platformFALSE;

    if( atReq.pAtCmd == NULL )
    {
        LogError( ( "PKT_STATUS_BAD_REQUEST, null AT param" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_REQUEST;
    }
    else
    {
        LogDebug( ( ">>>>>Start sending [%s]<<<<<", atReq.pAtCmd ) );

        /* Fill in request info structure. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->pktRespCB = atReq.respCallback;
        pContext->pPktUsrData = atReq.pData;
        pContext->PktUsrDataLen = ( uint16_t ) atReq.dataLen;
        pContext->pCurrentCmd = atReq.pAtCmd;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        pktStatus = _Cellular_PktioSendAtCmd( pContext, atReq.pAtCmd, atReq.atCmdType, atReq.pAtRspPrefix );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "Can't send req packet" ) );
        }
        else
        {
            /* Wait for a response. */
            qRet = PlatformQueue_Receive( pContext->pktRespQueue, &respCode, pdMS_TO_TICKS( timeoutMS ) );

            if( qRet == platformTRUE )
            {
                pktStatus = ( CellularPktStatus_t ) respCode;

                if( pktStatus != CELLULAR_PKT_STATUS_OK )
                {
                    LogWarn( ( "Modem returns error in sending AT command %s, pktStatus %d.",
                               atReq.pAtCmd, pktStatus ) );
                } /* Ignore errors from callbacks as they will be handled elsewhere. */
            }
            else
            {
                pktStatus = CELLULAR_PKT_STATUS_TIMED_OUT;
                LogError( ( "pkt_recv status=%d, AT cmd %s timed out", pktStatus, atReq.pAtCmd ) );
            }
        }

        /* No command is waiting response. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->PktioAtCmdType = CELLULAR_AT_NO_COMMAND;
        pContext->pktRespCB = NULL;
        pContext->pCurrentCmd = NULL;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );
        LogDebug( ( "<<<<<Exit sending [%s] status[%d]<<<<<", atReq.pAtCmd, pktStatus ) );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_DataSendWithTimeoutDelayRaw( CellularContext_t * pContext,
                                                                  CellularAtDataReq_t dataReq,
                                                                  uint32_t timeoutMs )
{
    CellularPktStatus_t respCode = CELLULAR_PKT_STATUS_OK;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    PlatformBaseType_t qStatus = platformFALSE;
    uint32_t sendEndPatternLen = 0U;

    if( ( dataReq.pData == NULL ) || ( dataReq.pSentDataLength == NULL ) )
    {
        LogError( ( "_Cellular_DataSendWithTimeoutDelayRaw, null input" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_REQUEST;
    }
    else
    {
        LogDebug( ( ">>>>>Start sending Data <<<<<" ) );

        /* Send the packet. Data send is regarded as CELLULAR_AT_NO_RESULT. Only
         * success or error token is expected in the result. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->PktioAtCmdType = CELLULAR_AT_NO_RESULT;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        *dataReq.pSentDataLength = _Cellular_PktioSendData( pContext, dataReq.pData, dataReq.dataLen );

        if( *dataReq.pSentDataLength != dataReq.dataLen )
        {
            LogError( ( "_Cellular_DataSendWithTimeoutDelayRaw, incomplete data transfer" ) );
            pktStatus = CELLULAR_PKT_STATUS_SEND_ERROR;
        }
    }

    /* End pattern for specific modem. */
    if( ( pktStatus == CELLULAR_PKT_STATUS_OK ) && ( dataReq.pEndPattern != NULL ) )
    {
        sendEndPatternLen = _Cellular_PktioSendData( pContext, dataReq.pEndPattern, dataReq.endPatternLen );

        if( sendEndPatternLen != dataReq.endPatternLen )
        {
            LogError( ( "_Cellular_DataSendWithTimeoutDelayRaw, incomplete endpattern transfer" ) );
            pktStatus = CELLULAR_PKT_STATUS_SEND_ERROR;
        }
    }

    /* Wait for a response. */
    if( pktStatus == CELLULAR_PKT_STATUS_OK )
    {
        qStatus = PlatformQueue_Receive( pContext->pktRespQueue, &respCode, pdMS_TO_TICKS( timeoutMs ) );

        if( qStatus == platformTRUE )
        {
            pktStatus = ( CellularPktStatus_t ) respCode;

            if( pktStatus == CELLULAR_PKT_STATUS_OK )
            {
                LogDebug( ( "Data sent successfully!" ) );
            }
            else
            {
                LogWarn( ( "Modem returns error in sending data, pktStatus %d.", pktStatus ) );
            }
        }
        else
        {
            pktStatus = CELLULAR_PKT_STATUS_TIMED_OUT;
            LogError( ( "pkt_recv status=%d, data sending timed out", pktStatus ) );
        }

        /* Set AT command type to CELLULAR_AT_NO_COMMAND for timeout case here. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->PktioAtCmdType = CELLULAR_AT_NO_COMMAND;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        LogDebug( ( "<<<<<Exit sending data ret[%d]>>>>>", pktStatus ) );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

static void _Cellular_PktHandlerAcquirePktRequestMutex( CellularContext_t * pContext )
{
    PlatformMutex_Lock( &( pContext->pktRequestMutex ) );
}

/*-----------------------------------------------------------*/

static void _Cellular_PktHandlerReleasePktRequestMutex( CellularContext_t * pContext )
{
    PlatformMutex_Unlock( &( pContext->pktRequestMutex ) );
}

/*-----------------------------------------------------------*/

static int32_t _searchCompareFunc( const void * pInputToken,
                                   const void * pBase )
{
    int32_t compareValue = 0;
    const char * pToken = ( const char * ) pInputToken;
    const CellularAtParseTokenMap_t * pBasePtr = ( const CellularAtParseTokenMap_t * ) pBase;
    uint32_t tokenLen = ( uint32_t ) strlen( pInputToken );
    uint32_t strLen = ( uint32_t ) strlen( pBasePtr->pStrValue );

    compareValue = strncmp( pToken,
                            pBasePtr->pStrValue,
                            MIN( tokenLen, strLen ) );

    /* To avoid undefined behavior, the table should not contain duplicated item and
     * compareValue is 0 only if the string is exactly the same. */
    if( ( compareValue == 0 ) && ( tokenLen != strLen ) )
    {
        if( tokenLen > strLen )
        {
            compareValue = 1;
        }
        else
        {
            compareValue = -1;
        }
    }

    return compareValue;
}

/*-----------------------------------------------------------*/

static int32_t _sortCompareFunc( const void * pElem1Ptr,
                                 const void * pElem2Ptr )
{
    int32_t compareValue = 0;
    const CellularAtParseTokenMap_t * pElement1Ptr = ( const CellularAtParseTokenMap_t * ) pElem1Ptr;
    const CellularAtParseTokenMap_t * pElement2Ptr = ( const CellularAtParseTokenMap_t * ) pElem2Ptr;
    uint32_t element1PtrLen = ( uint32_t ) strlen( pElement1Ptr->pStrValue );
    uint32_t element2PtrLen = ( uint32_t ) strlen( pElement2Ptr->pStrValue );

    compareValue = strncmp( pElement1Ptr->pStrValue,
                            pElement2Ptr->pStrValue,
                            MIN( element1PtrLen, element2PtrLen ) );

    /* To avoid undefined behavior, the table should not contain duplicated item and
     * compareValue is 0 only if the string is exactly the same. */
    if( ( compareValue == 0 ) && ( element1PtrLen != element2PtrLen ) )
    {
        if( element1PtrLen > element2PtrLen )
        {
            compareValue = 1;
        }
        else
        {
            compareValue = -1;
        }
    }

    return compareValue;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _atParseGetHandler( CellularContext_t * pContext,
                                               const char * pTokenPtr,
                                               char * pSavePtr )
{
    /* Now get the handler function based on the token. */
    const CellularAtParseTokenMap_t * pElementPtr = NULL;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    const CellularAtParseTokenMap_t * pTokenMap = pContext->tokenTable.pCellularUrcHandlerTable;
    uint32_t tokenMapSize = pContext->tokenTable.cellularPrefixToParserMapSize;

    /* MISRA Ref 21.9.1 [Use of bsearch] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-219 */
    /* coverity[misra_c_2012_rule_21_9_violation] */
    pElementPtr = ( CellularAtParseTokenMap_t * ) bsearch( ( const void * ) pTokenPtr,
                                                           ( const void * ) pTokenMap,
                                                           tokenMapSize,
                                                           sizeof( CellularAtParseTokenMap_t ),
                                                           _searchCompareFunc );

    if( pElementPtr != NULL )
    {
        if( pElementPtr->parserFunc != NULL )
        {
            pElementPtr->parserFunc( pContext, pSavePtr );
        }
        else
        {
            LogWarn( ( "No URC Callback func avail %s", pTokenPtr ) );
            pktStatus = CELLULAR_PKT_STATUS_FAILURE;
        }
    }
    else
    {
        /* No URC callback function available. */
        pktStatus = CELLULAR_PKT_STATUS_PREFIX_MISMATCH;
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

/*
 * @brief Handle AT_UNDEFINED message type.
 */
static CellularPktStatus_t _handleUndefinedMessage( CellularContext_t * pContext,
                                                    const char * pLine )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    LogInfo( ( "AT_UNDEFINED message received %s\r\n", pLine ) );

    /* undefined message received. Try to handle it with cellular module
     * specific handler. */
    if( pContext->undefinedRespCallback == NULL )
    {
        LogError( ( "No undefined callback for AT_UNDEFINED type message %s received.",
                    pLine ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_DATA;
    }
    else
    {
        pktStatus = pContext->undefinedRespCallback( pContext->pUndefinedRespCBContext, pLine );

        if( pktStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "undefinedRespCallback returns error %d for AT_UNDEFINED type message %s received.",
                        pktStatus, pLine ) );
            pktStatus = CELLULAR_PKT_STATUS_INVALID_DATA;
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

void _Cellular_PktHandlerCleanup( CellularContext_t * pContext )
{
    if( ( pContext != NULL ) && ( pContext->pktRespQueue != NULL ) )
    {
        /* Wait for response to finish. */
        _Cellular_PktHandlerAcquirePktRequestMutex( pContext );
        /* This is platform dependent api. */

        ( void ) PlatformQueue_Delete( pContext->pktRespQueue );
        pContext->pktRespQueue = NULL;
        _Cellular_PktHandlerReleasePktRequestMutex( pContext );
    }
}

/*-----------------------------------------------------------*/

CellularPktStatus_t _Cellular_HandlePacket( CellularContext_t * pContext,
                                            _atRespType_t atRespType,
                                            const void * pBuf )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    if( pContext == NULL )
    {
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( pBuf == NULL )
    {
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        switch( atRespType )
        {
            case AT_SOLICITED:
                pktStatus = _convertAndQueueRespPacket( pContext, pBuf );
                break;

            case AT_UNSOLICITED:
                pktStatus = _processUrcPacket( pContext, pBuf );
                break;

            case AT_UNDEFINED:
                pktStatus = _handleUndefinedMessage( pContext, pBuf );
                break;

            default:
                pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
                LogError( ( "_Cellular_HandlePacket Callback type (%d) error", atRespType ) );
                break;
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

CellularPktStatus_t _Cellular_PktHandler_AtcmdRequestWithCallback( CellularContext_t * pContext,
                                                                   CellularAtReq_t atReq,
                                                                   uint32_t timeoutMS )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    if( pContext == NULL )
    {
        LogError( ( "_Cellular_TimeoutAtcmdRequestWithCallback : Invalid cellular context" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else
    {
        _Cellular_PktHandlerAcquirePktRequestMutex( pContext );
        pktStatus = _Cellular_AtcmdRequestTimeoutWithCallbackRaw( pContext, atReq, timeoutMS );
        _Cellular_PktHandlerReleasePktRequestMutex( pContext );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

CellularPktStatus_t _Cellular_AtcmdRequestSuccessToken( CellularContext_t * pContext,
                                                        CellularAtReq_t atReq,
                                                        uint32_t atTimeoutMS,
                                                        const char ** pCellularSrcTokenSuccessTable,
                                                        uint32_t cellularSrcTokenSuccessTableSize )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    if( pContext == NULL )
    {
        LogError( ( "_Cellular_AtcmdRequestSuccessToken : Invalid cellular context" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( pCellularSrcTokenSuccessTable == NULL )
    {
        LogError( ( "_Cellular_AtcmdRequestSuccessToken : pCellularSrcTokenSuccessTable is NULL" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        _Cellular_PktHandlerAcquirePktRequestMutex( pContext );

        /* Set the extra Token table for this AT command. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->tokenTable.pCellularSrcExtraTokenSuccessTable = pCellularSrcTokenSuccessTable;
        pContext->tokenTable.cellularSrcExtraTokenSuccessTableSize = cellularSrcTokenSuccessTableSize;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        pktStatus = _Cellular_AtcmdRequestTimeoutWithCallbackRaw( pContext, atReq, atTimeoutMS );

        /* Clear the extra Token table for this AT command. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->tokenTable.cellularSrcExtraTokenSuccessTableSize = 0;
        pContext->tokenTable.pCellularSrcExtraTokenSuccessTable = NULL;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        _Cellular_PktHandlerReleasePktRequestMutex( pContext );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

CellularPktStatus_t _Cellular_TimeoutAtcmdDataRecvRequestWithCallback( CellularContext_t * pContext,
                                                                       CellularAtReq_t atReq,
                                                                       uint32_t timeoutMS,
                                                                       CellularATCommandDataPrefixCallback_t pktDataPrefixCallback,
                                                                       void * pCallbackContext )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    if( pContext == NULL )
    {
        LogError( ( "_Cellular_TimeoutAtcmdDataRecvRequestWithCallback : Invalid cellular context" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else
    {
        _Cellular_PktHandlerAcquirePktRequestMutex( pContext );

        /* Set the data receive prefix. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->pktDataPrefixCB = pktDataPrefixCallback;
        pContext->pDataPrefixCBContext = pCallbackContext;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        pktStatus = _Cellular_AtcmdRequestTimeoutWithCallbackRaw( pContext, atReq, timeoutMS );

        /* Clear the data receive prefix. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->pktDataPrefixCB = NULL;
        pContext->pDataPrefixCBContext = NULL;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        _Cellular_PktHandlerReleasePktRequestMutex( pContext );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

CellularPktStatus_t _Cellular_AtcmdDataSend( CellularContext_t * pContext,
                                             CellularAtReq_t atReq,
                                             CellularAtDataReq_t dataReq,
                                             CellularATCommandDataSendPrefixCallback_t pktDataSendPrefixCallback,
                                             void * pCallbackContext,
                                             uint32_t atTimeoutMS,
                                             uint32_t dataTimeoutMS,
                                             uint32_t interDelayMS )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    if( pContext == NULL )
    {
        LogError( ( "_Cellular_TimeoutAtcmdDataSendRequestWithCallback : Invalid cellular context" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else
    {
        _Cellular_PktHandlerAcquirePktRequestMutex( pContext );

        /* Set the data send prefix callback. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->pktDataSendPrefixCB = pktDataSendPrefixCallback;
        pContext->pDataSendPrefixCBContext = pCallbackContext;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        pktStatus = _Cellular_AtcmdRequestTimeoutWithCallbackRaw( pContext, atReq, atTimeoutMS );

        /* Clear the data send prefix callback. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->pDataSendPrefixCBContext = NULL;
        pContext->pktDataSendPrefixCB = NULL;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        if( pktStatus == CELLULAR_PKT_STATUS_OK )
        {
            if( interDelayMS > 0U )
            {
                /* Cellular modem may require a minimum delay before sending data. */
                Platform_Delay( interDelayMS );
            }

            pktStatus = _Cellular_DataSendWithTimeoutDelayRaw( pContext, dataReq, dataTimeoutMS );
        }

        _Cellular_PktHandlerReleasePktRequestMutex( pContext );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

CellularPktStatus_t _Cellular_TimeoutAtcmdDataSendRequestWithCallback( CellularContext_t * pContext,
                                                                       CellularAtReq_t atReq,
                                                                       CellularAtDataReq_t dataReq,
                                                                       uint32_t atTimeoutMS,
                                                                       uint32_t dataTimeoutMS )
{
    return _Cellular_AtcmdDataSend( pContext, atReq, dataReq, NULL, NULL, atTimeoutMS, dataTimeoutMS, 0U );
}

/*-----------------------------------------------------------*/

CellularPktStatus_t _Cellular_TimeoutAtcmdDataSendSuccessToken( CellularContext_t * pContext,
                                                                CellularAtReq_t atReq,
                                                                CellularAtDataReq_t dataReq,
                                                                uint32_t atTimeoutMS,
                                                                uint32_t dataTimeoutMS,
                                                                const char ** pCellularSrcTokenSuccessTable,
                                                                uint32_t cellularSrcTokenSuccessTableSize )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    if( pContext == NULL )
    {
        LogError( ( "_Cellular_TimeoutAtcmdDataSendSuccessToken : Invalid cellular context" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else
    {
        _Cellular_PktHandlerAcquirePktRequestMutex( pContext );

        /* Set the extra token table. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->tokenTable.pCellularSrcExtraTokenSuccessTable = pCellularSrcTokenSuccessTable;
        pContext->tokenTable.cellularSrcExtraTokenSuccessTableSize = cellularSrcTokenSuccessTableSize;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        pktStatus = _Cellular_AtcmdRequestTimeoutWithCallbackRaw( pContext, atReq, atTimeoutMS );

        /* Clear the extra token table. */
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->tokenTable.cellularSrcExtraTokenSuccessTableSize = 0;
        pContext->tokenTable.pCellularSrcExtraTokenSuccessTable = NULL;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        if( pktStatus == CELLULAR_PKT_STATUS_OK )
        {
            pktStatus = _Cellular_DataSendWithTimeoutDelayRaw( pContext, dataReq, dataTimeoutMS );
        }

        _Cellular_PktHandlerReleasePktRequestMutex( pContext );
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

CellularPktStatus_t _Cellular_PktHandlerInit( CellularContext_t * pContext )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    if( pContext != NULL )
    {
        /* Create the response queue which is used to post responses to the sender. */
        pContext->pktRespQueue = PlatformQueue_Create( 1, ( uint32_t ) sizeof( CellularPktStatus_t ) );

        if( pContext->pktRespQueue == NULL )
        {
            pktStatus = CELLULAR_PKT_STATUS_FAILURE;
        }
    }
    else
    {
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

CellularPktStatus_t _Cellular_AtParseInit( const CellularContext_t * pContext )
{
    uint32_t i = 0;
    bool finit = true;
    const CellularAtParseTokenMap_t * pTokenMap = NULL;
    uint32_t tokenMapSize = 0;
    int32_t result = 0;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    if( ( pContext != NULL ) && ( pContext->tokenTable.pCellularUrcHandlerTable != NULL ) &&
        ( pContext->tokenTable.cellularPrefixToParserMapSize > 0U ) )
    {
        pTokenMap = pContext->tokenTable.pCellularUrcHandlerTable;
        tokenMapSize = pContext->tokenTable.cellularPrefixToParserMapSize;

        /* Check order of the sorted Map. */
        for( i = 0; i < ( tokenMapSize - 1U ); i++ )
        {
            result = _sortCompareFunc( &( pTokenMap[ i ] ), &( pTokenMap[ i + 1U ] ) );

            if( result >= 0 )
            {
                LogError( ( "AtParseFail for %u: %d %s %s", ( unsigned int ) i, ( int ) result,
                            pTokenMap[ i ].pStrValue, pTokenMap[ i + 1U ].pStrValue ) );
                finit = false;
            }
        }

        if( finit != true )
        {
            pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
            LogError( ( "AtParseFail URC token table is not sorted" ) );
        }

        for( i = 0; i < tokenMapSize; i++ )
        {
            LogDebug( ( "Callbacks setup for %u : %s", ( unsigned int ) i, pTokenMap[ i ].pStrValue ) );
        }
    }
    else
    {
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

bool _Cellular_CreatePktRequestMutex( CellularContext_t * pContext )
{
    bool status = false;

    if( pContext != NULL )
    {
        status = PlatformMutex_Create( &( pContext->pktRequestMutex ), false );
    }

    return status;
}

/*-----------------------------------------------------------*/

bool _Cellular_CreatePktResponseMutex( CellularContext_t * pContext )
{
    bool status = false;

    if( pContext != NULL )
    {
        status = PlatformMutex_Create( &( pContext->PktRespMutex ), false );
    }

    return status;
}

/*-----------------------------------------------------------*/

void _Cellular_DestroyPktRequestMutex( CellularContext_t * pContext )
{
    if( pContext != NULL )
    {
        PlatformMutex_Destroy( &( pContext->pktRequestMutex ) );
    }
}

/*-----------------------------------------------------------*/

void _Cellular_DestroyPktResponseMutex( CellularContext_t * pContext )
{
    if( pContext != NULL )
    {
        PlatformMutex_Destroy( &( pContext->PktRespMutex ) );
    }
}

/*-----------------------------------------------------------*/
