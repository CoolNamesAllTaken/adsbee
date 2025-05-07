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
 * @brief FreeRTOS Cellular Library APIs implementation without AT commands.
 */

/* The config header is always included first. */

#ifndef CELLULAR_DO_NOT_USE_CUSTOM_CONFIG
    /* Include custom config file before other headers. */
    #include "cellular_config.h"
#endif
#include "cellular_config_defaults.h"

/* Standard includes. */
#include <stdio.h>
#include <string.h>

#include "cellular_platform.h"
#include "cellular_types.h"
#include "cellular_api.h"
#include "cellular_internal.h"
#include "cellular_common_internal.h"
#include "cellular_pkthandler_internal.h"
#include "cellular_pktio_internal.h"
#include "cellular_common_portable.h"
#include "cellular_common_api.h"

/*-----------------------------------------------------------*/

static CellularError_t _socketSetSockOptLevelTransport( CellularSocketOption_t option,
                                                        CellularSocketHandle_t socketHandle,
                                                        const uint8_t * pOptionValue,
                                                        uint32_t optionValueLength );

/*-----------------------------------------------------------*/

/* Internal function of Cellular_SocketSetSockOpt to reduce complexity. */
static CellularError_t _socketSetSockOptLevelTransport( CellularSocketOption_t option,
                                                        CellularSocketHandle_t socketHandle,
                                                        const uint8_t * pOptionValue,
                                                        uint32_t optionValueLength )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    const uint32_t * pTimeoutMs = NULL;

    if( option == CELLULAR_SOCKET_OPTION_SEND_TIMEOUT )
    {
        if( optionValueLength == sizeof( uint32_t ) )
        {
            /* MISRA Ref 11.3 [Misaligned access] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            pTimeoutMs = ( const uint32_t * ) pOptionValue;
            socketHandle->sendTimeoutMs = *pTimeoutMs;
        }
        else
        {
            cellularStatus = CELLULAR_INTERNAL_FAILURE;
        }
    }
    else if( option == CELLULAR_SOCKET_OPTION_RECV_TIMEOUT )
    {
        if( optionValueLength == sizeof( uint32_t ) )
        {
            /* MISRA Ref 11.3 [Misaligned access] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            pTimeoutMs = ( const uint32_t * ) pOptionValue;
            socketHandle->recvTimeoutMs = *pTimeoutMs;
        }
        else
        {
            cellularStatus = CELLULAR_INTERNAL_FAILURE;
        }
    }
    else if( option == CELLULAR_SOCKET_OPTION_PDN_CONTEXT_ID )
    {
        if( ( socketHandle->socketState == SOCKETSTATE_ALLOCATED ) && ( optionValueLength == sizeof( uint8_t ) ) )
        {
            socketHandle->contextId = *pOptionValue;
        }
        else
        {
            LogError( ( "Cellular_SocketSetSockOpt: Cannot change the contextID in this state %d or length %u is invalid.",
                        socketHandle->socketState, ( unsigned int ) optionValueLength ) );
            cellularStatus = CELLULAR_INTERNAL_FAILURE;
        }
    }
    else if( option == CELLULAR_SOCKET_OPTION_SET_LOCAL_PORT )
    {
        if( ( socketHandle->socketState == SOCKETSTATE_ALLOCATED ) && ( optionValueLength == sizeof( uint16_t ) ) )
        {
            /* MISRA Ref 11.3 [Misaligned access] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-113 */
            /* coverity[misra_c_2012_rule_11_3_violation] */
            socketHandle->localPort = *( ( uint16_t * ) pOptionValue );
        }
        else
        {
            LogError( ( "Cellular_SocketSetSockOpt: Cannot change the localPort in this state %d or length %u is invalid.",
                        socketHandle->socketState, ( unsigned int ) optionValueLength ) );
            cellularStatus = CELLULAR_INTERNAL_FAILURE;
        }
    }
    else
    {
        LogError( ( "Cellular_SocketSetSockOpt: Option not supported" ) );
        cellularStatus = CELLULAR_UNSUPPORTED;
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonInit( CellularHandle_t * pCellularHandle,
                                     const CellularCommInterface_t * pCommInterface,
                                     const CellularTokenTable_t * pTokenTable )
{
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularContext_t * pContext = NULL;

    if( pCellularHandle == NULL )
    {
        LogError( ( "Cellular_CommonInit pCellularHandle is NULL." ) );
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else if( pCommInterface == NULL )
    {
        LogError( ( "Cellular_CommonInit pCommInterface is NULL." ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else if( pTokenTable == NULL )
    {
        LogError( ( "Cellular_CommonInit pTokenTable is NULL." ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        /* Init the common library. */
        cellularStatus = _Cellular_LibInit( pCellularHandle, pCommInterface, pTokenTable );

        if( cellularStatus == CELLULAR_SUCCESS )
        {
            pContext = ( CellularContext_t * ) ( *pCellularHandle );

            cellularStatus = Cellular_ModuleInit( pContext, &( pContext->pModuleContext ) );

            if( cellularStatus == CELLULAR_SUCCESS )
            {
                cellularStatus = Cellular_ModuleEnableUE( pContext );

                if( cellularStatus == CELLULAR_SUCCESS )
                {
                    cellularStatus = Cellular_ModuleEnableUrc( pContext );
                }

                if( cellularStatus != CELLULAR_SUCCESS )
                {
                    /* Clean up the resource allocated by cellular module here if
                     * Cellular_ModuleEnableUE or Cellular_ModuleEnableUrc returns
                     * error. */
                    ( void ) Cellular_ModuleCleanUp( pContext );
                }
            }

            if( cellularStatus != CELLULAR_SUCCESS )
            {
                /* Clean up the resource in cellular common library if any of the
                 * module port function returns error. Error returned by _Cellular_LibInit
                 * is already handled in the implementation. */
                ( void ) _Cellular_LibCleanup( pContext );
            }
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonCleanup( CellularHandle_t cellularHandle )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    if( pContext == NULL )
    {
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else
    {
        ( void ) Cellular_ModuleCleanUp( pContext );
        ( void ) _Cellular_LibCleanup( cellularHandle );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonRegisterUrcNetworkRegistrationEventCallback( CellularHandle_t cellularHandle,
                                                                            CellularUrcNetworkRegistrationCallback_t networkRegistrationCallback,
                                                                            void * pCallbackContext )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else
    {
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->cbEvents.networkRegistrationCallback = networkRegistrationCallback;
        pContext->cbEvents.pNetworkRegistrationCallbackContext = pCallbackContext;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonRegisterUrcPdnEventCallback( CellularHandle_t cellularHandle,
                                                            CellularUrcPdnEventCallback_t pdnEventCallback,
                                                            void * pCallbackContext )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else
    {
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->cbEvents.pdnEventCallback = pdnEventCallback;
        pContext->cbEvents.pPdnEventCallbackContext = pCallbackContext;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonRegisterUrcSignalStrengthChangedCallback( CellularHandle_t cellularHandle,
                                                                         CellularUrcSignalStrengthChangedCallback_t signalStrengthChangedCallback,
                                                                         void * pCallbackContext )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else
    {
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->cbEvents.signalStrengthChangedCallback = signalStrengthChangedCallback;
        pContext->cbEvents.pSignalStrengthChangedCallbackContext = pCallbackContext;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonRegisterUrcGenericCallback( CellularHandle_t cellularHandle,
                                                           CellularUrcGenericCallback_t genericCallback,
                                                           void * pCallbackContext )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else
    {
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->cbEvents.genericCallback = genericCallback;
        pContext->cbEvents.pGenericCallbackContext = pCallbackContext;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonRegisterModemEventCallback( CellularHandle_t cellularHandle,
                                                           CellularModemEventCallback_t modemEventCallback,
                                                           void * pCallbackContext )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else
    {
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pContext->cbEvents.modemEventCallback = modemEventCallback;
        pContext->cbEvents.pModemEventCallbackContext = pCallbackContext;
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonATCommandRaw( CellularHandle_t cellularHandle,
                                             const char * pATCommandPrefix,
                                             const char * pATCommandPayload,
                                             CellularATCommandType_t atCommandType,
                                             CellularATCommandResponseReceivedCallback_t responseReceivedCallback,
                                             void * pData,
                                             uint16_t dataLen )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularAtReq_t atReqGetResult = { 0 };

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pATCommandPayload == NULL )
    {
        LogError( ( "Cellular_ATCommandRaw: Input parameter is NULL" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        atReqGetResult.atCmdType = atCommandType;
        atReqGetResult.pAtRspPrefix = ( const char * ) pATCommandPrefix;
        atReqGetResult.pAtCmd = ( const char * ) pATCommandPayload;
        atReqGetResult.pData = pData;
        atReqGetResult.dataLen = dataLen;
        atReqGetResult.respCallback = responseReceivedCallback;

        pktStatus = _Cellular_TimeoutAtcmdRequestWithCallback( pContext,
                                                               atReqGetResult,
                                                               CELLULAR_AT_COMMAND_RAW_TIMEOUT_MS );
        cellularStatus = _Cellular_TranslatePktStatus( pktStatus );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonCreateSocket( CellularHandle_t cellularHandle,
                                             uint8_t pdnContextId,
                                             CellularSocketDomain_t socketDomain,
                                             CellularSocketType_t socketType,
                                             CellularSocketProtocol_t socketProtocol,
                                             CellularSocketHandle_t * pSocketHandle )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( pSocketHandle == NULL )
    {
        LogError( ( "pSocketHandle is NULL" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else if( _Cellular_IsValidPdn( pdnContextId ) != CELLULAR_SUCCESS )
    {
        LogError( ( "_Cellular_IsValidPdn failed" ) );
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else
    {
        cellularStatus = _Cellular_CreateSocketData( pContext, pdnContextId,
                                                     socketDomain, socketType, socketProtocol, pSocketHandle );
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonSocketSetSockOpt( CellularHandle_t cellularHandle,
                                                 CellularSocketHandle_t socketHandle,
                                                 CellularSocketOptionLevel_t optionLevel,
                                                 CellularSocketOption_t option,
                                                 const uint8_t * pOptionValue,
                                                 uint32_t optionValueLength )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( socketHandle == NULL )
    {
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else if( ( pOptionValue == NULL ) || ( optionValueLength == 0U ) )
    {
        LogError( ( "Cellular_SocketSetSockOpt: Invalid parameter" ) );
        cellularStatus = CELLULAR_BAD_PARAMETER;
    }
    else
    {
        if( optionLevel == CELLULAR_SOCKET_OPTION_LEVEL_IP )
        {
            LogError( ( "Cellular_SocketSetSockOpt: Option not supported" ) );
            cellularStatus = CELLULAR_UNSUPPORTED;
        }
        else /* optionLevel CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT. */
        {
            cellularStatus = _socketSetSockOptLevelTransport( option, socketHandle, pOptionValue, optionValueLength );
        }
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonSocketRegisterDataReadyCallback( CellularHandle_t cellularHandle,
                                                                CellularSocketHandle_t socketHandle,
                                                                CellularSocketDataReadyCallback_t dataReadyCallback,
                                                                void * pCallbackContext )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( socketHandle == NULL )
    {
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else
    {
        socketHandle->dataReadyCallback = dataReadyCallback;
        socketHandle->pDataReadyCallbackContext = pCallbackContext;
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonSocketRegisterSocketOpenCallback( CellularHandle_t cellularHandle,
                                                                 CellularSocketHandle_t socketHandle,
                                                                 CellularSocketOpenCallback_t socketOpenCallback,
                                                                 void * pCallbackContext )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( socketHandle == NULL )
    {
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else
    {
        socketHandle->openCallback = socketOpenCallback;
        socketHandle->pOpenCallbackContext = pCallbackContext;
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/

CellularError_t Cellular_CommonSocketRegisterClosedCallback( CellularHandle_t cellularHandle,
                                                             CellularSocketHandle_t socketHandle,
                                                             CellularSocketClosedCallback_t closedCallback,
                                                             void * pCallbackContext )
{
    CellularContext_t * pContext = ( CellularContext_t * ) cellularHandle;
    CellularError_t cellularStatus = CELLULAR_SUCCESS;

    /* pContext is checked in _Cellular_CheckLibraryStatus function. */
    cellularStatus = _Cellular_CheckLibraryStatus( pContext );

    if( cellularStatus != CELLULAR_SUCCESS )
    {
        LogDebug( ( "_Cellular_CheckLibraryStatus failed" ) );
    }
    else if( socketHandle == NULL )
    {
        cellularStatus = CELLULAR_INVALID_HANDLE;
    }
    else
    {
        socketHandle->closedCallback = closedCallback;
        socketHandle->pClosedCallbackContext = pCallbackContext;
    }

    return cellularStatus;
}

/*-----------------------------------------------------------*/
