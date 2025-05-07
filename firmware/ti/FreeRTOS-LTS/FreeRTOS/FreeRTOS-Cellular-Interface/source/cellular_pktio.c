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
 * @brief FreeRTOS Cellular Library common packet I/O functions to assemble packet from comm interface.
 */

#ifndef CELLULAR_DO_NOT_USE_CUSTOM_CONFIG
    /* Include custom config file before other headers. */
    #include "cellular_config.h"
#endif
#include "cellular_config_defaults.h"

/* Standard includes. */
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>

#include "cellular_platform.h"
#include "cellular_types.h"
#include "cellular_internal.h"
#include "cellular_pktio_internal.h"
#include "cellular_common_internal.h"

/*-----------------------------------------------------------*/

#define PKTIO_EVT_MASK_STARTED    ( 0x0001UL )
#define PKTIO_EVT_MASK_ABORT      ( 0x0002UL )
#define PKTIO_EVT_MASK_ABORTED    ( 0x0004UL )
#define PKTIO_EVT_MASK_RX_DATA    ( 0x0008UL )
#define PKTIO_EVT_MASK_ALL_EVENTS \
    ( PKTIO_EVT_MASK_STARTED      \
      | PKTIO_EVT_MASK_ABORT      \
      | PKTIO_EVT_MASK_ABORTED    \
      | PKTIO_EVT_MASK_RX_DATA )

#define FREE_AT_RESPONSE_AND_SET_NULL( pResp )    { ( _Cellular_AtResponseFree( ( pResp ) ) ); ( ( pResp ) = NULL ); }

#define PKTIO_SHUTDOWN_WAIT_INTERVAL_MS    ( 10U )

#ifdef CELLULAR_DO_NOT_USE_CUSTOM_CONFIG
    #define LOOP_FOREVER()    true
#endif
/*-----------------------------------------------------------*/

static void _saveData( char * pLine,
                       CellularATCommandResponse_t * pResp,
                       uint32_t dataLen );
static void _saveRawData( char * pLine,
                          CellularATCommandResponse_t * pResp,
                          uint32_t dataLen );
static void _saveATData( char * pLine,
                         CellularATCommandResponse_t * pResp );
static CellularPktStatus_t _processIntermediateResponse( char * pLine,
                                                         CellularATCommandResponse_t * pResp,
                                                         CellularATCommandType_t atType );
static CellularATCommandResponse_t * _Cellular_AtResponseNew( void );
static void _Cellular_AtResponseFree( CellularATCommandResponse_t * pResp );
static CellularPktStatus_t _Cellular_ProcessLine( CellularContext_t * pContext,
                                                  char * pLine,
                                                  CellularATCommandResponse_t * pResp,
                                                  CellularATCommandType_t atType,
                                                  const char * pRespPrefix );
static bool _checkUrcTokenWoPrefix( const CellularContext_t * pContext,
                                    const char * pLine );
static _atRespType_t _getMsgType( CellularContext_t * pContext,
                                  const char * pLine,
                                  const char * pRespPrefix );
static CellularCommInterfaceError_t _Cellular_PktRxCallBack( void * pUserData,
                                                             CellularCommInterfaceHandle_t commInterfaceHandle );
static char * _handleLeftoverBuffer( CellularContext_t * pContext );
static char * _Cellular_ReadLine( CellularContext_t * pContext,
                                  uint32_t * pBytesRead,
                                  const CellularATCommandResponse_t * pAtResp );
static CellularPktStatus_t _handleData( char * pStartOfData,
                                        CellularContext_t * pContext,
                                        CellularATCommandResponse_t * pAtResp,
                                        char ** ppLine,
                                        uint32_t bytesRead,
                                        uint32_t * pBytesLeft );
static CellularPktStatus_t _handleMsgType( CellularContext_t * pContext,
                                           CellularATCommandResponse_t ** ppAtResp,
                                           char * pLine );
static void _handleAllReceived( CellularContext_t * pContext,
                                CellularATCommandResponse_t ** ppAtResp,
                                char * pData,
                                uint32_t bytesInBuffer );
static uint32_t _handleRxDataEvent( CellularContext_t * pContext );
static void _pktioReadThread( void * pUserData );
static void _PktioInitProcessReadThreadStatus( CellularContext_t * pContext );
static bool _getNextLine( CellularContext_t * pContext,
                          char ** ppLine,
                          uint32_t * pBytesRead,
                          uint32_t currentLineLength,
                          CellularPktStatus_t pktStatus );
static bool _handleCallbackResult( CellularContext_t * pContext,
                                   CellularPktStatus_t pktStatus,
                                   char * pLine,
                                   uint32_t * pBytesRead );
static bool _preprocessInputBuffer( CellularContext_t * pContext,
                                    char ** pLine,
                                    uint32_t * pBytesRead );
static CellularPktStatus_t _setPrefixByAtCommandType( CellularContext_t * pContext,
                                                      CellularATCommandType_t atType,
                                                      const char * pAtRspPrefix );

/*-----------------------------------------------------------*/

static uint32_t _convertCharPtrDistance( const char * pEndPtr,
                                         const char * pStartPtr )
{
    int32_t ptrDistance = ( int32_t ) ( pEndPtr - pStartPtr );

    return ( uint32_t ) ptrDistance;
}

/*-----------------------------------------------------------*/

static void _saveData( char * pLine,
                       CellularATCommandResponse_t * pResp,
                       uint32_t dataLen )
{
    CellularATCommandLine_t * pNew = NULL, * pTemp = NULL;

    ( void ) dataLen;

    LogDebug( ( "_saveData : Save data %p with length %u", pLine, ( unsigned int ) dataLen ) );

    pNew = ( CellularATCommandLine_t * ) Platform_Malloc( sizeof( CellularATCommandLine_t ) );
    CELLULAR_CONFIG_ASSERT( ( pNew != NULL ) );

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

/*-----------------------------------------------------------*/

static void _saveRawData( char * pLine,
                          CellularATCommandResponse_t * pResp,
                          uint32_t dataLen )
{
    LogDebug( ( "Save [%p] %u data to pResp", pLine, ( unsigned int ) dataLen ) );
    _saveData( pLine, pResp, dataLen );
}

/*-----------------------------------------------------------*/

static void _saveATData( char * pLine,
                         CellularATCommandResponse_t * pResp )
{
    LogDebug( ( "Save [%s] %u AT data to pResp", pLine, ( unsigned int ) strlen( pLine ) ) );
    _saveData( pLine, pResp, ( uint32_t ) ( strlen( pLine ) + 1U ) );
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _processIntermediateResponse( char * pLine,
                                                         CellularATCommandResponse_t * pResp,
                                                         CellularATCommandType_t atType )
{
    CellularPktStatus_t pkStatus = CELLULAR_PKT_STATUS_PENDING_DATA;

    switch( atType )
    {
        case CELLULAR_AT_WO_PREFIX:

            if( pResp->pItm == NULL )
            {
                _saveATData( pLine, pResp );
            }
            else
            {
                /* We already have an intermediate response. */
                pkStatus = CELLULAR_PKT_STATUS_INVALID_DATA;
                LogError( ( "CELLULAR_AT_WO_PREFIX process intermediate response ERROR: %s, status: %d, previous line %s",
                            pLine, pkStatus, pResp->pItm->pLine ) );
            }

            break;

        case CELLULAR_AT_WITH_PREFIX:

            if( pResp->pItm == NULL )
            {
                /* The removed code which demonstrate the existence of the prefix has been done in
                 * function _getMsgType(), so the failure condition here won't be touched.
                 */
                _saveATData( pLine, pResp );
            }
            else
            {
                /* We already have an intermediate response. */
                pkStatus = CELLULAR_PKT_STATUS_INVALID_DATA;
                LogError( ( "CELLULAR_AT_WITH_PREFIX process intermediate response ERROR: %s, status: %d, previous line %s",
                            pLine, pkStatus, pResp->pItm->pLine ) );
            }

            break;

        case CELLULAR_AT_MULTI_WITH_PREFIX:

            /* The removed code which demonstrate the existence of the prefix has been done in
             * function _getMsgType(), so the failure condition here won't be touched.
             */
            _saveATData( pLine, pResp );

            break;

        case CELLULAR_AT_MULTI_WO_PREFIX:
            _saveATData( pLine, pResp );
            break;

        case CELLULAR_AT_MULTI_DATA_WO_PREFIX:
            _saveATData( pLine, pResp );
            pkStatus = CELLULAR_PKT_STATUS_PENDING_BUFFER;
            break;

        case CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE:
        case CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE:
            /* Save the line in the response. */
            _saveATData( pLine, pResp );

            /* Returns CELLULAR_PKT_STATUS_OK to indicate that the response of the
             * command is received. No success result code is expected. Set the response
             * status to true here. */
            pkStatus = CELLULAR_PKT_STATUS_OK;
            pResp->status = true;
            break;

        default:
            /* Unexpected message received when sending the AT command. */
            LogInfo( ( "Undefind message received %s when sending AT command type %d.",
                       pLine, atType ) );

            pkStatus = CELLULAR_PKT_STATUS_INVALID_DATA;
            break;
    }

    return pkStatus;
}

/*-----------------------------------------------------------*/

static CellularATCommandResponse_t * _Cellular_AtResponseNew( void )
{
    CellularATCommandResponse_t * pNew = NULL;

    pNew = ( CellularATCommandResponse_t * ) Platform_Malloc( sizeof( CellularATCommandResponse_t ) );
    CELLULAR_CONFIG_ASSERT( ( pNew != NULL ) );

    ( void ) memset( ( void * ) pNew, 0, sizeof( CellularATCommandResponse_t ) );

    return pNew;
}

/*-----------------------------------------------------------*/

/**
 * Returns a pointer to the end of the next line
 * special-cases the "> " SMS prompt.
 *
 * Returns NULL if there is no complete line.
 */
static void _Cellular_AtResponseFree( CellularATCommandResponse_t * pResp )
{
    CellularATCommandLine_t * pCurrLine = NULL;
    CellularATCommandLine_t * pToFree = NULL;

    if( pResp != NULL )
    {
        pCurrLine = pResp->pItm;

        while( pCurrLine != NULL )
        {
            pToFree = pCurrLine;
            pCurrLine = pCurrLine->pNext;

            /* Reuse the packet io buffer. No need to free pToFree->pLine here. */
            Platform_Free( pToFree );
        }

        Platform_Free( pResp );
    }
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _Cellular_ProcessLine( CellularContext_t * pContext,
                                                  char * pLine,
                                                  CellularATCommandResponse_t * pResp,
                                                  CellularATCommandType_t atType,
                                                  const char * pRespPrefix )
{
    CellularPktStatus_t pkStatus = CELLULAR_PKT_STATUS_FAILURE;
    bool result = false;
    const char * const * pTokenSuccessTable = NULL;
    const char * const * pTokenErrorTable = NULL;
    const char * const * pTokenExtraTable = NULL;
    uint32_t tokenSuccessTableSize = 0;
    uint32_t tokenErrorTableSize = 0;
    uint32_t tokenExtraTableSize = 0;

    /* This variable is used in warning message. */
    ( void ) pRespPrefix;

    /* Lock the response mutex when processing the input line. */
    PlatformMutex_Lock( &( pContext->PktRespMutex ) );

    if( ( pContext->tokenTable.pCellularSrcTokenErrorTable != NULL ) &&
        ( pContext->tokenTable.pCellularSrcTokenSuccessTable != NULL ) )
    {
        pTokenSuccessTable = pContext->tokenTable.pCellularSrcTokenSuccessTable;
        tokenSuccessTableSize = pContext->tokenTable.cellularSrcTokenSuccessTableSize;
        pTokenErrorTable = pContext->tokenTable.pCellularSrcTokenErrorTable;
        tokenErrorTableSize = pContext->tokenTable.cellularSrcTokenErrorTableSize;
        pTokenExtraTable = pContext->tokenTable.pCellularSrcExtraTokenSuccessTable;
        tokenExtraTableSize = pContext->tokenTable.cellularSrcExtraTokenSuccessTableSize;

        /* pResp has been checked while allocating memory, so we don't
         * need to demonstrate it here.
         */
        ( void ) Cellular_ATcheckErrorCode( pLine, pTokenExtraTable,
                                            tokenExtraTableSize, &result );

        if( result == true )
        {
            pResp->status = true;
            pkStatus = CELLULAR_PKT_STATUS_OK;
            LogDebug( ( "Final AT response is SUCCESS [%s] in extra table", pLine ) );
        }
        else
        {
            ( void ) Cellular_ATcheckErrorCode( pLine, pTokenSuccessTable,
                                                tokenSuccessTableSize, &result );

            if( result == true )
            {
                pResp->status = true;
                pkStatus = CELLULAR_PKT_STATUS_OK;
                LogDebug( ( "Final AT response is SUCCESS [%s]", pLine ) );
            }
        }

        if( result != true )
        {
            ( void ) Cellular_ATcheckErrorCode( pLine, pTokenErrorTable,
                                                tokenErrorTableSize, &result );

            if( result == true )
            {
                pResp->status = false;
                pkStatus = CELLULAR_PKT_STATUS_OK;
            }
        }

        if( result != true )
        {
            pkStatus = _processIntermediateResponse( pLine, pResp, atType );
        }
    }

    if( ( result == true ) && ( pResp->status == false ) )
    {
        LogWarn( ( "Modem return ERROR: line %s, cmd : %s, respPrefix %s",
                   pLine,
                   ( pContext->pCurrentCmd != NULL ? pContext->pCurrentCmd : "NULL" ),
                   ( pRespPrefix != NULL ? pRespPrefix : "NULL" ) ) );
    }

    PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

    return pkStatus;
}

/*-----------------------------------------------------------*/

static bool _checkUrcTokenWoPrefix( const CellularContext_t * pContext,
                                    const char * pLine )
{
    bool ret = false;
    uint32_t i = 0;
    uint32_t urcTokenTableSize = pContext->tokenTable.cellularUrcTokenWoPrefixTableSize;
    const char * const * const pUrcTokenTable = pContext->tokenTable.pCellularUrcTokenWoPrefixTable;

    if( ( pUrcTokenTable == NULL ) || ( urcTokenTableSize == 0U ) )
    {
        ret = false;
    }
    else
    {
        for( i = 0; i < urcTokenTableSize; i++ )
        {
            if( strcmp( pLine, pUrcTokenTable[ i ] ) == 0 )
            {
                ret = true;
                break;
            }
        }
    }

    return ret;
}

/*-----------------------------------------------------------*/

static _atRespType_t _getMsgType( CellularContext_t * pContext,
                                  const char * pLine,
                                  const char * pRespPrefix )
{
    _atRespType_t atRespType = AT_UNDEFINED;
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    bool inputWithPrefix = false;
    bool inputWithSrcPrefix = false;

    /* Lock the response mutex when deciding message type. */
    PlatformMutex_Lock( &( pContext->PktRespMutex ) );

    if( _checkUrcTokenWoPrefix( pContext, pLine ) == true )
    {
        atRespType = AT_UNSOLICITED;
    }
    else
    {
        /* Check if prefix exist in pLine. */
        ( void ) Cellular_ATIsPrefixPresent( pLine, &inputWithPrefix );

        if( ( inputWithPrefix == true ) && ( pRespPrefix != NULL ) )
        {
            /* Check if this line contains prefix expected in AT command response. */
            atStatus = Cellular_ATStrStartWith( pLine, pRespPrefix, &inputWithSrcPrefix );
        }
    }

    if( ( atStatus == CELLULAR_AT_SUCCESS ) && ( atRespType == AT_UNDEFINED ) )
    {
        if( inputWithPrefix == true )
        {
            if( ( pContext->PktioAtCmdType != CELLULAR_AT_NO_COMMAND ) && ( inputWithSrcPrefix == true ) )
            {
                /* Celluar interface is sending AT command and this line contains
                 * expected prefix in the response. Return AT_SOLICITED here. */
                atRespType = AT_SOLICITED;
            }
            else
            {
                /* Lines with prefix are considered AT_UNSOLICITED unless the prefix
                 * is expected in AT command response. */
                atRespType = AT_UNSOLICITED;
            }
        }
        else
        {
            if( pContext->PktioAtCmdType != CELLULAR_AT_NO_COMMAND )
            {
                /* Cellular interface is waiting for AT command response from
                 * cellular modem. The token without prefix can be success or error
                 * token to indicate the AT command status. Return AT_SOLICITED
                 * here and this line will be parsed in _Cellular_ProcessLine later. */
                atRespType = AT_SOLICITED;
            }
            else
            {
                /* This line doesn't contain any prefix and cellular interface is
                 * not sending AT command. Therefore, this line is unexpected.
                 * Return AT_UNDEFINED here. */
                atRespType = AT_UNDEFINED;
            }
        }
    }

    PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

    return atRespType;
}

/*-----------------------------------------------------------*/

static CellularCommInterfaceError_t _Cellular_PktRxCallBack( void * pUserData,
                                                             CellularCommInterfaceHandle_t commInterfaceHandle )
{
    const CellularContext_t * pContext = ( CellularContext_t * ) pUserData;
    PlatformBaseType_t xHigherPriorityTaskWoken = platformFALSE, xResult = platformFALSE;
    CellularCommInterfaceError_t retComm = IOT_COMM_INTERFACE_SUCCESS;

    ( void ) commInterfaceHandle; /* Comm if is not used in this function. */

    /* The context of this function is a ISR. */
    if( pContext->pPktioCommEvent == NULL )
    {
        retComm = IOT_COMM_INTERFACE_BAD_PARAMETER;
    }
    else
    {
        xResult = PlatformEventGroup_SetBitsFromISR( ( PlatformEventGroupHandle_t ) pContext->pPktioCommEvent,
                                                     ( PlatformEventBits_t ) PKTIO_EVT_MASK_RX_DATA,
                                                     &xHigherPriorityTaskWoken );

        if( xResult == platformPASS )
        {
            if( xHigherPriorityTaskWoken == platformTRUE )
            {
                retComm = IOT_COMM_INTERFACE_SUCCESS;
            }
            else
            {
                retComm = IOT_COMM_INTERFACE_BUSY;
            }
        }
        else
        {
            retComm = IOT_COMM_INTERFACE_FAILURE;
        }
    }

    return retComm;
}

/*-----------------------------------------------------------*/

static char * _handleLeftoverBuffer( CellularContext_t * pContext )
{
    char * pRead = NULL; /* Pointer to first empty space in pContext->pktioReadBuf. */

    /* Move the leftover data or AT command response to the start of buffer.
     * Set the pRead pointer to the empty buffer space. */

    LogDebug( ( "moved the partial line/data from %p to %p %u",
                pContext->pPktioReadPtr, pContext->pktioReadBuf, ( unsigned int ) pContext->partialDataRcvdLen ) );

    ( void ) memmove( pContext->pktioReadBuf, pContext->pPktioReadPtr, pContext->partialDataRcvdLen );
    pContext->pktioReadBuf[ pContext->partialDataRcvdLen ] = '\0';

    pRead = &( pContext->pktioReadBuf[ pContext->partialDataRcvdLen ] );

    pContext->pPktioReadPtr = pContext->pktioReadBuf;

    return pRead;
}

/*-----------------------------------------------------------*/

/* pBytesRead : bytes read from comm interface. */
/* partialData : leftover bytes in the pktioreadbuf. Not enough to be a command. */
static char * _Cellular_ReadLine( CellularContext_t * pContext,
                                  uint32_t * pBytesRead,
                                  const CellularATCommandResponse_t * pAtResp )
{
    char * pAtBuf = NULL; /* The returned start of data. */
    char * pRead = NULL;  /* pRead is the first empty ptr in the Buffer for comm intf to read. */
    uint32_t bytesRead = 0;
    uint32_t partialDataRead = pContext->partialDataRcvdLen;
    int32_t bufferEmptyLength = ( int32_t ) PKTIO_READ_BUFFER_SIZE;

    pAtBuf = pContext->pktioReadBuf;
    pRead = pContext->pktioReadBuf;

    /* pContext->pPktioReadPtr is valid data start pointer.
     * pContext->partialDataRcvdLen is the valid data length need to be handled.
     * if pContext->pPktioReadPtr is NULL, valid data start from pContext->pktioReadBuf.
     * pAtResp equals NULL indicate that no data is buffered in AT command response and
     * data before pPktioReadPtr is invalid data can be recycled. */
    if( ( pContext->pPktioReadPtr != NULL ) && ( pContext->pPktioReadPtr != pContext->pktioReadBuf ) &&
        ( pContext->partialDataRcvdLen != 0U ) && ( pAtResp == NULL ) )
    {
        pRead = _handleLeftoverBuffer( pContext );
        bufferEmptyLength = ( ( int32_t ) PKTIO_READ_BUFFER_SIZE - ( int32_t ) pContext->partialDataRcvdLen );
    }
    else
    {
        if( pContext->pPktioReadPtr != NULL )
        {
            /* There are still valid data before pPktioReadPtr. */
            pRead = &( pContext->pPktioReadPtr[ pContext->partialDataRcvdLen ] );
            pAtBuf = pContext->pPktioReadPtr;
            bufferEmptyLength = ( ( int32_t ) PKTIO_READ_BUFFER_SIZE -
                                  ( int32_t ) pContext->partialDataRcvdLen - ( int32_t ) _convertCharPtrDistance( pContext->pPktioReadPtr, pContext->pktioReadBuf ) );
        }
        else
        {
            /* There are valid data need to be handled with length pContext->partialDataRcvdLen. */
            pRead = &( pContext->pktioReadBuf[ pContext->partialDataRcvdLen ] );
            pAtBuf = pContext->pktioReadBuf;
            bufferEmptyLength = ( ( int32_t ) PKTIO_READ_BUFFER_SIZE - ( int32_t ) pContext->partialDataRcvdLen );
        }
    }

    if( bufferEmptyLength > 0 )
    {
        ( void ) pContext->pCommIntf->recv( pContext->hPktioCommIntf, ( uint8_t * ) pRead,
                                            ( uint32_t ) bufferEmptyLength,
                                            CELLULAR_COMM_IF_RECV_TIMEOUT_MS, &bytesRead );

        if( bytesRead > 0U )
        {
            /* Add a NULL after the bytesRead. This is required for further processing. */
            pRead[ bytesRead ] = '\0';

            LogDebug( ( "AT Read %u bytes, data[%p]", ( unsigned int ) bytesRead, pRead ) );
            /* Set the pBytesRead only when actual bytes read from comm interface. */
            *pBytesRead = bytesRead + partialDataRead;

            /* Clean the partial data and read pointer. */
            pContext->partialDataRcvdLen = 0;
        }
        else
        {
            pAtBuf = NULL;
            *pBytesRead = 0U;
        }
    }
    else
    {
        LogError( ( "No empty space from comm if to handle incoming data, reset all parameter for next incoming data." ) );
        *pBytesRead = 0;
        pContext->partialDataRcvdLen = 0;
        pContext->pPktioReadPtr = NULL;
    }

    return pAtBuf;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _handleData( char * pStartOfData,
                                        CellularContext_t * pContext,
                                        CellularATCommandResponse_t * pAtResp,
                                        char ** ppLine,
                                        uint32_t bytesRead,
                                        uint32_t * pBytesLeft )
{
    /* Calculate the size of data received so far. */
    uint32_t bytesBeforeData = _convertCharPtrDistance( pStartOfData, *ppLine );
    CellularPktStatus_t pkStatus = CELLULAR_PKT_STATUS_OK;
    uint32_t bytesDataAndLeft = 0;

    /* Bytes before pStartOfData is not data, skip the bytes received. */
    /* bytesRead = bytesBeforeData( data prefix ) + bytesData + bytesLeft( other AT command response ). */
    bytesDataAndLeft = bytesRead - bytesBeforeData;

    if( bytesDataAndLeft >= pContext->dataLength )
    {
        /* Add data to the response linked list. */
        _saveRawData( pStartOfData, pAtResp, pContext->dataLength );

        /* Advance pLine to a point after data. */
        *ppLine = &( pStartOfData[ pContext->dataLength ] );

        /* There are more bytes after the data. */
        *pBytesLeft = ( bytesDataAndLeft - pContext->dataLength );

        LogDebug( ( "_handleData : read buffer buffer %p start %p prefix %d left %d, read total %u",
                    pContext->pktioReadBuf,
                    pStartOfData,
                    ( unsigned int ) bytesBeforeData,
                    ( unsigned int ) *pBytesLeft,
                    ( unsigned int ) bytesRead ) );

        /* reset the data related variables. */
        pContext->dataLength = 0U;

        /* Set the pPktioReadPtr to indicate data already handled. */
        pContext->pPktioReadPtr = *ppLine;
        pContext->partialDataRcvdLen = *pBytesLeft;
    }
    else
    {
        /* The data received is partial. Store the start of data in read pointer. */
        pContext->pPktioReadPtr = pStartOfData;
        pContext->partialDataRcvdLen = bytesDataAndLeft;
        pkStatus = CELLULAR_PKT_STATUS_PENDING_BUFFER;
    }

    return pkStatus;
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _handleMsgType( CellularContext_t * pContext,
                                           CellularATCommandResponse_t ** ppAtResp,
                                           char * pLine )
{
    CellularPktStatus_t pkStatus = CELLULAR_PKT_STATUS_OK;

    if( pContext->recvdMsgType == AT_UNSOLICITED )
    {
        if( pContext->pPktioHandlepktCB != NULL )
        {
            ( void ) pContext->pPktioHandlepktCB( pContext, AT_UNSOLICITED, pLine );
        }
    }
    else if( pContext->recvdMsgType == AT_SOLICITED )
    {
        if( *ppAtResp == NULL )
        {
            *ppAtResp = _Cellular_AtResponseNew();
            LogDebug( ( "Allocate at response %p", ( void * ) *ppAtResp ) );
        }

        LogDebug( ( "AT solicited Resp[%s]", pLine ) );

        /* Process Line will store the Line data in AT response. */
        pkStatus = _Cellular_ProcessLine( pContext, pLine, *ppAtResp, pContext->PktioAtCmdType, pContext->pRespPrefix );

        if( pkStatus == CELLULAR_PKT_STATUS_OK )
        {
            /* Reset the command type. Further response from cellular modem won't be
             * regarded as AT_SOLICITED response. */
            PlatformMutex_Lock( &( pContext->PktRespMutex ) );
            pContext->PktioAtCmdType = CELLULAR_AT_NO_COMMAND;
            pContext->pRespPrefix = NULL;
            PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

            /* This command is completed. Call the user callback to parse the result. */
            if( pContext->pPktioHandlepktCB != NULL )
            {
                ( void ) pContext->pPktioHandlepktCB( pContext, AT_SOLICITED, *ppAtResp );
            }

            FREE_AT_RESPONSE_AND_SET_NULL( *ppAtResp );
        }
        else if( pkStatus == CELLULAR_PKT_STATUS_PENDING_BUFFER )
        {
            /* This command expects raw data to be appended to buffer. Check data
             * prefix first then store the data if this command has data response. */
        }
        else if( pkStatus == CELLULAR_PKT_STATUS_PENDING_DATA )
        {
            /* The command expects more response line. */
        }
        else
        {
            /* A unexpected message received when sending the AT command.Try to
             * handle it with undefined response callback. */
            pContext->recvdMsgType = AT_UNDEFINED;
        }
    }
    else
    {
        /* This is AT_UNDEFINED when not sending the AT command. */
    }

    if( pContext->recvdMsgType == AT_UNDEFINED )
    {
        /* Pktio receives AT_UNDEFINED response from modem. This could be module specific
         * response. Call the packet handler callback to handle this message. */
        if( pContext->pPktioHandlepktCB != NULL )
        {
            pkStatus = pContext->pPktioHandlepktCB( pContext, AT_UNDEFINED, pLine );
        }

        if( pkStatus != CELLULAR_PKT_STATUS_OK )
        {
            LogError( ( "recvdMsgType is AT_UNDEFINED for Message: %s, cmd %s",
                        pLine,
                        ( pContext->pCurrentCmd != NULL ? pContext->pCurrentCmd : "NULL" ) ) );

            /* Reset the command type. */
            PlatformMutex_Lock( &( pContext->PktRespMutex ) );
            pContext->PktioAtCmdType = CELLULAR_AT_NO_COMMAND;
            pContext->pRespPrefix = NULL;
            PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

            /* Clean the read buffer and read pointer. */
            ( void ) memset( pContext->pktioReadBuf, 0, PKTIO_READ_BUFFER_SIZE + 1U );
            pContext->pPktioReadPtr = NULL;
            pContext->partialDataRcvdLen = 0;
            FREE_AT_RESPONSE_AND_SET_NULL( *ppAtResp );

            /* Return invalid data error code. */
            pkStatus = CELLULAR_PKT_STATUS_INVALID_DATA;
        }
        else
        {
            /* The undefined response callback handle this message without problem. */
        }
    }

    return pkStatus;
}

/*-----------------------------------------------------------*/

static bool _findLineInStream( CellularContext_t * pContext,
                               char * pLine,
                               uint32_t bytesRead,
                               uint32_t * pLineLength )
{
    bool keepProcess = true;
    char * pTempLine = pLine;
    uint32_t i = 0;

    /* Handle the complete line here. GetMsgType needs a complete Line or longer then maximum prefix line. */
    for( i = 0; i < bytesRead; i++ )
    {
        if( ( pTempLine[ i ] == '\0' ) || ( pTempLine[ i ] == '\r' ) || ( pTempLine[ i ] == '\n' ) )
        {
            break;
        }
    }

    /* A complete Line is found. */
    if( i < bytesRead )
    {
        pTempLine[ i ] = '\0';
        *pLineLength = i;
    }
    else
    {
        LogDebug( ( "%p is not a complete line", pTempLine ) );
        pContext->pPktioReadPtr = pTempLine;
        pContext->partialDataRcvdLen = bytesRead;
        keepProcess = false;
    }

    return keepProcess;
}

/*-----------------------------------------------------------*/

static bool _handleCallbackResult( CellularContext_t * pContext,
                                   CellularPktStatus_t pktStatus,
                                   char * pLine,
                                   uint32_t * pBytesRead )
{
    bool keepProcess;

    if( pktStatus == CELLULAR_PKT_STATUS_PREFIX_MISMATCH )
    {
        /* Input buffer is not handled in the callback. pktio should keep processing
         * the input buffer. */
        keepProcess = true;
    }
    else if( pktStatus == CELLULAR_PKT_STATUS_SIZE_MISMATCH )
    {
        /* Input buffer is handled in the callback. The callback expects to be called
         * again with more data received. pktio won't keep process this input buffer. */
        pContext->pPktioReadPtr = pLine;
        pContext->partialDataRcvdLen = *pBytesRead;
        keepProcess = false;
    }
    else if( pktStatus != CELLULAR_PKT_STATUS_OK )
    {
        /* Modem returns unexpected response. */
        LogError( ( "Input buffer callback returns error %d. Clean the read buffer.", pktStatus ) );

        /* Clean the read buffer and read pointer. */
        ( void ) memset( pContext->pktioReadBuf, 0, PKTIO_READ_BUFFER_SIZE + 1U );
        pContext->pPktioReadPtr = NULL;
        pContext->partialDataRcvdLen = 0;
        keepProcess = false;
    }
    else
    {
        /* Callback function returns CELLULAR_PKT_STATUS_OK. pktio can keep processing
         * the input buffer. */
        keepProcess = true;
    }

    return keepProcess;
}

/*-----------------------------------------------------------*/

static bool _preprocessInputBuffer( CellularContext_t * pContext,
                                    char ** pLine,
                                    uint32_t * pBytesRead )
{
    char * pTempLine = *pLine;
    bool keepProcess = true;
    uint32_t bufferLength = 0;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    if( pContext->inputBufferCallback != NULL )
    {
        PlatformMutex_Lock( &( pContext->PktRespMutex ) );
        pktStatus = pContext->inputBufferCallback( pContext->pInputBufferCallbackContext,
                                                   pTempLine,
                                                   *pBytesRead,
                                                   &bufferLength );
        PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

        if( pktStatus == CELLULAR_PKT_STATUS_OK )
        {
            /* Handle the callback result is CELLULAR_PKT_STATUS_OK in this function.
             * Check the bufferLength returned by callback function here. */
            if( bufferLength > *pBytesRead )
            {
                /* The input buffer callback returns incorrect buffer length. */
                LogError( ( "Input buffer callback returns bufferLength %u. Modem returns length %u. Clean the read buffer.",
                            ( unsigned int ) bufferLength, ( unsigned int ) *pBytesRead ) );

                /* Clean the read buffer and read pointer. */
                ( void ) memset( pContext->pktioReadBuf, 0, PKTIO_READ_BUFFER_SIZE + 1U );
                pContext->pPktioReadPtr = NULL;
                pContext->partialDataRcvdLen = 0;
                keepProcess = false;
            }
            else
            {
                /* The input buffer is handled in the callback successfully. Move
                 * the read pointer forward. pktio will keep processing the line
                 * after. */
                pTempLine = &( pTempLine[ bufferLength ] );
                *pLine = pTempLine;
                pContext->pPktioReadPtr = *pLine;

                /* Calculate remain bytes in the buffer. */
                *pBytesRead = *pBytesRead - bufferLength;
            }
        }
        else
        {
            keepProcess = _handleCallbackResult( pContext, pktStatus, pTempLine, pBytesRead );
        }
    }

    return keepProcess;
}

/*-----------------------------------------------------------*/

static bool _preprocessLine( CellularContext_t * pContext,
                             char * pLine,
                             uint32_t * pBytesRead,
                             char ** ppStartOfData )
{
    char * pTempLine = pLine;
    bool keepProcess = true;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    CellularATCommandDataPrefixCallback_t pktDataPrefixCB = NULL;
    void * pDataPrefixCBContext = NULL;
    CellularATCommandDataSendPrefixCallback_t pktDataSendPrefixCB = NULL;
    void * pDataSendPrefixCBContext = NULL;

    /* Acquire the response lock to keep consistency. */
    PlatformMutex_Lock( &( pContext->PktRespMutex ) );
    pktDataPrefixCB = pContext->pktDataPrefixCB;
    pDataPrefixCBContext = pContext->pDataPrefixCBContext;
    pktDataSendPrefixCB = pContext->pktDataSendPrefixCB;
    pDataSendPrefixCBContext = pContext->pDataSendPrefixCBContext;
    PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

    /* The line only has change line. */
    if( *pBytesRead <= 0U )
    {
        pContext->pPktioReadPtr = pTempLine;
        pContext->partialDataRcvdLen = 0;
        keepProcess = false;
    }
    else
    {
        if( pktDataSendPrefixCB != NULL )
        {
            /* Check if the AT command response is the data send prefix.
             * Data send prefix is an SRC success token for data send AT command.
             * It is used to indicate modem can receive data now. */
            /* This function may fix the data stream if the data send prefix is not a line. */
            pktStatus = pktDataSendPrefixCB( pDataSendPrefixCBContext, pTempLine, pBytesRead );

            keepProcess = _handleCallbackResult( pContext, pktStatus, pTempLine, pBytesRead );
        }
        else if( pktDataPrefixCB != NULL )
        {
            /* Check if the AT command response is the data receive prefix.
             * Data receive prefix is an SRC success token for data receive AT commnad.
             * It is used to indicate modem will start to send data. Don't parse the content. */
            /* ppStartOfData and pDataLength are not set if this function failed. */

            /* This function may fix the data stream if the AT response and data
             * received are in the same line. */
            pktStatus = pktDataPrefixCB( pDataPrefixCBContext,
                                         pTempLine, *pBytesRead,
                                         ppStartOfData, &( pContext->dataLength ) );

            keepProcess = _handleCallbackResult( pContext, pktStatus, pTempLine, pBytesRead );
        }
        else
        {
            /* This is the case AT command don't need data send or data receive prefix. */
            /* MISRA empty else. */
        }
    }

    return keepProcess;
}

/*-----------------------------------------------------------*/

static bool _handleDataResult( CellularContext_t * pContext,
                               CellularATCommandResponse_t * const * ppAtResp,
                               char * pStartOfData,
                               char ** ppLine,
                               uint32_t * pBytesRead )
{
    uint32_t bytesLeft = 0;
    bool keepProcess = true;

    /* The input line is a data recv command. Handle the data buffer. */
    ( void ) _handleData( pStartOfData, pContext, *ppAtResp, ppLine, *pBytesRead, &bytesLeft );

    /* pktStatus will never be CELLULAR_PKT_STATUS_PENDING_BUFFER from _handleData(). */
    if( bytesLeft == 0U )
    {
        LogDebug( ( "Complete Data received" ) );
        keepProcess = false;
    }
    else
    {
        *pBytesRead = bytesLeft;
        LogDebug( ( "_handleData okay, keep processing %u bytes %p", ( unsigned int ) bytesLeft, *ppLine ) );
    }

    return keepProcess;
}

/*-----------------------------------------------------------*/

static bool _getNextLine( CellularContext_t * pContext,
                          char ** ppLine,
                          uint32_t * pBytesRead,
                          uint32_t currentLineLength,
                          CellularPktStatus_t pktStatus )
{
    bool keepProcess = true;

    /* Advanced 1 byte to read next Line. */
    *ppLine = &( ( *ppLine )[ ( currentLineLength + 1U ) ] );
    *pBytesRead = *pBytesRead - ( currentLineLength + 1U );
    pContext->pPktioReadPtr = *ppLine;
    pContext->partialDataRcvdLen = *pBytesRead;

    if( ( pktStatus == CELLULAR_PKT_STATUS_OK ) && ( pContext->recvdMsgType == AT_SOLICITED ) )
    {
        /* Garbage collection. */
        LogDebug( ( "Garbage collection" ) );
        ( void ) memmove( pContext->pktioReadBuf, *ppLine, *pBytesRead );
        *ppLine = pContext->pktioReadBuf;
        pContext->pPktioReadPtr = pContext->pktioReadBuf;
        pContext->partialDataRcvdLen = *pBytesRead;
    }

    return keepProcess;
}

/*-----------------------------------------------------------*/

/* This function handle message in line( string terminated with \r or \n ). */
static void _handleAllReceived( CellularContext_t * pContext,
                                CellularATCommandResponse_t ** ppAtResp,
                                char * pData,
                                uint32_t bytesInBuffer )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    char * pStartOfData = NULL, * pTempLine = pData;
    uint32_t bytesRead = bytesInBuffer;
    uint32_t currentLineLength = 0U;
    bool keepProcess = true;

    while( keepProcess == true )
    {
        /* Pktio is reading command. Skip over the change line and leading NULL character.
         * And the reason we don't consider the variable bytesInBuffer is because
         * that the input variable bytesInBuffer is bounded by the caller already.
         */
        while( ( bytesRead > 0U ) && ( ( *pTempLine == '\r' ) || ( *pTempLine == '\n' ) || ( *pTempLine == '\0' ) ) )
        {
            pTempLine++;
            bytesRead = bytesRead - 1U;
        }

        /* Preprocess the input buffer in the callback function. pktio processes the
         * input buffer in line. This function allows the porting to process the input
         * buffer before pktio processing lines in the buffer. For example, porting
         * can make use of input buffer callback to handle binary stream in URC. */
        keepProcess = _preprocessInputBuffer( pContext, &pTempLine, &bytesRead );

        /* Preprocess line. */
        if( keepProcess == true )
        {
            keepProcess = _preprocessLine( pContext, pTempLine, &bytesRead, &pStartOfData );
        }

        if( keepProcess == true )
        {
            keepProcess = _findLineInStream( pContext, pTempLine, bytesRead, &currentLineLength );
        }

        if( keepProcess == true )
        {
            /* A complete Line received. Get the message type. */
            pContext->recvdMsgType = _getMsgType( pContext, pTempLine, pContext->pRespPrefix );

            /* Handle the message according the received message type. */
            pktStatus = _handleMsgType( pContext, ppAtResp, pTempLine );

            if( pktStatus == CELLULAR_PKT_STATUS_PENDING_BUFFER )
            {
                /* The input line is a data recv command. Handle the data buffer. */
                if( pContext->dataLength != 0U )
                {
                    keepProcess = _handleDataResult( pContext, ppAtResp, pStartOfData, &pTempLine, &bytesRead );
                }
                else
                {
                    keepProcess = _getNextLine( pContext, &pTempLine, &bytesRead, currentLineLength, pktStatus );
                }
            }
            else if( ( pktStatus == CELLULAR_PKT_STATUS_OK ) || ( pktStatus == CELLULAR_PKT_STATUS_PENDING_DATA ) )
            {
                /* Process AT response success. Get the next Line. */
                keepProcess = _getNextLine( pContext, &pTempLine, &bytesRead, currentLineLength, pktStatus );
            }
            else
            {
                LogDebug( ( "_handleMsgType failed %d", pktStatus ) );
                keepProcess = false;
            }
        }
    }
}

/*-----------------------------------------------------------*/

static uint32_t _handleRxDataEvent( CellularContext_t * pContext )
{
    char * pLine = NULL;
    uint32_t bytesRead = 0;
    uint32_t bytesLeft = 0;

    /* Return the first line, may be more lines in buffer. */
    /* Start from pLine there are bytesRead bytes. */
    pLine = _Cellular_ReadLine( pContext, &bytesRead, pContext->pAtCmdResp );

    if( bytesRead > 0U )
    {
        if( pContext->dataLength != 0U )
        {
            ( void ) _handleData( pLine, pContext, pContext->pAtCmdResp, &pLine, bytesRead, &bytesLeft );
        }
        else
        {
            bytesLeft = bytesRead;
        }

        /* If bytesRead in _Cellular_ReadLine is all for data, don't parse the AT command response. */
        if( bytesLeft > 0U )
        {
            /* Add the null terminated char to the end of pLine. */
            pLine[ bytesLeft ] = '\0';
            _handleAllReceived( pContext, &( pContext->pAtCmdResp ), pLine, bytesLeft );
        }
    }

    /* Return the bytes read from comm interface to do more reading. */
    return bytesRead;
}

/*-----------------------------------------------------------*/
static void _pktioReadThread( void * pUserData )
{
    CellularContext_t * pContext = ( CellularContext_t * ) pUserData;
    PlatformEventBits_t uxBits = 0;
    uint32_t bytesRead = 0U;

    /* Open main communication port. */
    if( ( pContext->pCommIntf != NULL ) &&
        ( pContext->pCommIntf->open( _Cellular_PktRxCallBack, ( void * ) pContext,
                                     &( pContext->hPktioCommIntf ) ) == IOT_COMM_INTERFACE_SUCCESS ) )
    {
        /* Send thread started event. */
        ( void ) PlatformEventGroup_SetBits( ( PlatformEventGroupHandle_t ) pContext->pPktioCommEvent, ( PlatformEventBits_t ) PKTIO_EVT_MASK_STARTED );

        do
        {
            /* Wait events for abort thread or rx data available. */
            uxBits = PlatformEventGroup_WaitBits( ( PlatformEventGroupHandle_t ) pContext->pPktioCommEvent,
                                                  ( ( PlatformEventBits_t ) PKTIO_EVT_MASK_ABORT | ( PlatformEventBits_t ) PKTIO_EVT_MASK_RX_DATA ),
                                                  platformTRUE,
                                                  platformFALSE,
                                                  platformMAX_DELAY );

            if( ( uxBits & ( PlatformEventBits_t ) PKTIO_EVT_MASK_ABORT ) != 0U )
            {
                LogDebug( ( "Abort received, cleaning up!" ) );
                FREE_AT_RESPONSE_AND_SET_NULL( pContext->pAtCmdResp );
                break;
            }
            else if( ( uxBits & ( PlatformEventBits_t ) PKTIO_EVT_MASK_RX_DATA ) != 0U )
            {
                /* Keep Reading until there is no more bytes in comm interface. */
                do
                {
                    bytesRead = _handleRxDataEvent( pContext );
                } while( ( bytesRead != 0U ) );
            }
            else
            {
                /* Empty else to avoid MISRA violation */
            }
        } while( true );

        ( void ) pContext->pCommIntf->close( pContext->hPktioCommIntf );
        pContext->hPktioCommIntf = NULL;
        pContext->pPktioShutdownCB( pContext );
    }
    else
    {
        LogError( ( "Comm port open failed" ) );
    }

    ( void ) PlatformEventGroup_SetBits( ( PlatformEventGroupHandle_t ) pContext->pPktioCommEvent, ( PlatformEventBits_t ) PKTIO_EVT_MASK_ABORTED );

    /* Call the shutdown callback if it is defined. */
    if( pContext->pPktioShutdownCB != NULL )
    {
        pContext->pPktioShutdownCB( pContext );
    }
}

/*-----------------------------------------------------------*/

static void _PktioInitProcessReadThreadStatus( CellularContext_t * pContext )
{
    PlatformEventBits_t uxBits = 0;

    uxBits = ( PlatformEventBits_t ) PlatformEventGroup_WaitBits( ( PlatformEventGroupHandle_t ) pContext->pPktioCommEvent,
                                                                  ( ( PlatformEventBits_t ) PKTIO_EVT_MASK_STARTED | ( PlatformEventBits_t ) PKTIO_EVT_MASK_ABORTED ),
                                                                  platformTRUE,
                                                                  platformFALSE,
                                                                  ( ( PlatformTickType_t ) ~( 0UL ) ) );

    if( ( uxBits & ( PlatformEventBits_t ) PKTIO_EVT_MASK_ABORTED ) != ( PlatformEventBits_t ) PKTIO_EVT_MASK_ABORTED )
    {
        pContext->bPktioUp = true;
    }
}

/*-----------------------------------------------------------*/

static CellularPktStatus_t _setPrefixByAtCommandType( CellularContext_t * pContext,
                                                      CellularATCommandType_t atType,
                                                      const char * pAtRspPrefix )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    switch( atType )
    {
        case CELLULAR_AT_NO_RESULT:
        case CELLULAR_AT_WO_PREFIX:
        case CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE:
            /* Response with prefix is not expected with these AT command types. */
            pContext->pRespPrefix = NULL;
            break;

        case CELLULAR_AT_WITH_PREFIX:
        case CELLULAR_AT_MULTI_WITH_PREFIX:
        case CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE:

            /* Response with prefix is expected with these AT command types. */
            if( pAtRspPrefix != NULL )
            {
                ( void ) strncpy( pContext->pktRespPrefixBuf, pAtRspPrefix, CELLULAR_CONFIG_MAX_PREFIX_STRING_LENGTH );
                pContext->pRespPrefix = pContext->pktRespPrefixBuf;
            }
            else
            {
                LogError( ( "_setPrefixByAtCommandType : Sending a AT command type %d but pAtRspPrefix is not set.", atType ) );
                pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
            }

            break;

        case CELLULAR_AT_MULTI_WO_PREFIX:
        case CELLULAR_AT_MULTI_DATA_WO_PREFIX:

            /* Response may come with or without prefix. */
            if( pAtRspPrefix != NULL )
            {
                ( void ) strncpy( pContext->pktRespPrefixBuf, pAtRspPrefix, CELLULAR_CONFIG_MAX_PREFIX_STRING_LENGTH );
                pContext->pRespPrefix = pContext->pktRespPrefixBuf;
            }
            else
            {
                pContext->pRespPrefix = NULL;
            }

            break;

        default:
            /* This is CELLULAR_AT_NO_COMMAND case. */
            LogError( ( "_setPrefixByAtCommandType : Sending invalid AT command type." ) );
            pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
            break;
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

CellularPktStatus_t _Cellular_PktioInit( CellularContext_t * pContext,
                                         _pPktioHandlePacketCallback_t handlePacketCb )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    bool status = false;

    if( pContext == NULL )
    {
        pktStatus = ( CellularPktStatus_t ) CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else
    {
        pContext->bPktioUp = false;
        pContext->PktioAtCmdType = CELLULAR_AT_NO_COMMAND;
        pContext->pPktioCommEvent = ( PlatformEventGroupHandle_t ) PlatformEventGroup_Create();

        if( pContext->pPktioCommEvent == NULL )
        {
            LogError( ( "Can't create event group" ) );
            pktStatus = CELLULAR_PKT_STATUS_CREATION_FAIL;
        }
    }

    if( pktStatus == CELLULAR_PKT_STATUS_OK )
    {
        pContext->pPktioHandlepktCB = handlePacketCb;
        ( void ) PlatformEventGroup_ClearBits( ( PlatformEventGroupHandle_t ) pContext->pPktioCommEvent,
                                               ( ( PlatformEventBits_t ) PKTIO_EVT_MASK_ALL_EVENTS ) );

        /* Create the Read thread. */
        status = Platform_CreateDetachedThread( _pktioReadThread,
                                                ( void * ) pContext,
                                                PLATFORM_THREAD_DEFAULT_PRIORITY,
                                                PLATFORM_THREAD_DEFAULT_STACK_SIZE );

        if( status == true )
        {
            LogDebug( ( "Reader thread created" ) );
            _PktioInitProcessReadThreadStatus( pContext );

            if( pContext->bPktioUp == false )
            {
                LogError( ( "Reader thread aborted" ) );
                pktStatus = CELLULAR_PKT_STATUS_FAILURE;
            }
        }
        else
        {
            LogError( ( "Can't create reader thread" ) );
            pktStatus = CELLULAR_PKT_STATUS_CREATION_FAIL;
        }
    }

    if( pktStatus == CELLULAR_PKT_STATUS_OK )
    {
        LogDebug( ( "Thread create: read_thread status:%d", pktStatus ) );
    }
    else
    {
        if( pContext != NULL )
        {
            pContext->pPktioHandlepktCB = NULL;

            if( pContext->pPktioCommEvent != NULL )
            {
                ( void ) PlatformEventGroup_Delete( ( PlatformEventGroupHandle_t ) pContext->pPktioCommEvent );
                pContext->pPktioCommEvent = ( PlatformEventGroupHandle_t ) ( uintptr_t ) ( uintptr_t * ) NULL;
            }
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

/* Sends the AT command to the modem. */
CellularPktStatus_t _Cellular_PktioSendAtCmd( CellularContext_t * pContext,
                                              const char * pAtCmd,
                                              CellularATCommandType_t atType,
                                              const char * pAtRspPrefix )
{
    uint32_t cmdLen = 0, newCmdLen = 0;
    uint32_t sentLen = 0;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    if( pContext == NULL )
    {
        LogError( ( "_Cellular_PktioSendAtCmd : invalid cellular context" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( ( pContext->pCommIntf == NULL ) || ( pContext->hPktioCommIntf == NULL ) )
    {
        LogError( ( "_Cellular_PktioSendAtCmd : invalid comm interface handle" ) );
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }
    else if( pAtCmd == NULL )
    {
        LogError( ( "_Cellular_PktioSendAtCmd : invalid pAtCmd" ) );
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        cmdLen = ( uint32_t ) strlen( pAtCmd );

        if( cmdLen > PKTIO_WRITE_BUFFER_SIZE )
        {
            LogError( ( "_Cellular_PktioSendAtCmd : invalid pAtCmd" ) );
            pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
        }
        else
        {
            PlatformMutex_Lock( &( pContext->PktRespMutex ) );

            pktStatus = _setPrefixByAtCommandType( pContext, atType, pAtRspPrefix );

            if( pktStatus == CELLULAR_PKT_STATUS_OK )
            {
                pContext->PktioAtCmdType = atType;
                newCmdLen = cmdLen;
                newCmdLen += 1U; /* Include space for \r. */

                ( void ) strncpy( pContext->pktioSendBuf, pAtCmd, cmdLen );
                pContext->pktioSendBuf[ cmdLen ] = '\r';

                PlatformMutex_Unlock( &( pContext->PktRespMutex ) );

                ( void ) pContext->pCommIntf->send( pContext->hPktioCommIntf,
                                                    ( const uint8_t * ) &( pContext->pktioSendBuf ), newCmdLen,
                                                    CELLULAR_COMM_IF_SEND_TIMEOUT_MS, &sentLen );
            }
            else
            {
                PlatformMutex_Unlock( &( pContext->PktRespMutex ) );
            }
        }
    }

    return pktStatus;
}

/*-----------------------------------------------------------*/

/* Sends data to the modem. */
uint32_t _Cellular_PktioSendData( CellularContext_t * pContext,
                                  const uint8_t * pData,
                                  uint32_t dataLen )
{
    uint32_t sentLen = 0;

    if( pContext == NULL )
    {
        LogError( ( "_Cellular_PktioSendData : invalid cellular context" ) );
    }
    else if( ( pContext->pCommIntf == NULL ) || ( pContext->hPktioCommIntf == NULL ) )
    {
        LogError( ( "_Cellular_PktioSendData : invalid comm interface handle" ) );
    }
    else if( pData == NULL )
    {
        LogError( ( "_Cellular_PktioSendData : invalid pData" ) );
    }
    else
    {
        ( void ) pContext->pCommIntf->send( pContext->hPktioCommIntf, pData,
                                            dataLen, CELLULAR_COMM_IF_SEND_TIMEOUT_MS, &sentLen );
    }

    LogDebug( ( "PktioSendData sent %u bytes", ( unsigned int ) sentLen ) );
    return sentLen;
}

/*-----------------------------------------------------------*/

void _Cellular_PktioShutdown( CellularContext_t * pContext )
{
    PlatformEventBits_t uxBits = 0;

    if( ( pContext != NULL ) && ( pContext->bPktioUp ) )
    {
        if( pContext->pPktioCommEvent != NULL )
        {
            ( void ) PlatformEventGroup_SetBits( ( PlatformEventGroupHandle_t ) pContext->pPktioCommEvent, ( PlatformEventBits_t ) PKTIO_EVT_MASK_ABORT );
            uxBits = ( PlatformEventBits_t ) PlatformEventGroup_GetBits( ( PlatformEventGroupHandle_t ) pContext->pPktioCommEvent );

            while( ( PlatformEventBits_t ) ( uxBits & PKTIO_EVT_MASK_ABORTED ) != ( PlatformEventBits_t ) ( PKTIO_EVT_MASK_ABORTED ) )
            {
                Platform_Delay( PKTIO_SHUTDOWN_WAIT_INTERVAL_MS );
                uxBits = ( PlatformEventBits_t ) PlatformEventGroup_GetBits( ( PlatformEventGroupHandle_t ) pContext->pPktioCommEvent );
            }

            ( void ) PlatformEventGroup_Delete( pContext->pPktioCommEvent );
            pContext->pPktioCommEvent = ( PlatformEventGroupHandle_t ) ( uintptr_t ) ( uintptr_t * ) NULL;
        }

        pContext->pPktioHandlepktCB = NULL;
        pContext->bPktioUp = false;
    }
}

/*-----------------------------------------------------------*/
