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

/* Standard includes. */
#include <stdint.h>

/* Cellular APIs includes. */
#include "cellular_config.h"
#include "cellular_config_defaults.h"
#include "cellular_types.h"
#include "cellular_common_internal.h"
#include "cellular_common_api.h"

#define ensure_memory_is_valid( px, length )    ( px != NULL ) && __CPROVER_w_ok( ( px ), length )

/* Extern the com interface in comm_if_windows.c */
extern CellularCommInterface_t CellularCommInterface;

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

/****************************************************************
* The signature of the function under test.
****************************************************************/

CellularError_t Cellular_CommonSocketSetSockOpt( CellularHandle_t cellularHandle,
                                                 CellularSocketHandle_t socketHandle,
                                                 CellularSocketOptionLevel_t optionLevel,
                                                 CellularSocketOption_t option,
                                                 const uint8_t * pOptionValue,
                                                 uint32_t optionValueLength );

/****************************************************************
* The proof of Cellular_CommonSocketSetSockOpt
****************************************************************/
void harness()
{
    CellularHandle_t pHandle = NULL;
    uint8_t CellularSocketPdnContextId;
    CellularSocketDomain_t cellularSocketDomain;
    CellularSocketType_t cellularSocketType;
    CellularSocketProtocol_t cellularSocketProtocol;
    CellularSocketHandle_t pTcpSocket;
    CellularError_t socketStatus = CELLULAR_INVALID_HANDLE;
    CellularSocketOptionLevel_t cellularSocketOptionLevel;
    CellularSocketOption_t cellularSocketOption;
    uint32_t optionValueLength;
    uint32_t * pSendTimeoutMs = safeMalloc( optionValueLength );
    CellularSocketState_t socketState;

    /****************************************************************
    * Initialize the member of Cellular_CommonInit.
    ****************************************************************/
    Cellular_CommonInit( nondet_bool() ? NULL : &pHandle, &CellularCommInterface, &tokenTable );

    if( ( pHandle != NULL ) && ensure_memory_is_valid( pHandle, sizeof( CellularContext_t ) ) )
    {
        /* Create a new TCP socket. */
        socketStatus = Cellular_CommonCreateSocket( pHandle,
                                                    CellularSocketPdnContextId,
                                                    cellularSocketDomain,
                                                    cellularSocketType,
                                                    cellularSocketProtocol,
                                                    &pTcpSocket );

        if( ( pTcpSocket == NULL ) ||
            ( ( socketStatus == CELLULAR_SUCCESS ) &&
              ( pTcpSocket != NULL ) &&
              ensure_memory_is_valid( pTcpSocket, sizeof( struct CellularSocketContext ) ) ) )
        {
            if( pTcpSocket != NULL )
            {
                pTcpSocket->socketState = socketState;
            }

            Cellular_CommonSocketSetSockOpt( pHandle,
                                             pTcpSocket,
                                             cellularSocketOptionLevel,
                                             cellularSocketOption,
                                             ( const uint8_t * ) pSendTimeoutMs,
                                             optionValueLength );
        }
    }
}
