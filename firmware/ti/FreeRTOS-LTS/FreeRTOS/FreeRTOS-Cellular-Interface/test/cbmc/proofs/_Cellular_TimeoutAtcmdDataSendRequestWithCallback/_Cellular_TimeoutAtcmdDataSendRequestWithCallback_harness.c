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

/* Cellular default config includes. */
#include "cellular_config.h"
#include "cellular_config_defaults.h"

/* Cellular APIs includes. */
#include "cellular_platform.h"
#include "cellular_types.h"
#include "cellular_common_internal.h"
#include "cellular_common_api.h"

#define ensure_memory_is_valid( px, length )    ( px != NULL ) && __CPROVER_w_ok( ( px ), length ) && __CPROVER_r_ok( ( px ), length )

/* Extern the com interface in comm_if_windows.c */
extern CellularCommInterface_t CellularCommInterface;

/****************************************************************
* The signature of the function under test.
****************************************************************/

CellularPktStatus_t _Cellular_TimeoutAtcmdDataSendRequestWithCallback( CellularContext_t * pContext,
                                                                       CellularAtReq_t atReq,
                                                                       CellularAtDataReq_t dataReq,
                                                                       uint32_t atTimeoutMS,
                                                                       uint32_t dataTimeoutMS );


/****************************************************************
* The proof of _Cellular_TimeoutAtcmdDataSendRequestWithCallback
****************************************************************/
void harness()
{
    CellularHandle_t pHandle = NULL;
    uint16_t atCmdLen;
    uint16_t atRspCmdLen;
    uint16_t atReqDataLen;
    char * pAtRspPrefix;
    char * pAtCmd;
    CellularATCommandType_t atCmdType;
    CellularATCommandResponseReceivedCallback_t respCallback;
    void * pData;
    uint32_t atDataReqDataLen;
    uint8_t * pAtDataReqData = ( uint8_t * ) safeMalloc( atDataReqDataLen );
    uint32_t * pSentDataLength = safeMalloc( sizeof( uint32_t ) );
    uint32_t endPatternLen;
    uint8_t * pEndPattern = ( uint8_t * ) safeMalloc( endPatternLen );

    __CPROVER_assume( atCmdLen > 0 && atCmdLen < CBMC_MAX_BUFSIZE );
    __CPROVER_assume( atRspCmdLen > 0 && atRspCmdLen < CBMC_MAX_BUFSIZE );

    pAtCmd = ( char * ) safeMalloc( atCmdLen );

    if( pAtCmd )
    {
        __CPROVER_assume( ensure_memory_is_valid( pAtCmd, atCmdLen ) );
        pAtCmd[ atCmdLen - 1 ] = '\0';
    }

    pAtRspPrefix = ( char * ) safeMalloc( atRspCmdLen );

    if( pAtRspPrefix )
    {
        __CPROVER_assume( ensure_memory_is_valid( pAtRspPrefix, atRspCmdLen ) );
        pAtRspPrefix[ atRspCmdLen - 1 ] = '\0';
    }

    CellularAtReq_t atReq =
    {
        pAtCmd,
        atCmdType,
        pAtRspPrefix,
        respCallback,
        pData,
        atReqDataLen,
    };

    CellularAtDataReq_t dataReq =
    {
        pAtDataReqData,
        atDataReqDataLen,
        pSentDataLength,
        pEndPattern,
        endPatternLen
    };
    uint32_t atTimeoutMS;
    uint32_t dataTimeoutMS;

    pHandle = ( CellularContext_t * ) safeMalloc( sizeof( CellularContext_t ) );

    if( ( pHandle == NULL ) ||
        ( ( pHandle != NULL ) && ensure_memory_is_valid( pHandle, sizeof( CellularContext_t ) ) ) )
    {
        _Cellular_TimeoutAtcmdDataSendRequestWithCallback( pHandle,
                                                           atReq,
                                                           dataReq,
                                                           atTimeoutMS,
                                                           dataTimeoutMS );
    }
}
