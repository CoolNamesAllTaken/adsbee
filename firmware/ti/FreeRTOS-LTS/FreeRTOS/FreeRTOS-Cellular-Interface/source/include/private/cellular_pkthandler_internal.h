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

#ifndef __CELLULAR_PKTHANDLER_INTERNAL_H__
#define __CELLULAR_PKTHANDLER_INTERNAL_H__

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

#ifndef CELLULAR_DO_NOT_USE_CUSTOM_CONFIG
    /* Include custom config file before other headers. */
    #include "cellular_config.h"
#endif
#include "cellular_config_defaults.h"
#include "cellular_types.h"
#include "cellular_common.h"
#include "cellular_pktio_internal.h"

/*-----------------------------------------------------------*/

/*  AT Command timeout for general AT commands. */
#define PACKET_REQ_TIMEOUT_MS    CELLULAR_COMMON_AT_COMMAND_TIMEOUT_MS

/*-----------------------------------------------------------*/

/**
 * @brief Create the packet request mutex.
 *
 * Create the mutex for packet request in cellular context.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 */
bool _Cellular_CreatePktRequestMutex( CellularContext_t * pContext );

/**
 * @brief Destroy the packet request mutex.
 *
 * Destroy the mutex for packet request in cellular context.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 */
void _Cellular_DestroyPktRequestMutex( CellularContext_t * pContext );

/**
 * @brief Create the packet response mutex.
 *
 * Create the mutex for packet response in cellular context.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 */
bool _Cellular_CreatePktResponseMutex( CellularContext_t * pContext );

/**
 * @brief Destroy the packet response mutex.
 *
 * Destroy the mutex for packet response in cellular context.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 */
void _Cellular_DestroyPktResponseMutex( CellularContext_t * pContext );

/**
 * @brief Packet handler init function.
 *
 * This function init the packet handler in FreeRTOS Cellular Library common.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 *
 * @return CELLULAR_PKT_STATUS_OK if the operation is successful, otherwise an error
 * code indicating the cause of the error.
 */
CellularPktStatus_t _Cellular_PktHandlerInit( CellularContext_t * pContext );

/**
 * @brief Packet handler cleanup function.
 *
 * This function cleanup the packet handler in FreeRTOS Cellular Library common.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 */
void _Cellular_PktHandlerCleanup( CellularContext_t * pContext );

/**
 * @brief Packet handler function.
 *
 * This function is the callback function of packet handler. It is called by packet IO thread.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 * @param[in] atRespType The AT response type from packet IO.
 * @param[in] pBuf The input data buffer from packet IO.
 *
 * @return CELLULAR_PKT_STATUS_OK if the operation is successful, otherwise an error
 * code indicating the cause of the error.
 */
CellularPktStatus_t _Cellular_HandlePacket( CellularContext_t * pContext,
                                            _atRespType_t atRespType,
                                            const void * pBuf );

/**
 * @brief The URC handler init function.
 *
 * This function setup the URC handler table query function.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 *
 * @return CELLULAR_PKT_STATUS_OK if the operation is successful, otherwise an error
 * code indicating the cause of the error.
 */
CellularPktStatus_t _Cellular_AtParseInit( const CellularContext_t * pContext );


/**
 * @brief Wrapper for sending the AT command to cellular modem.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 * @param[in] atReq The AT command data structure with send command response callback.
 * @param[in] timeoutMS The timeout value to wait for the response from cellular modem.
 *
 * @return CELLULAR_PKT_STATUS_OK if the operation is successful, otherwise an error
 * code indicating the cause of the error.
 */
CellularPktStatus_t _Cellular_PktHandler_AtcmdRequestWithCallback( CellularContext_t * pContext,
                                                                   CellularAtReq_t atReq,
                                                                   uint32_t timeoutMS );

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* __CELLULAR_PKTHANDLER_INTERNAL_H__ */
