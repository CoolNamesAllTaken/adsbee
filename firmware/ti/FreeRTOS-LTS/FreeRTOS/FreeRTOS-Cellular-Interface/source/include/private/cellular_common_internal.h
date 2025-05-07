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

#ifndef __CELLULAR_COMMON_INTERNAL_H__
#define __CELLULAR_COMMON_INTERNAL_H__

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* Cellular includes. */

#include "cellular_platform.h"
#ifndef CELLULAR_DO_NOT_USE_CUSTOM_CONFIG
    /* Include custom config file before other headers. */
    #include "cellular_config.h"
#endif
#include "cellular_config_defaults.h"
#include "cellular_pkthandler_internal.h"
#include "cellular_at_core.h"
#include "cellular_pktio_internal.h"

/*-----------------------------------------------------------*/

#define PKTIO_READ_BUFFER_SIZE     ( CELLULAR_CONFIG_PKTIO_READ_BUFFER_SIZE )
#define PKTIO_WRITE_BUFFER_SIZE    ( CELLULAR_AT_CMD_MAX_SIZE )

/*-----------------------------------------------------------*/

/**
 * @ingroup cellular_datatypes_enums
 * @brief Cellular network register URC type.
 */
typedef enum CellularNetworkRegType
{
    CELLULAR_REG_TYPE_CREG = 0, /**<  Register type for circuit switched network. */
    CELLULAR_REG_TYPE_CGREG,    /**<  Register type for GPRS packet networks. */
    CELLULAR_REG_TYPE_CEREG,    /**<  Register type for EPS(LTE) packet networks. */
    CELLULAR_REG_TYPE_MAX,      /**<  Maximum value for register type. */
    CELLULAR_REG_TYPE_UNKNOWN   /**<  Unknown value for register type. */
} CellularNetworkRegType_t;

/**
 * @ingroup cellular_datatypes_structs
 * @brief Represents different URC event callback registration function.
 */
typedef struct _callbackEvents
{
    CellularUrcNetworkRegistrationCallback_t networkRegistrationCallback;     /**<  Callback used to inform about a Network Registration URC event. */
    void * pNetworkRegistrationCallbackContext;                               /**<  The context passed to CellularUrcNetworkRegistrationCallback_t. */
    CellularUrcPdnEventCallback_t pdnEventCallback;                           /**<  Callback used to inform about PDN URC events. */
    void * pPdnEventCallbackContext;                                          /**<  The context passed to CellularUrcPdnEventCallback_t. */
    CellularUrcSignalStrengthChangedCallback_t signalStrengthChangedCallback; /**<  Callback used to inform about signal strength changed URC event. */
    void * pSignalStrengthChangedCallbackContext;                             /**<  The context passed to CellularUrcSignalStrengthChangedCallback_t. */
    CellularUrcGenericCallback_t genericCallback;                             /**<  Generic callback used to inform all other URC events. */
    void * pGenericCallbackContext;                                           /**<  The context passed to CellularUrcGenericCallback_t. */
    CellularModemEventCallback_t modemEventCallback;                          /**<  Callback used to inform about modem events. */
    void * pModemEventCallbackContext;                                        /**<  The context passed to CellularModemEventCallback_t. */
} _callbackEvents_t;

/**
 * @ingroup cellular_datatypes_structs
 * @brief Structure containing all the control plane parameters of Modem.
 */
typedef struct cellularAtData
{
    CellularRat_t rat;                               /**<  Device registered Radio Access Technology (Cat-M, Cat-NB, GPRS etc).  */
    CellularNetworkRegistrationStatus_t csRegStatus; /**<  CS (Circuit Switched) registration status (registered/searching/roaming etc.). */
    CellularNetworkRegistrationStatus_t psRegStatus; /**<  PS (Packet Switched) registration status (registered/searching/roaming etc.). */
    uint8_t csRejectType;                            /**<  CS Reject Type. 0 - 3GPP specific Reject Cause. 1 - Manufacture specific. */
    uint8_t csRejCause;                              /**<  Circuit Switch Reject cause. */
    uint8_t psRejectType;                            /**<  PS Reject Type. 0 - 3GPP specific Reject Cause. 1 - Manufacture specific. */
    uint8_t psRejCause;                              /**<  Packet Switch Reject cause. */
    uint32_t cellId;                                 /**<  Registered network operator cell Id. */
    uint16_t lac;                                    /**<  Registered network operator Location Area Code. */
    uint16_t rac;                                    /**<  Registered network operator Routing Area Code. */
    uint16_t tac;                                    /**<  Registered network operator Tracking Area Code. */
} cellularAtData_t;

/**
 * @ingroup cellular_datatypes_structs
 * @brief Parameters involved in maintaining the context for the modem.
 */
struct CellularContext
{
    const CellularCommInterface_t * pCommIntf; /**<  Communication interface for target specific. */

    /* Common library. */
    bool bLibOpened;                 /**<  CellularLib is currently open. */
    bool bLibShutdown;               /**<  CellularLib prematurely shut down. */
    bool bLibClosing;                /**<  Graceful shutdown in progress. */
    PlatformMutex_t libStatusMutex;  /**<  The mutex for changing lib status. */
    PlatformMutex_t libAtDataMutex;  /**<  The mutex for AT data in cellular context. */
    _callbackEvents_t cbEvents;      /**<  Call back functions registered to report events. */
    cellularAtData_t libAtData;      /**<  Global variables. */

    CellularTokenTable_t tokenTable; /**<  Token table to config pkthandler and pktio. */

    /* Packet handler. */
    PlatformMutex_t pktRequestMutex;                               /**<  The mutex for sending request. */
    PlatformMutex_t PktRespMutex;                                  /**<  The mutex for parsing the response from modem. */
    PlatformQueueHandle_t pktRespQueue;                            /**<  Message queue to send/receive response. */
    CellularATCommandResponseReceivedCallback_t pktRespCB;         /**<  Callback used to inform about the response of an AT command sent using Cellular_ATCommandRaw API. */
    CellularATCommandDataPrefixCallback_t pktDataPrefixCB;         /**<  Data prefix callback function for socket receive function. */
    void * pDataPrefixCBContext;                                   /**<  The pCallbackContext passed to CellularATCommandDataPrefixCallback_t. */
    CellularATCommandDataSendPrefixCallback_t pktDataSendPrefixCB; /**<  Data prefix callback function for socket send function. */
    void * pDataSendPrefixCBContext;                               /**<  The pCallbackContext passed to CellularATCommandDataSendPrefixCallback_t. */
    void * pPktUsrData;                                            /**<  The pData passed to CellularATCommandResponseReceivedCallback_t. */
    uint16_t PktUsrDataLen;                                        /**<  The dataLen passed to CellularATCommandResponseReceivedCallback_t. */
    const char * pCurrentCmd;                                      /**<  Debug purpose. */

    /* Packet IO. */
    bool bPktioUp;                                                     /**<  A flag to indicate if packet IO up. */
    CellularCommInterfaceHandle_t hPktioCommIntf;                      /**<  Opaque handle to comm interface. */
    PlatformEventGroupHandle_t pPktioCommEvent;                        /**<  Event group handler for common event in packet IO. */
    _pPktioShutdownCallback_t pPktioShutdownCB;                        /**<  Callback used to inform packet IO thread shutdown. */
    _pPktioHandlePacketCallback_t pPktioHandlepktCB;                   /**<  Callback used to inform packet received. */
    char pktioSendBuf[ PKTIO_WRITE_BUFFER_SIZE + 1 ];                  /**<  Buffer to send AT command to cellular devices. */
    char pktioReadBuf[ PKTIO_READ_BUFFER_SIZE + 1 ];                   /**<  Buffer to receive messages from cellular devices. */
    char * pPktioReadPtr;                                              /**<  Pointer points to unhandled read buffer. */
    const char * pRespPrefix;                                          /**<  The prefix to check in the response message. */
    char pktRespPrefixBuf[ CELLULAR_CONFIG_MAX_PREFIX_STRING_LENGTH ]; /**<  Buffer to store prefix string. */
    CellularATCommandType_t PktioAtCmdType;                            /**<  Represents AT Command type. */
    _atRespType_t recvdMsgType;                                        /**<  The received AT response type. */
    CellularUndefinedRespCallback_t undefinedRespCallback;             /**<  Undefined response callback function. */
    void * pUndefinedRespCBContext;                                    /**<  The pCallbackContext passed to CellularUndefinedRespCallback_t. */
    CellularInputBufferCallback_t inputBufferCallback;                 /**<  URC data preprocess callback function. */
    void * pInputBufferCallbackContext;                                /**<  The callback context passed to inputBufferCallback. */
    CellularATCommandResponse_t * pAtCmdResp;                          /**<  The AT command response pointer. */

    /* PktIo data handling. */
    uint32_t dataLength;                                              /**<  The data length in pLine. */
    uint32_t partialDataRcvdLen;                                      /**<  The valid data length need to be handled. */

    CellularSocketContext_t * pSocketData[ CELLULAR_NUM_SOCKET_MAX ]; /**<  All socket related information. */

    void * pModuleContext;                                            /**<  Module Context. */
};

/*-----------------------------------------------------------*/

/**
 * @brief Network registration respone parsing function.
 *
 * Parse the network registration response from AT command response or URC.
 * The result is stored in the pContext.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 * @param[in] pRegPayload The input string from AT command respnose or URC.
 * @param[in] isUrc The input string source type.
 * @param[in] regType The network registration type.
 *
 * @return CELLULAR_PKT_STATUS_OK if the operation is successful, otherwise an error
 * code indicating the cause of the error.
 */
CellularPktStatus_t _Cellular_ParseRegStatus( CellularContext_t * pContext,
                                              char * pRegPayload,
                                              bool isUrc,
                                              CellularNetworkRegType_t regType );

/**
 * @brief Initializes the AT data structures.
 *
 * Function is invokes to initialize the AT data structure during
 * very first initialization, upon deregistration and upon receiving
 * network reject during registration.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 * @param[in] mode Parameter that identifies which elements in Data Structure
 * to be initialized.
 */
void _Cellular_InitAtData( CellularContext_t * pContext,
                           uint32_t mode );

/**
 * @brief Create the AT data mutex.
 *
 * Create the mutex for AT data in cellular context.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 */
bool _Cellular_CreateAtDataMutex( CellularContext_t * pContext );

/**
 * @brief Destroy the AT data mutex.
 *
 * Destroy the mutex for AT data in cellular context.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 *
 */
void _Cellular_DestroyAtDataMutex( CellularContext_t * pContext );


/**
 * @brief Lock the AT data mutex.
 *
 * Lock the mutex for AT data in cellular context.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 */
void _Cellular_LockAtDataMutex( CellularContext_t * pContext );

/**
 * @brief Unlock the AT data mutex.
 *
 * Unlock the mutex for AT data in cellular context.
 *
 * @param[in] pContext The opaque cellular context pointer created by Cellular_Init.
 */
void _Cellular_UnlockAtDataMutex( CellularContext_t * pContext );

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef __CELLULAR_COMMON_INTERNAL_H__ */
