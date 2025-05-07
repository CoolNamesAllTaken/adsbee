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
 * @file cellular_pktio_utest.c
 * @brief Unit tests for functions in cellular_pktio_internal.h.
 */

#include <string.h>
#include <stdbool.h>

#include "unity.h"

#include "cellular_config.h"
#include "cellular_config_defaults.h"

/* Include paths for public enums, structures, and macros. */
#include "cellular_platform.h"
#include "cellular_common_internal.h"
#include "cellular_pktio_internal.h"
#include "cellular_types.h"

#define PKTIO_EVT_MASK_STARTED                               ( 0x0001UL )
#define PKTIO_EVT_MASK_ABORT                                 ( 0x0002UL )
#define PKTIO_EVT_MASK_ABORTED                               ( 0x0004UL )
#define PKTIO_EVT_MASK_RX_DATA                               ( 0x0008UL )

#define CELLULAR_URC_TOKEN_STRING_INPUT                      "RDY"
#define CELLULAR_AT_CMD_MULTI_WO_PREFIX                      "\rTEST1\r\n_TEST2\n_TEST3\r\n\0TEST4"

#define CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_RESP         "+QIRD: 32\r123243154354364576587utrhfgdghfg"
#define CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING              "+QIRD:"

#define CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_LESS_RESP    "+QIRD: 32\r123243154354364576587utrhf"

#define CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_COMBO        "+QIRD: 32\r123243154354364576587utrhfgdghfg\r+QIRD: 32\r123243154354364576587utrhf"

#define CELLULAR_AT_WITH_PREFIX_STRING_RESP                  "+CGPADDR: 1,10.199.237.147"
#define CELLULAR_AT_WITH_PREFIX_STRING                       "+CGPADDR"

#define CELLULAR_AT_WO_PREFIX_STRING_RESP                    "GO OK"

#define CELLULAR_AT_TOKEN_SUCCESS                            "OK"
#define CELLULAR_AT_TOKEN_ERROR                              "NO CARRIER"
#define CELLULAR_AT_TOKEN_EXTRA                              "EXTRA_TOKEN_1"

#define CELLULAR_AT_UNDEFINED_STRING_RESP                    "1, CONNECT OK"

#define CELLULAR_URC_TOKEN_PREFIX_STRING_RESP                "+QIURC: \"recv\",0"
#define CELLULAR_URC_TOKEN_PREFIX_STRING                     "+QIURC"

#define DATA_PREFIX_STRING                                   "+QIRD:"
#define DATA_PREFIX_STRING_LENGTH                            ( 6U )

#define MAX_QIRD_STRING_PREFIX_STRING                        ( 14U )           /* The max data prefix string is "+QIRD: 1460\r\n" */

/* URC data callback test string. */
#define URC_DATA_CALLBACK_PREFIX_MISMATCH_STR                "+URC_PREFIX_MISMATCH:\r\n"
#define URC_DATA_CALLBACK_OTHER_ERROR_STR                    "+URC_OTHER_ERROR:\r\n"
#define URC_DATA_CALLBACK_INCORRECT_BUFFER_LEN_STR           "+URC_INCORRECT_LENGTH:\r\n"
#define URC_DATA_CALLBACK_MATCH_STR                          "+URC_DATA:123\r\n"
#define URC_DATA_CALLBACK_MATCH_STR_LENGTH                   15
#define URC_DATA_CALLBACK_LEFT_OVER_STR                      "+URC_STRING:123\r\n"

#define URC_DATA_CALLBACK_MATCH_STR_PREFIX                   "+URC_PART_DATA:"
#define URC_DATA_CALLBACK_MATCH_STR_PREFIX_LENGTH            15
#define URC_DATA_CALLBACK_MATCH_STR_PART1                    URC_DATA_CALLBACK_MATCH_STR_PREFIX "14\r\n1234"
#define URC_DATA_CALLBACK_MATCH_STR_PART2                    "1234567890\r\n"
#define URC_DATA_CALLBACK_MATCH_STR_PART_LENGTH              35

struct _cellularCommContext
{
    int test1;
    int test2;
    int test3;
};

typedef enum commIfRecvType
{
    COMM_IF_RECV_CUSTOM_STRING,
    COMM_IF_RECV_NORMAL
} commIfRecvType_t;

static uint16_t pktioEvtMask = 0x0000U;

static MockPlatformEventGroup_t evtGroup = { 0 };
static MockPlatformEventGroupHandle_t evtGroupHandle = NULL;

static int recvCount = 0;
static int testInfiniteLoop = 0;

static int eventDesiredCount = 0;
static uint16_t desiredPktioEvtMask = 0x0000U;

static bool threadReturn = true;

static int atCmdType = 0;

static int tokenTableType = 0;
static int isWrongString = 0;

static int setBitFromIsrReturn = 1;
static int higherPriorityTaskWokenReturn = 1;

static int isSendDataPrefixCbkSuccess = 1;
static int pktDataPrefixCBReturn = 0;

static int recvDataLenFail = 0;
static int recvCommFail = 0;
static int setpktDataPrefixCBReturn = 0;

static int32_t customCallbackContext = 0;

static commIfRecvType_t testCommIfRecvType = COMM_IF_RECV_NORMAL;
static char * pCommIntfRecvCustomString = NULL;
static void ( * pCommIntfRecvCustomStringCallback )( void ) = NULL;

static bool atCmdStatusUndefindTest = false;

static void * inputBufferCallbackContext = NULL;

static int dataUrcPktHandlerCallbackIsCalled = 0;
static char * pInputBufferPkthandlerString;

/* Try to Keep this map in Alphabetical order. */
/* FreeRTOS Cellular Common Library porting interface. */
/* coverity[misra_c_2012_rule_8_7_violation] */
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
const uint32_t CellularUrcHandlerTableSize = sizeof( CellularUrcHandlerTable ) / sizeof( CellularAtParseTokenMap_t );

const char * CellularSrcTokenErrorTable[] =
{ "ERROR", "BUSY", "NO CARRIER", "NO ANSWER", "NO DIALTONE", "ABORTED", "+CMS ERROR", "+CME ERROR", "SEND FAIL" };
const uint32_t CellularSrcTokenErrorTableSize = sizeof( CellularSrcTokenErrorTable ) / sizeof( char * );

const char * CellularSrcTokenSuccessTable[] =
{ "OK", "CONNECT", "SEND OK", ">" };
const uint32_t CellularSrcTokenSuccessTableSize = sizeof( CellularSrcTokenSuccessTable ) / sizeof( char * );

const char * CellularUrcTokenWoPrefixTable[] =
{ "NORMAL POWER DOWN", "PSM POWER DOWN", "RDY" };

const uint32_t CellularUrcTokenWoPrefixTableSize = sizeof( CellularUrcTokenWoPrefixTable ) / sizeof( char * );

const char * CellularSrcExtraTokenSuccessTable[] =
{ "EXTRA_TOKEN_1", "EXTRA_TOKEN_2", "EXTRA_TOKEN_3" };

const uint32_t CellularSrcExtraTokenSuccessTableSize = sizeof( CellularSrcExtraTokenSuccessTable ) / sizeof( char * );

CellularTokenTable_t tokenTable =
{
    .pCellularUrcHandlerTable              = CellularUrcHandlerTable,
    .cellularPrefixToParserMapSize         = CellularUrcHandlerTableSize,
    .pCellularSrcTokenErrorTable           = CellularSrcTokenErrorTable,
    .cellularSrcTokenErrorTableSize        = CellularSrcTokenErrorTableSize,
    .pCellularSrcTokenSuccessTable         = CellularSrcTokenSuccessTable,
    .cellularSrcTokenSuccessTableSize      = CellularSrcTokenSuccessTableSize,
    .pCellularUrcTokenWoPrefixTable        = CellularUrcTokenWoPrefixTable,
    .cellularUrcTokenWoPrefixTableSize     = CellularUrcTokenWoPrefixTableSize,
    .pCellularSrcExtraTokenSuccessTable    = CellularSrcExtraTokenSuccessTable,
    .cellularSrcExtraTokenSuccessTableSize = CellularSrcExtraTokenSuccessTableSize
};

CellularTokenTable_t tokenTableWithoutErrorTable =
{
    .pCellularUrcHandlerTable              = CellularUrcHandlerTable,
    .cellularPrefixToParserMapSize         = CellularUrcHandlerTableSize,
    .pCellularSrcTokenErrorTable           = NULL,
    .cellularSrcTokenErrorTableSize        = 0,
    .pCellularSrcTokenSuccessTable         = CellularSrcTokenSuccessTable,
    .cellularSrcTokenSuccessTableSize      = CellularSrcTokenSuccessTableSize,
    .pCellularUrcTokenWoPrefixTable        = CellularUrcTokenWoPrefixTable,
    .cellularUrcTokenWoPrefixTableSize     = CellularUrcTokenWoPrefixTableSize,
    .pCellularSrcExtraTokenSuccessTable    = CellularSrcExtraTokenSuccessTable,
    .cellularSrcExtraTokenSuccessTableSize = CellularSrcExtraTokenSuccessTableSize
};

CellularTokenTable_t tokenTableWithoutSuccessTable =
{
    .pCellularUrcHandlerTable              = CellularUrcHandlerTable,
    .cellularPrefixToParserMapSize         = CellularUrcHandlerTableSize,
    .pCellularSrcTokenErrorTable           = CellularSrcTokenErrorTable,
    .cellularSrcTokenErrorTableSize        = CellularSrcTokenErrorTableSize,
    .pCellularSrcTokenSuccessTable         = NULL,
    .cellularSrcTokenSuccessTableSize      = 0,
    .pCellularUrcTokenWoPrefixTable        = CellularUrcTokenWoPrefixTable,
    .cellularUrcTokenWoPrefixTableSize     = CellularUrcTokenWoPrefixTableSize,
    .pCellularSrcExtraTokenSuccessTable    = CellularSrcExtraTokenSuccessTable,
    .cellularSrcExtraTokenSuccessTableSize = CellularSrcExtraTokenSuccessTableSize
};

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    /*Assume no loops unless we specify in a test */
    setBitFromIsrReturn = 1;
    higherPriorityTaskWokenReturn = 1;
    isWrongString = 0;
    isSendDataPrefixCbkSuccess = 1;
    pktDataPrefixCBReturn = 0;
    recvDataLenFail = 0;
    tokenTableType = 0;
    recvCommFail = 0;
    setpktDataPrefixCBReturn = 0;
    testInfiniteLoop = 0;
    evtGroupHandle = &evtGroup;

    testCommIfRecvType = COMM_IF_RECV_NORMAL;
    pCommIntfRecvCustomString = NULL;
    pCommIntfRecvCustomStringCallback = NULL;
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

void MockPlatformMutex_Unlock( PlatformMutex_t * pMutex )
{
    ( void ) pMutex;
}

void MockPlatformMutex_Lock( PlatformMutex_t * pMutex )
{
    ( void ) pMutex;
}

void * mock_malloc( size_t size )
{
    return ( void * ) malloc( size );
}

uint16_t MockPlatformEventGroup_Delete( PlatformEventGroupHandle_t groupEvent )
{
    ( void ) groupEvent;
    return 0U;
}

uint16_t MockPlatformEventGroup_ClearBits( PlatformEventGroupHandle_t xEventGroup,
                                           TickType_t uxBitsToClear )
{
    ( void ) xEventGroup;
    ( void ) uxBitsToClear;
    return 0;
}

MockPlatformEventGroupHandle_t MockPlatformEventGroup_Create( void )
{
    return evtGroupHandle;
}

uint16_t MockPlatformEventGroup_WaitBits( PlatformEventGroupHandle_t groupEvent,
                                          EventBits_t uxBitsToWaitFor,
                                          BaseType_t xClearOnExit,
                                          BaseType_t xWaitForAllBits,
                                          TickType_t xTicksToWait )
{
    ( void ) groupEvent;
    ( void ) uxBitsToWaitFor;
    ( void ) xClearOnExit;
    ( void ) xWaitForAllBits;
    ( void ) xTicksToWait;

    if( testInfiniteLoop > 0 )
    {
        testInfiniteLoop--;
    }
    else if( recvCount == 0 )
    {
        return PKTIO_EVT_MASK_ABORT;
    }

    return pktioEvtMask;
}

uint16_t MockPlatformEventGroup_SetBits( PlatformEventGroupHandle_t groupEvent,
                                         EventBits_t event )
{
    ( void ) groupEvent;
    ( void ) event;

    return pktioEvtMask;
}

int32_t MockPlatformEventGroup_SetBitsFromISR( PlatformEventGroupHandle_t groupEvent,
                                               EventBits_t event,
                                               BaseType_t * pHigherPriorityTaskWoken )
{
    int32_t ret = pdFALSE;

    ( void ) groupEvent;
    ( void ) event;
    ( void ) pHigherPriorityTaskWoken;

    if( setBitFromIsrReturn == 0 )
    {
        ret = pdFALSE;
    }
    else
    {
        if( higherPriorityTaskWokenReturn == 1 )
        {
            *pHigherPriorityTaskWoken = pdTRUE;
        }
        else
        {
            *pHigherPriorityTaskWoken = pdFALSE;
        }

        ret = pdPASS;
    }

    return ret;
}

uint16_t MockPlatformEventGroup_GetBits( PlatformEventGroupHandle_t groupEvent )
{
    ( void ) groupEvent;

    if( eventDesiredCount > 0 )
    {
        eventDesiredCount--;
    }
    else
    {
        pktioEvtMask = desiredPktioEvtMask;
    }

    return pktioEvtMask;
}

bool Platform_CreateDetachedThread( void ( * threadRoutine )( void * pArgument ),
                                    void * pArgument,
                                    size_t priority,
                                    size_t stackSize )
{
    ( void ) pArgument;
    ( void ) priority;
    ( void ) stackSize;
    CellularContext_t * pContext = ( CellularContext_t * ) pArgument;

    if( threadReturn )
    {
        if( pContext )
        {
            pContext->PktioAtCmdType = atCmdType;
        }

        threadRoutine( pArgument );
    }

    return threadReturn;
}

static CellularCommInterfaceError_t prvCommIntfOpen( CellularCommInterfaceReceiveCallback_t receiveCallback,
                                                     void * pUserData,
                                                     CellularCommInterfaceHandle_t * pCommInterfaceHandle )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    ( void ) receiveCallback;
    CellularContext_t * pContext = ( CellularContext_t * ) pUserData;

    ( void ) pCommInterfaceHandle;

    commIntRet = receiveCallback( pContext, NULL );

    return commIntRet;
}

static CellularCommInterfaceError_t prvCommIntfOpenCallrecvCallbackNullContext( CellularCommInterfaceReceiveCallback_t receiveCallback,
                                                                                void * pUserData,
                                                                                CellularCommInterfaceHandle_t * pCommInterfaceHandle )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    ( void ) receiveCallback;
    CellularContext_t * pContext = ( CellularContext_t * ) pUserData;

    ( void ) pCommInterfaceHandle;

    memset( pContext, 0, sizeof( CellularContext_t ) );

    commIntRet = receiveCallback( pContext, NULL );

    return commIntRet;
}

static CellularCommInterfaceError_t prvCommIntfClose( CellularCommInterfaceHandle_t commInterfaceHandle )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    ( void ) commInterfaceHandle;

    return commIntRet;
}

static CellularCommInterfaceError_t prvCommIntfSend( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                     const uint8_t * pData,
                                                     uint32_t dataLength,
                                                     uint32_t timeoutMilliseconds,
                                                     uint32_t * pDataSentLength )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    ( void ) commInterfaceHandle;
    ( void ) pData;
    ( void ) dataLength;
    ( void ) timeoutMilliseconds;
    ( void ) pDataSentLength;

    *pDataSentLength = dataLength;

    return commIntRet;
}

static CellularCommInterfaceError_t prvCommIntfReceiveNormal( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                              uint8_t * pBuffer,
                                                              uint32_t bufferLength,
                                                              uint32_t timeoutMilliseconds,
                                                              uint32_t * pDataReceivedLength )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    ( void ) commInterfaceHandle;
    ( void ) pBuffer;
    ( void ) bufferLength;
    ( void ) timeoutMilliseconds;
    ( void ) pDataReceivedLength;
    char * pString;

    if( recvCount > 0 )
    {
        recvCount--;

        if( ( atCmdType == CELLULAR_AT_MULTI_DATA_WO_PREFIX ) ||
            ( atCmdType == CELLULAR_AT_MULTI_WITH_PREFIX ) )
        {
            if( recvCommFail == 0 )
            {
                pString = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_RESP;
            }
            else
            {
                pString = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING_COMBO;
            }
        }
        else if( atCmdType == CELLULAR_AT_MULTI_WO_PREFIX )
        {
            pString = CELLULAR_AT_CMD_MULTI_WO_PREFIX;
        }
        else if( atCmdType == CELLULAR_AT_NO_COMMAND )
        {
            /* Undefined response callback function. */
            if( recvCount % 3 == 0 )
            {
                if( customCallbackContext == 0 )
                {
                    /* Return the expected response to callback function. */
                    pString = CELLULAR_AT_UNDEFINED_STRING_RESP;
                }
                else
                {
                    /* Return the unexpected response to callback function. */
                    pString = CELLULAR_AT_CMD_MULTI_WO_PREFIX;
                }
            }
            else if( recvCount % 2 == 0 )
            {
                pString = CELLULAR_AT_WITH_PREFIX_STRING_RESP;
            }
            else
            {
                pString = CELLULAR_AT_CMD_MULTI_WO_PREFIX;
            }
        }
        else if( atCmdType == CELLULAR_AT_WITH_PREFIX )
        {
            if( recvCount > 0 )
            {
                pString = CELLULAR_AT_WITH_PREFIX_STRING_RESP;
            }
            else
            {
                pString = CELLULAR_AT_TOKEN_SUCCESS;
            }
        }
        else if( atCmdType == CELLULAR_AT_WO_PREFIX )
        {
            if( tokenTableType == 0 )
            {
                pString = CELLULAR_AT_WO_PREFIX_STRING_RESP;
            }
            else if( tokenTableType == 1 ) /* success token. */
            {
                pString = CELLULAR_AT_TOKEN_SUCCESS;
            }
            else if( tokenTableType == 2 ) /* error token. */
            {
                pString = CELLULAR_AT_TOKEN_ERROR;
            }
            else if( tokenTableType == 3 ) /* extra token. */
            {
                pString = CELLULAR_AT_TOKEN_EXTRA;
            }
            else if( tokenTableType == 4 ) /* string w/o terminator. */
            {
                pString = ( char * ) malloc( sizeof( char ) * 4 );
                pString[ 0 ] = 't';
                pString[ 1 ] = 'h';
                pString[ 2 ] = 'i';
                pString[ 3 ] = 's';
            }
            else if( tokenTableType == 5 ) /* string w/o terminator. */
            {
                pString = ( char * ) malloc( sizeof( char ) * 4 );
                pString[ 0 ] = '\r';
                pString[ 1 ] = '\n';
                pString[ 2 ] = '\r';
                pString[ 3 ] = 'A';
            }
        }
        else if( atCmdType == CELLULAR_AT_NO_RESULT )
        {
            pString = CELLULAR_URC_TOKEN_STRING_INPUT;
        }
        else
        {
            pString = CELLULAR_URC_TOKEN_PREFIX_STRING_RESP;
        }

        if( tokenTableType == 4 )
        {
            strncpy( ( char * ) pBuffer, pString, strlen( pString ) );
            *pDataReceivedLength = strlen( pString );
        }
        else if( tokenTableType == 5 )
        {
            strncpy( ( char * ) pBuffer, pString, 4 );
            *pDataReceivedLength = 2;
        }
        else if( recvCommFail > 0 )
        {
            strncpy( ( char * ) pBuffer, pString, strlen( pString ) - 2 );
            *pDataReceivedLength = strlen( ( char * ) pBuffer ) - 2;
        }
        else
        {
            strncpy( ( char * ) pBuffer, pString, strlen( pString ) + 1 );
            *pDataReceivedLength = strlen( pString ) + 1;
        }
    }
    else
    {
        *pDataReceivedLength = 0;
    }

    return commIntRet;
}


static CellularCommInterfaceError_t prvCommIntfReceiveCustomString( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                                    uint8_t * pBuffer,
                                                                    uint32_t bufferLength,
                                                                    uint32_t timeoutMilliseconds,
                                                                    uint32_t * pDataReceivedLength )
{
    CellularCommInterfaceError_t commIntRet = IOT_COMM_INTERFACE_SUCCESS;

    ( void ) commInterfaceHandle;
    ( void ) pBuffer;
    ( void ) bufferLength;
    ( void ) timeoutMilliseconds;
    ( void ) pDataReceivedLength;

    if( recvCount > 0 )
    {
        recvCount--;

        ( void ) strncpy( ( char * ) pBuffer, pCommIntfRecvCustomString, bufferLength );
        *pDataReceivedLength = strlen( pCommIntfRecvCustomString );

        if( pCommIntfRecvCustomStringCallback != NULL )
        {
            pCommIntfRecvCustomStringCallback();
        }
    }
    else
    {
        *pDataReceivedLength = 0;
    }

    return commIntRet;
}

static CellularCommInterfaceError_t prvCommIntfReceive( CellularCommInterfaceHandle_t commInterfaceHandle,
                                                        uint8_t * pBuffer,
                                                        uint32_t bufferLength,
                                                        uint32_t timeoutMilliseconds,
                                                        uint32_t * pDataReceivedLength )
{
    CellularCommInterfaceError_t commIfRet;

    if( testCommIfRecvType == COMM_IF_RECV_CUSTOM_STRING )
    {
        commIfRet = prvCommIntfReceiveCustomString( commInterfaceHandle,
                                                    pBuffer,
                                                    bufferLength,
                                                    timeoutMilliseconds,
                                                    pDataReceivedLength );
    }
    else
    {
        commIfRet = prvCommIntfReceiveNormal( commInterfaceHandle,
                                              pBuffer,
                                              bufferLength,
                                              timeoutMilliseconds,
                                              pDataReceivedLength );
    }

    return commIfRet;
}

static CellularCommInterface_t CellularCommInterface =
{
    .open  = prvCommIntfOpen,
    .send  = prvCommIntfSend,
    .recv  = prvCommIntfReceive,
    .close = prvCommIntfClose
};

static void _shutdownCallback( CellularContext_t * pContext )
{
    if( pContext != NULL )
    {
        pContext->bLibShutdown = true;
    }
}

static CellularPktStatus_t prvUndefinedHandlePacket( CellularContext_t * pContext,
                                                     _atRespType_t atRespType,
                                                     const void * pBuf )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    const CellularATCommandResponse_t * pAtResp = NULL;
    char * pLine = NULL;

    if( pContext != NULL )
    {
        switch( atRespType )
        {
            case AT_SOLICITED:
                pAtResp = ( const CellularATCommandResponse_t * ) pBuf;
                atCmdStatusUndefindTest = pAtResp->status;
                break;

            case AT_UNSOLICITED:
                break;

            default:
                pLine = ( char * ) pBuf;

                /* undefined message received. Try to handle it with cellular module
                 * specific handler. */
                if( pContext->undefinedRespCallback == NULL )
                {
                    pktStatus = CELLULAR_PKT_STATUS_INVALID_DATA;
                }
                else
                {
                    pktStatus = pContext->undefinedRespCallback( pContext->pUndefinedRespCBContext, pLine );

                    if( pktStatus != CELLULAR_PKT_STATUS_OK )
                    {
                        pktStatus = CELLULAR_PKT_STATUS_INVALID_DATA;
                    }
                }

                break;
        }
    }
    else
    {
        pktStatus = CELLULAR_PKT_STATUS_INVALID_HANDLE;
    }

    return pktStatus;
}

CellularPktStatus_t PktioHandlePacketCallback_t( CellularContext_t * pContext,
                                                 _atRespType_t atRespType,
                                                 const void * pBuffer )
{
    CellularPktStatus_t status = CELLULAR_PKT_STATUS_OK;

    ( void ) pContext;
    ( void ) atRespType;
    ( void ) pBuffer;
    ( void ) status;

    return status;
}

CellularPktStatus_t cellularATCommandDataPrefixCallback( void * pCallbackContext,
                                                         char * pLine,
                                                         uint32_t lineLength,
                                                         char ** ppDataStart,
                                                         uint32_t * pDataLength )
{
    char * pDataStart = NULL;
    uint32_t tempStrlen = 0;
    int32_t tempValue = 0;
    CellularATError_t atResult = CELLULAR_AT_SUCCESS;
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    uint32_t i = 0;
    char pLocalLine[ MAX_QIRD_STRING_PREFIX_STRING + 1 ] = "\0";
    uint32_t localLineLength = MAX_QIRD_STRING_PREFIX_STRING > lineLength ? lineLength : MAX_QIRD_STRING_PREFIX_STRING;

    ( void ) pCallbackContext;

    if( pktDataPrefixCBReturn == 1 )
    {
        return CELLULAR_PKT_STATUS_SIZE_MISMATCH;
    }
    else if( pktDataPrefixCBReturn > 1 )
    {
        return CELLULAR_PKT_STATUS_BAD_PARAM;
    }

    if( ( pLine == NULL ) || ( ppDataStart == NULL ) || ( pDataLength == NULL ) )
    {
        pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
    }
    else
    {
        /* Check if the message is a data response. */
        if( strncmp( pLine, DATA_PREFIX_STRING, DATA_PREFIX_STRING_LENGTH ) == 0 )
        {
            strncpy( pLocalLine, pLine, MAX_QIRD_STRING_PREFIX_STRING );
            pLocalLine[ MAX_QIRD_STRING_PREFIX_STRING ] = '\0';
            pDataStart = pLocalLine;

            /* Add a '\0' char at the end of the line. */
            for( i = 0; i < localLineLength; i++ )
            {
                if( ( pDataStart[ i ] == '\r' ) || ( pDataStart[ i ] == '\n' ) )
                {
                    pDataStart[ i ] = '\0';
                    break;
                }
            }

            if( i == localLineLength )
            {
                pDataStart = NULL;
            }
        }

        if( pDataStart != NULL )
        {
            tempStrlen = strlen( "+QIRD:" );
            atResult = Cellular_ATStrtoi( &pDataStart[ tempStrlen ], 10, &tempValue );

            if( ( atResult == CELLULAR_AT_SUCCESS ) && ( tempValue >= 0 ) &&
                ( tempValue <= ( int32_t ) CELLULAR_MAX_RECV_DATA_LEN ) )
            {
                /* Save the start of data point in pTemp. */
                if( ( uint32_t ) ( strnlen( pDataStart, MAX_QIRD_STRING_PREFIX_STRING ) + 2 ) > lineLength )
                {
                    /* More data is required. */
                    *pDataLength = 0;
                    pDataStart = NULL;
                    pktStatus = CELLULAR_PKT_STATUS_SIZE_MISMATCH;
                }
                else
                {
                    pDataStart = &pLine[ strnlen( pDataStart, MAX_QIRD_STRING_PREFIX_STRING ) ];
                    pDataStart[ 0 ] = '\0';
                    pDataStart = &pDataStart[ 2 ];
                    *pDataLength = ( uint32_t ) tempValue;
                }
            }
            else
            {
                *pDataLength = 0;
                pDataStart = NULL;
            }
        }

        *ppDataStart = pDataStart;

        if( ( *pDataLength > 2 ) && ( recvDataLenFail > 0 ) )
        {
            *pDataLength -= 2;
        }
    }

    if( setpktDataPrefixCBReturn )
    {
        pktDataPrefixCBReturn = 1;
    }

    return pktStatus;
}

CellularPktStatus_t sendDataPrefix( void * pCallbackContext,
                                    char * pLine,
                                    uint32_t * pBytesRead )
{
    ( void ) pCallbackContext;
    ( void ) pLine;
    ( void ) pBytesRead;

    if( isSendDataPrefixCbkSuccess == 1 )
    {
        isSendDataPrefixCbkSuccess = 0;
        return CELLULAR_PKT_STATUS_OK;
    }
    else
    {
        isSendDataPrefixCbkSuccess = 1;
        return CELLULAR_PKT_STATUS_BAD_PARAM;
    }
}

CellularPktStatus_t undefinedRespCallback( void * pCallbackContext,
                                           const char * pLine )
{
    CellularPktStatus_t undefineReturnStatus = CELLULAR_PKT_STATUS_OK;

    /* Verify pCallbackContext. */
    TEST_ASSERT_EQUAL_PTR( &customCallbackContext, pCallbackContext );

    /* Verify pLine. */
    if( strcmp( CELLULAR_AT_UNDEFINED_STRING_RESP, pLine ) == 0 )
    {
        *( ( int32_t * ) pCallbackContext ) = 1;
        undefineReturnStatus = CELLULAR_PKT_STATUS_OK;
    }
    else
    {
        *( ( int32_t * ) pCallbackContext ) = 0;
        undefineReturnStatus = CELLULAR_PKT_STATUS_FAILURE;
    }

    return undefineReturnStatus;
}

static CellularPktStatus_t cellularInputBufferCallback( void * pInputBufferCallbackContext,
                                                        char * pBuffer,
                                                        uint32_t bufferLength,
                                                        uint32_t * pInputBufferLength )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_FAILURE;

    /* Verify the callback context. */
    TEST_ASSERT_EQUAL( inputBufferCallbackContext, pInputBufferCallbackContext );

    /* Verify the callback context. */
    if( strncmp( pBuffer, URC_DATA_CALLBACK_PREFIX_MISMATCH_STR, bufferLength ) == 0 )
    {
        *pInputBufferLength = 0;
        pktStatus = CELLULAR_PKT_STATUS_PREFIX_MISMATCH;
    }
    else if( strncmp( pBuffer, URC_DATA_CALLBACK_OTHER_ERROR_STR, bufferLength ) == 0 )
    {
        *pInputBufferLength = 0;
        pktStatus = CELLULAR_PKT_STATUS_FAILURE;
    }
    else if( strncmp( pBuffer, URC_DATA_CALLBACK_INCORRECT_BUFFER_LEN_STR, bufferLength ) == 0 )
    {
        /* Return incorrect buffer length. */
        *pInputBufferLength = bufferLength + 1;
        pktStatus = CELLULAR_PKT_STATUS_OK;
    }
    else if( strncmp( pBuffer, URC_DATA_CALLBACK_MATCH_STR, URC_DATA_CALLBACK_MATCH_STR_LENGTH ) == 0 )
    {
        *pInputBufferLength = 15;
        pktStatus = CELLULAR_PKT_STATUS_OK;
    }
    else if( strncmp( pBuffer, URC_DATA_CALLBACK_MATCH_STR_PREFIX, URC_DATA_CALLBACK_MATCH_STR_PREFIX_LENGTH ) == 0 )
    {
        if( bufferLength < URC_DATA_CALLBACK_MATCH_STR_PART_LENGTH )
        {
            pktStatus = CELLULAR_PKT_STATUS_SIZE_MISMATCH;
        }
        else if( bufferLength == URC_DATA_CALLBACK_MATCH_STR_PART_LENGTH )
        {
            *pInputBufferLength = URC_DATA_CALLBACK_MATCH_STR_PART_LENGTH;
            pktStatus = CELLULAR_PKT_STATUS_OK;
        }
    }

    return pktStatus;
}

static CellularPktStatus_t prvDataUrcPktHandlerCallback( CellularContext_t * pContext,
                                                         _atRespType_t atRespType,
                                                         const void * pBuffer )
{
    int compareResult;

    ( void ) pContext;

    dataUrcPktHandlerCallbackIsCalled = 1;

    /* Verify the atRespType is AT_UNSOLICITED. */
    TEST_ASSERT_EQUAL( AT_UNSOLICITED, atRespType );

    /* Verify the pBuffer contains the same string passed in the test. */
    compareResult = strncmp( pBuffer, pInputBufferPkthandlerString, strlen( pBuffer ) );
    TEST_ASSERT_EQUAL( 0, compareResult );

    return CELLULAR_PKT_STATUS_OK;
}

static void prvInputBufferCommIntfRecvCallback( void )
{
    pCommIntfRecvCustomString = URC_DATA_CALLBACK_MATCH_STR_PART2;
}

static CellularPktStatus_t prvPacketCallbackError( CellularContext_t * pContext,
                                                   _atRespType_t atRespType,
                                                   const void * pBuffer )
{
    const CellularATCommandResponse_t * pAtResp = ( const CellularATCommandResponse_t * ) pBuffer;

    ( void ) pContext;

    /* Verify the response type is AT_SOLICITED. */
    TEST_ASSERT_EQUAL( AT_SOLICITED, atRespType );

    /* Verify that no item is added to the response. */
    TEST_ASSERT_NOT_EQUAL( NULL, pAtResp );
    TEST_ASSERT_EQUAL( NULL, pAtResp->pItm );

    /* Verify that the response indicate error. */
    TEST_ASSERT_EQUAL( false, pAtResp->status );

    return CELLULAR_PKT_STATUS_OK;
}

static CellularPktStatus_t prvPacketCallbackSuccess( CellularContext_t * pContext,
                                                     _atRespType_t atRespType,
                                                     const void * pBuffer )
{
    const CellularATCommandResponse_t * pAtResp = ( const CellularATCommandResponse_t * ) pBuffer;
    int cmpResult;

    ( void ) pContext;

    /* Verify the response type is AT_SOLICITED. */
    TEST_ASSERT_EQUAL( AT_SOLICITED, atRespType );

    /* Verify the string is the same as expected. */
    TEST_ASSERT_NOT_EQUAL( NULL, pAtResp );
    TEST_ASSERT_NOT_EQUAL( NULL, pAtResp->pItm );
    TEST_ASSERT_NOT_EQUAL( NULL, pAtResp->pItm->pLine );
    cmpResult = strncmp( pAtResp->pItm->pLine, pCommIntfRecvCustomString, strlen( pAtResp->pItm->pLine ) );
    TEST_ASSERT_EQUAL( 0, cmpResult );

    /* Verify that the response indicate error. */
    TEST_ASSERT_EQUAL( true, pAtResp->status );

    return CELLULAR_PKT_STATUS_OK;
}

/* ========================================================================== */

/**
 * @brief Test that any NULL parameter causes _Cellular_PktioInit to return CELLULAR_PKT_STATUS_INVALID_HANDLE.
 */
void test__Cellular_PktioInit_Invalid_Param( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;

    /* Check that CELLULAR_PKT_STATUS_INVALID_HANDLE is returned. */
    pktStatus = _Cellular_PktioInit( NULL, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test thread comm open fail due to the return false value of xHigherPriorityTaskWoken by
 * PlatformEventGroup_SetBitsFromISR in _Cellular_PktRxCallBack function called by _pktioReadThread.
 * Because the thread is called successfully, and that operation is in the thread. Thus _Cellular_PktioInit
 * will still return CELLULAR_PKT_STATUS_OK. But we could check the calling graph in coverage report.
 */
void test__Cellular_PktioInit_Thread_ReceiveCallback_xHigherPriorityTaskWoken_Fail( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t commIntf;

    memcpy( ( void * ) &commIntf, ( void * ) &CellularCommInterface, sizeof( CellularCommInterface_t ) );
    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = &commIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Make PlatformEventGroup_SetBitsFromISR return true. */
    setBitFromIsrReturn = 1;
    higherPriorityTaskWokenReturn = 0;

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread comm open fail due to the return false value from PlatformEventGroup_SetBitsFromISR
 * in _Cellular_PktRxCallBack function called by _pktioReadThread.
 * Because the thread is called successfully, and that operation is in the thread. Thus _Cellular_PktioInit
 * will still return CELLULAR_PKT_STATUS_OK. But we could check the calling graph in coverage report.
 */
void test__Cellular_PktioInit_Thread_ReceiveCallback_PlatformEventGroup_SetBitsFromISR_Fail( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t commIntf;

    memcpy( ( void * ) &commIntf, ( void * ) &CellularCommInterface, sizeof( CellularCommInterface_t ) );
    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = &commIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Make PlatformEventGroup_SetBitsFromISR return false. */
    setBitFromIsrReturn = 0;
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread comm open fail due to null context failed called by receiveCallback in comm open function.
 */
void test__Cellular_PktioInit_Thread_Comm_Open_ReceiveCallback_Null_Context_Fail( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t commIntf;

    memcpy( ( void * ) &commIntf, ( void * ) &CellularCommInterface, sizeof( CellularCommInterface_t ) );
    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = &commIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Assign the comm interface to pContext. */
    commIntf.open = prvCommIntfOpenCallrecvCallbackNullContext;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving abort event for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Receive_Abort_Event( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the abort event. */
    pktioEvtMask = PKTIO_EVT_MASK_ABORT;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread empty else case in while-loop for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Empty_Case( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test PKTIO_EVT_MASK_STARTED event for _pktioReadThread empty else case. */
    pktioEvtMask = PKTIO_EVT_MASK_STARTED;
    testInfiniteLoop = 1;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test that string w/o terminator for else case of function _findLineInStream.
 */
void test__Cellular_PktioInit_String_Wo_Terminator( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_WO_PREFIX;
    tokenTableType = 4;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pRespPrefix = NULL;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test that string w/ new line in the beginging.
 */
void test__Cellular_PktioInit_String_With_NewLine( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_WO_PREFIX;
    tokenTableType = 5;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pRespPrefix = NULL;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_MULTI_DATA_WO_PREFIX resp for
 * _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_MULTI_DATA_WO_PREFIX( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;
    context.pRespPrefix = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING;

    /* Test the rx_data event with CELLULAR_AT_MULTI_DATA_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 2;
    atCmdType = CELLULAR_AT_MULTI_DATA_WO_PREFIX;

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event calling pktDataPrefixCB with CELLULAR_PKT_STATUS_SIZE_MISMATCH return.
 * Because the thread is called successfully, and that operation is in the thread. Thus _Cellular_PktioInit
 * will still return CELLULAR_PKT_STATUS_OK. But we could check the calling graph in coverage report.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_pktDataPrefixCB_CELLULAR_PKT_STATUS_SIZE_MISMATCH_FAILURE( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;

    /* Test the rx_data event with CELLULAR_AT_MULTI_DATA_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    atCmdType = CELLULAR_AT_MULTI_DATA_WO_PREFIX;
    recvCount = 2;

    /* set pktDataPrefixCB return CELLULAR_PKT_STATUS_SIZE_MISMATCH. */
    pktDataPrefixCBReturn = 1;
    context.pRespPrefix = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event calling pktDataPrefixCB with CELLULAR_PKT_STATUS_BAD_PARAM return.
 * Because the thread is called successfully, and that operation is in the thread. Thus _Cellular_PktioInit
 * will still return CELLULAR_PKT_STATUS_OK. But we could check the calling graph in coverage report.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_pktDataPrefixCB_CELLULAR_PKT_STATUS_BAD_PARAM_FAILURE( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;
    context.pRespPrefix = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING;

    /* Test the rx_data event with CELLULAR_AT_MULTI_DATA_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    atCmdType = CELLULAR_AT_MULTI_DATA_WO_PREFIX;
    recvCount = 2;

    /* set pktDataPrefixCB return CELLULAR_PKT_STATUS_BAD_PARAM. */
    pktDataPrefixCBReturn = 2;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event calling pktDataPrefixCB with short byte read return.
 * Because the thread is called successfully, and that operation is in the thread. Thus _Cellular_PktioInit
 * will still return CELLULAR_PKT_STATUS_OK. But we could check the calling graph in coverage report.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_pktDataPrefixCB_RECV_DATA_LENGTH_FAILURE( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;
    context.pRespPrefix = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING;

    /* Test the rx_data event with CELLULAR_AT_MULTI_DATA_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    atCmdType = CELLULAR_AT_MULTI_DATA_WO_PREFIX;
    recvCount = 2;

    pktDataPrefixCBReturn = 0;
    /* Mock recv data length failure. */
    recvDataLenFail = 1;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event calling _handleLeftoverBuffer case.
 * Because the thread is called successfully, and that operation is in the thread. Thus _Cellular_PktioInit
 * will still return CELLULAR_PKT_STATUS_OK. But we could check the calling graph in coverage report.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_pktDataPrefixCB__handleLeftoverBuffer_Case( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;
    context.pRespPrefix = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING;
    atCmdType = CELLULAR_AT_MULTI_DATA_WO_PREFIX;

    /* Test the rx_data event with CELLULAR_AT_MULTI_DATA_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;

    recvCount = 2;
    pktDataPrefixCBReturn = 0;
    recvDataLenFail = 1;
    /* Call _Cellular_PktioInit to get partialDataRcvdLen. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );

    /* handle _handleLeftoverBuffer function case. */
    recvCount = 23;
    recvCommFail = 1;
    pktDataPrefixCBReturn = 1;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test that pAtResp null case in function _Cellular_ReadLine.
 * Because the thread is called successfully, and that operation is in the thread. Thus _Cellular_PktioInit
 * will still return CELLULAR_PKT_STATUS_OK. But we could check the calling graph in coverage report.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_pktDataPrefixCB__Test( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;
    context.pRespPrefix = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING;
    atCmdType = CELLULAR_AT_MULTI_DATA_WO_PREFIX;

    /* Test the rx_data event with CELLULAR_AT_MULTI_DATA_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;

    recvCount = 3;
    pktDataPrefixCBReturn = 0;
    setpktDataPrefixCBReturn = 1;
    recvDataLenFail = 1;
    /* Call _Cellular_PktioInit to get partialDataRcvdLen. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );

    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief _preprocessInputBuffer - inputBufferCallback returns CELLULAR_PKT_STATUS_PREFIX_MISMATCH.
 *
 * CELLULAR_PKT_STATUS_PREFIX_MISMATCH is returned by the callback function. Verify
 * that RX thread keep process the data.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( pktStatus == CELLULAR_PKT_STATUS_PREFIX_MISMATCH )
 * {
 *     keepProcess = true;
 * }
 * @endcode
 * ( pktStatus == CELLULAR_PKT_STATUS_PREFIX_MISMATCH ) is true.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event__preprocessInputBuffer_prefix_mismatch( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* RX data event for RX thread. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;

    /* Setup the URC data callback for testing. */
    context.inputBufferCallback = cellularInputBufferCallback;
    context.pInputBufferCallbackContext = NULL;
    recvCount = 1;
    atCmdType = CELLULAR_AT_NO_RESULT;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = URC_DATA_CALLBACK_PREFIX_MISMATCH_STR;
    pInputBufferPkthandlerString = URC_DATA_CALLBACK_PREFIX_MISMATCH_STR;
    dataUrcPktHandlerCallbackIsCalled = 0;

    /* API call. */
    pktStatus = _Cellular_PktioInit( &context, prvDataUrcPktHandlerCallback );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* This test verifies that the pktio rx thread will continue to process the
     * data in the callback function. */
    TEST_ASSERT_EQUAL( 1, dataUrcPktHandlerCallbackIsCalled );
}

/**
 * @brief _preprocessInputBuffer - inputBufferCallback returns other errors.
 *
 * Other error is returned by the callback function. Verify that RX thread stop
 * processing the data.
 *
 * <b>Coverage</b>
 * @code{c}
 * else if( pktStatus != CELLULAR_PKT_STATUS_OK )
 * {
 *     ...
 *     ( void ) memset( pContext->pktioReadBuf, 0, PKTIO_READ_BUFFER_SIZE + 1U );
 *     pContext->pPktioReadPtr = NULL;
 *     pContext->partialDataRcvdLen = 0;
 *     keepProcess = false;
 * }
 * @endcode
 * ( pktStatus != CELLULAR_PKT_STATUS_OK ) is true.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event__preprocessInputBuffer_other_error( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* RX data event for RX thread. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;

    /* Setup the URC data callback for testing. */
    context.inputBufferCallback = cellularInputBufferCallback;
    context.pInputBufferCallbackContext = NULL;
    recvCount = 1;
    atCmdType = CELLULAR_AT_NO_RESULT;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = URC_DATA_CALLBACK_OTHER_ERROR_STR;
    dataUrcPktHandlerCallbackIsCalled = 0;

    /* API call. */
    pktStatus = _Cellular_PktioInit( &context, prvDataUrcPktHandlerCallback );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* The pkthandler callback should not be called. */
    TEST_ASSERT_EQUAL( 0, dataUrcPktHandlerCallbackIsCalled );
}

/**
 * @brief _preprocessInputBuffer - inputBufferCallback returns incorrect buffer length.
 *
 * Incorrect buffer length is returned by the callback function. Verify that RX
 * thread stop processing the data.
 *
 * <b>Coverage</b>
 * @code{c}
 * else if( bufferLength > *pBytesRead )
 * {
 *     ...
 *     ( void ) memset( pContext->pktioReadBuf, 0, PKTIO_READ_BUFFER_SIZE + 1U );
 *     pContext->pPktioReadPtr = NULL;
 *     pContext->partialDataRcvdLen = 0;
 *     keepProcess = false;
 * }
 * @endcode
 * ( bufferLength > *pBytesRead ) is true.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event__preprocessInputBuffer_incorrect_buffer_length( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* RX data event for RX thread. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;

    /* Setup the URC data callback for testing. */
    context.inputBufferCallback = cellularInputBufferCallback;
    context.pInputBufferCallbackContext = NULL;
    recvCount = 1;
    atCmdType = CELLULAR_AT_NO_RESULT;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = URC_DATA_CALLBACK_INCORRECT_BUFFER_LEN_STR;
    dataUrcPktHandlerCallbackIsCalled = 0;

    /* API call. */
    pktStatus = _Cellular_PktioInit( &context, prvDataUrcPktHandlerCallback );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* The pkthandler callback should not be called. */
    TEST_ASSERT_EQUAL( 0, dataUrcPktHandlerCallbackIsCalled );
}

/**
 * @brief _preprocessInputBuffer - inputBufferCallback returns success.
 *
 * Callback function successfully handle the URC data line. Verify that RX
 * thread keep processing the data after the URC data.
 *
 * <b>Coverage</b>
 * @code{c}
 * else
 * {
 *     ...
 *     pTempLine = &pTempLine[ bufferLength ];
 *     *pLine = pTempLine;
 *     pContext->pPktioReadPtr = *pLine;
 *
 *     *pBytesRead = *pBytesRead - bufferLength;
 * }
 * @endcode
 * The else case.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event__preprocessInputBuffer_success( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* RX data event for RX thread. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;

    /* Setup the URC data callback for testing. */
    context.inputBufferCallback = cellularInputBufferCallback;
    context.pInputBufferCallbackContext = NULL;
    recvCount = 1;
    atCmdType = CELLULAR_AT_NO_RESULT;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = URC_DATA_CALLBACK_MATCH_STR ""URC_DATA_CALLBACK_LEFT_OVER_STR;
    pInputBufferPkthandlerString = URC_DATA_CALLBACK_LEFT_OVER_STR;
    dataUrcPktHandlerCallbackIsCalled = 0;

    /* API call. */
    pktStatus = _Cellular_PktioInit( &context, prvDataUrcPktHandlerCallback );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* The pkthandler callback should not be called. */
    TEST_ASSERT_EQUAL( 1, dataUrcPktHandlerCallbackIsCalled );
}

/**
 * @brief _preprocessInputBuffer - inputBufferCallback returns size mismatch.
 *
 * Callback function returns size mismatch. Verify that the RX thread stop processing
 * the data and receive more data from comm interface. The callback function will be
 * called again with more data.
 *
 * <b>Coverage</b>
 * @code{c}
 * else if( pktStatus == CELLULAR_PKT_STATUS_SIZE_MISMATCH )
 * {
 *     ...
 *     pContext->pPktioReadPtr = pTempLine;
 *     pContext->partialDataRcvdLen = *pBytesRead;
 *     keepProcess = false;
 * }
 * @endcode
 * ( pktStatus == CELLULAR_PKT_STATUS_SIZE_MISMATCH ) is true.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event__preprocessInputBuffer_size_mismatch( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* RX data event for RX thread. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;

    /* Setup the URC data callback for testing. */
    context.inputBufferCallback = cellularInputBufferCallback;
    context.pInputBufferCallbackContext = NULL;
    recvCount = 2;
    atCmdType = CELLULAR_AT_NO_RESULT;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = URC_DATA_CALLBACK_MATCH_STR_PART1;
    pCommIntfRecvCustomStringCallback = prvInputBufferCommIntfRecvCallback;
    dataUrcPktHandlerCallbackIsCalled = 0;

    /* API call. */
    pktStatus = _Cellular_PktioInit( &context, prvDataUrcPktHandlerCallback );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* The pkthandler callback should not be called. */
    TEST_ASSERT_EQUAL( 0, dataUrcPktHandlerCallbackIsCalled );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_MULTI_WITH_PREFIX resp for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_MULTI_WITH_PREFIX( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_MULTI_WITH_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 2;
    atCmdType = CELLULAR_AT_MULTI_WITH_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;
    context.pRespPrefix = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_MULTI_WO_PREFIX resp for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_MULTI_WO_PREFIX( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_MULTI_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 2;
    atCmdType = CELLULAR_AT_MULTI_WO_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;
    context.pRespPrefix = NULL;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_NO_COMMAND resp for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_NO_COMMAND( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_NO_COMMAND resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 3;
    atCmdType = CELLULAR_AT_NO_COMMAND;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;
    context.pRespPrefix = NULL;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_NO_COMMAND resp for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_AT_UNDEFINED_callback_okay( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_NO_COMMAND resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_NO_COMMAND;
    context.undefinedRespCallback = undefinedRespCallback;
    customCallbackContext = 0;
    context.pUndefinedRespCBContext = &customCallbackContext;

    /* Copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, prvUndefinedHandlePacket );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* Verify undefinedRespCallback is called and the expected string is received. */
    TEST_ASSERT_EQUAL_INT32( 1, customCallbackContext );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_NO_COMMAND resp for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_AT_UNDEFINED_callback_fail( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_NO_COMMAND resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_NO_COMMAND;
    context.undefinedRespCallback = undefinedRespCallback;
    customCallbackContext = 1;
    context.pUndefinedRespCBContext = &customCallbackContext;

    /* Copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, prvUndefinedHandlePacket );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* Verify undefinedRespCallback is called and the expected string is not received. */
    TEST_ASSERT_EQUAL_INT32( 0, customCallbackContext );
}

/**
 * @brief Test undefined message callback handling okay in pktio thread when sending AT command.
 *
 * The following sequence should have no error :
 * 1. Sending CELLULAR_AT_NO_RESULT type message ( for example, AT+CFUN=1 )
 * 2. Receiving "OK\r\n", CELLULAR_AT_UNDEFINED_STRING_RESP"\r\n"
 * 3. The AT command should success. The UNKNOW_TOKEN should cause a call to undefined callback.
 * 4. Okay is returned in the undefined response callback.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_SRC_AT_undefined_callback( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_NO_RESULT type AT command. */
    atCmdStatusUndefindTest = false;
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_NO_RESULT;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = "OK\r\n"CELLULAR_AT_UNDEFINED_STRING_RESP "\r\n";

    /* Setup the callback to handle the undefined message. */
    context.undefinedRespCallback = undefinedRespCallback;
    customCallbackContext = 0;
    context.pUndefinedRespCBContext = &customCallbackContext;

    /* Copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    threadReturn = true; /* Set pktio thread return flag. */
    pktStatus = _Cellular_PktioInit( &context, prvUndefinedHandlePacket );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* Verify the command should return success. */
    TEST_ASSERT_EQUAL( atCmdStatusUndefindTest, true );

    /* Verify undefinedRespCallback is called and the expected string is received. */
    TEST_ASSERT_EQUAL_INT32( 1, customCallbackContext );
}

/**
 * @brief Test undefined message callback handling okay in pktio thread when sending AT command.
 *
 * The following sequence should have no error :
 * 1. Sending CELLULAR_AT_NO_RESULT type message ( for example, AT+CFUN=1 )
 * 2. Receiving CELLULAR_AT_UNDEFINED_STRING_RESP"\r\n", "OK\r\n"
 * 3. The AT command should success. The UNKNOW_TOKEN should cause a call to undefined callback.
 * 4. Okay is returned in the undefined response callback.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_SRC_AT_undefined_callback_okay( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_NO_RESULT type AT command. */
    atCmdStatusUndefindTest = false;
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_NO_RESULT;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = CELLULAR_AT_UNDEFINED_STRING_RESP "\r\nOK\r\n";

    /* Setup the callback to handle the undefined message. */
    context.undefinedRespCallback = undefinedRespCallback;
    customCallbackContext = 0;
    context.pUndefinedRespCBContext = &customCallbackContext;

    /* Copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    threadReturn = true; /* Set pktio thread return flag. */
    pktStatus = _Cellular_PktioInit( &context, prvUndefinedHandlePacket );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* Verify the command should return success. */
    TEST_ASSERT_EQUAL( atCmdStatusUndefindTest, true );

    /* Verify undefinedRespCallback is called and the expected string is received. */
    TEST_ASSERT_EQUAL_INT32( 1, customCallbackContext );
}

/**
 * @brief Test undefined message callback handling error in pktio thread when sending AT command.
 *
 * The following sequence should have no error :
 * 1. Sending CELLULAR_AT_NO_RESULT type message ( for example, AT+CFUN=1 )
 * 2. Receiving CELLULAR_AT_UNDEFINED_STRING_RESP"\r\n", "OK\r\n"
 * 3. The AT command should success. The UNKNOW_TOKEN should cause a call to undefined callback.
 * 4. Error is returned in the undefined response callback. This would flush the
 *    pktio read buffer.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_SRC_AT_undefined_callback_fail( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_NO_RESULT type AT command. */
    atCmdStatusUndefindTest = false;
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_NO_RESULT;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = "UNKNOWN_UNDEFINED\r\nOK\r\n";

    /* Setup the callback to handle the undefined message. */
    context.undefinedRespCallback = undefinedRespCallback;
    customCallbackContext = 1;
    context.pUndefinedRespCBContext = &customCallbackContext;

    /* Copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    threadReturn = true; /* Set pktio thread return flag. */
    pktStatus = _Cellular_PktioInit( &context, prvUndefinedHandlePacket );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* Verify the command should has error. */
    TEST_ASSERT_EQUAL( atCmdStatusUndefindTest, false );

    /* Verify undefinedRespCallback is called but the expected string is not received. */
    TEST_ASSERT_EQUAL_INT32( 0, customCallbackContext );
}

/**
 * @brief Test undefined message no callback in pktio thread when sending AT command.
 *
 * The following sequence should have no error :
 * 1. Sending CELLULAR_AT_NO_RESULT type message ( for example, AT+CFUN=1 )
 * 2. Receiving CELLULAR_AT_UNDEFINED_STRING_RESP"\r\n", "OK\r\n"
 * 3. The AT command should success. The UNKNOW_TOKEN should cause a call to undefined callback.
 * 4. The command callback won't be called. This would cause a timeout in pkthandler.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_SRC_AT_undefined_no_callback_fail( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_NO_RESULT type AT command. */
    atCmdStatusUndefindTest = false;
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_NO_RESULT;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = "UNKNOWN_UNDEFINED\r\nOK\r\n";

    /* Copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    threadReturn = true; /* Set pktio thread return flag. */
    pktStatus = _Cellular_PktioInit( &context, prvUndefinedHandlePacket );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* Verify the command should has error. */
    TEST_ASSERT_EQUAL( atCmdStatusUndefindTest, false );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_MULTI_WO_PREFIX resp for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_MULTI_WO_PREFIX_Without_SrcToken_Table( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    ( void ) pktStatus;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_MULTI_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 2;
    atCmdType = CELLULAR_AT_MULTI_WO_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTableWithoutErrorTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;
    context.pRespPrefix = NULL;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );

    setUp();
    /* Test the rx_data event with CELLULAR_AT_MULTI_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 2;
    atCmdType = CELLULAR_AT_MULTI_WO_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTableWithoutSuccessTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;
    context.pRespPrefix = NULL;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_WITH_PREFIX_STRING resp for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_WITH_PREFIX_STRING( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WITH_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 4;
    atCmdType = CELLULAR_AT_WITH_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pRespPrefix = CELLULAR_AT_WITH_PREFIX_STRING;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief _Cellular_PktioInit - Sending CELLULAR_AT_WITH_PREFIX with empty response prefix.
 *
 * Empty response prefix will be considered invalid string. Verify AT_UNDEFINED type
 * is returned in _getMsgType function.
 *
 * <b>Coverage</b>
 * @code{c}
 * else
 * {
 *     {
 *         atStatus = Cellular_ATStrStartWith( pLine, pRespPrefix, &inputWithSrcPrefix );
 *     }
 * }
 *
 * if( ( atStatus == CELLULAR_AT_SUCCESS ) && ( atRespType == AT_UNDEFINED ) )
 * {
 *     ...
 * }
 * @endcode
 * ( atStatus == CELLULAR_AT_SUCCESS ) is false.
 * ( atRespType == AT_UNDEFINED ) is true.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_WITH_PREFIX_empty_prefix( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WITH_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 4;
    atCmdType = CELLULAR_AT_WITH_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pRespPrefix = ""; /* Use empty string to cover Cellular_ATStrStartWith failed case. */

    /* API call. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* This command returns an AT_UNDEFINED type, which is unhandled in the test
     * test case. Ensure the context is cleaned. */
    TEST_ASSERT_EQUAL( CELLULAR_AT_NO_COMMAND, context.PktioAtCmdType );
    TEST_ASSERT_EQUAL( NULL, context.pRespPrefix );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_WITH_PREFIX_STRING resp for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_WITH_PREFIX_STRING_MISMATCH_PREFIX( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WITH_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 2;
    atCmdType = CELLULAR_AT_WITH_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pRespPrefix = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_WO_PREFIX_STRING_RESP resp for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_WO_PREFIX_STRING_RESP( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 2;
    atCmdType = CELLULAR_AT_WO_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pRespPrefix = NULL;
    tokenTableType = 0;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief _processIntermediateResponse - Successfully handle AT command type CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE.
 *
 * Successfully handle at command type CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE. Verify
 * the response string in the callback function.
 *
 * <b>Coverage</b>
 * @code{c}
 *         case CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE:
 *             ...
 *             _saveATData( pLine, pResp );
 *
 *             pktStatus = CELLULAR_PKT_STATUS_OK;
 *             break;
 * @endcode
 * The CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE case.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE_success( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = "12345\r\n"; /* Dummy string to be verified in the callback. */

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, prvPacketCallbackSuccess );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* The result is verified in prvPacketCallbackSuccess. */
}

/**
 * @brief _processIntermediateResponse - Modem returns error when sending AT command type CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE.
 *
 * Modem returns error when sending AT command type CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE_error( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = "ERROR\r\n"; /* Return one of the error token. */

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, prvPacketCallbackError );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* The result is verified in prvPacketCallbackError. */
}


/**
 * @brief _processIntermediateResponse - Successfully handle AT command type CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE.
 *
 * Successfully handle at command type CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE. Verify
 * the response string in the callback function.
 *
 * <b>Coverage</b>
 * @code{c}
 *         case CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE:
 *             _saveATData( pLine, pResp );
 *
 *             pkStatus = CELLULAR_PKT_STATUS_OK;
 *             break;
 * @endcode
 * The CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE case.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE_success( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    context.pRespPrefix = "+CMD_PREFIX";
    pCommIntfRecvCustomString = "+CMD_PREFIX:12345\r\n"; /* Dummy string to be verified in the callback. */

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, prvPacketCallbackSuccess );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* The result is verified in prvPacketCallbackSuccess. */
}

/**
 * @brief _processIntermediateResponse - Modem returns error when sending AT command type CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE.
 *
 * Modem returns error when sending AT command type CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE_error( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    context.pRespPrefix = "+CMD_PREFIX";
    pCommIntfRecvCustomString = "ERROR\r\n"; /* Return one of the error token. */

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, prvPacketCallbackError );

    /* Verification. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* The result is verified in prvPacketCallbackError. */
}

/**
 * @brief Test thread receiving rx data event with success token for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_TOKEN_TABLE_SUCCESS_TOKEN( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    atCmdType = CELLULAR_AT_WO_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pRespPrefix = NULL;

    /* Set success token. */
    tokenTableType = 1;
    recvCount = 2;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event with error token for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_TOKEN_TABLE_ERROR_TOKEN( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    atCmdType = CELLULAR_AT_WO_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pRespPrefix = NULL;

    /* Set error token. */
    tokenTableType = 2;
    recvCount = 2;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event with extra token for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_TOKEN_TABLE_EXTRA_TOKEN( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    atCmdType = CELLULAR_AT_WO_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pRespPrefix = NULL;

    /* Set extra token. */
    tokenTableType = 3;
    recvCount = 2;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, NULL );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event with success token memory failure for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_TOKEN_TABLE_SUCCESS_TOKEN_MEMORY_FAIL( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    atCmdType = CELLULAR_AT_WO_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pRespPrefix = NULL;

    /* Set success token. */
    tokenTableType = 1;
    recvCount = 2;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_NO_RESULT resp for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_CELLULAR_AT_NO_RESULT_URC_TOKEN( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 2;
    atCmdType = CELLULAR_AT_NO_RESULT;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pRespPrefix = NULL;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief Test thread receiving rx data event with CELLULAR_AT_NO_COMMAND resp for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_OK.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_URC_TOKEN_STRING_RESP( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_NO_COMMAND resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 2;
    atCmdType = CELLULAR_AT_NO_COMMAND;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = NULL;
    context.pktDataSendPrefixCB = sendDataPrefix;
    isSendDataPrefixCbkSuccess = 0;
    context.pRespPrefix = CELLULAR_URC_TOKEN_PREFIX_STRING;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief _Cellular_PktioInit - urcTokenTableSize is set to 0 in _checkUrcTokenWoPrefix.
 *
 * Cover urcTokenTableSize is set to 0 in _checkUrcTokenWoPrefix. This function
 * should return false. Verify AT_UNDEFINED type is returned With input string "TEST1"
 * and the context is cleaned for unhandled AT_UNDEFINED type input.
 *
 * <b>Coverage</b>
 * @code{c}
 * static bool _checkUrcTokenWoPrefix( const CellularContext_t * pContext,
 *                                     const char * pLine )
 * {
 *     ...
 *     if( ( pUrcTokenTable == NULL ) || ( urcTokenTableSize == 0 ) )
 *     {
 *         ret = false;
 *     }
 *     ...
 * }
 * @endcode
 * ( pUrcTokenTable == NULL ) is false.
 * ( urcTokenTableSize == 0 ) is true.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_URC_WO_PREFIX_zero_table_size( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_NO_COMMAND resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 2;
    atCmdType = CELLULAR_AT_NO_COMMAND;

    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    /* Set the URC without prefix table size to 0 for testing here. */
    context.tokenTable.cellularUrcTokenWoPrefixTableSize = 0;

    /* API call. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* This command returns an AT_UNDEFINED type, which is unhandled in the test
     * test case. Ensure the context is cleaned. */
    TEST_ASSERT_EQUAL( CELLULAR_AT_NO_COMMAND, context.PktioAtCmdType );
    TEST_ASSERT_EQUAL( NULL, context.pRespPrefix );
}

/**
 * @brief Test RX data event _handle_data function.
 *
 * pktio read thread is in data mode and expects more data to be received. Modem returns
 * not enough data to pktio. These data will be stored as partial data.
 */
void test__Cellular_PktioInit_Thread_Rx_Data_Event_handle_data( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_NO_RESULT type AT command. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_NO_RESULT;
    testCommIfRecvType = COMM_IF_RECV_CUSTOM_STRING;
    pCommIntfRecvCustomString = "12345";

    /* Copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );

    /* Pktio read thread enter data mode by setting dataLength. */
    context.dataLength = 10;

    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    threadReturn = true; /* Set pktio thread return flag. */
    pktStatus = _Cellular_PktioInit( &context, prvUndefinedHandlePacket );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );

    /* Store 5 bytes in the partial data. */
    TEST_ASSERT_EQUAL_UINT( context.partialDataRcvdLen, 5 );

    /* The data is incomplete. pPktioReadPtr should be the same pktioReadBuf. */
    TEST_ASSERT_EQUAL( context.pPktioReadPtr, context.pktioReadBuf );
}

/**
 * @brief Test pkio aborted event case for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_FAILURE.
 */
void test__Cellular_PktioInit_Event_Aborted( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Test the aborted event. */
    pktioEvtMask = PKTIO_EVT_MASK_ABORTED;
    recvCount = 1;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_FAILURE, pktStatus );
}

/**
 * @brief Test the error path for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_CREATION_FAIL.
 */
void test__Cellular_PktioInit_Event_Group_Create_Null( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Test the pPktioCommEvent NULL case. */
    context.pPktioCommEvent = NULL;
    evtGroupHandle = NULL;
    /* Check that CELLULAR_PKT_STATUS_CREATION_FAIL is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_CREATION_FAIL, pktStatus );
}

/**
 * @brief Test the creating thread failure case for _Cellular_PktioInit to return CELLULAR_PKT_STATUS_CREATION_FAIL.
 */
void test__Cellular_PktioInit_Create_Thread_Fail( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Test the Platform_CreateDetachedThread fail case. */
    threadReturn = false;
    /* Check that CELLULAR_PKT_STATUS_CREATION_FAIL is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_CREATION_FAIL, pktStatus );
}

/**
 * @brief Test thread receiving rx data event without pCellularUrcTokenWoPrefixTable.
 */
void test__Cellular_PktioInit_No_UrcToken_Prefix_Table( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;

    threadReturn = true;
    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Assign the comm interface to pContext. */
    context.pCommIntf = pCommIntf;
    context.pPktioShutdownCB = _shutdownCallback;

    /* Test the rx_data event with CELLULAR_AT_MULTI_DATA_WO_PREFIX resp. */
    pktioEvtMask = PKTIO_EVT_MASK_RX_DATA;
    recvCount = 1;
    atCmdType = CELLULAR_AT_MULTI_DATA_WO_PREFIX;
    /* copy the token table. */
    ( void ) memcpy( &context.tokenTable, &tokenTable, sizeof( CellularTokenTable_t ) );
    context.pktDataPrefixCB = cellularATCommandDataPrefixCallback;
    context.pRespPrefix = CELLULAR_AT_MULTI_DATA_WO_PREFIX_STRING;
    context.tokenTable.pCellularUrcTokenWoPrefixTable = NULL;
    /* Check that CELLULAR_PKT_STATUS_OK is returned. */
    pktStatus = _Cellular_PktioInit( &context, PktioHandlePacketCallback_t );
    TEST_ASSERT_EQUAL( CELLULAR_AT_SUCCESS, pktStatus );
}

/**
 * @brief Test that any NULL context for _Cellular_PktioSendAtCmd.
 */
void test__Cellular_PktioSendAtCmd_Null_Context( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularAtReq_t atReqSetRatPriority =
    {
        "AT+QCFG=\"nwscanseq\"",
        CELLULAR_AT_WITH_PREFIX,
        "+QCFG",
        NULL,
        NULL,
        0,
    };

    memset( &context, 0, sizeof( CellularContext_t ) );

    pktStatus = _Cellular_PktioSendAtCmd( NULL, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that any NULL Comm interface for _Cellular_PktioSendAtCmd.
 */
void test__Cellular_PktioSendAtCmd_Null_CommInf( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    CellularAtReq_t atReqSetRatPriority =
    {
        "AT+QCFG=\"nwscanseq\"",
        CELLULAR_AT_WITH_PREFIX,
        "+QCFG",
        NULL,
        NULL,
        0,
    };

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.pCommIntf = NULL;
    context.hPktioCommIntf = NULL;
    pktStatus = _Cellular_PktioSendAtCmd( &context, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );

    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = NULL;
    pktStatus = _Cellular_PktioSendAtCmd( &context, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_INVALID_HANDLE, pktStatus );
}

/**
 * @brief Test that any NULL at command for _Cellular_PktioSendAtCmd.
 */
void test__Cellular_PktioSendAtCmd_Null_AtCmd( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    CellularAtReq_t atReqSetRatPriority =
    {
        "AT+QCFG=\"nwscanseq\"",
        CELLULAR_AT_WITH_PREFIX,
        "+QCFG",
        NULL,
        NULL,
        0,
    };

    memset( &context, 0, sizeof( CellularContext_t ) );

    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;
    pktStatus = _Cellular_PktioSendAtCmd( &context, NULL,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test that invalid string for _Cellular_PktioSendAtCmd.
 */
void test__Cellular_PktioSendAtCmd_Invalid_String( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    CellularAtReq_t atReqSetRatPriority =
    {
        "AT+QCFG=\"Story for Littel Red Riding Hood: Once upon a time there was a dear little girl who was loved by every one who looked at her, but most of all by her grandmother, and there was nothing that she would not have given to the child. Once she gave her a little cap of red velvet, which suited her so well that she would never wear anything else. So she was always called Little Red Riding Hood.\"",
        CELLULAR_AT_WITH_PREFIX,
        "+QCFG",
        NULL,
        NULL,
        0,
    };

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;
    pktStatus = _Cellular_PktioSendAtCmd( &context, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test that happy path for _Cellular_PktioSendAtCmd.
 */
void test__Cellular_PktioSendAtCmd_Happy_Path( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    CellularAtReq_t atReqSetRatPriority =
    {
        "AT+QCFG=\"nwscanseq\"",
        CELLULAR_AT_WITH_PREFIX,
        "+QCFG",
        NULL,
        NULL,
        0,
    };

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;

    /* API call. */
    pktStatus = _Cellular_PktioSendAtCmd( &context, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
    /* The context.PrespPrefix should be set to pktRespPrefixBuf. */
    TEST_ASSERT_EQUAL( &context.pktRespPrefixBuf, context.pRespPrefix );
}

/**
 * @brief Test that happy path for _Cellular_PktioSendAtCmd.
 */
void test__Cellular_PktioSendAtCmd_Happy_Path_No_Prefix( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    CellularAtReq_t atReqSetRatPriority =
    {
        "ATE0",
        CELLULAR_AT_NO_RESULT,
        NULL,
        NULL,
        NULL,
        0,
    };

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;
    pktStatus = _Cellular_PktioSendAtCmd( &context, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
}

/**
 * @brief _Cellular_PktioSendAtCmd - Sending CELLULAR_AT_WO_PREFIX with prefix.
 *
 * Prefix won't be parsed for CELLULAR_AT_WO_PREFIX type command. pRespPrefix should
 * be set NULL in _setPrefixByAtCommandType.
 *
 * <b>Coverage</b>
 * @code{c}
 * static CellularPktStatus_t _setPrefixByAtCommandType( ... )
 * ...
 *     switch( atType )
 *     {
 *         case CELLULAR_AT_NO_RESULT:
 *         case CELLULAR_AT_WO_PREFIX:
 *         case CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE:
 *             pContext->pRespPrefix = NULL;
 *             break;
 *         ...
 * @endcode
 * atType is CELLULAR_AT_WO_PREFIX and pAtRspPrefix is not NULL.
 */
void test__Cellular_PktioSendAtCmd_CELLULAR_AT_WO_PREFIX_with_prefix( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    CellularAtReq_t atReqSetRatPriority =
    {
        "ATE0",
        CELLULAR_AT_WO_PREFIX,
        "+QCFG",
        NULL,
        NULL,
        0,
    };

    /* Setup variable. */
    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;

    /* API call. */
    pktStatus = _Cellular_PktioSendAtCmd( &context, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
    TEST_ASSERT_EQUAL( NULL, context.pRespPrefix ); /* The context.PrespPrefix should be set NULL. */
}

/**
 * @brief _Cellular_PktioSendAtCmd - Sending CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE with prefix.
 *
 * Prefix won't be parsed for CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE type command.
 * pRespPrefix should be set NULL in _setPrefixByAtCommandType.
 *
 * <b>Coverage</b>
 * @code{c}
 * static CellularPktStatus_t _setPrefixByAtCommandType( ... )
 * ...
 *     switch( atType )
 *     {
 *         case CELLULAR_AT_NO_RESULT:
 *         case CELLULAR_AT_WO_PREFIX:
 *         case CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE:
 *             pContext->pRespPrefix = NULL;
 *             break;
 * @endcode
 * atType is CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE and pAtRspPrefix is not NULL.
 */
void test__Cellular_PktioSendAtCmd_CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE_with_prefix( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    CellularAtReq_t atReqSetRatPriority =
    {
        "ATE0",
        CELLULAR_AT_WO_PREFIX_NO_RESULT_CODE,
        "+QCFG",
        NULL,
        NULL,
        0,
    };

    /* Setup variable. */
    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;

    /* API call. */
    pktStatus = _Cellular_PktioSendAtCmd( &context, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
    TEST_ASSERT_EQUAL( NULL, context.pRespPrefix ); /* The context.PrespPrefix should be set NULL. */
}

/**
 * @brief _Cellular_PktioSendAtCmd - Sending CELLULAR_AT_WITH_PREFIX with pAtRspPrefix is NULL.
 *
 * Sending AT command type CELLULAR_AT_WITH_PREFIX but set pAtRspPrefix to NULL. Verify
 * CELLULAR_PKT_STATUS_BAD_PARAM is returned.
 *
 * <b>Coverage</b>
 * @code{c}
 * static CellularPktStatus_t _setPrefixByAtCommandType( ... )
 * ...
 *         case CELLULAR_AT_WITH_PREFIX:
 *         case CELLULAR_AT_MULTI_WITH_PREFIX:
 *         case CELLULAR_AT_WITH_PREFIX_NO_RESULT_CODE:
 *             if( pAtRspPrefix != NULL )
 *             {
 *                 ...
 *             }
 *             else
 *             {
 *                 LogWarn( ( "_setPrefixByAtCommandType : Sending a AT command type %d but pAtRspPrefix is not set.", atType ) );
 *                 pContext->pRespPrefix = NULL;
 *             }
 *             break;
 * @endcode
 * atType is CELLULAR_AT_WITH_PREFIX and pAtRspPrefix is NULL.
 */
void test__Cellular_PktioSendAtCmd_CELLULAR_AT_WITH_PREFIX_without_prefix( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    CellularAtReq_t atReqSetRatPriority =
    {
        "ATE0",
        CELLULAR_AT_WITH_PREFIX,
        NULL,
        NULL,
        NULL,
        0,
    };

    /* Setup variable. */
    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;

    /* API call. */
    pktStatus = _Cellular_PktioSendAtCmd( &context, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief _Cellular_PktioSendAtCmd - Sending CELLULAR_AT_MULTI_WO_PREFIX with pAtRspPrefix is not NULL.
 *
 * Sending AT command type CELLULAR_AT_MULTI_WO_PREFIX but set pAtRspPrefix to NULL. Verify
 * pRespPrefix is set to pktRespPrefixBuf.
 *
 * <b>Coverage</b>
 * @code{c}
 * static CellularPktStatus_t _setPrefixByAtCommandType( ... )
 * ...
 *         case CELLULAR_AT_MULTI_WO_PREFIX:
 *         case CELLULAR_AT_MULTI_DATA_WO_PREFIX:
 *             if( pAtRspPrefix != NULL )
 *             {
 *                 ( void ) strncpy( pContext->pktRespPrefixBuf, pAtRspPrefix, CELLULAR_CONFIG_MAX_PREFIX_STRING_LENGTH );
 *                 pContext->pRespPrefix = pContext->pktRespPrefixBuf;
 *             }
 *             else
 *             {
 *                 ...
 *             }
 *             break;
 * @endcode
 * atType is CELLULAR_AT_MULTI_WO_PREFIX and pAtRspPrefix is not NULL.
 */
void test__Cellular_PktioSendAtCmd_CELLULAR_AT_MULTI_WO_PREFIX_with_prefix( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    CellularAtReq_t atReqSetRatPriority =
    {
        "ATE0",
        CELLULAR_AT_MULTI_WO_PREFIX,
        "+QCFG",
        NULL,
        NULL,
        0,
    };

    /* Setup variable. */
    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;

    /* API call. */
    pktStatus = _Cellular_PktioSendAtCmd( &context, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
    TEST_ASSERT_EQUAL( &context.pktRespPrefixBuf, context.pRespPrefix );
}

/**
 * @brief _Cellular_PktioSendAtCmd - Sending CELLULAR_AT_MULTI_WO_PREFIX with pAtRspPrefix is NULL.
 *
 * Sending AT command type CELLULAR_AT_MULTI_WO_PREFIX but set pAtRspPrefix to NULL. Verify
 * pRespPrefix is set to NULL.
 *
 * <b>Coverage</b>
 * @code{c}
 * static CellularPktStatus_t _setPrefixByAtCommandType( ... )
 * ...
 *         case CELLULAR_AT_MULTI_WO_PREFIX:
 *         case CELLULAR_AT_MULTI_DATA_WO_PREFIX:
 *             if( pAtRspPrefix != NULL )
 *             {
 *                 ( void ) strncpy( pContext->pktRespPrefixBuf, pAtRspPrefix, CELLULAR_CONFIG_MAX_PREFIX_STRING_LENGTH );
 *                 pContext->pRespPrefix = pContext->pktRespPrefixBuf;
 *             }
 *             else
 *             {
 *                 pContext->pRespPrefix = NULL;
 *             }
 *             break;
 * @endcode
 * atType is CELLULAR_AT_MULTI_WO_PREFIX and pAtRspPrefix is NULL.
 */
void test__Cellular_PktioSendAtCmd_CELLULAR_AT_MULTI_WO_PREFIX_without_prefix( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    CellularAtReq_t atReqSetRatPriority =
    {
        "ATE0",
        CELLULAR_AT_MULTI_WO_PREFIX,
        NULL,
        NULL,
        NULL,
        0,
    };

    /* Setup variable. */
    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;

    /* API call. */
    pktStatus = _Cellular_PktioSendAtCmd( &context, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_OK, pktStatus );
    TEST_ASSERT_EQUAL( NULL, context.pRespPrefix ); /* The context.PrespPrefix should be set NULL. */
}

/**
 * @brief _Cellular_PktioSendAtCmd - Sending CELLULAR_AT_NO_COMMAND.
 *
 * Sending AT command type CELLULAR_AT_NO_COMMAND. Verify CELLULAR_PKT_STATUS_BAD_PARAM
 * is returned.
 *
 * <b>Coverage</b>
 * @code{c}
 * static CellularPktStatus_t _setPrefixByAtCommandType( ... )
 * ...
 *         default:
 *             LogError( ( "_setPrefixByAtCommandType : Sending invalid AT command type." ) );
 *             pktStatus = CELLULAR_PKT_STATUS_BAD_PARAM;
 *             break;
 * @endcode
 * atType is CELLULAR_AT_NO_COMMAND.
 */
void test__Cellular_PktioSendAtCmd_CELLULAR_AT_NO_COMMAND( void )
{
    CellularPktStatus_t pktStatus = CELLULAR_PKT_STATUS_OK;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    CellularAtReq_t atReqSetRatPriority =
    {
        "ATE0",
        CELLULAR_AT_NO_COMMAND,
        NULL,
        NULL,
        NULL,
        0,
    };

    /* Setup variable. */
    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;

    /* API call. */
    pktStatus = _Cellular_PktioSendAtCmd( &context, atReqSetRatPriority.pAtCmd,
                                          atReqSetRatPriority.atCmdType,
                                          atReqSetRatPriority.pAtRspPrefix );

    /* Validation. */
    TEST_ASSERT_EQUAL( CELLULAR_PKT_STATUS_BAD_PARAM, pktStatus );
}

/**
 * @brief Test that any NULL parameter for _Cellular_PktioSendData.
 */
void test__Cellular_PktioSendData_Invalid_Param( void )
{
    uint32_t sentLen = 0;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    char pString[] = CELLULAR_AT_CMD_MULTI_WO_PREFIX;

    memset( &context, 0, sizeof( CellularContext_t ) );
    sentLen = _Cellular_PktioSendData( NULL,
                                       ( uint8_t * ) pString,
                                       strlen( pString ) + 1 );
    TEST_ASSERT_EQUAL( 0, sentLen );
    /* Not assign pCommIntf and hPktioCommIntf. */
    sentLen = _Cellular_PktioSendData( &context,
                                       ( uint8_t * ) pString,
                                       strlen( pString ) + 1 );
    TEST_ASSERT_EQUAL( 0, sentLen );

    context.pCommIntf = pCommIntf;
    sentLen = _Cellular_PktioSendData( &context,
                                       NULL,
                                       0 );
    TEST_ASSERT_EQUAL( 0, sentLen );

    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;
    sentLen = _Cellular_PktioSendData( &context,
                                       NULL,
                                       0 );
    TEST_ASSERT_EQUAL( 0, sentLen );
}

/**
 * @brief Test that happy path for _Cellular_PktioSendData.
 */
void test__Cellular_PktioSendData_Happy_Path( void )
{
    uint32_t sentLen = 0;
    CellularContext_t context;
    CellularCommInterface_t * pCommIntf = &CellularCommInterface;
    struct _cellularCommContext commInterfaceHandle = { 0 };
    char pString[] = CELLULAR_AT_CMD_MULTI_WO_PREFIX;

    memset( &context, 0, sizeof( CellularContext_t ) );
    context.pCommIntf = pCommIntf;
    context.hPktioCommIntf = ( CellularCommInterfaceHandle_t ) &commInterfaceHandle;

    sentLen = _Cellular_PktioSendData( &context,
                                       ( uint8_t * ) pString,
                                       strlen( pString ) + 1 );
    TEST_ASSERT_EQUAL( strlen( pString ) + 1, sentLen );
}

/**
 * @brief Test that any null parameter for _Cellular_PktioShutdown.
 */
void test__Cellular_PktioShutdown_Null_Parameter( void )
{
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );

    /* Mock null context */
    _Cellular_PktioShutdown( NULL );

    /* Mock context exist but member bPktioUp is false. */
    _Cellular_PktioShutdown( &context );
}

/**
 * @brief Test that null pPktioCommEvent for _Cellular_PktioShutdown.
 */
void test__Cellular_PktioShutdown_Null_PktioCommEvent( void )
{
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    eventDesiredCount = 2;
    desiredPktioEvtMask = PKTIO_EVT_MASK_ABORTED;
    context.bPktioUp = true;

    context.pPktioCommEvent = NULL;
    _Cellular_PktioShutdown( &context );

    TEST_ASSERT_EQUAL( false, context.bPktioUp );
}

/**
 * @brief Test that happy path for _Cellular_PktioShutdown.
 */
void test__Cellular_PktioShutdown_Happy_Path( void )
{
    CellularContext_t context;

    memset( &context, 0, sizeof( CellularContext_t ) );
    eventDesiredCount = 2;
    desiredPktioEvtMask = PKTIO_EVT_MASK_ABORTED;
    context.bPktioUp = true;

    context.pPktioCommEvent = PlatformEventGroup_Create();
    _Cellular_PktioShutdown( &context );

    TEST_ASSERT_EQUAL( false, context.bPktioUp );
}
