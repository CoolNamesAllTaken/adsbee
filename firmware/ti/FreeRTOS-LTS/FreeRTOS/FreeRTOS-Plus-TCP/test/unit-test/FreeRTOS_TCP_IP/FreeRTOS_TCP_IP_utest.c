/*
 * FreeRTOS+TCP V4.2.2
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */


/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_TCP_IP_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_TCP_State_Handling.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_TCP_Transmission.h"
#include "mock_FreeRTOS_TCP_Reception.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_TCP_IP_stubs.c"
#include "FreeRTOS_TCP_IP.h"

/* =========================== EXTERN VARIABLES =========================== */

FreeRTOS_Socket_t xSocket, * pxSocket;
NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;

extern BaseType_t xTCPWindowLoggingLevel;
extern FreeRTOS_Socket_t * xSocketToClose;
extern FreeRTOS_Socket_t * xSocketToListen;

uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ] =
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x08, 0x00, 0x45, 0x00,
    0x00, 0x34, 0x15, 0xc2, 0x40, 0x00, 0x40, 0x06, 0xa8, 0x8e, 0xc0, 0xa8, 0x00, 0x08, 0xac, 0xd9,
    0x0e, 0xea, 0xea, 0xfe, 0x01, 0xbb, 0x8b, 0xaf, 0x8a, 0x24, 0xdc, 0x96, 0x95, 0x7a, 0x80, 0x10,
    0x01, 0xf5, 0x7c, 0x9a, 0x00, 0x00, 0x01, 0x01, 0x08, 0x0a, 0xb8, 0x53, 0x57, 0x27, 0xb2, 0xce,
    0xc3, 0x17
};

static void test_Helper_ListInitialise( List_t * const pxList );

static void test_Helper_ListInsertEnd( List_t * const pxList,
                                       ListItem_t * const pxNewListItem );

/* ============================== Test Cases ============================== */

/**
 * @brief Test the functionality when socket is NULL.
 */
void test_vSocketCloseNextTime_Null_Socket( void )
{
    vSocketCloseNextTime( NULL );
}

/**
 * @brief Test the functionality to not close the
 *        socket.
 */
void test_vSocketCloseNextTime_Not_Close_Socket( void )
{
    memset( &xSocket, 0, sizeof( xSocket ) );

    vSocketCloseNextTime( &xSocket );
}

/**
 * @brief Test the functionality to not close the
 *        same socket.
 */
void test_vSocketCloseNextTime_Not_Close_Same_Socket( void )
{
    memset( &xSocket, 0, sizeof( xSocket ) );

    vSocketCloseNextTime( &xSocket );
}

/**
 * @brief Test the functionality to close the
 *        same socket.
 */
/* test vSocketCloseNextTime function */
void test_vSocketCloseNextTime_Close_Previous_Socket( void )
{
    FreeRTOS_Socket_t NewSocket;

    vSocketClose_ExpectAnyArgsAndReturn( NULL );
    vSocketCloseNextTime( &NewSocket );
}

/**
 * @brief Test the functionality to Postpone a call
 *        to FreeRTOS_listen() to avoid recursive calls.
 */
void test_vSocketListenNextTime( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };

    xSocketToListen = NULL;

    vSocketListenNextTime( &xSocket );

    TEST_ASSERT_EQUAL( &xSocket, xSocketToListen );
}

/**
 * @brief Test the functionality to Postpone a call
 *        to FreeRTOS_listen() to avoid recursive calls.
 */
void test_vSocketListenNextTime1( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };

    xSocketToListen = &xSocket;

    FreeRTOS_listen_ExpectAndReturn( ( Socket_t ) xSocketToListen, xSocketToListen->u.xTCP.usBacklog, 0 );
    vSocketListenNextTime( NULL );

    TEST_ASSERT_EQUAL( NULL, xSocketToListen );
}

/**
 * @brief Test the functionality to Postpone a call
 *        to FreeRTOS_listen() to avoid recursive calls.
 */
void test_vSocketListenNextTime2( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };

    xSocketToListen = &xSocket;

    vSocketListenNextTime( xSocketToListen );

    TEST_ASSERT_EQUAL( &xSocket, xSocketToListen );
}

/**
 * @brief Test the functionality to Postpone a call
 *        to FreeRTOS_listen() to avoid recursive calls
 *        when all inputs are set to zero.
 */
void test_xTCPSocketCheck_AllInputsZero1( void )
{
    BaseType_t xReturn, xToReturn = 0xAABBCCDD;
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &xDelayReturn );

    prvTCPStatusAgeCheck_ExpectAnyArgsAndReturn( xToReturn );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
}

/**
 * @brief Test the functionality to Postpone a call
 *        to FreeRTOS_listen() to avoid recursive calls
 *        when the tcp state is set to eESTABLISHED.
 */
void test_xTCPSocketCheck_StateEstablished( void )
{
    BaseType_t xReturn, xToReturn = 0xAABBCCDD;
    FreeRTOS_Socket_t xSocket = { 0 };
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.eTCPState = eESTABLISHED;

    prvTCPSendPacket_ExpectAndReturn( &xSocket, 0 );

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &xDelayReturn );

    prvTCPStatusAgeCheck_ExpectAnyArgsAndReturn( xToReturn );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
}

/**
 * @brief Test the functionality to Postpone a call
 *        to FreeRTOS_listen() to avoid recursive calls
 *        when the tcp state is set to eESTABLISHED
 *        and tcp stream is NULL.
 */
void test_xTCPSocketCheck_StateEstablished_TxStreamNonNull( void )
{
    BaseType_t xReturn, xToReturn = 0xAABBCCDD;
    FreeRTOS_Socket_t xSocket = { 0 };
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;

    prvTCPAddTxData_Expect( &xSocket );

    prvTCPSendPacket_ExpectAndReturn( &xSocket, 0 );

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &xDelayReturn );

    prvTCPStatusAgeCheck_ExpectAnyArgsAndReturn( xToReturn );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
}

/**
 * @brief Test the functionality to Postpone a call
 *        to FreeRTOS_listen() to avoid recursive calls
 *        when the tcp state is set to eESTABLISHED
 *        and a valid TCP stream.
 */
void test_xTCPSocketCheck_StateEstablished_TxStreamNonNull1( void )
{
    BaseType_t xReturn, xToReturn = 0xAABBCCDD;
    FreeRTOS_Socket_t xSocket = { 0 };
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;
    xSocket.u.xTCP.pxAckMessage = ( void * ) &xSocket;

    prvTCPAddTxData_Expect( &xSocket );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    prvTCPReturnPacket_Expect( &xSocket, xSocket.u.xTCP.pxAckMessage, ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER, ipconfigZERO_COPY_TX_DRIVER );

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &xDelayReturn );

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    prvTCPSendPacket_ExpectAndReturn( &xSocket, 0 );

    prvTCPStatusAgeCheck_ExpectAndReturn( &xSocket, xToReturn );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 1U, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Test the functionality to Postpone a call
 *        to FreeRTOS_listen() to avoid recursive calls
 *        when the tcp state is set to eESTABLISHED.
 */
void test_xTCPSocketCheck_StateEstablished_TxStreamNonNull_BufferFreed( void )
{
    BaseType_t xReturn, xToReturn = 0xAABBCCDD;
    FreeRTOS_Socket_t xSocket = { 0 };
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;
    xSocket.u.xTCP.pxAckMessage = ( void * ) &xSocket;

    prvTCPAddTxData_Expect( &xSocket );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    prvTCPReturnPacket_Stub( prvTCPReturnPacket_StubReturnNULL );

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &xDelayReturn );

    prvTCPSendPacket_ExpectAndReturn( &xSocket, 0 );

    prvTCPStatusAgeCheck_ExpectAndReturn( &xSocket, xToReturn );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 1U, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Test functionality when the stream is non-NULL and the
 *        time out is non-zero.
 */
void test_xTCPSocketCheck_StateEstablished_TxStreamNonNull1_NonZeroTimeout( void )
{
    BaseType_t xReturn, xToReturn = 0;
    FreeRTOS_Socket_t xSocket = { 0 };
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;
    xSocket.u.xTCP.pxAckMessage = ( void * ) &xSocket;
    xSocket.u.xTCP.usTimeout = 100;

    prvTCPAddTxData_Expect( &xSocket );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    prvTCPReturnPacket_Expect( &xSocket, xSocket.u.xTCP.pxAckMessage, ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER, ipconfigZERO_COPY_TX_DRIVER );

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 100U, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Test functionality when the stream is non-NULL and the
 *        time out is non-zero. The port number cannot be allowed to issue log
 *        messages.
 */
void test_xTCPSocketCheck_StateEstablished_TxStreamNonNull1_NonZeroTimeout_NoLogPort( void )
{
    BaseType_t xReturn, xToReturn = 0, xBackup;
    FreeRTOS_Socket_t xSocket = { 0 };
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;
    xSocket.u.xTCP.pxAckMessage = ( void * ) &xSocket;
    xSocket.u.xTCP.usTimeout = 100;
    xSocket.usLocalPort = 23U;

    xBackup = xTCPWindowLoggingLevel;
    xTCPWindowLoggingLevel = 2;

    prvTCPAddTxData_Expect( &xSocket );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    prvTCPReturnPacket_Expect( &xSocket, xSocket.u.xTCP.pxAckMessage, ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER, ipconfigZERO_COPY_TX_DRIVER );

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 100U, xSocket.u.xTCP.usTimeout );

    xTCPWindowLoggingLevel = xBackup;
}

/**
 * @brief Test functionality when the stream is non-NULL and the
 *        time out is non-zero. The port number cannot be allowed to issue log
 *        messages.
 */
void test_xTCPSocketCheck_StateCLOSED_TxStreamNonNull1_NonZeroTimeout( void )
{
    BaseType_t xReturn, xToReturn = 0;
    FreeRTOS_Socket_t xSocket = { 0 };
    TickType_t xDelayReturn = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.eTCPState = eCLOSED;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;
    xSocket.u.xTCP.pxAckMessage = ( void * ) &xSocket;
    xSocket.u.xTCP.usTimeout = 100;
    xSocket.usLocalPort = 23U;

    xTCPWindowLoggingLevel = 2;

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 100U, xSocket.u.xTCP.usTimeout );

    xTCPWindowLoggingLevel = 1;
}

/**
 * @brief Test functionality when the stream is non-NULL and the
 *        time out is non-zero. Additionally, the user has requested to shutdown
 *        the socket.
 */
void test_xTCPSocketCheck_StateeCONNECT_SYN_TxStreamNonNull_UserShutdown( void )
{
    BaseType_t xReturn, xToReturn = 0;
    FreeRTOS_Socket_t xSocket = { 0 };

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.eTCPState = eCONNECT_SYN;
    xSocket.u.xTCP.txStream = ( void * ) &xSocket;
    xSocket.u.xTCP.pxAckMessage = ( void * ) &xSocket;
    xSocket.u.xTCP.usTimeout = 100;
    xSocket.u.xTCP.bits.bUserShutdown = pdTRUE_UNSIGNED;

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    prvTCPSendPacket_ExpectAndReturn( &xSocket, 0 );

    prvTCPStatusAgeCheck_ExpectAndReturn( &xSocket, xToReturn );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    /* ARP phase. Check every half second. */
    TEST_ASSERT_EQUAL( 500U, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Test to validate 'Touching' the socket
 *        to keep it alive/updated.
 */
void test_prvTCPTouchSocket( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0xAA, sizeof( xSocket ) );

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );

    prvTCPTouchSocket( &xSocket );

    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 * @brief Test to validate Calculate after how much
 *        time this socket needs to be checked again
 *        when tcp state is eCONNECT_SYN.
 */
void test_prvTCPNextTimeout_ConnSyn_State_Not_Active( void )
{
    TickType_t Return = 0;

    pxSocket = &xSocket;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.bits.bConnPrepared = pdFALSE;
    pxSocket->u.xTCP.ucRepCount = 0;

    Return = prvTCPNextTimeout( pxSocket );
    TEST_ASSERT_EQUAL( 500, Return );
}

/**
 * @brief Test to validate Calculate after how much
 *        time this socket needs to be checked again
 *        when tcp state is eCONNECT_SYN and connection
 *        is prepared.
 */
void test_prvTCPNextTimeout_ConnSyn_State_Active_Rep0( void )
{
    TickType_t Return = 0;

    pxSocket = &xSocket;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;
    pxSocket->u.xTCP.ucRepCount = 0;

    Return = prvTCPNextTimeout( pxSocket );
    TEST_ASSERT_EQUAL( 1, Return );
}

/**
 * @brief Test to validate Calculate after how much
 *        time this socket needs to be checked again
 *        when tcp state is eCONNECT_SYN and rep count
 *        is less than 3.
 */
void test_prvTCPNextTimeout_ConnSyn_State_Active_Rep1( void )
{
    TickType_t Return = 0;

    pxSocket = &xSocket;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;
    pxSocket->u.xTCP.ucRepCount = 1;

    Return = prvTCPNextTimeout( pxSocket );
    TEST_ASSERT_EQUAL( 3000, Return );
}

/**
 * @brief Test to validate Calculate after how much
 *        time this socket needs to be checked again
 *        when tcp state is eCONNECT_SYN and rep count
 *        is 3.
 */
void test_prvTCPNextTimeout_ConnSyn_State_Active_Rep3( void )
{
    TickType_t Return = 0;

    pxSocket = &xSocket;

    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.bits.bConnPrepared = pdTRUE;
    pxSocket->u.xTCP.ucRepCount = 3;

    Return = prvTCPNextTimeout( pxSocket );
    TEST_ASSERT_EQUAL( 11000, Return );
}

/**
 * @brief Test to validate Calculate after how much
 *        time this socket needs to be checked again
 *        when tcp state is eESTABLISHED and an active
 *        time out being set.
 */
void test_prvTCPNextTimeout_Established_State_Active_Timeout_Set( void )
{
    TickType_t Return = 0;

    pxSocket = &xSocket;

    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usTimeout = 5000;
    pxSocket->u.xTCP.ucRepCount = 3;

    Return = prvTCPNextTimeout( pxSocket );
    TEST_ASSERT_EQUAL( 5000, Return );
}

/**
 * @brief Test to validate Calculate after how much
 *        time this socket needs to be checked again
 *        when tcp state is eESTABLISHED and an active
 *        time out is not set but has timeout delay.
 */
void test_prvTCPNextTimeout_Established_State_Active_Timeout_Not_Set_Has_Data_With_Delay( void )
{
    TickType_t Return = 0;

    pxSocket = &xSocket;
    TickType_t TxWinReturn = 1000;

    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usTimeout = 0;
    pxSocket->u.xTCP.ucRepCount = 3;

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &TxWinReturn );

    Return = prvTCPNextTimeout( pxSocket );
    TEST_ASSERT_EQUAL( 1000, Return );
}

/**
 * @brief Test to validate Calculate after how much
 *        time this socket needs to be checked again
 *        when tcp state is eESTABLISHED valid with TX data
 *        and no timeout delay.
 */
void test_prvTCPNextTimeout_Established_State_Active_Timeout_Not_Set_Has_Data_Without_Delay( void )
{
    TickType_t Return = 0;

    pxSocket = &xSocket;
    TickType_t TxWinReturn = 0;

    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usTimeout = 0;
    pxSocket->u.xTCP.ucRepCount = 3;

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdTRUE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &TxWinReturn );

    Return = prvTCPNextTimeout( pxSocket );
    TEST_ASSERT_EQUAL( 1, Return );
}

/**
 * @brief Test to validate Calculate after how much
 *        time this socket needs to be checked again
 *        when tcp state is eESTABLISHED valid with no
 *        TX data and no timeout delay.
 */
void test_prvTCPNextTimeout_Established_State_Active_Timeout_Not_Set_No_Data_Without_Delay( void )
{
    TickType_t Return = 0;

    pxSocket = &xSocket;
    TickType_t TxWinReturn = 0;

    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.usTimeout = 0;
    pxSocket->u.xTCP.ucRepCount = 3;

    xTCPWindowTxHasData_ExpectAnyArgsAndReturn( pdFALSE );
    xTCPWindowTxHasData_ReturnThruPtr_pulDelay( &TxWinReturn );

    Return = prvTCPNextTimeout( pxSocket );
    TEST_ASSERT_EQUAL( tcpMAXIMUM_TCP_WAKEUP_TIME_MS, Return );
}

/**
 * @brief Test functionality when the state to be reached and the
 *        current state equal to closed state.
 */
void test_vTCPStateChange_ClosedState( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSED;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 * @brief Test functionality when the state to be reached and the
 *        current state equal to closed state, with child socket.
 */
void test_vTCPStateChange_ClosedState_ChildSocket( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    FreeRTOS_Socket_t xChildSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSED;
    xSocket.u.xTCP.pxPeerSocket = &xChildSocket;
    xChildSocket.u.xTCP.pxPeerSocket = &xSocket;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xChildSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 * @brief Test functionality when the state to be reached and the
 *        current state equal to closed state, with child socket.
 */
void test_vTCPStateChange_EstablishedState_ChildSocket2( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    FreeRTOS_Socket_t xSocketParent2 = { 0 };
    FreeRTOS_Socket_t xChildSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSED;
    xSocket.u.xTCP.pxPeerSocket = &xChildSocket;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xChildSocket.u.xTCP.pxPeerSocket = &xSocketParent2;
    xSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;
    xSocket.u.xTCP.bits.bReuseSocket = pdFALSE_UNSIGNED;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );
    vTaskSuspendAll_Expect();

    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket2;

    memset( &xSocket2, 0, sizeof( xSocket ) );

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 40000;
    pxSocket->xBoundSocketListItem.pvOwner = pxSocket;
    pxSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    pxSocket->u.xTCP.bits.bPassAccept = pdTRUE;

    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vSocketClose_ExpectAnyArgsAndReturn( NULL );

    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xChildSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 * @brief Test functionality when the state to be reached is closed wait
 *        and current state is equal to connect syn.
 */
void test_vTCPStateChange_ClosedWaitState_PrvStateSyn( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSE_WAIT;

    xSocket.u.xTCP.eTCPState = eCONNECT_SYN;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );
    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSE_WAIT, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 * @brief Test functionality when the state to be reached is closed wait
 *        and current state is equal to syn first.
 */
void test_vTCPStateChange_ClosedWaitState_PrvStateSynFirst( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSE_WAIT;

    xSocket.u.xTCP.eTCPState = eSYN_FIRST;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );
    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSE_WAIT, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 * @brief Test functionality when the state to be reached is closed wait
 *        and current state is equal to syn first.
 */
void test_vTCPStateChange_ClosedWaitState_CurrentStateSynFirstNextStateCloseWait( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSE_WAIT;

    xSocketToListen = NULL;

    xSocket.u.xTCP.eTCPState = eSYN_FIRST;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );
    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( &xSocket, xSocketToListen );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 * @brief Test functionality when the state to be reached is closed wait
 *        and current state is equal to syn received.
 */
void test_vTCPStateChange_ClosedWaitState_PrvStateSynRecvd( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSE_WAIT;

    xSocket.u.xTCP.eTCPState = eSYN_RECEIVED;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );
    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSE_WAIT, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 *  @brief Test functionality when the state to be reached and the
 *        current state equal to close wait state.
 */
void test_vTCPStateChange_ClosedWaitState( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSE_WAIT;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSE_WAIT, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 *  @brief Test functionality when the state to be reached and the
 *        current state equal to close wait state. Socket bIsIPv6 bit is set
 *        indicating IPv6 socket.
 */
void test_vTCPStateChange_ClosedWaitState_bIsIPv6( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.bits.bIsIPv6 = 1;
    eTCPState = eCLOSE_WAIT;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSE_WAIT, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 *  @brief Test functionality when the state to be reached and the
 *        current state equal to close wait state. Socket bIsIPv6 bit is set
 *        indicating IPv6 socket and port set as 23 as ipconfigTCP_MAY_LOG_PORT
 *        definition will not generate log messages for ports 23.
 */
void test_vTCPStateChange_ClosedWaitState_IncorrectPort( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.usLocalPort = 23U;

    eTCPState = eCLOSE_WAIT;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSE_WAIT, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 *  @brief Test functionality when the state to be reached and the
 *        current state equal to close wait state. Additionally, the pass queued
 *        bit is set and the function is being called from IP task.
 */
void test_vTCPStateChange_ClosedWaitState_CallingFromIPTask( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.u.xTCP.eTCPState = eCLOSE_WAIT;
    eTCPState = eCLOSE_WAIT;

    xSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;

    vTaskSuspendAll_Expect();
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket2;

    memset( &xSocket2, 0, sizeof( xSocket ) );

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 40000;
    pxSocket->xBoundSocketListItem.pvOwner = pxSocket;
    pxSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    pxSocket->u.xTCP.bits.bPassAccept = pdTRUE;

    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );


    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    /* FIXME: Different behaviour with -fsanitize=address,undefined. */
    if( xSocketToClose != &xSocket )
    {
        vSocketClose_ExpectAnyArgsAndReturn( NULL );
    }

    xTaskResumeAll_ExpectAndReturn( 0 );

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSE_WAIT, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 * @brief Test functionality when the state to be reached and the
 *        current state equal to close wait state. Additionally, the pass queued
 *        bit is set and the function is not being called from IP task.
 */
void test_vTCPStateChange_ClosedWaitState_NotCallingFromIPTask( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSE_WAIT;

    xSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;

    vTaskSuspendAll_Expect();
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket2;

    memset( &xSocket2, 0, sizeof( xSocket ) );

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 40000;
    pxSocket->xBoundSocketListItem.pvOwner = pxSocket;
    pxSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    pxSocket->u.xTCP.bits.bPassAccept = pdTRUE;

    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );


    catch_assert( vTCPStateChange( &xSocket, eTCPState ) );
}

/**
 * @brief Test functionality when the state to be reached and the
 *        current state equal to close wait state. Additionally, the pass accept
 *        bit is set and the function is being called from IP task.
 */
void test_vTCPStateChange_ClosedWaitState_CallingFromIPTask1( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSE_WAIT;

    xSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;

    vTaskSuspendAll_Expect();
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket2;

    memset( &xSocket2, 0, sizeof( xSocket ) );

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 40000;
    pxSocket->xBoundSocketListItem.pvOwner = pxSocket;
    pxSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    pxSocket->u.xTCP.bits.bPassAccept = pdTRUE;

    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    /* FIXME: Different behaviour with -fsanitize=address,undefined. */
    if( xSocketToClose != &xSocket )
    {
        vSocketClose_ExpectAnyArgsAndReturn( NULL );
    }

    xTaskResumeAll_ExpectAndReturn( 0 );

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSE_WAIT, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 * @brief Test functionality when the state to be reached and the
 *        current state equal to close wait state. Additionally, the pass accept
 *        bit is set and the function is not being called from IP task.
 */
void test_vTCPStateChange_ClosedWaitState_NotCallingFromIPTask1( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSE_WAIT;

    xSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;

    vTaskSuspendAll_Expect();
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket2;

    memset( &xSocket2, 0, sizeof( xSocket ) );

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 40000;
    pxSocket->xBoundSocketListItem.pvOwner = pxSocket;
    pxSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    pxSocket->u.xTCP.bits.bPassAccept = pdTRUE;

    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    catch_assert( vTCPStateChange( &xSocket, eTCPState ) );
}

/**
 * @brief Test functionality when the state to be reached and the
 *        current state equal to close wait state. Additionally, the pass accept
 *        and reuse socket bits are set.
 */
void test_vTCPStateChange_ClosedWaitState_ReuseSocket( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSE_WAIT;

    xSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSE_WAIT, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
}

/**
 * @brief Test functionality when the state to be reached and the
 *        current state equal to established state. Additionally, the pass accept
 *        and reuse socket bits are set.
 */
void test_vTCPStateChange_EstablishedState_ReuseSocket( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;
    BaseType_t xBackup;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eESTABLISHED;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;

    xSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;

    xBackup = xTCPWindowLoggingLevel;
    xTCPWindowLoggingLevel = -1;

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eESTABLISHED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );

    xTCPWindowLoggingLevel = xBackup;
}

/**
 * @brief Test functionality when the state to be reached is closed and the
 *        current state is established state. Additionally, the pass accept
 *        and reuse socket bits are set.
 */
void test_vTCPStateChange_EstablishedToClosedState_SocketInactive( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;
    BaseType_t xBackup;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSED;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;

    xSocket.u.xTCP.usTimeout = 100;

    xBackup = xTCPWindowLoggingLevel;
    xTCPWindowLoggingLevel = 2;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, 0 );
    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( eSOCKET_CLOSED, xSocket.xEventBits );

    xTCPWindowLoggingLevel = xBackup;
}

/**
 * @brief Test functionality when the state to be reached is closed and the
 *        current state is established state.
 */
void test_vTCPStateChange_EstablishedToClosedState_SocketActive( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;
    BaseType_t xBackup;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSED;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;

    xSocket.u.xTCP.usTimeout = 100;
    xSocket.u.xTCP.pxHandleConnected = ( FOnConnected_t ) HandleConnected;

    xBackup = xTCPWindowLoggingLevel;
    xTCPWindowLoggingLevel = 2;

    xHandleConnectedSocket = &xSocket;
    xHandleConnectedLength = 0;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );
    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( 100, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( eSOCKET_CLOSED, xSocket.xEventBits );

    xTCPWindowLoggingLevel = xBackup;
}

/**
 * @brief Test functionality when the state to be reached is closed and the
 *        current state is established state. Socket select bit is set to select except.
 */
void test_vTCPStateChange_EstablishedToClosedState_SocketActive_SelectExcept( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;
    BaseType_t xBackup;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eCLOSED;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;

    xSocket.u.xTCP.usTimeout = 100;
    xSocket.u.xTCP.pxHandleConnected = ( FOnConnected_t ) HandleConnected;
    xSocket.xSelectBits = eSELECT_EXCEPT;

    xBackup = xTCPWindowLoggingLevel;
    xTCPWindowLoggingLevel = 2;

    xHandleConnectedSocket = &xSocket;
    xHandleConnectedLength = 0;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );
    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eCLOSED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( 100, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( eSOCKET_CLOSED | ( eSELECT_EXCEPT << SOCKET_EVENT_BIT_COUNT ), xSocket.xEventBits );

    xTCPWindowLoggingLevel = xBackup;
}

/**
 * @brief Test functionality when the state to be reached is established and the
 *        current state is closed. Socket select bit is set to select except.
 */
void test_vTCPStateChange_ClosedToEstablishedState_SocketActive_SelectExcept( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;
    BaseType_t xBackup;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eESTABLISHED;
    xSocket.u.xTCP.eTCPState = eCLOSED;

    xSocket.u.xTCP.usTimeout = 100;
    xSocket.u.xTCP.pxHandleConnected = ( FOnConnected_t ) HandleConnected;
    xSocket.xSelectBits = eSELECT_EXCEPT;

    xHandleConnectedSocket = &xSocket;
    /* Expect the connected field to be set. */
    xHandleConnectedLength = 1;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eESTABLISHED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( 100, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( eSOCKET_CONNECT, xSocket.xEventBits );
}

/**
 * @brief Test functionality when the state to be reached is established and the
 *        current state is closed. Socket select bit is set to select write.
 */
void test_vTCPStateChange_ClosedToEstablishedState_SocketActive_SelectWrite( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;
    BaseType_t xBackup;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eESTABLISHED;
    xSocket.u.xTCP.eTCPState = eCLOSED;

    xSocket.u.xTCP.usTimeout = 100;
    xSocket.u.xTCP.pxHandleConnected = ( FOnConnected_t ) HandleConnected;
    xSocket.xSelectBits = eSELECT_WRITE;

    xHandleConnectedSocket = &xSocket;
    /* Expect the connected field to be set. */
    xHandleConnectedLength = 1;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eESTABLISHED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( 100, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( eSOCKET_CONNECT | ( eSELECT_WRITE << SOCKET_EVENT_BIT_COUNT ), xSocket.xEventBits );
}

/**
 * @brief Test functionality when the state to be reached is established and the
 *        current state is closed. Socket select bit is set to select write. Also, this socket
 *        is an orphan. Since parent socket is NULL and reuse bit is not set, it will hit an
 *        assertion.
 */
void test_vTCPStateChange_ClosedToEstablishedState_SelectWrite_QueuedBitSet( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;
    BaseType_t xBackup;

    memset( &xSocket, 0, sizeof( xSocket ) );
    eTCPState = eESTABLISHED;
    xSocket.u.xTCP.eTCPState = eCLOSED;

    xSocket.u.xTCP.usTimeout = 100;
    xSocket.xSelectBits = eSELECT_WRITE;
    /* if bPassQueued is true, this socket is an orphan until it gets connected. */
    xSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;

    catch_assert( vTCPStateChange( &xSocket, eTCPState ) );
}

/**
 * @brief Test functionality when the state to be reached is established and the
 *        current state is closed. Socket select bit is set to select write. Also, this socket
 *        is an orphan. Parent socket is non-NULL and reuse bit is not set.
 */
void test_vTCPStateChange_ClosedToEstablishedState_SelectWrite_QueuedBitSet_ParentNonNULL( void )
{
    FreeRTOS_Socket_t xSocket, xParentSock;
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;
    BaseType_t xBackup;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xParentSock, 0, sizeof( xParentSock ) );
    eTCPState = eESTABLISHED;
    xSocket.u.xTCP.eTCPState = eCLOSED;

    xSocket.u.xTCP.usTimeout = 100;
    xSocket.u.xTCP.pxHandleConnected = ( FOnConnected_t ) HandleConnected;
    xSocket.xSelectBits = eSELECT_WRITE;
    /* if bPassQueued is true, this socket is an orphan until it gets connected. */
    xSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;
    xSocket.u.xTCP.pxPeerSocket = &xParentSock;

    xHandleConnectedSocket = &xSocket;
    /* Expect the connected field to be set. */
    xHandleConnectedLength = 1;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xParentSock );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eESTABLISHED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( 100, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( eSOCKET_ACCEPT, xParentSock.xEventBits );
    TEST_ASSERT_EQUAL( &xSocket, xParentSock.u.xTCP.pxPeerSocket );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bPassQueued );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xSocket.u.xTCP.bits.bPassAccept );
}

/**
 * @brief Test functionality when the state to be reached is established and the
 *        current state is closed. Socket select bit is set to select write. Also, this socket
 *        is an orphan. Parent socket is non-NULL and reuse bit is not set. Additionally, the
 *        parent socket has a connected handler.
 */
void test_vTCPStateChange_ClosedToEstablishedState_QueuedBitSet_ParentNonNULL_HasHandler( void )
{
    FreeRTOS_Socket_t xSocket, xParentSock;
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;
    BaseType_t xBackup;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xParentSock, 0, sizeof( xParentSock ) );
    eTCPState = eESTABLISHED;
    xSocket.u.xTCP.eTCPState = eCLOSED;

    xSocket.u.xTCP.usTimeout = 100;
    xParentSock.u.xTCP.pxHandleConnected = ( FOnConnected_t ) HandleConnected;
    /* if bPassQueued is true, this socket is an orphan until it gets connected. */
    xSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;
    xSocket.u.xTCP.pxPeerSocket = &xParentSock;

    xHandleConnectedSocket = &xParentSock;
    /* Expect the connected field to be set. */
    xHandleConnectedLength = 1;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xParentSock );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eESTABLISHED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( 100, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( eSOCKET_ACCEPT, xParentSock.xEventBits );
    TEST_ASSERT_EQUAL( &xSocket, xParentSock.u.xTCP.pxPeerSocket );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bPassQueued );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xSocket.u.xTCP.bits.bPassAccept );
}

/**
 * @brief Test functionality when the state to be reached is established and the
 *        current state is closed. Socket select bit is set to select write. Also, this socket
 *        is an orphan. Parent socket is non-NULL and reuse bit is not set. Additionally, the
 *        parent socket has a connected handler.
 */
void test_vTCPStateChange_ClosedToEstablishedState_QueuedBitSet_ParentNonNULL_HasHandler1( void )
{
    FreeRTOS_Socket_t xSocket, xParentSock;
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;
    BaseType_t xBackup;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xParentSock, 0, sizeof( xParentSock ) );
    eTCPState = eESTABLISHED;
    xSocket.u.xTCP.eTCPState = eCLOSED;

    xSocket.u.xTCP.usTimeout = 100;
    xParentSock.u.xTCP.pxHandleConnected = ( FOnConnected_t ) HandleConnected;
    xSocket.u.xTCP.pxHandleConnected = ( FOnConnected_t ) HandleConnected;
    /* if bPassQueued is true, this socket is an orphan until it gets connected. */
    xSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;
    xSocket.u.xTCP.pxPeerSocket = &xParentSock;
    xParentSock.u.xTCP.pxPeerSocket = &xSocket;

    xHandleConnectedSocket = &xParentSock;
    /* Expect the connected field to be set. */
    xHandleConnectedLength = 1;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xParentSock );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eESTABLISHED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( 100, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( eSOCKET_ACCEPT, xParentSock.xEventBits );
    TEST_ASSERT_EQUAL( &xSocket, xParentSock.u.xTCP.pxPeerSocket );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bPassQueued );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xSocket.u.xTCP.bits.bPassAccept );
}

/**
 * @brief Test functionality when the state to be reached is established and the
 *        current state is closed. Socket select bit is set to select read. Also, this socket
 *        is an orphan. Parent socket is NULL and reuse bit is set.
 */
void test_vTCPStateChange_ClosedToEstablishedState_SelectRead_QueuedBitSet_ParentNULLReuse( void )
{
    FreeRTOS_Socket_t xSocket = { 0 };
    enum eTCP_STATE eTCPState;
    BaseType_t xTickCountAck = 0xAABBEEDD;
    BaseType_t xTickCountAlive = 0xAABBEFDD;
    BaseType_t xBackup;

    memset( &xSocket, 0, sizeof( xSocket ) );

    eTCPState = eESTABLISHED;
    xSocket.u.xTCP.eTCPState = eCLOSED;

    xSocket.u.xTCP.usTimeout = 100;
    xSocket.u.xTCP.pxHandleConnected = ( FOnConnected_t ) HandleConnected;
    xSocket.xSelectBits = eSELECT_READ;
    /* if bPassQueued is true, this socket is an orphan until it gets connected. */
    xSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;

    xHandleConnectedSocket = &xSocket;
    /* Expect the connected field to be set. */
    xHandleConnectedLength = 1;

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( &xSocket );

    vTCPStateChange( &xSocket, eTCPState );

    TEST_ASSERT_EQUAL( eESTABLISHED, xSocket.u.xTCP.eTCPState );
    TEST_ASSERT_EQUAL( xTickCountAck, xSocket.u.xTCP.xLastActTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bWaitKeepAlive );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bSendKeepAlive );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.ucKeepRepCount );
    TEST_ASSERT_EQUAL( xTickCountAlive, xSocket.u.xTCP.xLastAliveTime );
    TEST_ASSERT_EQUAL( 100, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xSocket.u.xTCP.bits.bPassQueued );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xSocket.u.xTCP.bits.bPassAccept );
    TEST_ASSERT_EQUAL( eSOCKET_ACCEPT | ( eSELECT_READ << SOCKET_EVENT_BIT_COUNT ), xSocket.xEventBits );
}

/**
 * @brief This function catch assert when  received a TCP packet
 *        with NULL descriptor.
 */
void test_xProcessReceivedTCPPacket_Null_Descriptor( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxNetworkBuffer->xDataLength = 40;

    catch_assert( xProcessReceivedTCPPacket( NULL ) );
}

/**
 * @brief This function catch assert when  received a TCP packet
 *        with NULL buffer.
 */
void test_xProcessReceivedTCPPacket_Null_Buffer( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = NULL;

    pxNetworkBuffer->xDataLength = 40;

    catch_assert( xProcessReceivedTCPPacket( pxNetworkBuffer ) );
}

/**
 * @brief This function validates received a TCP packet of
 *        frame type IPv6 and process the packet.
 */
void test_xProcessReceivedTCPPacket_IPv6_FrameType( void )
{
    BaseType_t Return = pdFALSE;
    uint8_t xEthBuffer[ 1500 ] = { 0 };

    ( ( EthernetHeader_t * ) xEthBuffer )->usFrameType = ipIPv6_FRAME_TYPE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = xEthBuffer;

    pxNetworkBuffer->xDataLength = 100;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv6_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( NULL );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFAIL, Return );
}

/**
 * @brief This function validates handling of a TCP packet of
 *        invalid frame type.
 */
void test_xProcessReceivedTCPPacket_Incorrect_FrameType( void )
{
    BaseType_t Return = pdFALSE;
    EthernetHeader_t xEthHeader;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xEthHeader;

    xEthHeader.usFrameType = 0;

    pxNetworkBuffer->xDataLength = 40;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet as data length check fails.
 */
void test_xProcessReceivedTCPPacket_Minimal_Data_Length( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    pxNetworkBuffer->xDataLength = 40;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet as socket is NULL.
 */
void test_xProcessReceivedTCPPacket_No_Socket( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_ACK;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( NULL );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet where there is no active socket.
 */
void test_xProcessReceivedTCPPacket_No_Active_Socket( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eCLOSE_WAIT;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdFALSE );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet when there is no active socket and there is a send reset.
 */
void test_xProcessReceivedTCPPacket_No_Active_Socket_Send_Reset( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eCLOSE_WAIT;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_ACK | tcpTCP_FLAG_FIN;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdFALSE );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet when tcp state is eTCP_LISTEN.
 */
void test_xProcessReceivedTCPPacket_Listen_State_Not_Syn_No_Rst( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eTCP_LISTEN;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet when tcp state is eTCP_LISTEN.
 */
void test_xProcessReceivedTCPPacket_Listen_State_Not_Syn_Rst( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eTCP_LISTEN;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_ACK;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    prvTCPSendReset_ExpectAnyArgsAndReturn( pdTRUE );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet when tcp state is eTCP_LISTEN and socket is NULL socket.
 */
void test_xProcessReceivedTCPPacket_Listen_State_Syn_Null_Socket( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eTCP_LISTEN;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    prvHandleListen_ExpectAnyArgsAndReturn( NULL );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates success in processing received TCP
 *        packet when tcp state is eTCP_LISTEN.
 */
void test_xProcessReceivedTCPPacket_Listen_State_Syn_NoOp_Sent_Something( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eTCP_LISTEN;
    pxSocket->u.xTCP.usTimeout = 1000;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = 0x50;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    prvHandleListen_ExpectAnyArgsAndReturn( pxSocket );
    xTaskGetTickCount_ExpectAndReturn( 1000 );
    xTaskGetTickCount_ExpectAndReturn( 1500 );
    prvTCPHandleState_ExpectAnyArgsAndReturn( 70 );
    prvTCPSendRepeated_ExpectAnyArgsAndReturn( 70 );
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdTRUE, Return );
}

/**
 * @brief This function validates success in processing received TCP
 *        packet when tcp state is eTCP_LISTEN.
 */
void test_xProcessReceivedTCPPacket_Listen_State_Syn_NoOp_Sent_None( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eTCP_LISTEN;
    pxSocket->u.xTCP.usTimeout = 1000;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = 0x50;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    prvHandleListen_ExpectAnyArgsAndReturn( pxSocket );
    xTaskGetTickCount_ExpectAndReturn( 1000 );
    xTaskGetTickCount_ExpectAndReturn( 1500 );
    prvTCPHandleState_ExpectAnyArgsAndReturn( 0 );
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdTRUE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet when tcp state is eTCP_LISTEN.
 */
void test_xProcessReceivedTCPPacket_Listen_State_Syn_With_Op_Check_Failed( void )
{
    BaseType_t Return = pdFALSE;
    NetworkBufferDescriptor_t * pNullBuffer = NULL;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eTCP_LISTEN;
    pxSocket->u.xTCP.usTimeout = 1000;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = 0x80;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    prvHandleListen_ExpectAnyArgsAndReturn( pxSocket );
    xTaskGetTickCount_ExpectAndReturn( 1000 );
    xTaskGetTickCount_ExpectAndReturn( 1500 );
    prvCheckOptions_ExpectAnyArgsAndReturn( pdFALSE );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}


/**
 * @brief This function validates success in processing received TCP
 *        packet when tcp state is eTCP_LISTEN.
 */
void test_xProcessReceivedTCPPacket_Listen_State_Syn_With_Op_Sent_Something_Buffer_Gone( void )
{
    BaseType_t Return = pdFALSE;
    NetworkBufferDescriptor_t * pNullBuffer = NULL;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eTCP_LISTEN;
    pxSocket->u.xTCP.usTimeout = 1000;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = 0x80;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    prvHandleListen_ExpectAnyArgsAndReturn( pxSocket );
    xTaskGetTickCount_ExpectAndReturn( 1000 );
    xTaskGetTickCount_ExpectAndReturn( 1500 );
    prvCheckOptions_ExpectAnyArgsAndReturn( pdTRUE );
    prvTCPHandleState_ExpectAnyArgsAndReturn( 70 );
    prvTCPSendRepeated_ExpectAnyArgsAndReturn( 70 );
    prvTCPSendRepeated_ReturnThruPtr_ppxNetworkBuffer( &pNullBuffer );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdTRUE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet when tcp state is eESTABLISHED.
 */
void test_xProcessReceivedTCPPacket_Establish_State_Syn( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet when tcp state is eESTABLISHED.
 */
void test_xProcessReceivedTCPPacket_ConnectSyn_State_Rst_Change_State( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 0;
    pxProtocolHeaders->xTCPHeader.ulAckNr = FreeRTOS_htonl( 1 );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( 1000 );
    xTaskGetTickCount_ExpectAndReturn( 1500 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( pxSocket );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( eCLOSED, pxSocket->u.xTCP.eTCPState );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet when tcp state is eESTABLISHED.
 */
void test_xProcessReceivedTCPPacket_ConnectSyn_State_Rst_SeqNo_Wrong( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket->u.xTCP.xTCPWindow.ulOurSequenceNumber = 0;
    pxProtocolHeaders->xTCPHeader.ulAckNr = FreeRTOS_htonl( 100 );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates success in processing received TCP
 *        packet when tcp state is eESTABLISHED.
 */
void test_xProcessReceivedTCPPacket_SynReceived_State_Rst( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eSYN_RECEIVED;
    pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber = 1000;
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = 0x50;
    pxProtocolHeaders->xTCPHeader.ulSequenceNumber = FreeRTOS_htonl( 1001 );
    pxProtocolHeaders->xTCPHeader.ulAckNr = FreeRTOS_htonl( 100 );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    xTaskGetTickCount_ExpectAndReturn( 1000 );
    xTaskGetTickCount_ExpectAndReturn( 1500 );
    prvTCPHandleState_ExpectAnyArgsAndReturn( 0 );
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdTRUE, Return );
}


/**
 * @brief This function validates failure in processing received TCP
 *        packet when tcp state is eESTABLISHED.
 */
void test_xProcessReceivedTCPPacket_Establish_State_Rst_Change_State( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber = 1000;
    pxProtocolHeaders->xTCPHeader.ulSequenceNumber = FreeRTOS_htonl( 1000 );
    pxProtocolHeaders->xTCPHeader.ulAckNr = FreeRTOS_htonl( 100 );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( 0 );
    xTaskGetTickCount_ExpectAndReturn( 1000 );
    xTaskGetTickCount_ExpectAndReturn( 1500 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vSocketWakeUpUser_Expect( pxSocket );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( eCLOSED, pxSocket->u.xTCP.eTCPState );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet when tcp state is eESTABLISHED.
 */
void test_xProcessReceivedTCPPacket_Establish_State_Rst_Seq_InRange( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber = 1000;
    pxProtocolHeaders->xTCPHeader.ulSequenceNumber = FreeRTOS_htonl( 1001 );
    pxProtocolHeaders->xTCPHeader.ulAckNr = FreeRTOS_htonl( 100 );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    xSequenceGreaterThan_ExpectAnyArgsAndReturn( pdTRUE );
    xSequenceLessThan_ExpectAnyArgsAndReturn( pdTRUE );
    prvTCPSendChallengeAck_ExpectAnyArgsAndReturn( pdTRUE );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet when tcp state is eESTABLISHED.
 */
void test_xProcessReceivedTCPPacket_Establish_State_Rst_Seq_OutRange1( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber = 1000;
    pxProtocolHeaders->xTCPHeader.ulSequenceNumber = FreeRTOS_htonl( 1001 );
    pxProtocolHeaders->xTCPHeader.ulAckNr = FreeRTOS_htonl( 100 );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    xSequenceGreaterThan_ExpectAnyArgsAndReturn( pdTRUE );
    xSequenceLessThan_ExpectAnyArgsAndReturn( pdFALSE );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates failure in processing received TCP
 *        packet when tcp state is eESTABLISHED.
 */
void test_xProcessReceivedTCPPacket_Establish_State_Rst_Seq_OutRange2( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber = 1000;
    pxProtocolHeaders->xTCPHeader.ulSequenceNumber = FreeRTOS_htonl( 1001 );
    pxProtocolHeaders->xTCPHeader.ulAckNr = FreeRTOS_htonl( 100 );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_RST;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    xSequenceGreaterThan_ExpectAnyArgsAndReturn( pdFALSE );

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}


/**
 * @brief This function validates success in processing received TCP
 *        packet when tcp state is eESTABLISHED.
 */
void test_xProcessReceivedTCPPacket_Establish_State_Ack( void )
{
    BaseType_t Return = pdFALSE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxSocket = &xSocket;
    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );

    pxNetworkBuffer->xDataLength = 100;
    pxSocket->u.xTCP.eTCPState = eESTABLISHED;
    pxSocket->u.xTCP.xTCPWindow.rx.ulCurrentSequenceNumber = 1000;
    pxProtocolHeaders->xTCPHeader.ucTCPOffset = 0x50;
    pxProtocolHeaders->xTCPHeader.ulSequenceNumber = FreeRTOS_htonl( 1001 );
    pxProtocolHeaders->xTCPHeader.ulAckNr = FreeRTOS_htonl( 100 );
    pxProtocolHeaders->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_ACK;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxTCPSocketLookup_ExpectAnyArgsAndReturn( pxSocket );
    prvTCPSocketIsActive_ExpectAnyArgsAndReturn( pdTRUE );
    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    xTaskGetTickCount_ExpectAndReturn( 1000 );
    xTaskGetTickCount_ExpectAndReturn( 1500 );
    prvTCPHandleState_ExpectAnyArgsAndReturn( 0 );
    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    Return = xProcessReceivedTCPPacket( pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdTRUE, Return );
}

static void test_Helper_ListInitialise( List_t * const pxList )
{
    /* The list structure contains a list item which is used to mark the
     * end of the list.  To initialise the list the list end is inserted
     * as the only list entry. */
    pxList->pxIndex = ( ListItem_t * ) &( pxList->xListEnd ); /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */

    /* The list end value is the highest possible value in the list to
     * ensure it remains at the end of the list. */
    pxList->xListEnd.xItemValue = portMAX_DELAY;

    /* The list end next and previous pointers point to itself so we know
     * when the list is empty. */
    pxList->xListEnd.pxNext = ( ListItem_t * ) &( pxList->xListEnd );     /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */
    pxList->xListEnd.pxPrevious = ( ListItem_t * ) &( pxList->xListEnd ); /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */

    pxList->uxNumberOfItems = ( UBaseType_t ) 0U;

    /* Write known values into the list if
     * configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    listSET_LIST_INTEGRITY_CHECK_1_VALUE( pxList );
    listSET_LIST_INTEGRITY_CHECK_2_VALUE( pxList );
}

static void test_Helper_ListInsertEnd( List_t * const pxList,
                                       ListItem_t * const pxNewListItem )
{
    ListItem_t * const pxIndex = pxList->pxIndex;

    /* Only effective when configASSERT() is also defined, these tests may catch
     * the list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
    listTEST_LIST_INTEGRITY( pxList );
    listTEST_LIST_ITEM_INTEGRITY( pxNewListItem );

    /* Insert a new list item into pxList, but rather than sort the list,
     * makes the new list item the last item to be removed by a call to
     * listGET_OWNER_OF_NEXT_ENTRY(). */
    pxNewListItem->pxNext = pxIndex;
    pxNewListItem->pxPrevious = pxIndex->pxPrevious;

    /* Only used during decision coverage testing. */
    mtCOVERAGE_TEST_DELAY();

    pxIndex->pxPrevious->pxNext = pxNewListItem;
    pxIndex->pxPrevious = pxNewListItem;

    /* Remember which list the item is in. */
    pxNewListItem->pxContainer = pxList;

    ( pxList->uxNumberOfItems )++;
}

/**
 * @brief This function validates not finding a new client
 *        in case the list to iterate through is empty.
 */
void test_xTCPCheckNewClient_Empty_List( void )
{
    BaseType_t Return = pdFALSE;

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    MiniListItem_t EndItem;

    test_Helper_ListInitialise( pSocketList );

    pxSocket->usLocalPort = 40000;
    Return = xTCPCheckNewClient( pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxPeerSocket );
}

/**
 * @brief This function validates not finding a new client
 *        with a given port.
 */
void test_xTCPCheckNewClient_Not_Found_No_Port( void )
{
    BaseType_t Return = pdFALSE;

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 443;

    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );

    pxSocket->usLocalPort = FreeRTOS_ntohs( 40000 );
    Return = xTCPCheckNewClient( pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxPeerSocket );
}

/**
 * @brief This function validates not finding a new client
 *        in of UDP protocol.
 */
void test_xTCPCheckNewClient_Not_Found_Not_TCP( void )
{
    BaseType_t Return = pdFALSE;

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 40000;
    pxSocket->xBoundSocketListItem.pvOwner = pxSocket;
    pxSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    pxSocket->u.xTCP.bits.bPassAccept = pdTRUE;


    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );

    pxSocket->usLocalPort = FreeRTOS_ntohs( 40000 );
    Return = xTCPCheckNewClient( pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxPeerSocket );
}

/**
 * @brief This function validates not finding a new client
 *        in case bPassAccept is not set.
 */
void test_xTCPCheckNewClient_Not_Found_Not_Accept( void )
{
    BaseType_t Return = pdFALSE;

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 40000;
    pxSocket->xBoundSocketListItem.pvOwner = pxSocket;
    pxSocket->ucProtocol = FREERTOS_IPPROTO_TCP;
    pxSocket->u.xTCP.bits.bPassAccept = pdFALSE;


    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );

    pxSocket->usLocalPort = FreeRTOS_ntohs( 40000 );
    Return = xTCPCheckNewClient( pxSocket );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
    TEST_ASSERT_EQUAL( NULL, pxSocket->u.xTCP.pxPeerSocket );
}

/**
 * @brief This function validates the case of finding
 *        a new client.
 */
void test_xTCPCheckNewClient_Found( void )
{
    BaseType_t Return = pdFALSE;

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 40000;
    pxSocket->xBoundSocketListItem.pvOwner = pxSocket;
    pxSocket->ucProtocol = FREERTOS_IPPROTO_TCP;
    pxSocket->u.xTCP.bits.bPassAccept = pdTRUE;

    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );

    pxSocket->usLocalPort = FreeRTOS_ntohs( 40000 );
    Return = xTCPCheckNewClient( pxSocket );
    TEST_ASSERT_EQUAL( pdTRUE, Return );
    TEST_ASSERT_EQUAL_PTR( pxSocket, pxSocket->u.xTCP.pxPeerSocket );
}

/**
 * @brief This function validates the case when the child socket is found in
 * the bounded socket list.
 */
void test_vTCPRemoveTCPChild_ChildSocketFound( void )
{
    BaseType_t Return = pdFALSE;

    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xChildSocket;

    memset( &xChildSocket, 0, sizeof( xSocket ) );

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 40000;
    pxSocket->xBoundSocketListItem.pvOwner = pxSocket;
    pxSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    pxSocket->u.xTCP.bits.bPassAccept = pdTRUE;
    pxSocket->u.xTCP.pxPeerSocket = &xChildSocket;

    xChildSocket.usLocalPort = FreeRTOS_ntohs( 40000 );

    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );

    pxSocket->usLocalPort = FreeRTOS_ntohs( 40000 );
    Return = vTCPRemoveTCPChild( &xChildSocket );
    TEST_ASSERT_EQUAL( pdTRUE, Return );
}

/**
 * @brief This function validates the case when the child socket is found in
 * the bounded socket list but non matching port number.
 */
void test_vTCPRemoveTCPChild_ChildSocketFound_DifferentPortNumber( void )
{
    BaseType_t Return = pdFALSE;

    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xChildSocket;

    memset( &xChildSocket, 0, sizeof( xSocket ) );

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 40000;
    pxSocket->xBoundSocketListItem.pvOwner = pxSocket;
    pxSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    pxSocket->u.xTCP.bits.bPassAccept = pdTRUE;
    pxSocket->u.xTCP.pxPeerSocket = &xChildSocket;

    xChildSocket.usLocalPort = FreeRTOS_ntohs( 80000 );

    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );

    pxSocket->usLocalPort = FreeRTOS_ntohs( 40000 );
    Return = vTCPRemoveTCPChild( &xChildSocket );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}

/**
 * @brief This function validates the case when no child socket is found in
 * the bounded socket list but matching port number is present.
 */
void test_vTCPRemoveTCPChild_NoChildSocketFound_MatchingPortNumber( void )
{
    BaseType_t Return = pdFALSE;

    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xChildSocket;

    memset( &xChildSocket, 0, sizeof( xSocket ) );

    pxSocket = &xSocket;
    List_t * pSocketList = &xBoundTCPSocketsList;
    ListItem_t NewEntry;

    pxSocket->xBoundSocketListItem.xItemValue = 40000;
    pxSocket->xBoundSocketListItem.pvOwner = pxSocket;
    pxSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    pxSocket->u.xTCP.bits.bPassAccept = pdTRUE;
    pxSocket->u.xTCP.pxPeerSocket = NULL;

    xChildSocket.usLocalPort = FreeRTOS_ntohs( 40000 );

    test_Helper_ListInitialise( pSocketList );
    test_Helper_ListInsertEnd( &xBoundTCPSocketsList, &( pxSocket->xBoundSocketListItem ) );

    pxSocket->usLocalPort = FreeRTOS_ntohs( 40000 );
    Return = vTCPRemoveTCPChild( &xChildSocket );
    TEST_ASSERT_EQUAL( pdFALSE, Return );
}
