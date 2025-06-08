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

/*#include "mock_task.h" */
#include "mock_TCP_IP_DiffConfig_list_macros.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_queue.h"
#include "mock_task.h"
#include "mock_event_groups.h"
#include "mock_list.h"

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

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_TCP_IP.h"

FreeRTOS_Socket_t xSocket, * pxSocket;
NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;

extern BaseType_t xTCPWindowLoggingLevel;
extern FreeRTOS_Socket_t * xSocketToListen;

uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ] =
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x08, 0x00, 0x45, 0x00,
    0x00, 0x34, 0x15, 0xc2, 0x40, 0x00, 0x40, 0x06, 0xa8, 0x8e, 0xc0, 0xa8, 0x00, 0x08, 0xac, 0xd9,
    0x0e, 0xea, 0xea, 0xfe, 0x01, 0xbb, 0x8b, 0xaf, 0x8a, 0x24, 0xdc, 0x96, 0x95, 0x7a, 0x80, 0x10,
    0x01, 0xf5, 0x7c, 0x9a, 0x00, 0x00, 0x01, 0x01, 0x08, 0x0a, 0xb8, 0x53, 0x57, 0x27, 0xb2, 0xce,
    0xc3, 0x17
};

static Socket_t xHandleConnectedSocket;
static size_t xHandleConnectedLength;
static void HandleConnected( Socket_t xSocket,
                             size_t xLength )
{
    TEST_ASSERT_EQUAL( xHandleConnectedSocket, xSocket );
    TEST_ASSERT_EQUAL( xHandleConnectedLength, xLength );
}

/* test xTCPSocketCheck function */
void test_xTCPSocketCheck_StateEstablished_TxStreamNonNull1( void )
{
    BaseType_t xReturn, xToReturn = 0xAABBCCDD;
    FreeRTOS_Socket_t xSocket;
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

    prvTCPSendPacket_ExpectAndReturn( &xSocket, 0 );

    prvTCPStatusAgeCheck_ExpectAndReturn( &xSocket, xToReturn );

    xReturn = xTCPSocketCheck( &xSocket );

    TEST_ASSERT_EQUAL( xToReturn, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxAckMessage );
    TEST_ASSERT_EQUAL( 1U, xSocket.u.xTCP.usTimeout );
}

/* @brief Test vTCPStateChange function when the state to be reached is established and the
 *        current state is closed. Socket select bit is set to select write. Also, this socket
 *        is an orphan. Since parent socket is NULL and reuse bit is not set, it will lead to
 *        the socket being NULL. */
void test_vTCPStateChange_ClosedToEstablishedState_SelectWrite_QueuedBitSet( void )
{
    FreeRTOS_Socket_t xSocket;
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

    prvTCPSocketIsActive_ExpectAndReturn( xSocket.u.xTCP.eTCPState, pdTRUE );

    xTaskGetTickCount_ExpectAndReturn( xTickCountAck );
    xTaskGetTickCount_ExpectAndReturn( xTickCountAlive );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    vTCPStateChange( &xSocket, eTCPState );
}

/* @brief Test vTCPStateChange function when the state to be reached is closed wait
 *        and current state is equal to syn first. */
void test_vTCPStateChange_ClosedWaitState_CurrentStateSynFirstNextStateCloseWait( void )
{
    FreeRTOS_Socket_t xSocket;
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
