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
#include "mock_Sockets_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_portable.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_IPv4_Sockets.h"
#include "mock_FreeRTOS_IPv6_Sockets.h"
#include "mock_FreeRTOS_Sockets.h"

#include "FreeRTOS_Sockets.h"

#include "FreeRTOS_Sockets_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

extern List_t xBoundUDPSocketsList;
extern List_t xBoundTCPSocketsList;

/* 2001::1 */
static IPv6_Address_t xIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

/* ============================== Test Cases ============================== */

/**
 * @brief Creation of socket when socket size determination fails as IP task is not ready.
 */
void test_FreeRTOS_socket_SockSizeFailure( void )
{
    Socket_t xSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, xSocket );
}

/**
 * @brief Creation of socket when socket size determination fails as IP task is not ready.
 */
void test_FreeRTOS_socket_SockSizeFailure_SockDependent( void )
{
    Socket_t xSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM | FREERTOS_SOCK_DGRAM;
    BaseType_t xProtocol = FREERTOS_SOCK_DEPENDENT_PROTO;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, xSocket );
}

/**
 * @brief Creation of socket when no memory could be allocated.
 */
void test_FreeRTOS_socket_NoMemory( void )
{
    Socket_t xSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), NULL );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, xSocket );
}

/**
 * @brief Creation of socket when event group creation fails.
 */
void test_FreeRTOS_socket_EventGroupCreationFailed( void )
{
    Socket_t xSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    FreeRTOS_Socket_t const * pxSocket = NULL;
    uint8_t ucSocket[ ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ) ];

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), ( void * ) ucSocket );

    xEventGroupCreate_ExpectAndReturn( NULL );

    vPortFree_Expect( ucSocket );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, xSocket );
}

/**
 * @brief Creation of socket when the protocol is TCP.
 */
void test_FreeRTOS_socket_TCPSocket_ProtocolDependent( void )
{
    Socket_t xSocket;
    FreeRTOS_Socket_t * pxSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_SOCK_DEPENDENT_PROTO;
    uint8_t ucSocket[ ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ) ];
    uint8_t xEventGroup[ sizeof( uintptr_t ) ];

    pxSocket = ( FreeRTOS_Socket_t * ) ucSocket;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), ( void * ) ucSocket );

    xEventGroupCreate_ExpectAndReturn( ( EventGroupHandle_t ) xEventGroup );

    FreeRTOS_round_up_ExpectAndReturn( ipconfigTCP_TX_BUFFER_LENGTH, ipconfigTCP_MSS, 0xAABB );
    FreeRTOS_max_size_t_ExpectAndReturn( 1U, ( uint32_t ) ( ipconfigTCP_RX_BUFFER_LENGTH / 2U ) / ipconfigTCP_MSS, 0x1234 );
    FreeRTOS_max_size_t_ExpectAndReturn( 1U, ( uint32_t ) ( 0xAABB / 2U ) / ipconfigTCP_MSS, 0x3456 );

    vListInitialiseItem_Expect( &( pxSocket->xBoundSocketListItem ) );

    listSET_LIST_ITEM_OWNER_Expect( &( pxSocket->xBoundSocketListItem ), pxSocket );


    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( ucSocket, xSocket );
    TEST_ASSERT_EQUAL( xSocket->xEventGroup, xEventGroup );
    TEST_ASSERT_EQUAL( xSocket->xReceiveBlockTime, ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->xSendBlockTime, ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->ucSocketOptions, ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT );
    TEST_ASSERT_EQUAL( xSocket->ucProtocol, ( uint8_t ) FREERTOS_IPPROTO_TCP );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.usMSS, ( uint16_t ) ipconfigTCP_MSS );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.uxRxStreamSize, ( size_t ) ipconfigTCP_RX_BUFFER_LENGTH );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.uxTxStreamSize, 0xAABB );
    TEST_ASSERT_EQUAL( 0x1234, pxSocket->u.xTCP.uxRxWinSize );
    TEST_ASSERT_EQUAL( 0x3456, pxSocket->u.xTCP.uxTxWinSize );
}

/**
 * @brief Creation of socket when the protocol is TCP.
 */
void test_FreeRTOS_socket_TCPSocket( void )
{
    Socket_t xSocket;
    FreeRTOS_Socket_t * pxSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    uint8_t ucSocket[ ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ) ];
    uint8_t xEventGroup[ sizeof( uintptr_t ) ];

    pxSocket = ( FreeRTOS_Socket_t * ) ucSocket;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), ( void * ) ucSocket );

    xEventGroupCreate_ExpectAndReturn( ( EventGroupHandle_t ) xEventGroup );

    FreeRTOS_round_up_ExpectAndReturn( ipconfigTCP_TX_BUFFER_LENGTH, ipconfigTCP_MSS, 0xAABB );
    FreeRTOS_max_size_t_ExpectAndReturn( 1U, ( uint32_t ) ( ipconfigTCP_RX_BUFFER_LENGTH / 2U ) / ipconfigTCP_MSS, 0x1234 );
    FreeRTOS_max_size_t_ExpectAndReturn( 1U, ( uint32_t ) ( 0xAABB / 2U ) / ipconfigTCP_MSS, 0x3456 );

    vListInitialiseItem_Expect( &( pxSocket->xBoundSocketListItem ) );

    listSET_LIST_ITEM_OWNER_Expect( &( pxSocket->xBoundSocketListItem ), pxSocket );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( ucSocket, xSocket );
    TEST_ASSERT_EQUAL( xSocket->xEventGroup, xEventGroup );
    TEST_ASSERT_EQUAL( xSocket->xReceiveBlockTime, ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->xSendBlockTime, ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->ucSocketOptions, ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT );
    TEST_ASSERT_EQUAL( xSocket->ucProtocol, ( uint8_t ) xProtocol );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.usMSS, ( uint16_t ) ipconfigTCP_MSS );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.uxRxStreamSize, ( size_t ) ipconfigTCP_RX_BUFFER_LENGTH );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.uxTxStreamSize, 0xAABB );
    TEST_ASSERT_EQUAL( 0x1234, pxSocket->u.xTCP.uxRxWinSize );
    TEST_ASSERT_EQUAL( 0x3456, pxSocket->u.xTCP.uxTxWinSize );
}

/**
 * @brief Creation of socket when the protocol is UDP.
 */
void test_FreeRTOS_socket_UDPSocket( void )
{
    Socket_t xSocket;
    FreeRTOS_Socket_t * pxSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_IPPROTO_UDP;
    uint8_t ucSocket[ ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xUDP ) ];
    uint8_t xEventGroup[ sizeof( uintptr_t ) ];

    pxSocket = ( FreeRTOS_Socket_t * ) ucSocket;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xUDP ), ( void * ) ucSocket );

    xEventGroupCreate_ExpectAndReturn( ( EventGroupHandle_t ) xEventGroup );

    vListInitialise_Expect( &( pxSocket->u.xUDP.xWaitingPacketsList ) );

    vListInitialiseItem_Expect( &( pxSocket->xBoundSocketListItem ) );

    listSET_LIST_ITEM_OWNER_Expect( &( pxSocket->xBoundSocketListItem ), pxSocket );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( ucSocket, xSocket );
    TEST_ASSERT_EQUAL( xSocket->xEventGroup, xEventGroup );
    TEST_ASSERT_EQUAL( xSocket->xReceiveBlockTime, ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->xSendBlockTime, ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->ucSocketOptions, ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT );
    TEST_ASSERT_EQUAL( xSocket->ucProtocol, ( uint8_t ) xProtocol );
    TEST_ASSERT_EQUAL( xSocket->u.xUDP.uxMaxPackets, ( UBaseType_t ) ipconfigUDP_MAX_RX_PACKETS );
}

/**
 * @brief Creation of socket when the protocol is UDP.
 */
void test_FreeRTOS_socket_UDPSocket_ProtocolDependent( void )
{
    Socket_t xSocket;
    FreeRTOS_Socket_t * pxSocket;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_SOCK_DEPENDENT_PROTO;
    uint8_t ucSocket[ ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xUDP ) ];
    uint8_t xEventGroup[ sizeof( uintptr_t ) ];

    pxSocket = ( FreeRTOS_Socket_t * ) ucSocket;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xUDP ), ( void * ) ucSocket );

    xEventGroupCreate_ExpectAndReturn( ( EventGroupHandle_t ) xEventGroup );

    vListInitialise_Expect( &( pxSocket->u.xUDP.xWaitingPacketsList ) );

    vListInitialiseItem_Expect( &( pxSocket->xBoundSocketListItem ) );

    listSET_LIST_ITEM_OWNER_Expect( &( pxSocket->xBoundSocketListItem ), pxSocket );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( ucSocket, xSocket );
    TEST_ASSERT_EQUAL( xSocket->xEventGroup, xEventGroup );
    TEST_ASSERT_EQUAL( xSocket->xReceiveBlockTime, ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->xSendBlockTime, ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->ucSocketOptions, ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT );
    TEST_ASSERT_EQUAL( xSocket->ucProtocol, ( uint8_t ) FREERTOS_IPPROTO_UDP );
    TEST_ASSERT_EQUAL( xSocket->u.xUDP.uxMaxPackets, ( UBaseType_t ) ipconfigUDP_MAX_RX_PACKETS );
}

/**
 * @brief Assertion when unknown domain comes.
 */
void test_FreeRTOS_socket_unknownDomain( void )
{
    BaseType_t xDomain = FREERTOS_AF_INET + 1, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_SOCK_DEPENDENT_PROTO;

    catch_assert( FreeRTOS_socket( xDomain, xType, xProtocol ) );
}

/**
 * @brief Creation of socket when the protocol is TCPv6.
 */
void test_FreeRTOS_socket_TCPv6Socket( void )
{
    Socket_t xSocket;
    FreeRTOS_Socket_t * pxSocket;
    BaseType_t xDomain = FREERTOS_AF_INET6, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    uint8_t ucSocket[ ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ) ];
    uint8_t xEventGroup[ sizeof( uintptr_t ) ];

    pxSocket = ( FreeRTOS_Socket_t * ) ucSocket;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    pvPortMalloc_ExpectAndReturn( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), ( void * ) ucSocket );

    xEventGroupCreate_ExpectAndReturn( ( EventGroupHandle_t ) xEventGroup );

    FreeRTOS_round_up_ExpectAndReturn( ipconfigTCP_TX_BUFFER_LENGTH, ipconfigTCP_MSS, 0xAABB );
    FreeRTOS_max_size_t_ExpectAndReturn( 1U, ( uint32_t ) ( ipconfigTCP_RX_BUFFER_LENGTH / 2U ) / ipconfigTCP_MSS, 0x1234 );
    FreeRTOS_max_size_t_ExpectAndReturn( 1U, ( uint32_t ) ( 0xAABB / 2U ) / ipconfigTCP_MSS, 0x3456 );

    vListInitialiseItem_Expect( &( pxSocket->xBoundSocketListItem ) );

    listSET_LIST_ITEM_OWNER_Expect( &( pxSocket->xBoundSocketListItem ), pxSocket );

    xSocket = FreeRTOS_socket( xDomain, xType, xProtocol );

    TEST_ASSERT_EQUAL( ucSocket, xSocket );
    TEST_ASSERT_EQUAL( xSocket->xEventGroup, xEventGroup );
    TEST_ASSERT_EQUAL( xSocket->xReceiveBlockTime, ipconfigSOCK_DEFAULT_RECEIVE_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->xSendBlockTime, ipconfigSOCK_DEFAULT_SEND_BLOCK_TIME );
    TEST_ASSERT_EQUAL( xSocket->ucSocketOptions, ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT );
    TEST_ASSERT_EQUAL( xSocket->ucProtocol, ( uint8_t ) xProtocol );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.usMSS, ( uint16_t ) ipconfigTCP_MSS - ( ipSIZE_OF_IPv6_HEADER - ipSIZE_OF_IPv4_HEADER ) );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.uxRxStreamSize, ( size_t ) ipconfigTCP_RX_BUFFER_LENGTH );
    TEST_ASSERT_EQUAL( xSocket->u.xTCP.uxTxStreamSize, 0xAABB );
    TEST_ASSERT_EQUAL( 0x1234, pxSocket->u.xTCP.uxRxWinSize );
    TEST_ASSERT_EQUAL( 0x3456, pxSocket->u.xTCP.uxTxWinSize );
}

/**
 * @brief Creation of socket-set when there is no memory.
 */
void test_FreeRTOS_CreateSocketSet_NoMemory( void )
{
    SocketSelect_t * pxSocketSet;

    pvPortMalloc_ExpectAndReturn( sizeof( *pxSocketSet ), NULL );

    pxSocketSet = FreeRTOS_CreateSocketSet();

    TEST_ASSERT_EQUAL( NULL, pxSocketSet );
}

/**
 * @brief Creation of socket-set when event group creation fails.
 */
void test_FreeRTOS_CreateSocketSet_EventGroupCreationFails( void )
{
    SocketSelect_t * pxSocketSet;
    uint8_t ucSocket[ sizeof( *pxSocketSet ) ];

    pvPortMalloc_ExpectAndReturn( sizeof( *pxSocketSet ), ucSocket );

    xEventGroupCreate_ExpectAndReturn( NULL );

    vPortFree_Expect( ucSocket );

    pxSocketSet = FreeRTOS_CreateSocketSet();

    TEST_ASSERT_EQUAL( NULL, pxSocketSet );
}

/**
 * @brief Creation of socket-set happy path.
 */
void test_FreeRTOS_CreateSocketSet_HappyPath( void )
{
    SocketSelect_t * pxSocketSet;
    uint8_t ucSocketSet[ sizeof( *pxSocketSet ) ];
    uint8_t xEventGroup[ sizeof( uintptr_t ) ];

    pvPortMalloc_ExpectAndReturn( sizeof( *pxSocketSet ), ucSocketSet );

    xEventGroupCreate_ExpectAndReturn( ( EventGroupHandle_t ) xEventGroup );

    pxSocketSet = FreeRTOS_CreateSocketSet();

    TEST_ASSERT_EQUAL( ucSocketSet, pxSocketSet );
    TEST_ASSERT_EQUAL( xEventGroup, pxSocketSet->xSelectGroup );
}

/**
 * @brief Deletion of socket-set happy path.
 */
void test_FreeRTOS_DeleteSocketSet_happyPath( void )
{
    SocketSet_t xSocketSet;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    FreeRTOS_DeleteSocketSet( xSocketSet );
}

/**
 * @brief Deletion of socket-set when sending of event to IP task fails.
 */
void test_FreeRTOS_DeleteSocketSet_SendingFailed( void )
{
    SocketSet_t xSocketSet;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdFAIL );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    FreeRTOS_DeleteSocketSet( xSocketSet );
}

/**
 * @brief Assertion when socket is NULL.
 */
void test_FreeRTOS_FD_SET_CatchAssert1( void )
{
    Socket_t xSocket = NULL;
    SocketSet_t xSocketSet;
    EventBits_t xBitsToSet;

    catch_assert( FreeRTOS_FD_SET( xSocket, xSocketSet, xBitsToSet ) );
}

/**
 * @brief Assertion when socket-set is NULL.
 */
void test_FreeRTOS_FD_SET_CatchAssert2( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    SocketSet_t xSocketSet = NULL;
    EventBits_t xBitsToSet;

    catch_assert( FreeRTOS_FD_SET( xSocket, xSocketSet, xBitsToSet ) );
}

/**
 * @brief Test when no-bits are to be set.
 */
void test_FreeRTOS_FD_SET_NoBitsToSet( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    SocketSet_t xSocketSet = ( SocketSet_t ) ucSocketSet;
    EventBits_t xBitsToSet = 0;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    FreeRTOS_FD_SET( xSocket, xSocketSet, xBitsToSet );

    TEST_ASSERT_EQUAL( 0, xSocket->xSelectBits );
}

/**
 * @brief Test for when all bits are to be set.
 */
void test_FreeRTOS_FD_SET_AllBitsToSet( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    SocketSet_t xSocketSet = ( SocketSet_t ) ucSocketSet;
    EventBits_t xBitsToSet = eSELECT_ALL;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, 0 );
    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    FreeRTOS_FD_SET( xSocket, xSocketSet, xBitsToSet );

    TEST_ASSERT_EQUAL( eSELECT_ALL, xSocket->xSelectBits );
    TEST_ASSERT_EQUAL( ucSocketSet, xSocket->pxSocketSet );
}

/**
 * @brief Assertion when socket is NULL.
 */
void test_FreeRTOS_FD_CLR_CatchAssert1( void )
{
    Socket_t xSocket = NULL;
    SocketSet_t xSocketSet;
    EventBits_t xBitsToClear;

    catch_assert( FreeRTOS_FD_CLR( xSocket, xSocketSet, xBitsToClear ) );
}

/**
 * @brief Assertion when socket-set is NULL.
 */
void test_FreeRTOS_FD_CLR_CatchAssert2( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    SocketSet_t xSocketSet = NULL;
    EventBits_t xBitsToClear;

    catch_assert( FreeRTOS_FD_CLR( xSocket, xSocketSet, xBitsToClear ) );
}

/**
 * @brief No bits to be cleared.
 */
void test_FreeRTOS_FD_CLR_NoBitsToClear( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    SocketSet_t xSocketSet = ( SocketSet_t ) ucSocketSet;
    EventBits_t xBitsToClear = 0;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    xSocket->xSelectBits = 0;

    FreeRTOS_FD_CLR( xSocket, xSocketSet, xBitsToClear );

    TEST_ASSERT_EQUAL( NULL, xSocket->pxSocketSet );
    TEST_ASSERT_EQUAL( 0, xSocket->xSelectBits );
}

/**
 * @brief All bits to be cleared.
 */
void test_FreeRTOS_FD_CLR_AllBitsToClear( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    SocketSet_t xSocketSet = ( SocketSet_t ) ucSocketSet;
    EventBits_t xBitsToClear = 0;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    xSocket->xSelectBits = eSELECT_ALL;

    FreeRTOS_FD_CLR( xSocket, xSocketSet, xBitsToClear );

    TEST_ASSERT_EQUAL( xSocketSet, xSocket->pxSocketSet );
    TEST_ASSERT_EQUAL( eSELECT_ALL, xSocket->xSelectBits );
}

/**
 * @brief Assertion when socket is NULL.
 */
void test_FreeRTOS_FD_ISSET_CatchAssert1( void )
{
    Socket_t xSocket = NULL;
    SocketSet_t xSocketSet;

    /* Assertion that the socket must be non-NULL. */
    catch_assert( FreeRTOS_FD_ISSET( xSocket, xSocketSet ) );
}

/**
 * @brief Assertion when socket-set is NULL.
 */
void test_FreeRTOS_FD_ISSET_CatchAssert2( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    SocketSet_t xSocketSet = NULL;

    /* Assertion that the socket set must be non-NULL. */
    catch_assert( FreeRTOS_FD_ISSET( xSocket, xSocketSet ) );
}

/**
 * @brief Test for when the socket set is different.
 */
void test_FreeRTOS_FD_ISSET_SocketSetDifferent( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    SocketSet_t xSocketSet = ( SocketSet_t ) ucSocketSet;
    EventBits_t xReturn;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    xReturn = FreeRTOS_FD_ISSET( xSocket, xSocketSet );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Happy path.
 */
void test_FreeRTOS_FD_ISSET_SocketSetSame( void )
{
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    SocketSet_t xSocketSet = ( SocketSet_t ) ucSocketSet;
    EventBits_t xReturn;

    memset( ucSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( ucSocketSet, 0, sizeof( SocketSelect_t ) );

    xSocket->pxSocketSet = xSocketSet;

    xSocket->xSocketBits = 0x12;

    xReturn = FreeRTOS_FD_ISSET( xSocket, xSocketSet );

    TEST_ASSERT_EQUAL( 0x12 & eSELECT_ALL, xReturn );
}

/**
 * @brief Assertion when socket-set is NULL.
 */
void test_FreeRTOS_select_CatchAssert( void )
{
    BaseType_t xReturn;
    SocketSet_t xSocketSet = NULL;
    TickType_t xBlockTimeTicks;

    /* Assertion that the socket set must be non-NULL. */
    catch_assert( FreeRTOS_select( xSocketSet, xBlockTimeTicks ) );
}

/**
 * @brief Test case when bits matched.
 */
void test_FreeRTOS_select_BitsMatched( void )
{
    BaseType_t xReturn;
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    SocketSet_t xSocketSet = ( SocketSet_t ) ucSocketSet;
    TickType_t xBlockTimeTicks = 0xAB12;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( ( EventBits_t ) eSELECT_ALL ), pdFALSE, pdFALSE, xBlockTimeTicks, pdFALSE );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdFALSE );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, 0, 0x123 );

    xReturn = FreeRTOS_select( xSocketSet, xBlockTimeTicks );

    TEST_ASSERT_EQUAL( 0x123, xReturn );
}

/**
 * @brief Call to select timed out.
 */
void test_FreeRTOS_select_Timeout( void )
{
    BaseType_t xReturn;
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    SocketSet_t xSocketSet = ( SocketSet_t ) ucSocketSet;
    TickType_t xBlockTimeTicks = 0xAB12;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( ( EventBits_t ) eSELECT_ALL ), pdFALSE, pdFALSE, xBlockTimeTicks, pdFALSE );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdFALSE );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, 0, 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xReturn = FreeRTOS_select( xSocketSet, xBlockTimeTicks );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Call to select timed out second time.
 */
void test_FreeRTOS_select_TimeoutSecondTime( void )
{
    BaseType_t xReturn;
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    SocketSet_t xSocketSet = ( SocketSet_t ) ucSocketSet;
    TickType_t xBlockTimeTicks = 0xAB12;
    int i;

    vTaskSetTimeOutState_ExpectAnyArgs();

    for( i = 0; i < 2; i++ )
    {
        xEventGroupWaitBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( ( EventBits_t ) eSELECT_ALL ), pdFALSE, pdFALSE, xBlockTimeTicks, pdFALSE );

        xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdFALSE );

        xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

        xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, 0, 0 );

        if( i == 0 )
        {
            xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );
        }
        else
        {
            xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );
        }
    }

    xReturn = FreeRTOS_select( xSocketSet, xBlockTimeTicks );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Found the bits for which the select function was waiting.
 */
void test_FreeRTOS_select_FoundWaitBits( void )
{
    BaseType_t xReturn;
    uint8_t ucSocketSet[ sizeof( SocketSelect_t ) ];
    SocketSet_t xSocketSet = ( SocketSet_t ) ucSocketSet;
    TickType_t xBlockTimeTicks = 0xAB12;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( ( EventBits_t ) eSELECT_ALL ), pdFALSE, pdFALSE, xBlockTimeTicks, eSELECT_INTR );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet->xSelectGroup, ( BaseType_t ) eSELECT_INTR, pdFALSE );

    xReturn = FreeRTOS_select( xSocketSet, xBlockTimeTicks );

    TEST_ASSERT_EQUAL( eSELECT_INTR, xReturn );
}

/**
 * @brief Bind cannot be call from IP task.
 */
void test_FreeRTOS_bind_catchAssert( void )
{
    BaseType_t xReturn;
    Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength = 0;

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    catch_assert( FreeRTOS_bind( xSocket, &xAddress, xAddressLength ) );
}

/**
 * @brief Binding a NULL socket.
 */
void test_FreeRTOS_bind_SocketIsNULL( void )
{
    BaseType_t xReturn;
    Socket_t xSocket = NULL;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength = 0;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xReturn = FreeRTOS_bind( xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Binding invalid socket.
 */
void test_FreeRTOS_bind_SocketIsInvalid( void )
{
    BaseType_t xReturn;
    Socket_t xSocket = FREERTOS_INVALID_SOCKET;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength = 0;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    xReturn = FreeRTOS_bind( xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Binding already bound socket.
 */
void test_FreeRTOS_bind_SocketIsAlreadyBound( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xReturn = FreeRTOS_bind( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Binding event to IP task cannot be sent.
 */
void test_FreeRTOS_bind_SendToIPTaskFailed( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdFAIL );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_bind( &xSocket, NULL, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ECANCELED, xReturn );
}

/**
 * @brief IP task did not bind the socket.
 */
void test_FreeRTOS_bind_IPTaskDidNotBindTheSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, ( EventBits_t ) eSOCKET_BOUND, pdTRUE, pdFALSE, portMAX_DELAY, pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xReturn = FreeRTOS_bind( &xSocket, NULL, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief IP task bound to socket to a NULL address.
 */
void test_FreeRTOS_bind_NonNullAddress( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, ( EventBits_t ) eSOCKET_BOUND, pdTRUE, pdFALSE, portMAX_DELAY, pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xReturn = FreeRTOS_bind( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief IPv4 socket did not bind the socket.
 */
void test_FreeRTOS_bind_IPTaskDidNotBindTheSocketIPv4Address( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;
    uint32_t ulExpectIPAddress = 0xC0A80101; /* 192.168.1.1 */
    uint16_t usExpectPort = 0x1234;

    xAddress.sin_family = FREERTOS_AF_INET4;
    xAddress.sin_address.ulIP_IPv4 = FreeRTOS_htonl( ulExpectIPAddress );
    xAddress.sin_port = FreeRTOS_htons( usExpectPort );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, ( EventBits_t ) eSOCKET_BOUND, pdTRUE, pdFALSE, portMAX_DELAY, pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xReturn = FreeRTOS_bind( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.bits.bIsIPv6 );
    TEST_ASSERT_EQUAL( ulExpectIPAddress, xSocket.xLocalAddress.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( usExpectPort, xSocket.usLocalPort );
}

/**
 * @brief IPv6 socket did not bind the socket.
 */
void test_FreeRTOS_bind_IPTaskDidNotBindTheSocketIPv6Address( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;
    IPv6_Address_t xExpectIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } }; /* 2001::1 */
    uint16_t usExpectPort = 0x1234;

    xAddress.sin_family = FREERTOS_AF_INET6;
    memcpy( xAddress.sin_address.xIP_IPv6.ucBytes, xExpectIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xAddress.sin_port = FreeRTOS_htons( usExpectPort );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, ( EventBits_t ) eSOCKET_BOUND, pdTRUE, pdFALSE, portMAX_DELAY, pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xReturn = FreeRTOS_bind( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.bits.bIsIPv6 );
    TEST_ASSERT_EQUAL_MEMORY( xExpectIPv6Address.ucBytes, xSocket.xLocalAddress.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( usExpectPort, xSocket.usLocalPort );
}

/**
 * @brief Trying to close a NULL socket.
 */
void test_FreeRTOS_closesocket_NULLSocket( void )
{
    BaseType_t xReturn;
    Socket_t xSocket = NULL;

    xReturn = FreeRTOS_closesocket( xSocket );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Trying to close an invalid socket.
 */
void test_FreeRTOS_closesocket_InvalidSocket( void )
{
    BaseType_t xReturn;
    Socket_t xSocket = ( Socket_t ) ( uintptr_t ) FREERTOS_INVALID_SOCKET;

    xReturn = FreeRTOS_closesocket( xSocket );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Sending event to IP task failed.
 */
void test_FreeRTOS_closesocket_TCPSocketSendFail( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdFAIL );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_closesocket( &xSocket );

    TEST_ASSERT_EQUAL( -1, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleConnected );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleReceive );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleSent );
}

/**
 * @brief Closing socket successful.
 */
void test_FreeRTOS_closesocket_TCPSocketSendPass( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_closesocket( &xSocket );

    TEST_ASSERT_EQUAL( 1, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleConnected );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleReceive );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xTCP.pxHandleSent );
}

/**
 * @brief UDP socket closing failed as sending event to IP task failed.
 */
void test_FreeRTOS_closesocket_UDPSocketSendFail( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdFAIL );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_closesocket( &xSocket );

    TEST_ASSERT_EQUAL( -1, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xUDP.pxHandleReceive );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xUDP.pxHandleSent );
}

/**
 * @brief Closing UDP socket successful.
 */
void test_FreeRTOS_closesocket_UDPSocketSendPass( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_closesocket( &xSocket );

    TEST_ASSERT_EQUAL( 1, xReturn );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xUDP.pxHandleReceive );
    TEST_ASSERT_EQUAL( NULL, xSocket.u.xUDP.pxHandleSent );
}

/**
 * @brief Closing socket with unknown protocol.
 */
void test_FreeRTOS_closesocket_UnknownProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSendEventStructToIPTask_ExpectAndReturn( NULL, portMAX_DELAY, pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();

    xReturn = FreeRTOS_closesocket( &xSocket );

    TEST_ASSERT_EQUAL( 1, xReturn );
}

/**
 * @brief Setting option of a NULL socket.
 */
void test_FreeRTOS_setsockopt_NULLSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName;
    const void * pvOptionValue;
    size_t uxOptionLength;

    xReturn = FreeRTOS_setsockopt( NULL, lLevel, lOptionName, pvOptionValue, uxOptionLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Setting option of an invalid socket.
 */
void test_FreeRTOS_setsockopt_InvalidSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName;
    const void * pvOptionValue;
    size_t uxOptionLength;

    xReturn = FreeRTOS_setsockopt( FREERTOS_INVALID_SOCKET, lLevel, lOptionName, pvOptionValue, uxOptionLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief
 */
void test_FreeRTOS_setsockopt_RecvTimeOut( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_RCVTIMEO;
    TickType_t vOptionValue = 0x123;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );
    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.xReceiveBlockTime );
}

/**
 * @brief Setting timeout option.
 */
void test_FreeRTOS_setsockopt_SendTimeOut( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SNDTIMEO;
    TickType_t vOptionValue = 0x123;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.xSendBlockTime );
}

/**
 * @brief Setting send timeout option for UDP socket.
 */
void test_FreeRTOS_setsockopt_SendTimeOutUDP( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SNDTIMEO;
    TickType_t vOptionValue = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.xSendBlockTime );
}

/**
 * @brief Setting send timeout option for UDP socket, timeout is more than maximum allowed value.
 */
void test_FreeRTOS_setsockopt_SendTimeOutUDPMoreBockingTime( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SNDTIMEO;
    TickType_t vOptionValue = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS + 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS, xSocket.xSendBlockTime );
}

/**
 * @brief Setting maximum waiting packet limit in UDP socket.
 */
void test_FreeRTOS_setsockopt_UDPMaxRxPackets( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_MAX_RX_PACKETS;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 100, xSocket.u.xUDP.uxMaxPackets );
}

/**
 * @brief Setting maximum waiting packet limit in non-UDP socket.
 */
void test_FreeRTOS_setsockopt_UDPMaxRxPacketsNonUDPSock( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_MAX_RX_PACKETS;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xUDP.uxMaxPackets );
}

/**
 * @brief Set UDP checksum option with NULL value.
 */
void test_FreeRTOS_setsockopt_UDPChkSumNULL( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDPCKSUM_OUT;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.ucSocketOptions = ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, NULL, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0, xSocket.ucSocketOptions );
}

/**
 * @brief Set UDP checksum option.
 */
void test_FreeRTOS_setsockopt_UDPChkSum( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDPCKSUM_OUT;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( FREERTOS_SO_UDPCKSUM_OUT, xSocket.ucSocketOptions );
}

/**
 * @brief Set TCP connection handler for UDP socket.
 */
void test_FreeRTOS_setsockopt_TCPConnInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_CONN_HANDLER;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief TCP connection handler success.
 */
void test_FreeRTOS_setsockopt_TCPConnSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_CONN_HANDLER;
    F_TCP_UDP_Handler_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.pxOnTCPConnected = ( FOnConnected_t ) 0x123ABD;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0x123ABD, xSocket.u.xTCP.pxHandleConnected );
}

/**
 * @brief
 */
void test_FreeRTOS_setsockopt_TCPRecvInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_RECV_HANDLER;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief TCP receive handler success.
 */
void test_FreeRTOS_setsockopt_TCPRecvSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_RECV_HANDLER;
    F_TCP_UDP_Handler_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.pxOnTCPReceive = ( FOnTCPReceive_t ) 0x123ABD;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0x123ABD, xSocket.u.xTCP.pxHandleReceive );
}

/**
 * @brief Setting TCP send handler for a UDP socket.
 */
void test_FreeRTOS_setsockopt_TCPSendInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_SENT_HANDLER;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set TCP sending handler.
 */
void test_FreeRTOS_setsockopt_TCPSendSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_TCP_SENT_HANDLER;
    F_TCP_UDP_Handler_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.pxOnTCPSent = ( FOnTCPSent_t ) 0x123ABD;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0x123ABD, xSocket.u.xTCP.pxHandleSent );
}

/**
 * @brief Set UDP receive handler for a TCP socket.
 */
void test_FreeRTOS_setsockopt_UDPRecvInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_RECV_HANDLER;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set UDP receive handler.
 */
void test_FreeRTOS_setsockopt_UDPRecvSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_RECV_HANDLER;
    F_TCP_UDP_Handler_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    vOptionValue.pxOnUDPReceive = ( FOnUDPReceive_t ) 0x123ABD;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0x123ABD, xSocket.u.xUDP.pxHandleReceive );
}

/**
 * @brief UDP send handler for TCP socket.
 */
void test_FreeRTOS_setsockopt_UDPSendInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_SENT_HANDLER;
    UBaseType_t vOptionValue = 100;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set UDP send handler.
 */
void test_FreeRTOS_setsockopt_UDPSendSuccess( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_UDP_SENT_HANDLER;
    F_TCP_UDP_Handler_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    vOptionValue.pxOnUDPSent = ( FOnUDPSent_t ) 0x123ABD;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0x123ABD, xSocket.u.xUDP.pxHandleSent );
}

/**
 * @brief Set semaphore for a socket.
 */
void test_FreeRTOS_setsockopt_SetSemaphore( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_SEMAPHORE;
    SemaphoreHandle_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.pxUserSemaphore );
}

/**
 * @brief Set wakeup callback.
 */
void test_FreeRTOS_setsockopt_WakeUpCallback( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WAKEUP_CALLBACK;
    SemaphoreHandle_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( &vOptionValue, xSocket.pxUserWakeCallback );
}

/**
 * @brief Set low high water mark of socket having invalid protocol.
 */
void test_FreeRTOS_setsockopt_SetLowHighWaterInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_LOW_HIGH_WATER;
    SemaphoreHandle_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set low high water mark of socket with invalid values.
 */
void test_FreeRTOS_setsockopt_SetLowHighWaterInvalidValues1( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_LOW_HIGH_WATER;
    LowHighWater_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.uxLittleSpace = 0x123;
    vOptionValue.uxEnoughSpace = vOptionValue.uxLittleSpace;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set low high water mark of socket with invalid values.
 */
void test_FreeRTOS_setsockopt_SetLowHighWaterInvalidValues2( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_LOW_HIGH_WATER;
    LowHighWater_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.uxLittleSpace = 0x123;
    vOptionValue.uxEnoughSpace = vOptionValue.uxLittleSpace - 0x12;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set low high water mark of socket with invalid values.
 */
void test_FreeRTOS_setsockopt_SetLowHighWaterInvalidValues3( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_LOW_HIGH_WATER;
    LowHighWater_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.uxLittleSpace = 0x123;
    vOptionValue.uxEnoughSpace = vOptionValue.uxLittleSpace + 0x123;
    xSocket.u.xTCP.uxRxStreamSize = vOptionValue.uxEnoughSpace - 0x12;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set low high water mark of socket.
 */
void test_FreeRTOS_setsockopt_SetLowHighWaterHappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_LOW_HIGH_WATER;
    LowHighWater_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    vOptionValue.uxLittleSpace = 0x123;
    vOptionValue.uxEnoughSpace = vOptionValue.uxLittleSpace + 0x123;
    xSocket.u.xTCP.uxRxStreamSize = vOptionValue.uxEnoughSpace + 0x12;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue.uxLittleSpace, xSocket.u.xTCP.uxLittleSpace );
    TEST_ASSERT_EQUAL( vOptionValue.uxEnoughSpace, xSocket.u.xTCP.uxEnoughSpace );
}

/**
 * @brief Send buffer set for TCP socket.
 */
void test_FreeRTOS_setsockopt_SendBuff( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SNDBUF;
    uint32_t vOptionValue = 0xABCD1234;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = NULL;
    xSocket.u.xTCP.usMSS = 0x12;

    FreeRTOS_round_up_ExpectAndReturn( vOptionValue, xSocket.u.xTCP.usMSS, 0xAB );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0xAB, xSocket.u.xTCP.uxTxStreamSize );
}

/**
 * @brief Receive buffer set for TCP socket.
 */
void test_FreeRTOS_setsockopt_RecvBuff( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_RCVBUF;
    uint32_t vOptionValue = 0xABCD1234;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.rxStream = NULL;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.u.xTCP.uxRxStreamSize );
}

/**
 * @brief Set windows properties of a socket for a UDP socket.
 */
void test_FreeRTOS_setsockopt_WinPropsInvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WIN_PROPERTIES;
    uint32_t vOptionValue = 0xABCD1234;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set windows properties of a socket which doesn't have a valid Tx stream.
 */
void test_FreeRTOS_setsockopt_WinPropsInvalidTxStream( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WIN_PROPERTIES;
    uint32_t vOptionValue = 0xABCD1234;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) 0x1234;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set windows properties of a socket which doesn't have a valid Rx stream.
 */
void test_FreeRTOS_setsockopt_WinPropsInvalidRxStream( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WIN_PROPERTIES;
    WinProperties_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    vOptionValue.lTxBufSize = 0xBB;

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) 0x1234;
    xSocket.u.xTCP.usMSS = 0x12;

    FreeRTOS_round_up_ExpectAndReturn( vOptionValue.lTxBufSize, xSocket.u.xTCP.usMSS, 0xAB );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set windows properties of a socket whose windowing has not been initialised.
 */
void test_FreeRTOS_setsockopt_WinPropsTCPWinNotInit( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WIN_PROPERTIES;
    WinProperties_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &vOptionValue, 0xCB, sizeof( vOptionValue ) );

    vOptionValue.lTxBufSize = 0xBB;

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.usMSS = 0x12;
    xSocket.u.xTCP.xTCPWindow.u.bits.bHasInit = pdFALSE;

    FreeRTOS_round_up_ExpectAndReturn( vOptionValue.lTxBufSize, xSocket.u.xTCP.usMSS, 0xAB );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( ( uint32_t ) vOptionValue.lTxWinSize, xSocket.u.xTCP.uxRxWinSize );
    TEST_ASSERT_EQUAL( ( uint32_t ) vOptionValue.lTxWinSize, xSocket.u.xTCP.uxTxWinSize );
}

/**
 * @brief Set windows properties of a socket whose windowing has been initialised.
 */
void test_FreeRTOS_setsockopt_WinPropsTCPWinInit( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_WIN_PROPERTIES;
    WinProperties_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &vOptionValue, 0xCB, sizeof( vOptionValue ) );

    vOptionValue.lTxBufSize = 0xBB;

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.usMSS = 0x12;
    xSocket.u.xTCP.xTCPWindow.u.bits.bHasInit = pdTRUE;

    FreeRTOS_round_up_ExpectAndReturn( vOptionValue.lTxBufSize, xSocket.u.xTCP.usMSS, 0xAB );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( ( uint32_t ) vOptionValue.lRxWinSize, xSocket.u.xTCP.uxRxWinSize );
    TEST_ASSERT_EQUAL( ( uint32_t ) vOptionValue.lTxWinSize, xSocket.u.xTCP.uxTxWinSize );
    TEST_ASSERT_EQUAL_UINT32( ( ( uint32_t ) vOptionValue.lRxWinSize * xSocket.u.xTCP.usMSS ), xSocket.u.xTCP.xTCPWindow.xSize.ulRxWindowLength );
    TEST_ASSERT_EQUAL_UINT32( ( ( uint32_t ) vOptionValue.lTxWinSize * xSocket.u.xTCP.usMSS ), xSocket.u.xTCP.xTCPWindow.xSize.ulTxWindowLength );
}

/**
 * @brief Set option to reuse socket of a UDP socket.
 */
void test_FreeRTOS_setsockopt_ReUseListenSock_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_REUSE_LISTEN_SOCKET;
    BaseType_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &vOptionValue, 0xCB, sizeof( vOptionValue ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set reuse of a socket to true.
 */
void test_FreeRTOS_setsockopt_ReUseListenSock_Set( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_REUSE_LISTEN_SOCKET;
    BaseType_t vOptionValue = pdTRUE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bReuseSocket );
}

/**
 * @brief Set reuse of a socket to false.
 */
void test_FreeRTOS_setsockopt_ReUseListenSock_Reset( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_REUSE_LISTEN_SOCKET;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bReuseSocket );
}

/**
 * @brief Close after send of a UDP socket.
 */
void test_FreeRTOS_setsockopt_SockClose_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_CLOSE_AFTER_SEND;
    BaseType_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Close after send option set.
 */
void test_FreeRTOS_setsockopt_SockClose_Set( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_CLOSE_AFTER_SEND;
    BaseType_t vOptionValue = pdTRUE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bCloseAfterSend );
}

/**
 * @brief Close after send option reset.
 */
void test_FreeRTOS_setsockopt_SockClose_Reset( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_CLOSE_AFTER_SEND;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bCloseAfterSend );
}

/**
 * @brief Set full size of UDP socket.
 */
void test_FreeRTOS_setsockopt_SetFullSize_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_FULL_SIZE;
    BaseType_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Set full size option set.
 */
void test_FreeRTOS_setsockopt_SetFullSize_Set( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_FULL_SIZE;
    BaseType_t vOptionValue = pdTRUE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.xTCPWindow.u.bits.bSendFullSize );
}

/**
 * @brief Set full size option reset but the state is not correct.
 */
void test_FreeRTOS_setsockopt_SetFullSize_Reset_StateIncorrect( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_FULL_SIZE;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;
    xSocket.u.xTCP.eTCPState = eESTABLISHED - 1;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.xTCPWindow.u.bits.bSendFullSize );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Set full size option reset.
 */
void test_FreeRTOS_setsockopt_SetFullSize_Reset_StateCorrect( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_FULL_SIZE;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.xTCPWindow.u.bits.bSendFullSize );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Set full size option reset.
 */
void test_FreeRTOS_setsockopt_SetFullSize_Reset_HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_SET_FULL_SIZE;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) 0xABCD;

    uxStreamBufferGetSize_ExpectAndReturn( xSocket.u.xTCP.txStream, 0x123 );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdTRUE );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.xTCPWindow.u.bits.bSendFullSize );
    TEST_ASSERT_EQUAL( 1, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Stop receive with a UDP socket.
 */
void test_FreeRTOS_setsockopt_StopRx_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_STOP_RX;
    BaseType_t vOptionValue;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Stop receive set.
 */
void test_FreeRTOS_setsockopt_StopRx_Set( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_STOP_RX;
    BaseType_t vOptionValue = pdTRUE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bRxStopped );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Stop receive reset.
 */
void test_FreeRTOS_setsockopt_StopRx_Reset( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = FREERTOS_SO_STOP_RX;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.bits.bReuseSocket = pdTRUE;

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bRxStopped );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Setting an invalid option.
 */
void test_FreeRTOS_setsockopt_InvalidOption( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    int32_t lLevel;
    int32_t lOptionName = 100;
    BaseType_t vOptionValue = pdFALSE;
    size_t uxOptionLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_setsockopt( &xSocket, lLevel, lOptionName, &vOptionValue, uxOptionLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOPROTOOPT, xReturn );
}

/**
 * @brief Translate 32-bit IP to string.
 */
void test_FreeRTOS_inet_ntoa_1( void )
{
    const char * pucReturn;
    uint32_t ulIPAddress = 0;
    char pcBuffer[ 255 ];
    char * pucIdealReturn = "0.0.0.0";

    pucReturn = FreeRTOS_inet_ntoa( ulIPAddress, pcBuffer );

    TEST_ASSERT_EQUAL( pucReturn, pcBuffer );
    TEST_ASSERT_EQUAL_STRING( pucIdealReturn, pucReturn );
}

/**
 * @brief Translate 32-bit IP to string.
 */
void test_FreeRTOS_inet_ntoa_2( void )
{
    const char * pucReturn;
    uint32_t ulIPAddress = 0xAAAAAAAA;
    char pcBuffer[ 255 ];
    char * pucIdealReturn = "170.170.170.170";

    pucReturn = FreeRTOS_inet_ntoa( ulIPAddress, pcBuffer );

    TEST_ASSERT_EQUAL( pucReturn, pcBuffer );
    TEST_ASSERT_EQUAL_STRING( pucIdealReturn, pucReturn );
}

/**
 * @brief Translate 32-bit IP to string.
 */
void test_FreeRTOS_inet_ntoa_3( void )
{
    const char * pucReturn;
    uint32_t ulIPAddress = 0xFFFFFFFF;
    char pcBuffer[ 255 ];
    char * pucIdealReturn = "255.255.255.255";

    pucReturn = FreeRTOS_inet_ntoa( ulIPAddress, pcBuffer );

    TEST_ASSERT_EQUAL( pucReturn, pcBuffer );
    TEST_ASSERT_EQUAL_STRING( pucIdealReturn, pucReturn );
}

/**
 * @brief Incorrect address family.
 */
void test_FreeRTOS_inet_pton_IncorrectAddressFamily( void )
{
    BaseType_t xReturn;
    BaseType_t xAddressFamily = FREERTOS_AF_INET + 1;
    const char * pcSource;
    void * pvDestination;

    xReturn = FreeRTOS_inet_pton( xAddressFamily, pcSource, pvDestination );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAFNOSUPPORT, xReturn );
}

/**
 * @brief Octal notation being converted.
 */
void test_FreeRTOS_inet_pton_Octal( void )
{
    BaseType_t xReturn;
    BaseType_t xAddressFamily = FREERTOS_AF_INET;
    const char * pcSource = "00.01.2.3";
    uint32_t ulDestination = 0;

    FreeRTOS_inet_pton4_ExpectAndReturn( pcSource, &ulDestination, pdFAIL );
    xReturn = FreeRTOS_inet_pton( xAddressFamily, pcSource, &ulDestination );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL( 0, ulDestination );
}

/**
 * @brief Happy path of this function.
 */
void test_FreeRTOS_inet_pton_HappyPath( void )
{
    BaseType_t xReturn;
    BaseType_t xAddressFamily = FREERTOS_AF_INET;
    const char * pcSource = "255.255.255.255";
    uint32_t ulDestination;
    uint32_t ulExpectDestination = 0xFFFFFFFF;

    FreeRTOS_inet_pton4_ExpectAndReturn( pcSource, &ulDestination, pdPASS );
    FreeRTOS_inet_pton4_ReturnMemThruPtr_pvDestination( &ulExpectDestination, sizeof( ulExpectDestination ) );
    xReturn = FreeRTOS_inet_pton( xAddressFamily, pcSource, &ulDestination );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL_UINT32( ulExpectDestination, ulDestination );
}

/**
 * @brief Happy path of this function for IPv6.
 */
void test_FreeRTOS_inet_pton_IPv6HappyPath( void )
{
    BaseType_t xReturn;
    BaseType_t xAddressFamily = FREERTOS_AF_INET6;
    const char * pcSource = "2001::1";
    IPv6_Address_t xDestination;
    IPv6_Address_t * pxExpectDestination = &xIPv6Address;

    FreeRTOS_inet_pton6_ExpectAndReturn( pcSource, &xDestination, pdPASS );
    FreeRTOS_inet_pton6_ReturnMemThruPtr_pvDestination( pxExpectDestination->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xReturn = FreeRTOS_inet_pton( xAddressFamily, pcSource, &xDestination );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL_MEMORY( pxExpectDestination->ucBytes, xDestination.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief Translate array to string for MAC address.
 */
void test_FreeRTOS_EUI48_ntop1( void )
{
    uint8_t pucSource[ 6 ] = { 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA };
    char pcTarget[ 18 ];
    char cTen = 'A';
    char cSeparator = ':';

    memset( pcTarget, 0, sizeof( pcTarget ) );

    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "AA:AA:AA:AA:AA:AA", pcTarget );

    cTen = 'a';
    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "aa:aa:aa:aa:aa:aa", pcTarget );

    cTen = 'a';
    cSeparator = '-';
    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "aa-aa-aa-aa-aa-aa", pcTarget );
}

/**
 * @brief Translate array to string for MAC address.
 */
void test_FreeRTOS_EUI48_ntop2( void )
{
    uint8_t pucSource[ 6 ] = { 0x12, 0x34, 0x56, 0x78, 0xef, 0xdc };
    char pcTarget[ 18 ];
    char cTen = 'A';
    char cSeparator = ':';

    memset( pcTarget, 0, sizeof( pcTarget ) );

    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "12:34:56:78:EF:DC", pcTarget );

    cSeparator = '-';
    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "12-34-56-78-EF-DC", pcTarget );

    cTen = 'a';
    cSeparator = ':';
    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "12:34:56:78:ef:dc", pcTarget );

    cTen = 'a';
    cSeparator = '-';
    FreeRTOS_EUI48_ntop( pucSource, pcTarget, cTen, cSeparator );
    TEST_ASSERT_EQUAL_STRING( "12-34-56-78-ef-dc", pcTarget );
}

/**
 * @brief Translate array to string for MAC address. Invalid values.
 */
void test_FreeRTOS_EUI48_pton_InvalidInput( void )
{
    BaseType_t xReturn;
    const char * pcSource = "12345678::::";
    uint8_t pucTarget[ 6 ];

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief Translate array to string for MAC address. Invalid values.
 */
void test_FreeRTOS_EUI48_pton_InvalidInput2( void )
{
    BaseType_t xReturn;
    const char * pcSource = "12:34:56:78:ab:ty";
    uint8_t pucTarget[ 6 ];

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief Translate array to string for MAC address. Invalid values.
 */
void test_FreeRTOS_EUI48_pton_InvalidInput3( void )
{
    BaseType_t xReturn;
    const char * pcSource = "12:34#56:78:ab:cd";
    uint8_t pucTarget[ 6 ];

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief Translate array to string for MAC address. Invalid values.
 */
void test_FreeRTOS_EUI48_pton_InvalidInput4( void )
{
    BaseType_t xReturn;
    const char * pcSource = "";
    uint8_t pucTarget[ 6 ];

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief Translate string to array for MAC address.
 */
void test_FreeRTOS_EUI48_pton_HappyPath( void )
{
    BaseType_t xReturn;
    const char * pcSource = "12:34:56:78:ab:cd";
    uint8_t pucTarget[ 6 ];
    uint8_t pucIdeal[] = { 0x12, 0x34, 0x56, 0x78, 0xab, 0xcd };

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( pucIdeal, pucTarget, 6 );
}

/**
 * @brief Translate string to array for MAC address.
 */
void test_FreeRTOS_EUI48_pton_HappyPath1( void )
{
    BaseType_t xReturn;
    const char * pcSource = "12-34-56-78-ab-cd";
    uint8_t pucTarget[ 6 ];
    uint8_t pucIdeal[] = { 0x12, 0x34, 0x56, 0x78, 0xab, 0xcd };

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( pucIdeal, pucTarget, 6 );
}

/**
 * @brief Translate string to array for MAC address.
 */
void test_FreeRTOS_EUI48_pton_HappyPath2( void )
{
    BaseType_t xReturn;
    const char * pcSource = "FF-34-56-78-ab-cd";
    uint8_t pucTarget[ 6 ];
    uint8_t pucIdeal[] = { 0xff, 0x34, 0x56, 0x78, 0xab, 0xcd };

    xReturn = FreeRTOS_EUI48_pton( pcSource, pucTarget );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( pucIdeal, pucTarget, 6 );
}

/**
 * @brief Invalid input to convert to IP address.
 */
void test_FreeRTOS_inet_addr_InvalidString( void )
{
    uint32_t ulReturn;
    char * pcIPAddress = "0..12.34.4";

    FreeRTOS_inet_pton4_ExpectAndReturn( pcIPAddress, NULL, pdFAIL );
    FreeRTOS_inet_pton4_IgnoreArg_pvDestination();
    ulReturn = FreeRTOS_inet_addr( pcIPAddress );
    TEST_ASSERT_EQUAL( 0, ulReturn );
}

/**
 * @brief Valid input to convert to IP address.
 */
void test_FreeRTOS_inet_addr_ValidString( void )
{
    uint32_t ulExpectAnswer = 0x04030201;
    uint32_t ulReturn;
    char * pcIPAddress = "1.2.3.4";

    FreeRTOS_inet_pton4_ExpectAndReturn( pcIPAddress, NULL, pdPASS );
    FreeRTOS_inet_pton4_IgnoreArg_pvDestination();
    FreeRTOS_inet_pton4_ReturnMemThruPtr_pvDestination( &ulExpectAnswer, sizeof( ulExpectAnswer ) );
    ulReturn = FreeRTOS_inet_addr( pcIPAddress );
    TEST_ASSERT_EQUAL( ulExpectAnswer, ulReturn );
}

/**
 * @brief Get local address from a socket.
 */
void test_FreeRTOS_GetLocalAddress( void )
{
    size_t uxReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.usLocalPort = 0xAB12;
    xSocket.xLocalAddress.ulIP_IPv4 = 0xABFC8769;

    uxReturn = FreeRTOS_GetLocalAddress( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( sizeof( xAddress ), uxReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 0xABFC8769 ), xAddress.sin_address.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( FreeRTOS_htons( 0xAB12 ), xAddress.sin_port );
}

/**
 * @brief Get local address from an IPv6 socket.
 */
void test_FreeRTOS_GetLocalAddress_IPv6( void )
{
    size_t uxReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    IPv6_Address_t xIPAddress = { { 0x20 } };

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.bits.bIsIPv6 = pdTRUE;
    xSocket.usLocalPort = 0xAB12;
    memcpy( xSocket.xLocalAddress.xIP_IPv6.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    uxReturn = FreeRTOS_GetLocalAddress( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, xAddress.sin_family );
    TEST_ASSERT_EQUAL_MEMORY( xIPv6Address.ucBytes, xAddress.sin_address.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( FreeRTOS_htons( 0xAB12 ), xAddress.sin_port );
}

/**
 * @brief All fields are NULL in the socket.
 */
void test_FreeRTOS_connect_SocketValuesNULL( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EBADF, xResult );
}

/**
 * @brief Test for invalid values.
 */
void test_FreeRTOS_connect_InvalidValues( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid protocol. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EBADF, xResult );

    /* Socket not bound. Binding failed. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );
    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ECANCELED, xResult );

    /* Socket NULL. */
    xResult = FreeRTOS_connect( NULL, &xAddress, xAddressLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EBADF, xResult );

    /* Address NULL. */
    xResult = FreeRTOS_connect( &xSocket, NULL, xAddressLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xResult );
}

/**
 * @brief Non blocking connect.
 */
void test_FreeRTOS_connect_NonBlocking( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xSocket, eCONNECT_SYN );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EWOULDBLOCK, xResult );
}

/**
 * @brief Timeout in connection.
 */
void test_FreeRTOS_connect_Timeout( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    /* Non 0 value to show blocking. */
    xSocket.xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xSocket, eCONNECT_SYN );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    /* Using a local variable. */
    vTaskSetTimeOutState_ExpectAnyArgs();

    /* No timeout the first time. */
    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_CONNECT | eSOCKET_CLOSED, pdTRUE, pdFALSE, xSocket.xReceiveBlockTime, pdTRUE );

    /* Timed out! */
    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ETIMEDOUT, xResult );
}

/**
 * @brief Timeout in connection.
 */
void test_FreeRTOS_connect_SocketClosed( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    /* Non 0 value to show blocking. */
    xSocket.xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xSocket, eCONNECT_SYN );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    /* Using a local variable. */
    vTaskSetTimeOutState_ExpectAnyArgs();

    /* No timeout the first time. */
    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_CONNECT | eSOCKET_CLOSED, pdTRUE, pdFALSE, xSocket.xReceiveBlockTime, eSOCKET_CLOSED );

    xResult = FreeRTOS_connect( &xSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOTCONN, xResult );
}

/**
 * @brief Connection successful.
 */
void test_FreeRTOS_connect_Connected( void )
{
    BaseType_t xResult;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xGlobalSocket, 0, sizeof( xGlobalSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xAddress.sin_family = FREERTOS_AF_INET4;

    xGlobalSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    /* Non 0 value to show blocking. */
    xGlobalSocket.xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xGlobalSocket, eCONNECT_SYN );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    /* Using a local variable. */
    vTaskSetTimeOutState_ExpectAnyArgs();

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_Stub( xStubForEventGroupWaitBits );

    xResult = FreeRTOS_connect( &xGlobalSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( 0, xResult );
}

/**
 * @brief Connection failed due to error happening during sleep.
 */
void test_FreeRTOS_connect_SocketErrorDuringSleep( void )
{
    BaseType_t xResult;
    struct freertos_sockaddr xAddress;
    socklen_t xAddressLength;

    memset( &xGlobalSocket, 0, sizeof( xGlobalSocket ) );

    xGlobalSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    /* Non 0 value to show blocking. */
    xGlobalSocket.xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xGlobalSocket, eCONNECT_SYN );
    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    /* Set the global socket handler to error during sleep. */
    vTaskSetTimeOutState_Stub( vStub_vTaskSetTimeOutState_socketError );

    xResult = FreeRTOS_connect( &xGlobalSocket, &xAddress, xAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xResult );
}

/**
 * @brief Invalid protocol.
 */
void test_FreeRTOS_GetRemoteAddress_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xReturn = FreeRTOS_GetRemoteAddress( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief happy path.
 */
void test_FreeRTOS_GetRemoteAddress_HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = 0xABCDEF12;
    xSocket.u.xTCP.usRemotePort = 0x1234;

    xReturn = FreeRTOS_GetRemoteAddress( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( sizeof( xAddress ), xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_htonl( 0xABCDEF12 ), xAddress.sin_address.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( FreeRTOS_htons( 0x1234 ), xAddress.sin_port );
}

/**
 * @brief IPv6 happy path.
 */
void test_FreeRTOS_GetRemoteAddress_IPv6HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    memcpy( xSocket.u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xSocket.u.xTCP.usRemotePort = 0x1234;

    xReturn = FreeRTOS_GetRemoteAddress( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( sizeof( xAddress ), xReturn );
    TEST_ASSERT_EQUAL_MEMORY( xIPv6Address.ucBytes, xAddress.sin_address.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( FreeRTOS_htons( 0x1234 ), xAddress.sin_port );
}

/**
 * @brief Invalid values.
 */
void test_FreeRTOS_maywrite_InvalidValues( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid Protocol. */
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    /* Invalid States. */
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eTCP_LISTEN; /* eCONNECT_SYN - 1 */
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( -1, xReturn );

    xSocket.u.xTCP.eTCPState = eFIN_WAIT_1; /* eESTABLISHED + 1 */
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( -1, xReturn );

    xSocket.u.xTCP.eTCPState = eCONNECT_SYN;
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    xSocket.u.xTCP.eTCPState = eSYN_FIRST; /* eCONNECT_SYN + 1 */
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    /* Transmission NULL. */
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.uxTxStreamSize = 0x123;
    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( 0x123, xReturn );
}

/**
 * @brief Happy path.
 */
void test_FreeRTOS_maywrite_HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    uint8_t ucStream[ 20 ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;

    uxStreamBufferGetSpace_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0x3344 );

    xReturn = FreeRTOS_maywrite( &xSocket );
    TEST_ASSERT_EQUAL( 0x3344, xReturn );
}

/**
 * @brief Test setting socket ID when the socket is NULL.
 */
void test_xSocketSetSocketID_NULLSocket( void )
{
    BaseType_t xReturn;

    xReturn = xSocketSetSocketID( NULL, NULL );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Test setting socket ID when the socket is invalid.
 */
void test_xSocketSetSocketID_InvalidSocket( void )
{
    BaseType_t xReturn;

    xReturn = xSocketSetSocketID( FREERTOS_INVALID_SOCKET, NULL );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Test setting socket ID when the socket is Valid.
 */
void test_xSocketSetSocketID_ValidSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t AnchorVariable;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = xSocketSetSocketID( &xSocket, &AnchorVariable );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( &AnchorVariable, xSocket.pvSocketID );
}

/**
 * @brief Test setting socket ID when the socket is NULL.
 */
void test_pvSocketGetSocketID_NULLSocket( void )
{
    void * pvReturn;

    pvReturn = pvSocketGetSocketID( NULL );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

/**
 * @brief Test setting socket ID when the socket is invalid.
 */
void test_pvSocketGetSocketID_InvalidSocket( void )
{
    void * pvReturn;

    pvReturn = pvSocketGetSocketID( FREERTOS_INVALID_SOCKET );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

/**
 * @brief Test setting socket ID when the socket is Valid.
 */
void test_pvSocketGetSocketID_ValidSocket( void )
{
    BaseType_t pvReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t AnchorVariable;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.pvSocketID = &AnchorVariable;

    pvReturn = ( BaseType_t ) pvSocketGetSocketID( &xSocket );

    TEST_ASSERT_EQUAL( &AnchorVariable, pvReturn );
}

/**
 * @brief This function just prints out some data. It is expected to make calls to the
 *        below functions when IP stack is not initialised.
 */
void test_vTCPNetStat_IPStackNotInit( void )
{
    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( 0 );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 0 );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdFALSE );

    vTCPNetStat();
}

/**
 * @brief This function just prints out some data. It is expected to make calls to the
 *        below functions when IP stack is initialised. It is expected to go through the
 *        list of TCP and UDP sockets which are bound and print them out.
 */
void test_vTCPNetStat_IPStackInit( void )
{
    ListItem_t xLocalTCPItem, xLocalUDPItem, xIterator;
    FreeRTOS_Socket_t xSocket, xSocket2;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xSocket2, 0, sizeof( xSocket2 ) );

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( 0 );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 0 );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    listGET_END_MARKER_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalTCPItem );
    listGET_END_MARKER_ExpectAndReturn( &xBoundUDPSocketsList, &xLocalUDPItem );

    /* First Iteration. */
    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xIterator );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xSocket );

    xTaskGetTickCount_ExpectAndReturn( 0x10 );

    uxIPHeaderSizeSocket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    /* Second Iteration. */
    xSocket2.u.xTCP.eTCPState = eTCP_LISTEN;
    listGET_NEXT_ExpectAndReturn( &xIterator, &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xSocket2 );

    xTaskGetTickCount_ExpectAndReturn( 0x20 );

    /* TCP last iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xLocalTCPItem );


    /* UDP */
    /* First Iteration. */
    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundUDPSocketsList, &xIterator );

    /* Second Iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xIterator );

    /* TCP last iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xLocalUDPItem );

    vTCPNetStat();
}

/**
 * @brief This function just prints out some data. It is expected to change the age ( current tick - last alive )
 * if it's greater than 999999.
 */
void test_vTCPNetStat_LongTimeSinceLastAlive( void )
{
    ListItem_t xLocalTCPItem, xLocalUDPItem, xIterator;
    FreeRTOS_Socket_t xSocket, xSocket2;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xSocket2, 0, sizeof( xSocket2 ) );

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( 0 );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 0 );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    listGET_END_MARKER_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalTCPItem );
    listGET_END_MARKER_ExpectAndReturn( &xBoundUDPSocketsList, &xLocalUDPItem );

    /* First Iteration. */
    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xIterator );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xSocket );

    xTaskGetTickCount_ExpectAndReturn( 1000000U );

    /* Second Iteration. */
    xSocket2.u.xTCP.eTCPState = eTCP_LISTEN;
    listGET_NEXT_ExpectAndReturn( &xIterator, &xIterator );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xSocket2 );

    xTaskGetTickCount_ExpectAndReturn( 0x20 );

    /* TCP last iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xLocalTCPItem );


    /* UDP */
    /* First Iteration. */
    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundUDPSocketsList, &xIterator );

    /* Second Iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xIterator );

    /* TCP last iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xLocalUDPItem );

    vTCPNetStat();
}

/**
 * @brief This function just prints out some data. It is able to print IPv6
 * socket as well.
 */
void test_vTCPNetStat_IPv6Socket( void )
{
    ListItem_t xLocalTCPItem, xLocalUDPItem, xIterator;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( 0 );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 0 );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    listGET_END_MARKER_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalTCPItem );
    listGET_END_MARKER_ExpectAndReturn( &xBoundUDPSocketsList, &xLocalUDPItem );

    /* First Iteration. */
    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xIterator );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xSocket );

    xTaskGetTickCount_ExpectAndReturn( 0x10 );

    /* TCP last iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xLocalTCPItem );

    /* UDP */
    /* First Iteration. */
    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundUDPSocketsList, &xIterator );

    /* Second Iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xIterator );

    /* TCP last iteration. */
    listGET_NEXT_ExpectAndReturn( &xIterator, &xLocalUDPItem );

    vTCPNetStat();
}

/**
 * @brief Socket select function when only UDP sockets are bound.
 */
void test_vSocketSelect_UDPSocketsOnly( void )
{
    SocketSelect_t xSocketSet;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket, xSocket2, xSocket3, xSocket4;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xSocket2, 0, sizeof( xSocket2 ) );
    memset( &xSocket3, 0, sizeof( xSocket3 ) );
    memset( &xSocket4, 0, sizeof( xSocket4 ) );

    xSocket2.pxSocketSet = &xSocketSet;
    xSocket3.pxSocketSet = &xSocketSet;
    xSocket4.pxSocketSet = &xSocketSet;

    /* Round 0. Not same socket set. */
    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundUDPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    /* Round 1. Same socket set. No select bits. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket2 );

    /* Round 2. Same socket set. elect bits. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket3 );

    xSocket3.xSelectBits = eSELECT_READ;
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket3.u.xUDP.xWaitingPacketsList ), 0 );

    /* Round 3. Same socket set. elect bits. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket4 );

    xSocket4.xSelectBits = eSELECT_READ;
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket4.u.xUDP.xWaitingPacketsList ), 3 );

    /* Last item. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, ( ListItem_t * ) &( xBoundUDPSocketsList.xListEnd ) );

    /* Last item. Nothing in TCP. */
    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet.xSelectGroup, 0, 0 );

    xEventGroupSetBits_ExpectAndReturn( xSocketSet.xSelectGroup, eSELECT_READ | eSELECT_CALL_IP, pdPASS );

    vSocketSelect( &xSocketSet );

    TEST_ASSERT_EQUAL( 0, xSocket.xSocketBits );
    TEST_ASSERT_EQUAL( 0, xSocket2.xSocketBits );
    TEST_ASSERT_EQUAL( 0, xSocket3.xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_READ, xSocket4.xSocketBits );
}

/**
 * @brief Socket select function when only TCP sockets are bound.
 */
void test_vSocketSelect_TCPSocketsOnly( void )
{
    SocketSelect_t xSocketSet;
    ListItem_t xLocalListItem;
    uint8_t ucStream[ 20 ];
    FreeRTOS_Socket_t xSocket[ 9 ], xPeerSocket, xPeerSocket1;
    int i;

    for( i = 1; i < 9; i++ )
    {
        memset( &xSocket[ i ], 0, sizeof( xSocket[ i ] ) );
        xSocket[ i ].pxSocketSet = &xSocketSet;
        xSocket[ i ].ucProtocol = FREERTOS_IPPROTO_TCP;
    }

    memset( &xPeerSocket, 0, sizeof( xPeerSocket ) );
    memset( &xPeerSocket1, 0, sizeof( xPeerSocket1 ) );
    memset( &xSocket[ 0 ], 0, sizeof( xSocket[ 0 ] ) );

    xSocket[ 0 ].ucProtocol = FREERTOS_IPPROTO_TCP;

    /* Last item. Nothing in UDP. */
    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundUDPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundUDPSocketsList.xListEnd ) );

    /* Round 0. Not same socket set. */
    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 0 ] );

    /* Round 1. Same socket set. No bits Set. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 1 ] );

    /* Round 2. Same socket set. All bits Set. */
    xSocket[ 2 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 2 ] );

    /* Round 3. */
    xSocket[ 3 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 3 ].u.xTCP.bits.bPassAccept = pdTRUE;
    xSocket[ 3 ].u.xTCP.eTCPState = eTCP_LISTEN;
    xSocket[ 3 ].u.xTCP.pxPeerSocket = &xPeerSocket;
    xSocket[ 3 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 3 ] );

    /* Round 4. */
    xSocket[ 4 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 4 ].u.xTCP.bits.bPassAccept = pdTRUE;
    xSocket[ 4 ].u.xTCP.eTCPState = eTCP_LISTEN;
    xSocket[ 4 ].u.xTCP.pxPeerSocket = &xPeerSocket1;
    xSocket[ 4 ].u.xTCP.pxPeerSocket->u.xTCP.bits.bPassAccept = pdTRUE;
    xSocket[ 4 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 4 ] );

    /* Round 5. */
    xSocket[ 5 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 5 ].u.xTCP.eTCPState = eTCP_LISTEN;
    xSocket[ 5 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    xSocket[ 5 ].u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 5 ] );
    uxStreamBufferGetSpace_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0xABCD );

    /* Round 5. */
    xSocket[ 6 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 6 ].u.xTCP.eTCPState = eCLOSE_WAIT;
    xSocket[ 6 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    xSocket[ 6 ].u.xTCP.txStream = ( StreamBuffer_t * ) ucStream;
    xSocket[ 6 ].u.xTCP.rxStream = ( StreamBuffer_t * ) ucStream;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 6 ] );
    uxStreamBufferGetSize_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0xAB );
    uxStreamBufferGetSpace_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0xABCD );

    /* Round 6. */
    xSocket[ 7 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 7 ].u.xTCP.eTCPState = eESTABLISHED;
    xSocket[ 7 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    xSocket[ 7 ].u.xTCP.bits.bPassQueued = pdTRUE;
    xSocket[ 7 ].u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 7 ] );

    /* Round 7. */
    xSocket[ 8 ].xSelectBits = eSELECT_READ | eSELECT_EXCEPT | eSELECT_WRITE;
    xSocket[ 8 ].u.xTCP.eTCPState = eESTABLISHED;
    xSocket[ 8 ].u.xTCP.bits.bConnPrepared = pdTRUE_UNSIGNED;
    xSocket[ 8 ].u.xTCP.bits.bPassQueued = pdTRUE;
    xSocket[ 8 ].u.xTCP.bits.bReuseSocket = pdTRUE_UNSIGNED;
    xSocket[ 8 ].u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xSocket[ 8 ].u.xTCP.bits.bConnPassed = pdTRUE_UNSIGNED;
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket[ 8 ] );

    /* Last item. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet.xSelectGroup, 0, eSELECT_READ );

    xEventGroupSetBits_ExpectAnyArgsAndReturn( pdPASS );

    vSocketSelect( &xSocketSet );

    TEST_ASSERT_EQUAL( 0, xSocket[ 0 ].xSocketBits );
    TEST_ASSERT_EQUAL( 0, xSocket[ 1 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_EXCEPT, xSocket[ 2 ].xSocketBits );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket[ 2 ].u.xTCP.bits.bConnPassed );
    TEST_ASSERT_EQUAL( 0, xSocket[ 3 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_READ, xSocket[ 4 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_WRITE, xSocket[ 5 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_WRITE | eSELECT_READ | eSELECT_EXCEPT, xSocket[ 6 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_WRITE, xSocket[ 7 ].xSocketBits );
    TEST_ASSERT_EQUAL( eSELECT_READ, xSocket[ 8 ].xSocketBits );
}

/**
 * @brief Socket select function when no sockets are bound.
 */
void test_vSocketSelect_NoSocketsAtAll( void )
{
    SocketSelect_t xSocketSet;
    ListItem_t xLocalListItem;
    uint8_t ucStream[ 20 ];

    /* Last item. Nothing in UDP. */
    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundUDPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundUDPSocketsList.xListEnd ) );

    /* Last item. Nothing in TCP. */
    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    xEventGroupClearBits_ExpectAndReturn( xSocketSet.xSelectGroup, 0, eSELECT_READ );
    xEventGroupClearBits_ExpectAnyArgsAndReturn( pdPASS );
    xEventGroupSetBits_ExpectAndReturn( xSocketSet.xSelectGroup, eSELECT_CALL_IP, pdPASS );

    vSocketSelect( &xSocketSet );
}

/**
 * @brief Signalling socket with invalid values given for socket.
 */
void test_FreeRTOS_SignalSocket_InvalidSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = FreeRTOS_SignalSocket( NULL );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );

    xReturn = FreeRTOS_SignalSocket( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Event group is present for the socket being signalled.
 */
void test_FreeRTOS_SignalSocket_NonNULLEventGroup( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    SocketSelect_t xSocketSet;
    uint8_t xEventGroup[ sizeof( size_t ) ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xSocketSet, 0, sizeof( xSocketSet ) );

    xSocket.pxSocketSet = &xSocketSet;
    xSocket.xEventGroup = ( EventGroupHandle_t ) xEventGroup;

    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_INTR, pdFALSE );

    xReturn = FreeRTOS_SignalSocket( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Select group is present for the socket being called.
 */
void test_FreeRTOS_SignalSocket_NonNULLSelectGroup( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    SocketSelect_t xSocketSet;
    uint8_t xSelectGroup[ sizeof( size_t ) ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xSocketSet, 0, sizeof( xSocketSet ) );

    xSocket.pxSocketSet = &xSocketSet;
    xSocket.pxSocketSet->xSelectGroup = ( EventGroupHandle_t ) xSelectGroup;

    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSELECT_INTR, pdFALSE );

    xReturn = FreeRTOS_SignalSocket( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Catch various asserts.
 */
void test_FreeRTOS_SignalSocketFromISR_catchAsserts( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xHigherPriorityTaskWoken;

    /* Socket cannot be NULL. */
    catch_assert( FreeRTOS_SignalSocketFromISR( NULL, &xHigherPriorityTaskWoken ) );

    memset( &xSocket, 0, sizeof( xSocket ) );
    /* Socket must have TCP protocol. */
    catch_assert( FreeRTOS_SignalSocketFromISR( &xSocket, &xHigherPriorityTaskWoken ) );

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    /* Event group must be non-NULL. */
    catch_assert( FreeRTOS_SignalSocketFromISR( &xSocket, &xHigherPriorityTaskWoken ) );
}

/**
 * @brief happy path of the function.
 */
void test_FreeRTOS_SignalSocketFromISR_HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xHigherPriorityTaskWoken;
    uint8_t xEventGroup[ sizeof( size_t ) ];

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.xEventGroup = ( EventGroupHandle_t ) xEventGroup;

    xQueueGenericSendFromISR_ExpectAnyArgsAndReturn( 0xABC );

    xReturn = FreeRTOS_SignalSocketFromISR( &xSocket, &xHigherPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 0xABC, xReturn );
}

/**
 * @brief Get TCPv4 packets property string.
 */
void test_prvSocketProps_TCPv4()
{
    FreeRTOS_Socket_t xSocket;
    uint32_t ulExpectSrcIP = 0xC0A80101;
    uint32_t ulExpectRemoteIP = 0xC0A80102;
    uint16_t usSrcPort = 1024U;
    uint16_t usRemotePort = 2048U;
    const char * pcReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.bits.bIsIPv6 = pdFALSE;
    xSocket.xLocalAddress.ulIP_IPv4 = ulExpectSrcIP;
    xSocket.usLocalPort = usSrcPort;
    xSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = ulExpectRemoteIP;
    xSocket.u.xTCP.usRemotePort = usRemotePort;

    pcReturn = prvSocketProps( &xSocket );
    TEST_ASSERT_EQUAL_STRING( "c0a80101ip port 1024 to c0a80102ip port 2048", pcReturn );
}

/**
 * @brief Get UDPv4 packets property string.
 */
void test_prvSocketProps_UDPv4()
{
    FreeRTOS_Socket_t xSocket;
    uint32_t ulExpectSrcIP = 0xC0A80101;
    const char * pcReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.bits.bIsIPv6 = pdFALSE;
    xSocket.xLocalAddress.ulIP_IPv4 = ulExpectSrcIP;
    xSocket.usLocalPort = 1024U;

    pcReturn = prvSocketProps( &xSocket );
    TEST_ASSERT_EQUAL_STRING( "c0a80101ip port 1024", pcReturn );
}

/**
 * @brief Get TCPv6 packets property string.
 */
void test_prvSocketProps_TCPv6()
{
    FreeRTOS_Socket_t xSocket;
    IPv6_Address_t * pxIPv6SrcAddress = &xIPv6Address;                                                                                          /* 2001::1 */
    IPv6_Address_t xIPv6RemoteAddress = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 } }; /* 2001::2 */
    uint16_t usSrcPort = 1024U;
    uint16_t usRemotePort = 2048U;
    const char * pcReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.bits.bIsIPv6 = pdTRUE;
    memcpy( xSocket.xLocalAddress.xIP_IPv6.ucBytes, pxIPv6SrcAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xSocket.usLocalPort = usSrcPort;
    memcpy( xSocket.u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, xIPv6RemoteAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xSocket.u.xTCP.usRemotePort = usRemotePort;

    pcReturn = prvSocketProps( &xSocket );
}

/**
 * @brief Get UDPv6 packets property string.
 */
void test_prvSocketProps_UDPv6()
{
    FreeRTOS_Socket_t xSocket;
    IPv6_Address_t * pxIPv6SrcAddress = &xIPv6Address; /* 2001::1 */
    uint16_t usSrcPort = 1024U;
    const char * pcReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.bits.bIsIPv6 = pdTRUE;
    memcpy( xSocket.xLocalAddress.xIP_IPv6.ucBytes, pxIPv6SrcAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xSocket.usLocalPort = usSrcPort;

    pcReturn = prvSocketProps( &xSocket );
}

/**
 * @brief Get packets property string with unknown protocol.
 */
void test_prvSocketProps_UnknownProtocol()
{
    FreeRTOS_Socket_t xSocket;
    IPv6_Address_t * pxIPv6SrcAddress = &xIPv6Address; /* 2001::1 */
    uint16_t usSrcPort = 1024U;
    const char * pcReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP + 1;
    xSocket.bits.bIsIPv6 = pdTRUE;
    memcpy( xSocket.xLocalAddress.xIP_IPv6.ucBytes, pxIPv6SrcAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xSocket.usLocalPort = usSrcPort;

    pcReturn = prvSocketProps( &xSocket );
}

/**
 * @brief Happy path of this function for IPv4.
 */
void test_FreeRTOS_inet_ntop_IPv4( void )
{
    const char * pcReturn;
    uint32_t ulIPAddress = 0x10101010; /* 16.16.16.16 */
    char * pcExpectResult = "16.16.16.16";
    const size_t xSize = 16;
    char cDestination[ xSize ];
    BaseType_t xAddressFamily = FREERTOS_AF_INET4;

    memset( cDestination, 0, sizeof( cDestination ) );

    FreeRTOS_inet_ntop4_ExpectAndReturn( &ulIPAddress, cDestination, xSize, cDestination );
    FreeRTOS_inet_ntop4_ReturnMemThruPtr_pcDestination( pcExpectResult, strlen( pcExpectResult ) );
    pcReturn = FreeRTOS_inet_ntop( xAddressFamily, &ulIPAddress, cDestination, xSize );

    TEST_ASSERT_EQUAL_STRING( pcExpectResult, pcReturn );
}

/**
 * @brief Happy path of this function for IPv4.
 */
void test_FreeRTOS_inet_ntop_IPv6( void )
{
    const char * pcReturn;
    IPv6_Address_t * pxIPAddress = &xIPv6Address;
    char * pcExpectResult = "2001::1";
    const size_t xSize = 16;
    char cDestination[ xSize ];
    BaseType_t xAddressFamily = FREERTOS_AF_INET6;

    memset( cDestination, 0, sizeof( cDestination ) );

    FreeRTOS_inet_ntop6_ExpectAndReturn( pxIPAddress, cDestination, xSize, cDestination );
    FreeRTOS_inet_ntop6_ReturnMemThruPtr_pcDestination( pcExpectResult, strlen( pcExpectResult ) );
    pcReturn = FreeRTOS_inet_ntop( xAddressFamily, pxIPAddress, cDestination, xSize );

    TEST_ASSERT_EQUAL_STRING( pcExpectResult, pcReturn );
}

/**
 * @brief Happy path of this function for unknown family.
 */
void test_FreeRTOS_inet_ntop_Unknown( void )
{
    const char * pcReturn;
    uint32_t ulIPAddress = 0x10101010; /* 16.16.16.16 */
    char * pcExpectResult = "16.16.16.16";
    const size_t xSize = 16;
    char cDestination[ xSize ];
    BaseType_t xAddressFamily = FREERTOS_AF_INET6 + 1;

    memset( cDestination, 0, sizeof( cDestination ) );

    pcReturn = FreeRTOS_inet_ntop( xAddressFamily, &ulIPAddress, cDestination, xSize );

    TEST_ASSERT_EQUAL( NULL, pcReturn );
}

/**
 * @brief Query socket type of IPv4 socket.
 */
void test_FreeRTOS_GetIPType_IPv4HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.bits.bIsIPv6 = pdFALSE_UNSIGNED;

    xReturn = FreeRTOS_GetIPType( &xSocket );

    TEST_ASSERT_EQUAL( ipTYPE_IPv4, xReturn );
}

/**
 * @brief Query socket type of IPv6 socket.
 */
void test_FreeRTOS_GetIPType_IPv6HappyPath( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;

    xReturn = FreeRTOS_GetIPType( &xSocket );

    TEST_ASSERT_EQUAL( ipTYPE_IPv6, xReturn );
}
