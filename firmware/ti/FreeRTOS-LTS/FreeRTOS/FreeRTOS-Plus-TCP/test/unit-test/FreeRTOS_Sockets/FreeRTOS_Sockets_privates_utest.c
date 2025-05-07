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
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_IPv6_Sockets.h"

#include "FreeRTOS_Sockets.h"


#include "FreeRTOS_Sockets_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

void prvFindSelectedSocket( SocketSelect_t * pxSocketSet );

BaseType_t prvDetermineSocketSize( BaseType_t xDomain,
                                   BaseType_t xType,
                                   BaseType_t xProtocol,
                                   size_t * pxSocketSize );

BaseType_t prvMakeSureSocketIsBound( FreeRTOS_Socket_t * pxSocket );

void prvTCPSetSocketCount( FreeRTOS_Socket_t const * pxSocketToDelete );

BaseType_t prvSockopt_so_buffer( FreeRTOS_Socket_t * pxSocket,
                                 int32_t lOptionName,
                                 const void * pvOptionValue );
uint16_t prvGetPrivatePortNumber( BaseType_t xProtocol );

const ListItem_t * pxListFindListItemWithValue( const List_t * pxList,
                                                TickType_t xWantedItemValue );

BaseType_t prvTCPConnectStart( FreeRTOS_Socket_t * pxSocket,
                               struct freertos_sockaddr const * pxAddress );

int32_t prvTCPSendCheck( FreeRTOS_Socket_t * pxSocket,
                         size_t uxDataLength );

StreamBuffer_t * prvTCPCreateStream( FreeRTOS_Socket_t * pxSocket,
                                     BaseType_t xIsInputStream );

BaseType_t prvValidSocket( const FreeRTOS_Socket_t * pxSocket,
                           BaseType_t xProtocol,
                           BaseType_t xIsBound );

BaseType_t bMayConnect( FreeRTOS_Socket_t const * pxSocket );

extern List_t xBoundUDPSocketsList;
extern List_t xBoundTCPSocketsList;

static IPv6_Address_t xIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

/* ============================== Test Cases ============================== */

/**
 * @brief Sending to IP-task fails.
 */
void test_prvFindSelectedSocket_SendFail( void )
{
    SocketSelect_t xSocketSet;

    xEventGroupClearBits_ExpectAndReturn( xSocketSet.xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdFALSE );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    prvFindSelectedSocket( &xSocketSet );
}

/**
 * @brief Sending to IP-task is successful.
 */
void test_prvFindSelectedSocket_SendSuccess( void )
{
    SocketSelect_t xSocketSet;

    xEventGroupClearBits_ExpectAndReturn( xSocketSet.xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdFALSE );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    xEventGroupWaitBits_ExpectAndReturn( xSocketSet.xSelectGroup, ( BaseType_t ) eSELECT_CALL_IP, pdTRUE, pdFALSE, portMAX_DELAY, pdTRUE );

    prvFindSelectedSocket( &xSocketSet );
}

/**
 * @brief Invalid or NULL socket test.
 */
void test_prvValidSocket_InvalidOrNULLSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t * pxSocket = ( FreeRTOS_Socket_t * ) FREERTOS_INVALID_SOCKET;
    BaseType_t xProtocol = FREERTOS_IPPROTO_UDP, xIsBound = pdFALSE;

    xReturn = prvValidSocket( NULL, xProtocol, xIsBound );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    xReturn = prvValidSocket( pxSocket, xProtocol, xIsBound );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief Socket bound variable set, but the socket is not actually bound.
 */
void test_prvValidSocket_SocketBoundSetButNotBound( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xProtocol = FREERTOS_IPPROTO_UDP, xIsBound = pdTRUE;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xReturn = prvValidSocket( &xSocket, xProtocol, xIsBound );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief Socket bound variable reset, but the socket is actually bound.
 */
void test_prvValidSocket_SocketBoundResetButBound( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xProtocol = FREERTOS_IPPROTO_UDP, xIsBound = pdFALSE;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket.ucProtocol = xProtocol;

    xReturn = prvValidSocket( &xSocket, xProtocol, xIsBound );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief Invalid protocol present in the socket structure.
 */
void test_prvValidSocket_InvalidProtocol( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xProtocol = FREERTOS_IPPROTO_UDP, xIsBound = pdTRUE;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xSocket.ucProtocol = xProtocol + 1;

    xReturn = prvValidSocket( &xSocket, xProtocol, xIsBound );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief This function is a wrapper expected to call only the initialisation functions for the bound sockets lists.
 */
void test_vNetworkSocketsInit( void )
{
    vListInitialise_Expect( &xBoundUDPSocketsList );
    vListInitialise_Expect( &xBoundTCPSocketsList );

    vNetworkSocketsInit();
}

/**
 * @brief Test case when IP-Task is not initialised.
 */
void test_prvDetermineSocketSize_IPTaskNotInit( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_IPPROTO_UDP;
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    xReturn = prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief Assertion when the domain is anything except FREERTOS_AF_INET.
 */
void test_prvDetermineSocketSize_CatchAssert( void )
{
    BaseType_t xDomain = FREERTOS_AF_INET + 1, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_IPPROTO_UDP;
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    /* Assertion when the domain is anything except FREERTOS_AF_INET. */
    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

/**
 * @brief Assertion that the UDP socket list must be initialized.
 */
void test_prvDetermineSocketSize_CatchAssert2( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_IPPROTO_UDP;
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdFALSE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );

    /* Assertion that the UDP socket list must be initialized. */
    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

/**
 * @brief Assertion that the TCP socket list must be initialized.
 */
void test_prvDetermineSocketSize_CatchAssert3( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_IPPROTO_UDP;
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdFALSE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );
    memset( &xBoundTCPSocketsList, 0, sizeof( xBoundTCPSocketsList ) );

    xBoundUDPSocketsList.xListEnd.xItemValue = portMAX_DELAY;

    /* Assertion that the TCP socket list must be initialized. */
    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

/**
 * @brief Assertion that the protocol must be either TCP or UDP.
 */
void test_prvDetermineSocketSize_CatchAssert4( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM, xProtocol = ~( FREERTOS_IPPROTO_UDP | FREERTOS_IPPROTO_TCP );
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );
    memset( &xBoundTCPSocketsList, 0, sizeof( xBoundTCPSocketsList ) );

    xBoundUDPSocketsList.xListEnd.xItemValue = portMAX_DELAY;
    xBoundTCPSocketsList.xListEnd.xItemValue = portMAX_DELAY;

    /* Assertion that the protocol must be either TCP or UDP. */
    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

/**
 * @brief Assertion that the protocol type and the socket type must match.
 */
void test_prvDetermineSocketSize_CatchAssert5( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM + 1, xProtocol = FREERTOS_IPPROTO_UDP;
    size_t xSocketSize;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );
    memset( &xBoundTCPSocketsList, 0, sizeof( xBoundTCPSocketsList ) );

    xBoundUDPSocketsList.xListEnd.xItemValue = portMAX_DELAY;
    xBoundTCPSocketsList.xListEnd.xItemValue = portMAX_DELAY;

    /* Assertion that the protocol type and the socket type must match. */
    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

/**
 * @brief Happy path with UDP socket size being determined.
 */
void test_prvDetermineSocketSize_UDPSocket( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_IPPROTO_UDP;
    size_t xSocketSize;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );
    memset( &xBoundTCPSocketsList, 0, sizeof( xBoundTCPSocketsList ) );

    xBoundUDPSocketsList.xListEnd.xItemValue = portMAX_DELAY;
    xBoundTCPSocketsList.xListEnd.xItemValue = portMAX_DELAY;

    xReturn = prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xUDP ), xSocketSize );
}

/**
 * @brief Assertion that the protocol type and the socket type must match.
 */
void test_prvDetermineSocketSize_CatchAssert6( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_DGRAM, xProtocol = FREERTOS_IPPROTO_TCP;
    size_t xSocketSize;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    memset( &xBoundUDPSocketsList, 0, sizeof( xBoundUDPSocketsList ) );
    memset( &xBoundTCPSocketsList, 0, sizeof( xBoundTCPSocketsList ) );

    xBoundUDPSocketsList.xListEnd.xItemValue = portMAX_DELAY;
    xBoundTCPSocketsList.xListEnd.xItemValue = portMAX_DELAY;

    /* Assertion that the protocol type and the socket type must match. */
    catch_assert( prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize ) );
}

/**
 * @brief Happy path with TCP socket size being determined.
 */
void test_prvDetermineSocketSize_TCPSocket( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    size_t xSocketSize;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    xReturn = prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), xSocketSize );
}

/**
 * @brief Happy path with TCPv6 socket size being determined.
 */
void test_prvDetermineSocketSize_TCPv6Socket( void )
{
    BaseType_t xReturn;
    BaseType_t xDomain = FREERTOS_AF_INET6, xType = FREERTOS_SOCK_STREAM, xProtocol = FREERTOS_IPPROTO_TCP;
    size_t xSocketSize;
    FreeRTOS_Socket_t const * pxSocket = NULL;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundUDPSocketsList, pdTRUE );
    listLIST_IS_INITIALISED_ExpectAndReturn( &xBoundTCPSocketsList, pdTRUE );

    xReturn = prvDetermineSocketSize( xDomain, xType, xProtocol, &xSocketSize );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL( ( sizeof( *pxSocket ) - sizeof( pxSocket->u ) ) + sizeof( pxSocket->u.xTCP ), xSocketSize );
}

/**
 * @brief Test for NULL Socket.
 */
void test_prvMakeSureSocketIsBound_NULLSocket( void )
{
    BaseType_t xResult;

    xResult = prvMakeSureSocketIsBound( NULL );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/**
 * @brief Incompatible protocol.
 */
void test_prvMakeSureSocketIsBound_TCPProtocol( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    xResult = prvMakeSureSocketIsBound( &xSocket );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/**
 * @brief Socket is already bound.
 */
void test_prvMakeSureSocketIsBound_SocketAlreadyBound( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xResult = prvMakeSureSocketIsBound( &xSocket );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

/**
 * @brief Socket is not bound but attempt of binding fails.
 */
void test_prvMakeSureSocketIsBound_SocketNotBound_BindingFails( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    xResult = prvMakeSureSocketIsBound( &xSocket );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/**
 * @brief Socket is not bound and binding is successful.
 */
void test_prvMakeSureSocketIsBound_SocketNotBound_BindingSuccess( void )
{
    BaseType_t xResult;
    FreeRTOS_Socket_t xSocket;

    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    xEventGroupWaitBits_ExpectAndReturn( xSocket.xEventGroup, ( EventBits_t ) eSOCKET_BOUND, pdTRUE, pdFALSE, portMAX_DELAY, pdTRUE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xResult = prvMakeSureSocketIsBound( &xSocket );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

/**
 * @brief Trying to bind a NULL socket.
 */
void test_vSocketBind_CatchAssert1( void )
{
    BaseType_t xReturn;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength = 0;
    BaseType_t xInternal = 0;

    catch_assert( vSocketBind( NULL, &xBindAddress, uxAddressLength, xInternal ) );
}

/**
 * @brief Trying to bind an invalid socket.
 */
void test_vSocketBind_CatchAssert2( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal;

    catch_assert( vSocketBind( FREERTOS_INVALID_SOCKET, &xBindAddress, uxAddressLength, xInternal ) );
}

/**
 * @brief Binding successful.
 */
void test_vSocketBind_TCP( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();



    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Address passed is NULL.
 */
void test_vSocketBind_TCPNULLAddress_v4( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocket.bits.bIsIPv6 = 0;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );
    xReturn = vSocketBind( &xSocket, NULL, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRNOTAVAIL, xReturn );
}

/**
 * @brief Address passed is NULL.
 */
void test_vSocketBind_TCPNULLAddress_v6( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocket.bits.bIsIPv6 = 1;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );
    xReturn = vSocketBind( &xSocket, NULL, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRNOTAVAIL, xReturn );
}

/**
 * @brief Random number generator fails to get a random port number.
 */
void test_vSocketBind_RNGFails( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xBindAddress.sin_port = 0;

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRNOTAVAIL, xReturn );
}

/**
 * @brief Binding the socket to a given port number.
 */
void test_vSocketBind_NonZeroPortNumber( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdFALSE;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xBindAddress.sin_port = 0x12;

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief NULL item returned.
 */
void test_vSocketBind_GotNULLItem( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdTRUE;
    ListItem_t xLocalList;
    ListItem_t * xListStart = NULL;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAnyArgsAndReturn( xListStart );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( xListStart, 0 );

    listGET_NEXT_ExpectAnyArgsAndReturn( xListStart );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( xListStart, xBindAddress.sin_port );

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xBindAddress.sin_port ), xSocket.usLocalPort );
}

/**
 * @brief Got a non-NULL list.
 */
void test_vSocketBind_GotANonNULLValue( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdTRUE;
    ListItem_t xLocalList;
    ListItem_t * xListStart = &xLocalList;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAnyArgsAndReturn( xListStart );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( xListStart, 0 );

    listGET_NEXT_ExpectAnyArgsAndReturn( xListStart );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( xListStart, xBindAddress.sin_port );

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EADDRINUSE, xReturn );
    TEST_ASSERT_EQUAL( 0, xSocket.usLocalPort );
}

/**
 * @brief TCP socket bind happy path.
 */
void test_vSocketBind_TCPGotAProperValue( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdTRUE;
    ListItem_t xLocalList;
    ListItem_t * xListStart = &xLocalList;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xBindAddress.sin_port ), xSocket.usLocalPort );
}

/**
 * @brief TCP trying to bind to port 0.
 */
void test_vSocketBind_TCPGotAProperValuePortZero( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdTRUE;
    MiniListItem_t xLocalList;

    xBoundTCPSocketsList.xListEnd = xLocalList;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );

    xBindAddress.sin_port = 0;

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), FreeRTOS_htons( 1024 ) );

    FreeRTOS_FindEndPointOnIP_IPv4_ExpectAnyArgsAndReturn( NULL );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xBindAddress.sin_port ), xSocket.usLocalPort );
}

/**
 * @brief TCPv6 socket bind happy path.
 */
void test_vSocketBind_TCPv6GotAProperValue( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdTRUE;
    ListItem_t xLocalList;
    ListItem_t * xListStart = &xLocalList;
    IPv6_Address_t xIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } }; /* 2001::1 */
    NetworkEndPoint_t xEndPoint;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xEndPoint.bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xBindAddress.sin_family = FREERTOS_AF_INET6;
    memcpy( xBindAddress.sin_address.xIP_IPv6.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xBindAddress.sin_port ), xSocket.usLocalPort );
    TEST_ASSERT_EQUAL_MEMORY( xIPv6Address.ucBytes, xSocket.xLocalAddress.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief TCP socket bind with FREERTOS_INADDR_ANY.
 */
void test_vSocketBind_TCPBindAnyAddress( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xBindAddress;
    size_t uxAddressLength;
    BaseType_t xInternal = pdTRUE;
    ListItem_t xLocalList;
    ListItem_t * xListStart = &xLocalList;
    IPv6_Address_t xIPv6Address;

    memset( &xBindAddress, 0xFC, sizeof( xBindAddress ) );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xIPv6Address, 0, sizeof( xIPv6Address ) );

    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xBindAddress.sin_family = FREERTOS_AF_INET4;
    xBindAddress.sin_address.ulIP_IPv4 = FREERTOS_INADDR_ANY;

    listSET_LIST_ITEM_VALUE_Expect( &( xSocket.xBoundSocketListItem ), xBindAddress.sin_port );

    vListInsertEnd_Expect( NULL, &( xSocket.xBoundSocketListItem ) );
    vListInsertEnd_IgnoreArg_pxList();

    xReturn = vSocketBind( &xSocket, &xBindAddress, uxAddressLength, xInternal );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( xBindAddress.sin_port ), xSocket.usLocalPort );
    TEST_ASSERT_EQUAL_MEMORY( xIPv6Address.ucBytes, xSocket.xLocalAddress.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief Closing unbound socket with unknown protocol.
 */
void test_vSocketClose_UnknownProtocol_NotBound( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    vEventGroupDelete_Expect( xSocket.xEventGroup );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

/**
 * @brief Closing unbound socket having a NULL event group with unknown protocol.
 */
void test_vSocketClose_UnknownProtocol_NotBound_EventGroupNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

/**
 * @brief Closing a TCP socket which has every object assigned.
 */
void test_vSocketClose_TCP_EverythingNonNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;
    ListItem_t xLocalList;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;
    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    vReleaseNetworkBufferAndDescriptor_Expect( xSocket.u.xTCP.pxAckMessage );

    vTCPWindowDestroy_Expect( &( xSocket.u.xTCP.xTCPWindow ) );

    vPortFree_Expect( xSocket.u.xTCP.rxStream );

    vPortFree_Expect( xSocket.u.xTCP.txStream );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

/**
 * @brief TCP socket being closed where there is still a pointer to last acknowledged packet.
 */
void test_vSocketClose_TCP_LastAckMessageNonNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;
    ListItem_t xLocalList;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;
    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xSocket.u.xTCP.pxAckMessage = NULL;

    vTCPWindowDestroy_Expect( &( xSocket.u.xTCP.xTCPWindow ) );

    vPortFree_Expect( xSocket.u.xTCP.rxStream );

    vPortFree_Expect( xSocket.u.xTCP.txStream );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

/**
 * @brief Closing a socket with streams non-NULL.
 */
void test_vSocketClose_TCP_AllFieldsNonNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;
    ListItem_t xLocalList;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;
    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;

    xSocket.u.xTCP.pxAckMessage = NULL;
    xSocket.u.xTCP.rxStream = NULL;
    xSocket.u.xTCP.txStream = NULL;

    vTCPWindowDestroy_Expect( &( xSocket.u.xTCP.xTCPWindow ) );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) 0x12345678 );

    uxListRemove_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0 );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

/**
 * @brief Closing a UDP socket which doesn't have any waiting packets.
 */
void test_vSocketClose_UDP_NoWaitingPackets( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;
    ListItem_t xLocalList;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;
    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket.u.xUDP.xWaitingPacketsList ), 0 );

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

/**
 * @brief Closing a UDP socket which has some waiting packets.
 */
void test_vSocketClose_UDP_SomeWaitingPackets( void )
{
    FreeRTOS_Socket_t xSocket;
    void * pvReturn;
    ListItem_t xLocalList;
    NetworkBufferDescriptor_t xNetworkBuffer;
    int i;

    memset( &xSocket, 0xAB, sizeof( xSocket ) );

    xSocket.xEventGroup = NULL;
    xSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket.u.xUDP.xWaitingPacketsList ), 5 );

    for( i = 0; i < 5; i++ )
    {
        listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xSocket.u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

        uxListRemove_ExpectAndReturn( &( xNetworkBuffer.xBufferListItem ), pdPASS );

        vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

        listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket.u.xUDP.xWaitingPacketsList ), 4 - i );
    }

    vPortFree_Expect( &xSocket );

    pvReturn = vSocketClose( &xSocket );

    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

/**
 * @brief Set children count of a listening socket which does not have any.
 */
void test_prvTCPSetSocketCount_ListeningSocketNoChildren( void )
{
    FreeRTOS_Socket_t xSocketToDelete;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eTCP_LISTEN;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );
}

/**
 * @brief Set children count of a listening socket which has non-zero children.
 */
void test_prvTCPSetSocketCount_ListeningSocketNonZeroChildren1( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eTCP_LISTEN;

    xChildSocket.u.xTCP.eTCPState = eTCP_LISTEN;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );
}

/**
 * @brief Set children count of a listening socket which has non-zero children.
 */
void test_prvTCPSetSocketCount_ListeningSocketNonZeroChildren2( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.eTCPState = eCONNECT_SYN;
    xChildSocket.usLocalPort = usLocalPort + 1;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );
}

/**
 * @brief Set children count of a listening socket which has non-zero children.
 */
void test_prvTCPSetSocketCount_ListeningSocketNonZeroChildren3( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.eTCPState = eCONNECT_SYN;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.bits.bPassQueued = pdFALSE_UNSIGNED;
    xChildSocket.u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );
}

/**
 * @brief Set children count of a listening socket which has non-zero children.
 */
void test_prvTCPSetSocketCount_ListeningSocketNonZeroChildren4( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.eTCPState = eCONNECT_SYN;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.bits.bPassQueued = pdFALSE_UNSIGNED;
    xChildSocket.u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );
}

/**
 * @brief Setting the socket count happy path.
 */
void test_prvTCPSetSocketCount_ListeningSock_HappyPath1( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.eTCPState = eCONNECT_SYN;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;
    xChildSocket.u.xTCP.bits.bPassAccept = pdFALSE_UNSIGNED;
    xChildSocket.xEventGroup = NULL;
    xChildSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xChildSocket.u.xTCP.pxAckMessage = NULL;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    vTCPWindowDestroy_Expect( &( xChildSocket.u.xTCP.xTCPWindow ) );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xChildSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xChildSocket );

    prvTCPSetSocketCount( &xSocketToDelete );
}

/**
 * @brief Setting the socket count happy path.
 */
void test_prvTCPSetSocketCount_ListeningSock_HappyPath2( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.eTCPState = eCONNECT_SYN;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.bits.bPassQueued = pdFALSE_UNSIGNED;
    xChildSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xChildSocket.xEventGroup = NULL;
    xChildSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xChildSocket.u.xTCP.pxAckMessage = NULL;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    vTCPWindowDestroy_Expect( &( xChildSocket.u.xTCP.xTCPWindow ) );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xChildSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xChildSocket );

    prvTCPSetSocketCount( &xSocketToDelete );
}

/**
 * @brief Setting the socket count happy path.
 */
void test_prvTCPSetSocketCount_ListeningSock_HappyPath3( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eTCP_LISTEN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.eTCPState = eCONNECT_SYN;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.bits.bPassQueued = pdTRUE_UNSIGNED;
    xChildSocket.u.xTCP.bits.bPassAccept = pdTRUE_UNSIGNED;
    xChildSocket.xEventGroup = NULL;
    xChildSocket.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xChildSocket.u.xTCP.pxAckMessage = NULL;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    vTCPWindowDestroy_Expect( &( xChildSocket.u.xTCP.xTCPWindow ) );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xChildSocket.xBoundSocketListItem ), NULL );

    vPortFree_Expect( &xChildSocket );

    prvTCPSetSocketCount( &xSocketToDelete );
}

/**
 * @brief Set the socket count of a non-listening socket.
 */
void test_prvTCPSetSocketCount_NotListeningSock_1( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eCONNECT_SYN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.eTCPState = eCONNECT_SYN;
    xChildSocket.u.xTCP.usChildCount = 100;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );

    TEST_ASSERT_EQUAL( 100, xChildSocket.u.xTCP.usChildCount );
}

/**
 * @brief Set the socket count of a non-listening socket.
 */
void test_prvTCPSetSocketCount_NotListeningSock_2( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eCONNECT_SYN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.eTCPState = eTCP_LISTEN;
    xChildSocket.usLocalPort = usLocalPort + 1;
    xChildSocket.u.xTCP.usChildCount = 100;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );

    TEST_ASSERT_EQUAL( 100, xChildSocket.u.xTCP.usChildCount );
}

/**
 * @brief Set the socket count of a non-listening socket.
 */
void test_prvTCPSetSocketCount_NotListeningSock_3( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eCONNECT_SYN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.eTCPState = eTCP_LISTEN;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.usChildCount = 0;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    listGET_NEXT_ExpectAndReturn( &( xIterator ), ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    prvTCPSetSocketCount( &xSocketToDelete );

    TEST_ASSERT_EQUAL( 0, xChildSocket.u.xTCP.usChildCount );
}

/**
 * @brief Happy path of setting socket count of a non-listening socket.
 */
void test_prvTCPSetSocketCount_NotListeningSock_HappyPath( void )
{
    FreeRTOS_Socket_t xSocketToDelete, xChildSocket;
    ListItem_t xIterator;
    uint16_t usLocalPort = 0x1234;

    memset( &xSocketToDelete, 0, sizeof( xSocketToDelete ) );
    memset( &xChildSocket, 0, sizeof( xChildSocket ) );

    xSocketToDelete.ucProtocol = ( uint8_t ) FREERTOS_IPPROTO_TCP;
    xSocketToDelete.u.xTCP.eTCPState = eCONNECT_SYN;
    xSocketToDelete.usLocalPort = usLocalPort;

    xChildSocket.u.xTCP.eTCPState = eTCP_LISTEN;
    xChildSocket.usLocalPort = usLocalPort;
    xChildSocket.u.xTCP.usChildCount = 100;

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &( xIterator ) );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xIterator, &xChildSocket );

    prvTCPSetSocketCount( &xSocketToDelete );

    TEST_ASSERT_EQUAL( 99, xChildSocket.u.xTCP.usChildCount );
}

/**
 * @brief Invalid protocol.
 */
void test_prvSockopt_so_buffer_InvalidProtocol( void )
{
    FreeRTOS_Socket_t xSocket;
    int32_t lOptionName;
    uint8_t vOptionValue[ sizeof( uintptr_t ) ];
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xReturn = prvSockopt_so_buffer( &xSocket, lOptionName, vOptionValue );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Invalid option.
 */
void test_prvSockopt_so_buffer_InvalidOption1( void )
{
    FreeRTOS_Socket_t xSocket;
    int32_t lOptionName;
    uint32_t vOptionValue = 0xABCD1234;
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    lOptionName = FREERTOS_SO_SNDBUF;
    xSocket.u.xTCP.txStream = NULL;
    xSocket.u.xTCP.usMSS = 0x12;

    FreeRTOS_round_up_ExpectAndReturn( vOptionValue, xSocket.u.xTCP.usMSS, 0xAB );

    xReturn = prvSockopt_so_buffer( &xSocket, lOptionName, &vOptionValue );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( 0xAB, xSocket.u.xTCP.uxTxStreamSize );
}

/**
 * @brief Invalid option.
 */
void test_prvSockopt_so_buffer_InvalidOption2( void )
{
    FreeRTOS_Socket_t xSocket;
    int32_t lOptionName;
    uint8_t vOptionValue[ sizeof( uintptr_t ) ];
    BaseType_t xReturn;
    StreamBuffer_t xBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    lOptionName = FREERTOS_SO_SNDBUF;
    xSocket.u.xTCP.txStream = &xBuffer;

    xReturn = prvSockopt_so_buffer( &xSocket, lOptionName, vOptionValue );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Invalid option.
 */
void test_prvSockopt_so_buffer_InvalidOption3( void )
{
    FreeRTOS_Socket_t xSocket;
    int32_t lOptionName;
    uint32_t vOptionValue = 0xABCD1234;
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    lOptionName = FREERTOS_SO_RCVBUF;
    xSocket.u.xTCP.rxStream = NULL;

    xReturn = prvSockopt_so_buffer( &xSocket, lOptionName, &vOptionValue );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( vOptionValue, xSocket.u.xTCP.uxRxStreamSize );
}

/**
 * @brief Invalid option.
 */
void test_prvSockopt_so_buffer_InvalidOption4( void )
{
    FreeRTOS_Socket_t xSocket;
    int32_t lOptionName;
    uint8_t vOptionValue[ sizeof( uintptr_t ) ];
    BaseType_t xReturn;
    StreamBuffer_t xBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    lOptionName = FREERTOS_SO_RCVBUF;
    xSocket.u.xTCP.rxStream = &xBuffer;

    xReturn = prvSockopt_so_buffer( &xSocket, lOptionName, vOptionValue );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Getting private port number fails as RNG fails.
 */
void test_prvGetPrivatePortNumber_TCP_RNGFails( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_TCP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( 0, usReturn );
}

/**
 * @brief Port number not received as IP task is not ready.
 */
void test_prvGetPrivatePortNumber_TCP_IPTaskNotReady( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_TCP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( 4, usReturn );
}

/**
 * @brief Port number acquired success.
 */
void test_prvGetPrivatePortNumber_TCP_Found( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_TCP;
    ListItem_t xLocalListEnd;
    ListItem_t xIterator;

    xRNGStatus = pdTRUE;
    xRandomNumberToReturn = 1234;
    TickType_t xWantedItemValue = 53768;

    xApplicationGetRandomNumber_Stub( xStubApplicationGetRandomNumber );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &xIterator );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &xIterator, xWantedItemValue );

    xApplicationGetRandomNumber_Stub( xStubApplicationGetRandomNumber );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( xWantedItemValue, usReturn );
}

/**
 * @brief Port number for UDP fails as RNG fails.
 */
void test_prvGetPrivatePortNumber_UDP_RNGFails( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_UDP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( 0, usReturn );
}

/**
 * @brief Don't get a port number as IP task is not ready.
 */
void test_prvGetPrivatePortNumber_UDP_IPTaskNotReady( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_UDP;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( 4, usReturn );
}

/**
 * @brief UDP port number found success.
 */
void test_prvGetPrivatePortNumber_UDP_Found( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_UDP;
    ListItem_t xLocalListEnd;
    ListItem_t xIterator;

    xRNGStatus = pdTRUE;
    xRandomNumberToReturn = 1234;
    TickType_t xWantedItemValue = 53768;

    xApplicationGetRandomNumber_Stub( xStubApplicationGetRandomNumber );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundUDPSocketsList.xListEnd ), &xIterator );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &xIterator, xWantedItemValue );

    xApplicationGetRandomNumber_Stub( xStubApplicationGetRandomNumber );

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( xWantedItemValue, usReturn );
}

/**
 * @brief UDP port number not found after all iterations.
 */
void test_prvGetPrivatePortNumber_UDP_NotFoundAfterAllIterations( void )
{
    uint16_t usReturn;
    BaseType_t xProtocol = FREERTOS_IPPROTO_UDP;
    ListItem_t xLocalListEnd;
    ListItem_t xIterator;

    xRNGStatus = pdTRUE;
    xRandomNumberToReturn = 1234;
    TickType_t xWantedItemValue = 53768;

    xApplicationGetRandomNumber_Stub( xStubApplicationGetRandomNumber );

    xIPIsNetworkTaskReady_IgnoreAndReturn( pdTRUE );

    listGET_NEXT_IgnoreAndReturn( &xIterator );

    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( xWantedItemValue );

    usReturn = prvGetPrivatePortNumber( xProtocol );

    TEST_ASSERT_EQUAL( 0, usReturn );
}

/**
 * @brief Finding in a NULL list.
 */
void test_pxListFindListItemWithValue_NULLList( void )
{
    const ListItem_t * pxReturn;
    List_t xList;
    TickType_t xWantedItemValue;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    pxReturn = pxListFindListItemWithValue( NULL, xWantedItemValue );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Finding in a list when IP task is not ready.
 */
void test_pxListFindListItemWithValue_IPTaskNotReady( void )
{
    const ListItem_t * pxReturn;
    List_t xList;
    TickType_t xWantedItemValue;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );

    pxReturn = pxListFindListItemWithValue( &xList, xWantedItemValue );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Finding in list when there is nothing in the list.
 */
void test_pxListFindListItemWithValue_ListLengthZero( void )
{
    const ListItem_t * pxReturn;
    List_t xList;
    TickType_t xWantedItemValue;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xList.xListEnd ), ( ListItem_t * ) &( xList.xListEnd ) );

    pxReturn = pxListFindListItemWithValue( &xList, xWantedItemValue );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Value being searched for not found.
 */
void test_pxListFindListItemWithValue_NotFound( void )
{
    const ListItem_t * pxReturn;
    List_t xList;
    ListItem_t xLocalListItem;
    TickType_t xWantedItemValue = 0xABAB;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xList.xListEnd ), ( ListItem_t * ) &( xLocalListItem ) );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xLocalListItem ), xWantedItemValue - 1 );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xLocalListItem ), ( ListItem_t * ) &( xList.xListEnd ) );

    pxReturn = pxListFindListItemWithValue( &xList, xWantedItemValue );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Value found.
 */
void test_pxListFindListItemWithValue_Found( void )
{
    const ListItem_t * pxReturn;
    List_t xList;
    ListItem_t xLocalListItem;
    TickType_t xWantedItemValue = 0xABAB;

    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xList.xListEnd ), &( xLocalListItem ) );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xLocalListItem ), xWantedItemValue );

    pxReturn = pxListFindListItemWithValue( &xList, xWantedItemValue );

    TEST_ASSERT_EQUAL_PTR( &( xLocalListItem ), pxReturn );
}

/**
 * @brief Could not find UDP socket.
 */
void test_pxUDPSocketLookup_NotFound( void )
{
    FreeRTOS_Socket_t * pxReturn;
    UBaseType_t uxLocalPort;

    vpxListFindListItemWithValue_NotFound();

    pxReturn = pxUDPSocketLookup( uxLocalPort );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief Found a NULL socket.
 */
void test_pxUDPSocketLookup_FoundNULLSocket( void )
{
    FreeRTOS_Socket_t * pxReturn;
    UBaseType_t uxLocalPort = 0xBCDEF;
    ListItem_t xListItem;

    vpxListFindListItemWithValue_Found( &xBoundUDPSocketsList, uxLocalPort, &xListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xListItem, NULL );

    catch_assert( pxUDPSocketLookup( uxLocalPort ) );
}

/**
 * @brief Found a proper UDP socket.
 */
void test_pxUDPSocketLookup_Found( void )
{
    FreeRTOS_Socket_t * pxReturn;
    UBaseType_t uxLocalPort = 0xBCDEF;
    ListItem_t xListItem;
    FreeRTOS_Socket_t xLocalSocket;

    vpxListFindListItemWithValue_Found( &xBoundUDPSocketsList, uxLocalPort, &xListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xListItem, &xLocalSocket );

    pxReturn = pxUDPSocketLookup( uxLocalPort );

    TEST_ASSERT_EQUAL( &xLocalSocket, pxReturn );
}

/**
 * @brief Convert ascii values to hexadecimal values.
 */
void test_ucASCIIToHex( void )
{
    uint8_t ucHex, IdealValue;
    char ucInput;

    ucInput = '0';
    IdealValue = 0;
    int i;
    char j;

    for( i = 0; i <= 9; i++ )
    {
        ucHex = ucASCIIToHex( ucInput + i );
        TEST_ASSERT_EQUAL( IdealValue + i, ucHex );
    }

    ucInput = 'a';
    IdealValue = 10;

    for( i = 0; i < 6; i++ )
    {
        ucHex = ucASCIIToHex( ucInput + i );
        TEST_ASSERT_EQUAL( IdealValue + i, ucHex );
    }

    ucInput = 'A';
    IdealValue = 10;

    for( i = 0; i < 6; i++ )
    {
        ucHex = ucASCIIToHex( ucInput + i );
        TEST_ASSERT_EQUAL( IdealValue + i, ucHex );
    }

    for( j = 0; ; j++ )
    {
        if( !( ( ( j >= 'a' ) && ( j <= 'f' ) ) ||
               ( ( j >= 'A' ) && ( j <= 'F' ) ) ||
               ( ( j >= '0' ) && ( j <= '9' ) ) ) )
        {
            ucHex = ucASCIIToHex( j );
            TEST_ASSERT_EQUAL( 0xFF, ucHex );
        }

        if( j == 125 )
        {
            break;
        }
    }
}

/**
 * @brief All fields NULL of socket.
 */
void test_vSocketWakeUpUser_AllNULL( void )
{
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    vSocketWakeUpUser( &xSocket );

    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
}

/**
 * @brief All fields are assigned of the socket.
 */
void test_vSocketWakeUpUser_AllNonNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    uint8_t xLocalSemaphore[ sizeof( xSocket.pxUserSemaphore ) ];
    uint8_t xLocalSocketSet[ sizeof( xSocket.pxSocketSet ) ];
    uint8_t xLocalEventGroup[ sizeof( xSocket.xEventGroup ) ];

    uxGlobalCallbackCount = 0;
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.pxUserSemaphore = ( SemaphoreHandle_t ) xLocalSemaphore;
    xSocket.pxUserWakeCallback = vUserCallbackLocal;
    xSocket.pxSocketSet = ( SocketSelect_t * ) xLocalSocketSet;
    xSocket.xEventGroup = ( EventGroupHandle_t ) xLocalEventGroup;

    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    vSocketWakeUpUser( &xSocket );

    TEST_ASSERT_EQUAL( 1, uxGlobalCallbackCount );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
}

/**
 * @brief Event bits are set for the socket.
 */
void test_vSocketWakeUpUser_AllNonNULL_EventBitsSet( void )
{
    FreeRTOS_Socket_t xSocket;
    uint8_t xLocalSemaphore[ sizeof( xSocket.pxUserSemaphore ) ];
    uint8_t xLocalSocketSet[ sizeof( xSocket.pxSocketSet ) ];
    uint8_t xLocalEventGroup[ sizeof( xSocket.xEventGroup ) ];

    uxGlobalCallbackCount = 0;
    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.pxUserSemaphore = ( SemaphoreHandle_t ) xLocalSemaphore;
    xSocket.pxUserWakeCallback = vUserCallbackLocal;
    xSocket.pxSocketSet = ( SocketSelect_t * ) xLocalSocketSet;
    xSocket.xEventGroup = ( EventGroupHandle_t ) xLocalEventGroup;

    xSocket.xEventBits = ( eSOCKET_ALL << SOCKET_EVENT_BIT_COUNT ) | eSOCKET_ALL;

    xQueueGenericSend_ExpectAndReturn( xSocket.pxUserSemaphore, NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK, pdPASS );

    xEventGroupSetBits_ExpectAndReturn( xSocket.pxSocketSet->xSelectGroup, eSOCKET_ALL & eSELECT_ALL, pdPASS );
    xEventGroupSetBits_ExpectAndReturn( xSocket.xEventGroup, eSOCKET_ALL, pdPASS );

    vSocketWakeUpUser( &xSocket );

    TEST_ASSERT_EQUAL( 1, uxGlobalCallbackCount );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
}

/**
 * @brief Test all states of which may connect.
 */
void test_bMayConnect( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.eTCPState = eCLOSED;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    xSocket.u.xTCP.eTCPState = eCLOSE_WAIT;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( 0, xReturn );

    xSocket.u.xTCP.eTCPState = eCONNECT_SYN;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINPROGRESS, xReturn );

    xSocket.u.xTCP.eTCPState = eTCP_LISTEN;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.eTCPState = eSYN_FIRST;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.eTCPState = eSYN_RECEIVED;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.eTCPState = eFIN_WAIT_1;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.eTCPState = eFIN_WAIT_2;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.eTCPState = eCLOSING;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.eTCPState = eLAST_ACK;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );

    xSocket.u.xTCP.eTCPState = eTIME_WAIT;
    xReturn = bMayConnect( &xSocket );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EAGAIN, xReturn );
}

/**
 * @brief Try to connect to NULL address.
 */
void test_prvTCPConnectStart_AddressNULL( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xReturn = prvTCPConnectStart( &xSocket, NULL );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, xReturn );
}

/**
 * @brief Trying to connect with a invalid socket.
 */
void test_prvTCPConnectStart_InvalidSocket( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EBADF, xReturn );
}

/**
 * @brief Trying to connect an already connected socket.
 */
void test_prvTCPConnectStart_SocketAlreadyConnected( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EISCONN, xReturn );
}

/**
 * @brief Connecting with an unbound socket.
 */
void test_prvTCPConnectStart_SocketNotBound_Success( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    xEventGroupWaitBits_ExpectAnyArgsAndReturn( pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xSocket, eCONNECT_SYN );

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Connecting with an unbound IPv6 socket.
 */
void test_prvTCPConnectStart_IPv6SocketNotBound_Success( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xAddress.sin_family = FREERTOS_AF_INET6;
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    xEventGroupWaitBits_ExpectAnyArgsAndReturn( pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xSocket, eCONNECT_SYN );

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.bits.bIsIPv6 );
}

/**
 * @brief Connecting with an unbound socket. Sending to IP task fails.
 */
void test_prvTCPConnectStart_SocketNotBound_Failure( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    xEventGroupWaitBits_ExpectAnyArgsAndReturn( pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), &xBoundTCPSocketsList );

    vTCPStateChange_Expect( &xSocket, eCONNECT_SYN );

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdFAIL );

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ECANCELED, xReturn );
}

/**
 * @brief Connecting with an unbound socket. Connection is in progress.
 */
void test_prvTCPConnectStart_SocketNotBound_Failure2( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eCONNECT_SYN;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), NULL );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    xEventGroupWaitBits_ExpectAnyArgsAndReturn( pdPASS );

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), &xBoundTCPSocketsList );

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINPROGRESS, xReturn );
}

/**
 * @brief Socket is already bound and is trying to connect.
 */
void test_prvTCPConnectStart_SocketBound_Failure( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;
    struct freertos_sockaddr xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eCONNECT_SYN;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), &xBoundTCPSocketsList );

    xReturn = prvTCPConnectStart( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINPROGRESS, xReturn );
}

/**
 * @brief invalid values.
 */
void test_prvTCPSendCheck_InvalidValues( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxDataLength;
    uint8_t ucStream[ 1500 ];
    eIPTCPState_t array[] = { eCLOSED, eCLOSE_WAIT, eCLOSING };
    StreamBuffer_t xLocalStreamBuffer;
    unsigned int i;

    memset( &xSocket, 0, sizeof( xSocket ) );

    /* Invalid protocol. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, lReturn );

    /* Unbound socket. */
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, lReturn );

    /* No memory. */
    xSocket.u.xTCP.bits.bMallocError = pdTRUE_UNSIGNED;
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOMEM, lReturn );

    /* Invalid states. */
    xSocket.u.xTCP.bits.bMallocError = pdFALSE_UNSIGNED;
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    for( i = 0; i < sizeof( array ) / sizeof( eIPTCPState_t ); i++ )
    {
        xSocket.u.xTCP.eTCPState = array[ i ];
        listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
        lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
        TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOTCONN, lReturn );
    }

    /* Closing connection. */
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdTRUE_UNSIGNED;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( 0, lReturn );

    /* 0 data length. */
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    uxDataLength = 0;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( 0, lReturn );

    /* Could not allocate a stream. */
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    uxDataLength = 10;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );
    vTCPStateChange_ExpectAnyArgs();
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_ENOMEM, lReturn );

    /* Allocate a stream. */
    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    uxDataLength = 10;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    size_t xSizeOfBufferRequested = ( ( sizeof( size_t ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xLocalStreamBuffer ) ) - sizeof( xLocalStreamBuffer.ucArray );
    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( 1, lReturn );
    TEST_ASSERT_EQUAL( ( sizeof( size_t ) & ( ~( sizeof( size_t ) - 1U ) ) ), ( ( StreamBuffer_t * ) ucStream )->LENGTH );
    TEST_ASSERT_EQUAL( ucStream, xSocket.u.xTCP.txStream );

    /* Already allocated a stream. */
    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.bits.bFinSent = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.txStream = &xLocalStreamBuffer;
    uxDataLength = 10;
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &xBoundTCPSocketsList );
    lReturn = prvTCPSendCheck( &xSocket, uxDataLength );
    TEST_ASSERT_EQUAL( 1, lReturn );
}

/**
 * @brief Bound TCP socket list is empty.
 */
void test_xTCPTimerCheck_EmptyList( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep = pdFALSE;

    xTaskGetTickCount_ExpectAndReturn( 0 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 1000 ), xReturn );
}

/**
 * @brief Socket checking results in an error.
 */
void test_xTCPTimerCheck_NonEmptyList_SocketCheckError( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep = pdFALSE;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.u.xTCP.usTimeout = 10;

    xTaskGetTickCount_ExpectAndReturn( 100 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    xTCPSocketCheck_ExpectAndReturn( &xSocket, -1 );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 1000 ), xReturn );
}

/**
 * @brief Socket checking successful.
 */
void test_xTCPTimerCheck_NonEmptyList_NoError( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep = pdFALSE;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.usTimeout = 10;

    xTaskGetTickCount_ExpectAndReturn( 100 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    xTCPSocketCheck_ExpectAndReturn( &xSocket, 0 );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 1000 ), xReturn );
}

/**
 * @brief Delta of times is less than the timeout value.
 */
void test_xTCPTimerCheck_NonEmptyList_DeltaLessThanTimeout( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket, xTimeOutZeroSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xTimeOutZeroSocket, 0, sizeof( xTimeOutZeroSocket ) );

    xSocket.u.xTCP.usTimeout = 10;

    xTaskGetTickCount_ExpectAndReturn( 0 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xTimeOutZeroSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 9 ), xReturn );
    TEST_ASSERT_EQUAL( 9, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Delta of times is less than the timeout value.
 */
void test_xTCPTimerCheck_NonEmptyList_DeltaLessThanTimeout1( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket, xTimeOutZeroSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xTimeOutZeroSocket, 0, sizeof( xTimeOutZeroSocket ) );

    xSocket.u.xTCP.usTimeout = 1008;

    xTaskGetTickCount_ExpectAndReturn( 0 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xTimeOutZeroSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 1000 ), xReturn );
    TEST_ASSERT_EQUAL( 1007, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Event bits are non-zero and will sleep flag is reset.
 */
void test_xTCPTimerCheck_EventBitsNonZeroWontSleep( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep = 0;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket, xTimeOutZeroSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xTimeOutZeroSocket, 0, sizeof( xTimeOutZeroSocket ) );

    xSocket.u.xTCP.usTimeout = 1008;
    xSocket.xEventBits = 12;

    xTaskGetTickCount_ExpectAndReturn( 0 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xTimeOutZeroSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 0 ), xReturn );
    TEST_ASSERT_EQUAL( 1007, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Event bits are non-zero and will sleep flag is set.
 */
void test_xTCPTimerCheck_EventBitsNonZeroWillSleep( void )
{
    TickType_t xReturn;
    BaseType_t xWillSleep = pdTRUE;
    ListItem_t xLocalListItem;
    FreeRTOS_Socket_t xSocket, xTimeOutZeroSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xTimeOutZeroSocket, 0, sizeof( xTimeOutZeroSocket ) );

    xSocket.u.xTCP.usTimeout = 1008;
    xSocket.xEventBits = 12;

    xTaskGetTickCount_ExpectAndReturn( 0 );

    listGET_HEAD_ENTRY_ExpectAndReturn( &xBoundTCPSocketsList, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xTimeOutZeroSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );

    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    listGET_NEXT_ExpectAndReturn( &xLocalListItem, ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    xReturn = xTCPTimerCheck( xWillSleep );

    TEST_ASSERT_EQUAL( pdMS_TO_TICKS( ( TickType_t ) 1000 ), xReturn );
    TEST_ASSERT_EQUAL( 1007, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief Found a matching socket in lookup.
 */
void test_pxTCPSocketLookup_FoundAMatch( void )
{
    FreeRTOS_Socket_t * pxReturn, xSocket, xMatchingSocket;
    uint32_t ulLocalIP = 0xAABBCCDD;
    UBaseType_t uxLocalPort = 0x1234;
    IPv46_Address_t xRemoteIP;

    xRemoteIP.xIs_IPv6 = pdFALSE;
    xRemoteIP.xIPAddress.ulIP_IPv4 = 0xBCBCDCDC;
    UBaseType_t uxRemotePort = 0x4567;
    ListItem_t xLocalListItem;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xMatchingSocket, 0, sizeof( xMatchingSocket ) );

    xMatchingSocket.usLocalPort = uxLocalPort;
    xMatchingSocket.u.xTCP.usRemotePort = uxRemotePort;
    xMatchingSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = xRemoteIP.xIPAddress.ulIP_IPv4;

    /* First iteration, no match. */
    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    /* Second iteration and we have a match. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xMatchingSocket );

    pxReturn = pxTCPSocketLookup( ulLocalIP, uxLocalPort, xRemoteIP, uxRemotePort );

    TEST_ASSERT_EQUAL_PTR( &xMatchingSocket, pxReturn );
}

/**
 * @brief No match found while looking up a socket. IP doesn't match.
 */
void test_pxTCPSocketLookup_NoMatch( void )
{
    FreeRTOS_Socket_t * pxReturn, xSocket, xMatchingSocket;
    uint32_t ulLocalIP = 0xAABBCCDD;
    UBaseType_t uxLocalPort = 0x1234;
    IPv46_Address_t xRemoteIP;

    xRemoteIP.xIs_IPv6 = pdFALSE;
    xRemoteIP.xIPAddress.ulIP_IPv4 = 0xBCBCDCDC;
    UBaseType_t uxRemotePort = 0x4567;
    ListItem_t xLocalListItem;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xMatchingSocket, 0, sizeof( xMatchingSocket ) );

    xMatchingSocket.usLocalPort = uxLocalPort;
    xMatchingSocket.u.xTCP.usRemotePort = uxRemotePort;
    xMatchingSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = xRemoteIP.xIPAddress.ulIP_IPv4 + 1;

    /* First iteration, no match. */
    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    /* Second iteration and we have a match. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xMatchingSocket );

    /* Third iteration. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    pxReturn = pxTCPSocketLookup( ulLocalIP, uxLocalPort, xRemoteIP, uxRemotePort );

    TEST_ASSERT_EQUAL_PTR( NULL, pxReturn );
}

/**
 * @brief No match found while looking up a socket. IP and port number doesn't match.
 */
void test_pxTCPSocketLookup_NoMatch2( void )
{
    FreeRTOS_Socket_t * pxReturn, xSocket, xMatchingSocket;
    uint32_t ulLocalIP = 0xAABBCCDD;
    UBaseType_t uxLocalPort = 0x1234;
    IPv46_Address_t xRemoteIP;

    xRemoteIP.xIs_IPv6 = pdFALSE;
    xRemoteIP.xIPAddress.ulIP_IPv4 = 0xBCBCDCDC;
    UBaseType_t uxRemotePort = 0x4567;
    ListItem_t xLocalListItem;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xMatchingSocket, 0, sizeof( xMatchingSocket ) );

    xMatchingSocket.usLocalPort = uxLocalPort;
    xMatchingSocket.u.xTCP.usRemotePort = uxRemotePort + 1;
    xMatchingSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = xRemoteIP.xIPAddress.ulIP_IPv4 + 1;

    /* First iteration, no match. */
    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    /* Second iteration and we have a match. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xMatchingSocket );

    /* Third iteration. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    pxReturn = pxTCPSocketLookup( ulLocalIP, uxLocalPort, xRemoteIP, uxRemotePort );

    TEST_ASSERT_EQUAL_PTR( NULL, pxReturn );
}

/**
 * @brief Found a partial match based on IP.
 */
void test_pxTCPSocketLookup_FoundAPartialMatch( void )
{
    FreeRTOS_Socket_t * pxReturn, xSocket, xMatchingSocket;
    uint32_t ulLocalIP = 0xAABBCCDD;
    UBaseType_t uxLocalPort = 0x1234;
    IPv46_Address_t xRemoteIP;

    xRemoteIP.xIs_IPv6 = pdFALSE;
    xRemoteIP.xIPAddress.ulIP_IPv4 = 0xBCBCDCDC;
    UBaseType_t uxRemotePort = 0x4567;
    ListItem_t xLocalListItem;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xMatchingSocket, 0, sizeof( xMatchingSocket ) );

    xMatchingSocket.usLocalPort = uxLocalPort;
    xMatchingSocket.u.xTCP.usRemotePort = uxRemotePort + 1;
    xMatchingSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = xRemoteIP.xIPAddress.ulIP_IPv4;
    xMatchingSocket.u.xTCP.eTCPState = eTCP_LISTEN;

    /* First iteration, no match. */
    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    /* Second iteration and we have a partial match. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xMatchingSocket );

    /* Third iteration. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ) );

    pxReturn = pxTCPSocketLookup( ulLocalIP, uxLocalPort, xRemoteIP, uxRemotePort );

    TEST_ASSERT_EQUAL_PTR( &xMatchingSocket, pxReturn );
}

/**
 * @brief Found a match socket based on IPv6.
 */
void test_pxTCPSocketLookup_IPv6Match( void )
{
    FreeRTOS_Socket_t * pxReturn, xSocket, xMatchingSocket;
    uint32_t ulLocalIP = 0xAABBCCDD;
    UBaseType_t uxLocalPort = 0x1234;
    IPv46_Address_t xRemoteIP;
    UBaseType_t uxRemotePort = 0x4567;
    ListItem_t xLocalListItem;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xRemoteIP, 0, sizeof( xRemoteIP ) );
    memset( &xMatchingSocket, 0, sizeof( xMatchingSocket ) );

    xRemoteIP.xIs_IPv6 = pdTRUE;
    memcpy( xRemoteIP.xIPAddress.xIP_IPv6.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xMatchingSocket.usLocalPort = uxLocalPort;
    xMatchingSocket.u.xTCP.usRemotePort = uxRemotePort;
    memcpy( xMatchingSocket.u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    /* First iteration, no match. */
    listGET_NEXT_ExpectAndReturn( ( ListItem_t * ) &( xBoundTCPSocketsList.xListEnd ), &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xSocket );

    /* Second iteration and we have a match. */
    listGET_NEXT_ExpectAndReturn( &xLocalListItem, &xLocalListItem );
    listGET_LIST_ITEM_OWNER_ExpectAndReturn( &xLocalListItem, &xMatchingSocket );
    pxTCPSocketLookup_IPv6_ExpectAndReturn( &xMatchingSocket, NULL, &xMatchingSocket );
    pxTCPSocketLookup_IPv6_IgnoreArg_pxAddress();

    pxReturn = pxTCPSocketLookup( ulLocalIP, uxLocalPort, xRemoteIP, uxRemotePort );

    TEST_ASSERT_EQUAL_PTR( &xMatchingSocket, pxReturn );
}

/**
 * @brief Low and high space fields zero.
 */
void test_prvTCPCreateStream( void )
{
    StreamBuffer_t * pxReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xIsInputStream = pdTRUE;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 20;
    xSocket.u.xTCP.usMSS = 2;
    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( *pxReturn ) ) - sizeof( pxReturn->ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ( StreamBuffer_t * ) ucStream );

    pxReturn = prvTCPCreateStream( &xSocket, xIsInputStream );

    TEST_ASSERT_EQUAL( 4, xSocket.u.xTCP.uxLittleSpace );
    TEST_ASSERT_EQUAL( 16, xSocket.u.xTCP.uxEnoughSpace );
    TEST_ASSERT_EQUAL( ucStream, xSocket.u.xTCP.rxStream );
}

/**
 * @brief Low and high space fields zero.
 */
void test_prvTCPCreateStream1( void )
{
    StreamBuffer_t * pxReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xIsInputStream = pdTRUE;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 0;
    xSocket.u.xTCP.usMSS = 2;
    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( *pxReturn ) ) - sizeof( pxReturn->ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ( StreamBuffer_t * ) ucStream );

    pxReturn = prvTCPCreateStream( &xSocket, xIsInputStream );

    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.uxLittleSpace );
    TEST_ASSERT_EQUAL( 0, xSocket.u.xTCP.uxEnoughSpace );
    TEST_ASSERT_EQUAL( ucStream, xSocket.u.xTCP.rxStream );
}

/**
 * @brief Low and high space fields non-zero.
 */
void test_prvTCPCreateStream_LowAndHighFieldsDefined( void )
{
    StreamBuffer_t * pxReturn;
    FreeRTOS_Socket_t xSocket;
    BaseType_t xIsInputStream = pdTRUE;
    uint8_t ucStream[ ipconfigTCP_MSS ];

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 20;
    xSocket.u.xTCP.uxLittleSpace = 3;
    xSocket.u.xTCP.uxEnoughSpace = 17;
    xSocket.u.xTCP.usMSS = 10;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( *pxReturn ) ) - sizeof( pxReturn->ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ( StreamBuffer_t * ) ucStream );

    pxReturn = prvTCPCreateStream( &xSocket, xIsInputStream );

    TEST_ASSERT_EQUAL( 3, xSocket.u.xTCP.uxLittleSpace );
    TEST_ASSERT_EQUAL( 17, xSocket.u.xTCP.uxEnoughSpace );
    TEST_ASSERT_EQUAL( ucStream, xSocket.u.xTCP.rxStream );
}

/**
 * @brief Failed to allocate the stream.
 */
void test_lTCPAddRxdata_StreamCannotBeAllocated( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount;
    StreamBuffer_t xStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 20;
    xSocket.u.xTCP.uxLittleSpace = 3;
    xSocket.u.xTCP.uxEnoughSpace = 17;
    xSocket.u.xTCP.usMSS = 10;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, NULL );

    vTCPStateChange_Expect( &xSocket, eCLOSE_WAIT );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( -1, lReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bMallocError );
}

/**
 * @brief Successfully added all bytes in the stream.
 */
void test_lTCPAddRxdata_SteamCreationSuccessful_AllBytesAdded( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 20;
    xSocket.u.xTCP.uxLittleSpace = 3;
    xSocket.u.xTCP.uxEnoughSpace = 17;
    xSocket.u.xTCP.usMSS = 10;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ( StreamBuffer_t * ) ucStream );

    uxStreamBufferAdd_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, uxOffset, pcData, ulByteCount, ulByteCount );

    uxStreamBufferFrontSpace_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 10 );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( eSOCKET_RECEIVE, xSocket.xEventBits );
}

/**
 * @brief Only able to add few bytes.
 */
void test_lTCPAddRxdata_SteamCreationSuccessful_AllBytesNotAdded( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 20;
    xSocket.u.xTCP.uxLittleSpace = 3;
    xSocket.u.xTCP.uxEnoughSpace = 17;
    xSocket.u.xTCP.usMSS = 10;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferAdd_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, uxOffset, pcData, ulByteCount, ulByteCount - 10 );

    uxStreamBufferFrontSpace_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 10 );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( eSOCKET_RECEIVE, xSocket.xEventBits );
}

/**
 * @brief Space in the front of the stream buffer is less than the low space value.
 */
void test_lTCPAddRxdata_FrontSpaceLessThanLowMark( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;
    xSocket.u.xTCP.usMSS = 10;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferAdd_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, uxOffset, pcData, ulByteCount, ulByteCount - 10 );

    uxStreamBufferFrontSpace_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 10 );

    xSendEventToIPTask_ExpectAndReturn( eTCPTimerEvent, pdPASS );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( eSOCKET_RECEIVE | ( eSELECT_READ << SOCKET_EVENT_BIT_COUNT ), xSocket.xEventBits );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdTRUE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 1U, xSocket.u.xTCP.usTimeout );
}

/**
 * @brief the low water bit is set.
 */
void test_lTCPAddRxdata_LowWaterTrue( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) ucStream;
    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;
    xSocket.u.xTCP.bits.bLowWater = pdTRUE;
    xSocket.u.xTCP.usMSS = 10;

    uxStreamBufferAdd_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, uxOffset, pcData, ulByteCount, ulByteCount - 10 );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( eSOCKET_RECEIVE | ( eSELECT_READ << SOCKET_EVENT_BIT_COUNT ), xSocket.xEventBits );
}

/**
 * @brief Receive callback is added.
 */
void test_lTCPAddRxdata_HasValidHandler( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    xLocalReceiveCallback_Called = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;
    xSocket.u.xTCP.pxHandleReceive = xLocalReceiveCallback;
    xSocket.u.xTCP.usMSS = 10;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferGetSize_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0U );

    uxStreamBufferAdd_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, uxOffset, NULL, ulByteCount, ulByteCount - 10 );

    uxStreamBufferGet_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0U, NULL, ulByteCount, pdFALSE, pdTRUE );

    uxStreamBufferGetPtr_ExpectAnyArgsAndReturn( 0U );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 0U, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( 1U, xLocalReceiveCallback_Called );
}

/**
 * @brief Call back added but the data to be added is NULL meaning peeking mode.
 */
void test_lTCPAddRxdata_HasValidHandler_DataNULL( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    xLocalReceiveCallback_Called = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;
    xSocket.u.xTCP.pxHandleReceive = xLocalReceiveCallback;
    xSocket.u.xTCP.usMSS = 10;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferGetSize_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0U );

    uxStreamBufferAdd_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, uxOffset, NULL, ulByteCount, ulByteCount - 10 );

    uxStreamBufferGetPtr_ExpectAnyArgsAndReturn( 0U );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, NULL, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 0U, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( 0U, xLocalReceiveCallback_Called );
}

/**
 * @brief Has a callback and the offset is non-zero unlike previous cases.
 */
void test_lTCPAddRxdata_HasValidHandler_NonZeroOffset( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 10;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    xLocalReceiveCallback_Called = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;
    xSocket.u.xTCP.pxHandleReceive = xLocalReceiveCallback;
    xSocket.u.xTCP.usMSS = 10;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferGetSize_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 0U );

    uxStreamBufferAdd_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, uxOffset, pcData, ulByteCount, ulByteCount - 10 );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 0U, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( 0U, xLocalReceiveCallback_Called );
}

/**
 * @brief Buffer size is non-zero.
 */
void test_lTCPAddRxdata_HasValidHandlerWithNonZeroSize( void )
{
    int32_t lReturn;
    FreeRTOS_Socket_t xSocket;
    size_t uxOffset = 0;
    uint8_t pcData[ 20 ];
    uint32_t ulByteCount = 120;
    uint8_t ucStream[ ipconfigTCP_MSS ];
    StreamBuffer_t xStreamBuffer;

    xLocalReceiveCallback_Called = 0;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.u.xTCP.uxRxStreamSize = 200;
    xSocket.u.xTCP.uxLittleSpace = 120;
    xSocket.u.xTCP.uxEnoughSpace = 200;
    xSocket.xSelectBits = eSELECT_READ;
    xSocket.u.xTCP.pxHandleReceive = xLocalReceiveCallback;
    xSocket.u.xTCP.usMSS = 10;

    size_t xSizeOfBufferRequested = ( ( ( sizeof( size_t ) + xSocket.u.xTCP.uxRxStreamSize ) & ( ~( sizeof( size_t ) - 1U ) ) ) + sizeof( xStreamBuffer ) ) - sizeof( xStreamBuffer.ucArray );

    pvPortMalloc_ExpectAndReturn( xSizeOfBufferRequested, ucStream );

    uxStreamBufferGetSize_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, 10U );

    uxStreamBufferAdd_ExpectAndReturn( ( StreamBuffer_t * ) ucStream, uxOffset, pcData, ulByteCount, ulByteCount - 10 );

    uxStreamBufferGetPtr_ExpectAnyArgsAndReturn( 0U );

    lReturn = lTCPAddRxdata( &xSocket, uxOffset, pcData, ulByteCount );

    TEST_ASSERT_EQUAL( ulByteCount - 10, lReturn );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bMallocError );
    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bLowWater );
    TEST_ASSERT_EQUAL( pdFALSE, xSocket.u.xTCP.bits.bWinChange );
    TEST_ASSERT_EQUAL( 0U, xSocket.u.xTCP.usTimeout );
    TEST_ASSERT_EQUAL( 0U, xLocalReceiveCallback_Called );
}

/**
 * @brief All combination of inputs. See below comments.
 */
void test_xSocketValid( void )
{
    BaseType_t xReturn;
    FreeRTOS_Socket_t xSocket;

    /* NULL Socket. */
    xReturn = xSocketValid( NULL );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    /* Invalid Socket. */
    xReturn = xSocketValid( ( FreeRTOS_Socket_t * ) FREERTOS_INVALID_SOCKET );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    /* Valid Socket. */
    xReturn = xSocketValid( &xSocket );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief This function just prints out some data. It is expected to make call to the
 *        below function. Nothing more.
 */
void test_FreeRTOS_netstat( void )
{
    xSendEventStructToIPTask_ExpectAndReturn( NULL, pdMS_TO_TICKS( 1000U ), pdPASS );
    xSendEventStructToIPTask_IgnoreArg_pxEvent();
    FreeRTOS_netstat();
}
