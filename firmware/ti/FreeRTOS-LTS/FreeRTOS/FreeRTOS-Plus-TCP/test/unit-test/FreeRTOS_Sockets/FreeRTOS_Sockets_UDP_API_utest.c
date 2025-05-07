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
#include "mock_FreeRTOS_IPv4_Sockets.h"
#include "mock_FreeRTOS_IPv6_Sockets.h"

#include "FreeRTOS_Sockets.h"

#include "FreeRTOS_Sockets_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

#define TEST_MAX_UDPV4_PAYLOAD_LENGTH    ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER )
#define TEST_MAX_UDPV6_PAYLOAD_LENGTH    ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv6_HEADER + ipSIZE_OF_UDP_HEADER )

/* ============================== Test Cases ============================== */

/**
 * @brief NULL socket.
 */
void test_FreeRTOS_recvfrom_NullSocket( void )
{
    int32_t lReturn;
    Socket_t xSocket = NULL;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, lReturn );
}

/**
 * @brief Receiving from a TCP socket (while a UDP socket should be called).
 */
void test_FreeRTOS_recvfrom_TCPSocket( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress = NULL;
    socklen_t * pxSourceAddressLength = NULL;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_TCP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, lReturn );
}

/**
 * @brief Call to the function is interrupted.
 */
void test_FreeRTOS_recvfrom_NonBlockingInterrupted( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0, eSOCKET_INTR );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINTR, lReturn );
}

/**
 * @brief Non blocking call which will block.
 */
void test_FreeRTOS_recvfrom_NonBlocking( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( EventBits_t ) eSOCKET_INTR, pdTRUE, pdFALSE, 0, ~eSOCKET_INTR );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EWOULDBLOCK, lReturn );
}

/**
 * @brief Non-blocking flag set but nothing received by the socket yet.
 */
void test_FreeRTOS_recvfrom_NonBlockingFlagSet( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = FREERTOS_MSG_DONTWAIT;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EWOULDBLOCK, lReturn );
}

/**
 * @brief Blocking read times out.
 */
void test_FreeRTOS_recvfrom_BlockingButTimeout( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EWOULDBLOCK, lReturn );
}

/**
 * @brief Blocking read - timeout in second iteration.
 */
void test_FreeRTOS_recvfrom_BlockingButTimeoutSecondTime( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EWOULDBLOCK, lReturn );
}

/**
 * @brief Blocking read interrupted.
 */
void test_FreeRTOS_recvfrom_BlockingButInterrupted( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, eSOCKET_INTR );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINTR, lReturn );
}

/**
 * @brief Blocking read interrupted and received.
 */
void test_FreeRTOS_recvfrom_BlockingButInterruptedAndReceived( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    void * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr * pxSourceAddress;
    socklen_t * pxSourceAddressLength;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );
    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, eSOCKET_INTR | eSOCKET_RECEIVE );

    xEventGroupSetBits_ExpectAndReturn( xSocket->xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE, pdFALSE );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, pxSourceAddress, pxSourceAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINTR, lReturn );
}

/**
 * @brief Blocking read socket gets a packet while it is waiting. However, the packet
 *        is only a UDP header.
 */
void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_JustUDPHeader( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = ipconfigTCP_MSS;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xSourceAddress;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t );
    xNetworkBuffer.xIPAddress.ulIP_IPv4 = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;
    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    vTaskSuspendAll_Expect();

    {
        listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

        uxListRemove_ExpectAndReturn( &( xNetworkBuffer.xBufferListItem ), 0 );
    }
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    xRecv_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xSourceAddress, ipUDP_PAYLOAD_OFFSET_IPv4 );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, &xSourceAddress, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 0, lReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, pvBuffer, ipconfigTCP_MSS );
}

/**
 * @brief Blocking read socket gets a packet while it is waiting. However, the packet
 *        is UDP header and 100 bytes.
 */
void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_Packet100( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = ipconfigTCP_MSS;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xSourceAddress;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.xIPAddress.ulIP_IPv4 = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    vTaskSuspendAll_Expect();
    {
        listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

        uxListRemove_ExpectAndReturn( &( xNetworkBuffer.xBufferListItem ), 0 );
    }
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    xRecv_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xSourceAddress, ipUDP_PAYLOAD_OFFSET_IPv4 );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, &xSourceAddress, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 100, lReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, 100 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, &pvBuffer[ 100 ], ipconfigTCP_MSS - 100 );
}

/**
 * @brief Blocking read socket gets a packet while it is waiting. However, the packet
 *        is UDP header and 100 bytes.
 */
void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_Packet100SizeSmall( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = 50;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xSourceAddress;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.xIPAddress.ulIP_IPv4 = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    vTaskSuspendAll_Expect();
    {
        listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

        uxListRemove_ExpectAndReturn( &( xNetworkBuffer.xBufferListItem ), 0 );
    }
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    xRecv_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xSourceAddress, ipUDP_PAYLOAD_OFFSET_IPv4 );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, &xSourceAddress, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 50, lReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, uxBufferLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, &pvBuffer[ uxBufferLength ], ipconfigTCP_MSS - uxBufferLength );
}

/**
 * @brief Blocking read socket gets a packet while it is waiting. The packet
 *        is UDP header and 100 bytes. But the buffer is small and the receive
 *        call is used to peek in the list.
 */
void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_Packet100SizeSmall_Peek( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = 50;
    BaseType_t xFlags = FREERTOS_MSG_PEEK;
    struct freertos_sockaddr xSourceAddress;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.xIPAddress.ulIP_IPv4 = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    vTaskSuspendAll_Expect();

    {
        listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );
    }

    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    xRecv_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xSourceAddress, ipUDP_PAYLOAD_OFFSET_IPv4 );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, &xSourceAddress, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 50, lReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, uxBufferLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, &pvBuffer[ uxBufferLength ], ipconfigTCP_MSS - uxBufferLength );
}

/**
 * @brief Blocking read socket gets a packet while it is waiting. The packet
 *        is UDP header and 100 bytes. But the buffer is small and the receive
 *        call is used to peek in the list. The source address param passed is NULL.
 */
void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_Packet100SizeSmall_Peek_SourceAddrNULL( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = 50;
    BaseType_t xFlags = FREERTOS_MSG_PEEK;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.xIPAddress.ulIP_IPv4 = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    vTaskSuspendAll_Expect();

    {
        listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );
    }
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    xRecv_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, NULL, ipUDP_PAYLOAD_OFFSET_IPv4 );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, NULL, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 50, lReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, uxBufferLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, &pvBuffer[ uxBufferLength ], ipconfigTCP_MSS - uxBufferLength );
}

/**
 * @brief Blocking read socket gets a packet while it is waiting. The packet
 *        is UDP header and 100 bytes. But the buffer is small and the receive
 *        call is used to peek in the list with zero copy flag.
 */
void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_Packet100SizeSmall_ZeroCopyAndPeek( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    char * pvBuffer;
    size_t uxBufferLength = 50;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.xIPAddress.ulIP_IPv4 = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    vTaskSuspendAll_Expect();

    {
        listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

        uxListRemove_ExpectAndReturn( &xNetworkBuffer.xBufferListItem, 0U );
    }

    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    xRecv_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, NULL, ipUDP_PAYLOAD_OFFSET_IPv4 );

    lReturn = FreeRTOS_recvfrom( xSocket, &pvBuffer, uxBufferLength, xFlags, NULL, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 100, lReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, 100 );
}

/**
 * @brief Blocking read socket gets a packet as soon as the function is called. The packet
 *        is UDP header and 100 bytes. But the buffer is small and the receive
 *        call is used to peek in the list.
 */
void test_FreeRTOS_recvfrom_BlockingGetsPacketInBegining_Packet100SizeSmall_ZeroCopyAndPeek( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    char * pvBuffer;
    size_t uxBufferLength = 50;
    BaseType_t xFlags = FREERTOS_MSG_PEEK | FREERTOS_ZERO_COPY;
    socklen_t xSourceAddressLength;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_t ) + 100;
    xNetworkBuffer.xIPAddress.ulIP_IPv4 = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    xListItem.pvOwner = &xNetworkBuffer;
    xSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSuspendAll_Expect();
    {
        listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );
    }
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    xRecv_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, NULL, ipUDP_PAYLOAD_OFFSET_IPv4 );

    lReturn = FreeRTOS_recvfrom( xSocket, &pvBuffer, uxBufferLength, xFlags, NULL, &xSourceAddressLength );

    TEST_ASSERT_EQUAL( 100, lReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, 100 );
}

/**
 * @brief Blocking read socket gets a packet while it is waiting. However, the packet
 *        is UDPv6 header and 100 bytes.
 */
void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_IPv6Packet100( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = ipconfigTCP_MSS;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xSourceAddress;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_IPv6_t ) + 100;
    xNetworkBuffer.xIPAddress.ulIP_IPv4 = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    vTaskSuspendAll_Expect();
    {
        listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

        uxListRemove_ExpectAndReturn( &( xNetworkBuffer.xBufferListItem ), 0 );
    }
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv6_HEADER );

    xRecv_Update_IPv6_ExpectAndReturn( &xNetworkBuffer, &xSourceAddress, ipUDP_PAYLOAD_OFFSET_IPv6 );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, &xSourceAddress, NULL );

    TEST_ASSERT_EQUAL( 100, lReturn );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pucEthernetBuffer, ipconfigTCP_MSS );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x12, pvBuffer, 100 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, &pvBuffer[ 100 ], ipconfigTCP_MSS - 100 );
}

/**
 * @brief Blocking read socket gets a packet while it is waiting. However, the packet
 *        is UDPv6 header and 100 bytes.
 */
void test_FreeRTOS_recvfrom_BlockingGetsPacketInBetween_UnknownIPHeaderSize( void )
{
    int32_t lReturn;
    uint8_t ucSocket[ sizeof( FreeRTOS_Socket_t ) ];
    Socket_t xSocket = ( Socket_t ) ucSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = ipconfigTCP_MSS;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;
    struct freertos_sockaddr xSourceAddress;
    ListItem_t xListItem;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( UDPPacket_IPv6_t ) + 100;
    xNetworkBuffer.xIPAddress.ulIP_IPv4 = 0x1234ABCD;
    xNetworkBuffer.usPort = 0xABCD;

    memset( xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( &xListItem, 0, sizeof( ListItem_t ) );
    memset( pucEthernetBuffer, 0x12, ipconfigTCP_MSS );
    memset( pvBuffer, 0xAB, ipconfigTCP_MSS );

    xSocket->ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket->xReceiveBlockTime = 0x123;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket->xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0 );

    xListItem.pvOwner = &xNetworkBuffer;
    xSocket->u.xUDP.xWaitingPacketsList.xListEnd.pxNext = &xListItem;

    vTaskSetTimeOutState_ExpectAnyArgs();

    xEventGroupWaitBits_ExpectAndReturn( xSocket->xEventGroup, ( ( EventBits_t ) eSOCKET_RECEIVE ) | ( ( EventBits_t ) eSOCKET_INTR ), pdTRUE, pdFALSE, xSocket->xReceiveBlockTime, 0 );

    listCURRENT_LIST_LENGTH_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), 0x12 );

    vTaskSuspendAll_Expect();
    {
        listGET_OWNER_OF_HEAD_ENTRY_ExpectAndReturn( &( xSocket->u.xUDP.xWaitingPacketsList ), &xNetworkBuffer );

        uxListRemove_ExpectAndReturn( &( xNetworkBuffer.xBufferListItem ), 0 );
    }
    xTaskResumeAll_ExpectAndReturn( pdFALSE );

    uxIPHeaderSizePacket_IgnoreAndReturn( 0xFF );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    lReturn = FreeRTOS_recvfrom( xSocket, pvBuffer, uxBufferLength, xFlags, &xSourceAddress, NULL );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, lReturn );
}

/**
 * @brief Assert to catch sending buffer is NULL.
 */
void test_FreeRTOS_sendto_CatchAssert( void )
{
    int32_t lResult;
    Socket_t xSocket;
    char * pvBuffer = NULL;
    size_t uxTotalDataLength = 0;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;

    catch_assert( FreeRTOS_sendto( xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength ) );
}

/**
 * @brief Assert to catch destination address is NULL.
 */
void test_FreeRTOS_sendto_CatchAssertNullDest( void )
{
    int32_t lResult;
    Socket_t xSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxTotalDataLength = 0;
    BaseType_t xFlags = 0;
    socklen_t xDestinationAddressLength;

    catch_assert( FreeRTOS_sendto( xSocket, pvBuffer, uxTotalDataLength, xFlags, NULL, xDestinationAddressLength ) );
}

/**
 * @brief Sending more than maximum allowed data in one go.
 */
void test_FreeRTOS_sendto_MoreDataThanUDPPayload( void )
{
    int32_t lResult;
    Socket_t xSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH + 1;
    BaseType_t xFlags;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;

    lResult = FreeRTOS_sendto( xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
}

/**
 * @brief Trying to send with a TCP socket.
 */
void test_FreeRTOS_sendto_TCPSocket( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH;
    BaseType_t xFlags;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;
    xSocket.ucProtocol = FREERTOS_IPPROTO_TCP;

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
}

/**
 * @brief Sending from IP task when a buffer cannot be allocated.
 */
void test_FreeRTOS_sendto_IPTaskCalling_NoNetworkBuffer( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
}

/**
 * @brief Sending from IP task without using zero copy.
 */
void test_FreeRTOS_sendto_IPTaskCalling_NonZeroCopy( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    memset( pucEthernetBuffer, 0, TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv4, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xSend_UDP_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xDestinationAddress, NULL );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( TEST_MAX_UDPV4_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
}

/**
 * @brief Sending from IP task without using zero copy.
 */
void test_FreeRTOS_sendto_IPTaskCalling_NonZeroCopy1( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    memset( pucEthernetBuffer, 0, TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv4, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xSend_UDP_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xDestinationAddress, NULL );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( TEST_MAX_UDPV4_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
}

/**
 * @brief Sending from IP task without using zero copy.
 */
void test_FreeRTOS_sendto_IPTaskCalling_NonZeroCopy2( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_MSG_DONTWAIT;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    memset( pucEthernetBuffer, 0, TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv4, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xSend_UDP_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xDestinationAddress, NULL );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( TEST_MAX_UDPV4_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
}

/**
 * @brief Sending from IP task without using zero copy. Checks if xIsCallingFromIPTask
 * gets called if xFlags's FREERTOS_MSG_DONTWAIT bit is unset.
 */
void test_FreeRTOS_sendto_IPTaskCalling_NonZeroCopy2_xFlagZero( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    memset( pucEthernetBuffer, 0, TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv4, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdTRUE );

    xSend_UDP_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xDestinationAddress, NULL );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( TEST_MAX_UDPV4_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
}

/**
 * @brief Sending from IP task without using zero copy.
 */
void test_FreeRTOS_sendto_IPTaskCalling_NonZeroCopy3( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_MSG_DONTWAIT;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    memset( pucEthernetBuffer, 0, TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv4, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xSend_UDP_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xDestinationAddress, NULL );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( TEST_MAX_UDPV4_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
}

/**
 * @brief  Sending from IP task with zero copy.
 */
void test_FreeRTOS_sendto_IPTaskCalling_ZeroCopy( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    memset( pucEthernetBuffer, 0, TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pvBuffer, &xNetworkBuffer );

    xSend_UDP_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xDestinationAddress, NULL );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( TEST_MAX_UDPV4_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
}

static uint32_t ulCalled = 0;
static void xLocalFunctionPointer( Socket_t xSocket,
                                   size_t xLength )
{
    ulCalled++;
}

/**
 * @brief Sending from IP task with zero copy. A valid callback function pointer is added.
 */
void test_FreeRTOS_sendto_IPTaskCalling_ZeroCopy_ValidFunctionPointer( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    ulCalled = 0;

    memset( pucEthernetBuffer, 0, TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = xLocalFunctionPointer;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pvBuffer, &xNetworkBuffer );

    xSend_UDP_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xDestinationAddress, NULL );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( TEST_MAX_UDPV4_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
    TEST_ASSERT_EQUAL( 1, ulCalled );
}

/**
 * @brief Sending from IP task with zero copy.Sending message to IP task fails.
 */
void test_FreeRTOS_sendto_IPTaskCalling_ZeroCopy_SendingToIPTaskFails( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_ZERO_COPY;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    ulCalled = 0;

    memset( pucEthernetBuffer, 0, TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = xLocalFunctionPointer;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pvBuffer, &xNetworkBuffer );

    xSend_UDP_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xDestinationAddress, NULL );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
    TEST_ASSERT_EQUAL( 0, ulCalled );
}

/**
 * @brief Sending from IP task without zero copy. Sending message to IP task fails.
 */
void test_FreeRTOS_sendto_IPTaskCalling_NonZeroCopy_SendingToIPTaskFails( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH;
    BaseType_t xFlags = 0;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 ];

    ulCalled = 0;

    memset( pucEthernetBuffer, 0, TEST_MAX_UDPV4_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv4 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = xLocalFunctionPointer;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv4, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xSend_UDP_Update_IPv4_ExpectAndReturn( &xNetworkBuffer, &xDestinationAddress, NULL );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdFAIL );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
    TEST_ASSERT_EQUAL( 0, ulCalled );
}

/**
 * @brief Sending an IPv6 packet from IP task without using zero copy.
 */
void test_FreeRTOS_sendto_IPTaskCalling_IPv6NonZeroCopy( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV6_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV6_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_MSG_DONTWAIT;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ TEST_MAX_UDPV6_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv6 ];

    memset( pucEthernetBuffer, 0, TEST_MAX_UDPV6_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv6 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xDestinationAddress.sin_family = FREERTOS_AF_INET6;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    listLIST_ITEM_CONTAINER_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), ( struct xLIST * ) ( uintptr_t ) 0x11223344 );

    vTaskSetTimeOutState_ExpectAnyArgs();

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxTotalDataLength + ipUDP_PAYLOAD_OFFSET_IPv6, 0, &xNetworkBuffer );

    xTaskCheckForTimeOut_ExpectAnyArgsAndReturn( pdFALSE );

    xSend_UDP_Update_IPv6_ExpectAndReturn( &xNetworkBuffer, &xDestinationAddress, NULL );

    listGET_LIST_ITEM_VALUE_ExpectAndReturn( &( xSocket.xBoundSocketListItem ), 0xAADF );

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( pdPASS );

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( TEST_MAX_UDPV6_PAYLOAD_LENGTH, lResult );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, uxTotalDataLength + sizeof( UDPPacket_IPv6_t ) );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usPort, xDestinationAddress.sin_port );
    TEST_ASSERT_EQUAL( xNetworkBuffer.usBoundPort, 0xAADF );
}

/**
 * @brief Sending an packet with unknown family.
 */
void test_FreeRTOS_sendto_UnknownDestinationFamily( void )
{
    int32_t lResult;
    FreeRTOS_Socket_t xSocket;
    char pvBuffer[ TEST_MAX_UDPV6_PAYLOAD_LENGTH ];
    size_t uxTotalDataLength = TEST_MAX_UDPV6_PAYLOAD_LENGTH;
    BaseType_t xFlags = FREERTOS_MSG_DONTWAIT;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ TEST_MAX_UDPV6_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv6 ];

    memset( pucEthernetBuffer, 0, TEST_MAX_UDPV6_PAYLOAD_LENGTH + ipUDP_PAYLOAD_OFFSET_IPv6 );
    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xNetworkBuffer, 0, sizeof( xNetworkBuffer ) );

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;

    xDestinationAddress.sin_family = 0xFF;
    xSocket.ucProtocol = FREERTOS_IPPROTO_UDP;
    xSocket.u.xUDP.pxHandleSent = NULL;

    lResult = FreeRTOS_sendto( &xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, lResult );
}
