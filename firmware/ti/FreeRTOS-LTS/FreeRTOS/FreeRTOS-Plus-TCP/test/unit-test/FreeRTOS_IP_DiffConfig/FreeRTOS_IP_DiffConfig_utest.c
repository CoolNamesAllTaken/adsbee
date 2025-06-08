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
#include "mock_IP_DiffConfig_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_Stream_Buffer.h"

#include "FreeRTOS_IP.h"

#include "FreeRTOS_IP_DiffConfig_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer );
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

extern BaseType_t xIPTaskInitialised;
extern BaseType_t xNetworkDownEventPending;
extern BaseType_t xNetworkUp;
extern UBaseType_t uxQueueMinimumSpace;

/* ============================ Unity Fixtures ============================ */

/*! called before each test case */
void setUp( void )
{
    pxNetworkEndPoints = NULL;
    pxNetworkInterfaces = NULL;
    xNetworkDownEventPending = pdFALSE;
}

/*! called after each test case */
void tearDown( void )
{
}

/* ======================== Stub Callback Functions ========================= */

BaseType_t NetworkInterfaceOutputFunction_Stub_Called = 0;
BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    NetworkInterfaceOutputFunction_Stub_Called++;
    return 0;
}

static uint8_t ReleaseTCPPayloadBuffer[ 1500 ];
static BaseType_t ReleaseTCPPayloadBufferxByteCount = 100;
static size_t StubuxStreamBufferGetPtr_ReturnBadAddress( StreamBuffer_t * pxBuffer,
                                                         uint8_t ** ppucData,
                                                         int lCounter )
{
    *ppucData = &ReleaseTCPPayloadBuffer[ 150 ];

    return 0xFFFFFF;
}

static size_t StubuxStreamBufferGetPtr_ReturnIncorrectSize( StreamBuffer_t * pxBuffer,
                                                            uint8_t ** ppucData,
                                                            int lCounter )
{
    *ppucData = &ReleaseTCPPayloadBuffer[ 0 ];

    return( ReleaseTCPPayloadBufferxByteCount >> 1 );
}

static size_t StubuxStreamBufferGetPtr_ReturnCorrectVals( StreamBuffer_t * pxBuffer,
                                                          uint8_t ** ppucData,
                                                          int lCounter )
{
    *ppucData = &ReleaseTCPPayloadBuffer[ 0 ];

    return ReleaseTCPPayloadBufferxByteCount;
}

/* ============================== Test Cases ============================== */

/**
 * @brief test_prvProcessIPEventsAndTimers_NoEventReceived
 * To validate the flow of prvProcessIPEventsAndTimers() to handle eNoEvent.
 */
void test_prvProcessIPEventsAndTimers_NoEventReceived( void )
{
    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    /* No event received. */
    xQueueReceive_ExpectAnyArgsAndReturn( pdFALSE );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eNetworkRxEventNULL_LessSpace
 * To validate the flow of prvProcessIPEventsAndTimers() doesn't update
 * uxQueueMinimumSpace when uxQueueSpacesAvailable() returns more.
 */
void test_prvProcessIPEventsAndTimers_eNetworkRxEventNULL_LessSpace( void )
{
    IPStackEvent_t xReceivedEvent;
    BaseType_t xQueueReturn = 100;

    xReceivedEvent.eEventType = eNetworkRxEvent;
    xReceivedEvent.pvData = NULL;

    uxQueueMinimumSpace = xQueueReturn - 10;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( xQueueReturn - 10, uxQueueMinimumSpace );
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eNetworkRxEventNULL_LessSpace
 * To validate the flow of prvProcessIPEventsAndTimers() updates uxQueueMinimumSpace
 * when uxQueueSpacesAvailable() returns less.
 */
void test_prvProcessIPEventsAndTimers_eNetworkRxEvent_MoreSpace( void )
{
    IPStackEvent_t xReceivedEvent;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    BaseType_t xQueueReturn = 100;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t ) - 1;
    pxNetworkBuffer->pxNextBuffer = NULL;

    xReceivedEvent.eEventType = eNetworkRxEvent;
    xReceivedEvent.pvData = pxNetworkBuffer;

    uxQueueMinimumSpace = xQueueReturn + 10;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( xQueueReturn, uxQueueMinimumSpace );
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eSocketSelectEvent
 * To validate if prvProcessIPEventsAndTimers() calls xTaskNotifyGive (xTaskGenericNotify)
 * while handling eSocketSelectEvent.
 */
void test_prvProcessIPEventsAndTimers_eSocketSelectEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    SocketSelectMessage_t xData;
    BaseType_t xQueueReturn = 100;

    memset( &xData, 0, sizeof( xData ) );
    xData.pxSocketSet = ( void * ) 0xFFAABBCC;
    xData.xTaskhandle = ( void * ) 0xABCDABCD;

    xReceivedEvent.eEventType = eSocketSelectEvent;
    xReceivedEvent.pvData = ( void * ) &xData;

    vCheckNetworkTimers_Expect();

    xCalculateSleepTime_ExpectAndReturn( 0 );

    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    uxQueueSpacesAvailable_ExpectAnyArgsAndReturn( xQueueReturn );

    vSocketSelect_Expect( ( SocketSelect_t * ) 0xFFAABBCC );
    xTaskGenericNotify_ExpectAndReturn( ( TaskHandle_t ) 0xABCDABCD, 0, ( 0 ), eIncrement, NULL, pdPASS );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBufferAssert
 * The input buffer pointer must be obtained by calling FreeRTOS_recv() with the FREERTOS_ZERO_COPY flag.
 * Because configASSERT is disabled in this configuration, there is no assertion in this test case.
 */
void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBufferAssert( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xByteCount = 100, xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnBadAddress );

    xReturn = FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, xByteCount );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectSizeAssert
 * Because configASSERT is disabled in this configuration, there is no assertion
 * even though available buffer size is less than input length.
 */
void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectSizeAssert( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnIncorrectSize );

    xReturn = FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, ReleaseTCPPayloadBufferxByteCount );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBytesReleasedAssert
 * Because configASSERT is disabled in this configuration, there is no assertion
 * even though bytes released from FreeRTOS_recv() is different from request.
 */
void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBytesReleasedAssert( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnCorrectVals );

    FreeRTOS_recv_ExpectAndReturn( &xSocket, NULL, ReleaseTCPPayloadBufferxByteCount, FREERTOS_MSG_DONTWAIT, ( ReleaseTCPPayloadBufferxByteCount >> 1 ) );

    xReturn = FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, ReleaseTCPPayloadBufferxByteCount );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_FreeRTOS_ReleaseTCPPayloadBuffer_HappyPath
 * To validate happy path for FreeRTOS_ReleaseTCPPayloadBuffer.
 */
void test_FreeRTOS_ReleaseTCPPayloadBuffer_HappyPath( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xReturn;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnCorrectVals );

    FreeRTOS_recv_ExpectAndReturn( &xSocket, NULL, ReleaseTCPPayloadBufferxByteCount, FREERTOS_MSG_DONTWAIT, ReleaseTCPPayloadBufferxByteCount );

    xReturn = FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, ReleaseTCPPayloadBufferxByteCount );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_vReturnEthernetFrame_DuplicationFailed
 * To validate if vReturnEthernetFrame is able to handle NULL network buffer descriptor.
 */
void test_vReturnEthernetFrame_DuplicationFailed( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdFALSE;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    xNetworkBuffer.xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;

    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( &xNetworkBuffer, xNetworkBuffer.xDataLength, NULL );

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxEndPoint );

    vReturnEthernetFrame( &xNetworkBuffer, xReleaseAfterSend );
}

/**
 * @brief test_vReturnEthernetFrame_DuplicationSuccess
 * To validate if vReturnEthernetFrame is able to handle duplicate network buffer descriptor.
 */
void test_vReturnEthernetFrame_DuplicationSuccess( void )
{
    NetworkBufferDescriptor_t xDuplicateNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdFALSE;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xDuplicateNetworkBuffer, 0, sizeof( xDuplicateNetworkBuffer ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    xDuplicateNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    memcpy( pxEndPoint->xMACAddress.ucBytes, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.pxNetworkInterface = &xInterfaces[ 0 ];
    xInterfaces->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    ( ( ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer ) )->usFrameType = ipIPv4_FRAME_TYPE;

    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( &xNetworkBuffer, xNetworkBuffer.xDataLength, &xDuplicateNetworkBuffer );

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxEndPoint );

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, xDuplicateNetworkBuffer.xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( xDefault_MacAddress.ucBytes, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
}

/**
 * @brief test_vReturnEthernetFrame_DuplicationSuccess
 * To validate if vReturnEthernetFrame is able to handle duplicate network buffer descriptor with cache hit.
 */
void test_vReturnEthernetFrame_DuplicationSuccessCacheHit( void )
{
    NetworkBufferDescriptor_t xDuplicateNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdFALSE;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    MACAddress_t xCacheMACAddress = { { 0x11, 0x22, 0x33, 0x44, 0x55, 0x66 } };

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xDuplicateNetworkBuffer, 0, sizeof( xDuplicateNetworkBuffer ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    xDuplicateNetworkBuffer.pucEthernetBuffer = ucEthBuffer;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    memcpy( pxEndPoint->xMACAddress.ucBytes, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.pxNetworkInterface = &xInterfaces[ 0 ];
    xInterfaces->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    ( ( ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer ) )->usFrameType = ipIPv4_FRAME_TYPE;

    pxDuplicateNetworkBufferWithDescriptor_ExpectAndReturn( &xNetworkBuffer, xNetworkBuffer.xDataLength, &xDuplicateNetworkBuffer );

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxEndPoint );

    eARPGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    eARPGetCacheEntry_ReturnMemThruPtr_pxMACAddress( &xCacheMACAddress, sizeof( MACAddress_t ) );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL( xNetworkBuffer.xDataLength, xDuplicateNetworkBuffer.xDataLength );
    TEST_ASSERT_EQUAL_MEMORY( xCacheMACAddress.ucBytes, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( xDefault_MacAddress.ucBytes, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
}

/**
 * @brief test_vReturnEthernetFrame_xReleaseAfterSend
 * To validate if vReturnEthernetFrame is able to send with input network buffer descriptor.
 */
void test_vReturnEthernetFrame_xReleaseAfterSend( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdTRUE;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );
    memcpy( pxEndPoint->xMACAddress.ucBytes, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.pxNetworkInterface = &xInterfaces[ 0 ];
    xInterfaces->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxEndPoint );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( xDefault_MacAddress.ucBytes, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
}

/**
 * @brief test_vReturnEthernetFrame_DataLenMoreThanRequired
 * To validate if vReturnEthernetFrame changes the source/destination MAC addresses correctly
 * and transmits though network interface. And the buffer length is equal to ipconfigETHERNET_MINIMUM_PACKET_BYTES.
 */
void test_vReturnEthernetFrame_DataLenMoreThanRequired( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdTRUE;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );
    memcpy( pxEndPoint->xMACAddress.ucBytes, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.pxNetworkInterface = &xInterfaces[ 0 ];
    xInterfaces->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxEndPoint );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAA, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( xDefault_MacAddress.ucBytes, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
}

/**
 * @brief test_uxGetMinimumIPQueueSpace
 * To validate if uxGetMinimumIPQueueSpace returns correct minimum queue space.
 */
void test_uxGetMinimumIPQueueSpace( void )
{
    UBaseType_t uxReturn;

    uxQueueMinimumSpace = 10;

    uxReturn = uxGetMinimumIPQueueSpace();

    TEST_ASSERT_EQUAL( 10, uxReturn );
}
