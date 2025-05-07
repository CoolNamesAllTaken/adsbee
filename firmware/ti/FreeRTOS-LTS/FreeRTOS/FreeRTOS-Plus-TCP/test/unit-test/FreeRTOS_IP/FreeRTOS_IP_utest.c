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
#include "mock_IP_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_FreeRTOS_Stream_Buffer.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IPv4_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_IPv6_Utils.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_TCP_IP.h"
#include "mock_FreeRTOS_ICMP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_DNS_Cache.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_ND.h"
#include "mock_FreeRTOS_IPv6.h"
#include "mock_FreeRTOS_IPv4.h"

#include "FreeRTOS_IP.h"

#include "FreeRTOS_IP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

extern NetworkInterface_t xInterfaces[ 1 ];
extern BaseType_t xIPTaskInitialised;
extern BaseType_t xNetworkDownEventPending;

void prvIPTask( void * pvParameters );
void prvProcessIPEventsAndTimers( void );
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket,
                                             NetworkBufferDescriptor_t * const pxNetworkBuffer );
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

static BaseType_t NetworkInterfaceOutputFunction_Stub_Called = 0;

/* First IPv6 address is 2001:1234:5678::5 */
const IPv6_Address_t xIPAddressFive = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05 };

/* Second IPv6 address is 2001:1234:5678::10 */
const IPv6_Address_t xIPAddressTen = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10 };

/* MAC Address for endpoint. */
const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };

/* This variable will be set when pfAddAllowedMAC() is called by vIPNetworkUpCalls(). */
static BaseType_t xMACFunctionCalled;

/* An implementation of pfAddAllowedMAC(). */
static void pfAddAllowedMAC( struct xNetworkInterface * pxInterface,
                             const uint8_t * pucMacAddress );

/* Testing all situations for vIPNetworkUpCalls() to increase coverage. */
#define ipHAS_METHOD       0x01U
#define ipHAS_INTERFACE    0x02U
#define ipHAS_IPV6         0x04U

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

static BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
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
 * @brief test_vIPNetworkUpCalls
 * To validate if vIPNetworkUpCalls calls corresponding APIs.
 */
void test_vIPNetworkUpCalls( void )
{
    NetworkEndPoint_t xEndPoint = { 0 };

    xEndPoint.bits.bEndPointUp = pdFALSE;
    xEndPoint.bits.bIPv6 = pdFALSE;

    vApplicationIPNetworkEventHook_Multi_Expect( eNetworkUp, &xEndPoint );
    vDNSInitialise_Expect();
    vARPTimerReload_Expect( pdMS_TO_TICKS( 10000 ) );

    vIPNetworkUpCalls( &xEndPoint );

    TEST_ASSERT_EQUAL( pdTRUE, xEndPoint.bits.bEndPointUp );
}

/**
 * @brief test_FreeRTOS_NetworkDown_SendToIPTaskSuccessful
 * To validate if FreeRTOS_NetworkDown calls queue send when it's called from IP task.
 */
void test_FreeRTOS_NetworkDown_SendToIPTaskSuccessful( void )
{
    struct xNetworkInterface xNetworkInterface;

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xQueueGenericSend_ExpectAnyArgsAndReturn( pdPASS );

    FreeRTOS_NetworkDown( &xNetworkInterface );

    TEST_ASSERT_EQUAL( pdFALSE, xIsNetworkDownEventPending() );
}

/**
 * @brief test_FreeRTOS_NetworkDown_SendToIPTaskNotSuccessful
 * To validate if FreeRTOS_NetworkDown set network down event correctly when queue send failed.
 */
void test_FreeRTOS_NetworkDown_SendToIPTaskNotSuccessful( void )
{
    struct xNetworkInterface xNetworkInterface;

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    xQueueGenericSend_ExpectAnyArgsAndReturn( pdFAIL );

    FreeRTOS_NetworkDown( &xNetworkInterface );

    TEST_ASSERT_EQUAL( pdTRUE, xIsNetworkDownEventPending() );
}

/**
 * @brief test_FreeRTOS_NetworkDownFromISR_SendToIPTaskSuccessful
 * FreeRTOS_NetworkDownFromISR sends by xQueueGenericSendFromISR and return value is true.
 */
void test_FreeRTOS_NetworkDownFromISR_SendToIPTaskSuccessful( void )
{
    BaseType_t xHasPriorityTaskAwoken = pdTRUE;
    BaseType_t xReturn;
    struct xNetworkInterface xNetworkInterface;

    xQueueGenericSendFromISR_ExpectAnyArgsAndReturn( pdPASS );
    xQueueGenericSendFromISR_ReturnThruPtr_pxHigherPriorityTaskWoken( &xHasPriorityTaskAwoken );

    xReturn = FreeRTOS_NetworkDownFromISR( &xNetworkInterface );

    TEST_ASSERT_EQUAL( pdFALSE, xIsNetworkDownEventPending() );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_FreeRTOS_NetworkDownFromISR_SendToIPTaskUnsuccessful
 * To validate if FreeRTOS_NetworkDownFromISR set network down event correct when send queue failed.
 */
void test_FreeRTOS_NetworkDownFromISR_SendToIPTaskUnsuccessful( void )
{
    BaseType_t xHasPriorityTaskAwoken = pdFALSE;
    BaseType_t xReturn;
    struct xNetworkInterface xNetworkInterface;

    xQueueGenericSendFromISR_ExpectAnyArgsAndReturn( pdFAIL );
    xQueueGenericSendFromISR_ReturnThruPtr_pxHigherPriorityTaskWoken( &xHasPriorityTaskAwoken );

    xReturn = FreeRTOS_NetworkDownFromISR( &xNetworkInterface );

    TEST_ASSERT_EQUAL( pdTRUE, xIsNetworkDownEventPending() );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeEqualToConfig
 * To validate if FreeRTOS_GetUDPPayloadBuffer_Multi can return correct network buffer with maximum block time.
 */
void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeEqualToConfig( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS;
    void * pvReturn;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t pucEthernetBuffer[ 1500 ];

    /* Put the ethernet buffer in place. */
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, uxBlockTimeTicks, pxNetworkBuffer );

    pvReturn = FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, ipTYPE_IPv4 );

    TEST_ASSERT_EQUAL( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL_PTR( &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_t ) ] ), pvReturn );
}

/**
 * @brief test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeLessThanConfig
 * To validate if FreeRTOS_GetUDPPayloadBuffer_Multi can return correct network buffer with maximum block time - 1.
 */
void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeLessThanConfig( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS - 1;
    void * pvReturn;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t pucEthernetBuffer[ 1500 ];

    /* Put the ethernet buffer in place. */
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, uxBlockTimeTicks, pxNetworkBuffer );

    pvReturn = FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, ipTYPE_IPv4 );

    TEST_ASSERT_EQUAL( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL_PTR( &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_t ) ] ), pvReturn );
}

/**
 * @brief test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeMoreThanConfig
 * To validate if FreeRTOS_GetUDPPayloadBuffer_Multi can return correct network buffer with maximum block time + 1.
 * And the block time is reduced to maximum block time.
 */
void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeMoreThanConfig( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS + 1;
    void * pvReturn;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t pucEthernetBuffer[ 1500 ];

    /* Put the ethernet buffer in place. */
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS, pxNetworkBuffer );

    pvReturn = FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, ipTYPE_IPv4 );

    TEST_ASSERT_EQUAL( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL_PTR( &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_t ) ] ), pvReturn );
}

/**
 * @brief test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeMoreThanConfig_NULLBufferReturned
 * To validate if FreeRTOS_GetUDPPayloadBuffer_Multi can return NULL when pxGetNetworkBufferWithDescriptor returns NULL.
 */
void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeMoreThanConfig_NULLBufferReturned( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS + 1;
    void * pvReturn;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS, NULL );

    pvReturn = FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, ipTYPE_IPv4 );

    TEST_ASSERT_NULL( pvReturn );
}

/**
 * @brief test_FreeRTOS_GetUDPPayloadBuffer_UnknownType
 * To validate if FreeRTOS_GetUDPPayloadBuffer_Multi can trigger assertion when the input type is neither IPv4 nor IPv6.
 */
void test_FreeRTOS_GetUDPPayloadBuffer_UnknownType( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS;

    /* An assert is expected and caught with the macro catch_assert. */
    catch_assert( FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, 0xFF ) );
}

/**
 * @brief test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeEqualToConfig_IPv6
 * To validate if FreeRTOS_GetUDPPayloadBuffer_Multi can return correct network buffer for IPv6.
 */
void test_FreeRTOS_GetUDPPayloadBuffer_BlockTimeEqualToConfig_IPv6( void )
{
    size_t uxRequestedSizeBytes = 300;
    TickType_t uxBlockTimeTicks = ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS;
    void * pvReturn;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t pucEthernetBuffer[ 1500 ];

    /* Put the ethernet buffer in place. */
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;
    pxNetworkBuffer->xDataLength = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( sizeof( UDPPacket_IPv6_t ) + uxRequestedSizeBytes, uxBlockTimeTicks, pxNetworkBuffer );

    pvReturn = FreeRTOS_GetUDPPayloadBuffer_Multi( uxRequestedSizeBytes, uxBlockTimeTicks, ipTYPE_IPv6 );

    TEST_ASSERT_EQUAL( sizeof( UDPPacket_IPv6_t ) + uxRequestedSizeBytes, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL_PTR( &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( UDPPacket_IPv6_t ) ] ), pvReturn );
}

/**
 * @brief test_FreeRTOS_ReleaseUDPPayloadBuffer
 * To validate if FreeRTOS_ReleaseUDPPayloadBuffer release the correct pointer of buffer.
 */
void test_FreeRTOS_ReleaseUDPPayloadBuffer( void )
{
    void * pvBuffer = ( void * ) 0xFFCDEA;

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( pvBuffer, ( NetworkBufferDescriptor_t * ) 0x12123434 );
    vReleaseNetworkBufferAndDescriptor_Expect( ( NetworkBufferDescriptor_t * ) 0x12123434 );

    FreeRTOS_ReleaseUDPPayloadBuffer( pvBuffer );
}

/**
 * @brief test_FreeRTOS_ReleaseUDPPayloadBuffer_NullNetworkDescriptor
 * To validate if FreeRTOS_ReleaseUDPPayloadBuffer triggers assertion when network descriptor is NULL.
 */
void test_FreeRTOS_ReleaseUDPPayloadBuffer_NullNetworkDescriptor( void )
{
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAndReturn( NULL, ( NetworkBufferDescriptor_t * ) NULL );

    catch_assert( FreeRTOS_ReleaseUDPPayloadBuffer( NULL ) );
}

/**
 * @brief test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBufferAssert
 * The input buffer pointer must be obtained by calling FreeRTOS_recv() with the FREERTOS_ZERO_COPY flag.
 * Trigger assertion if the input buffer pointer is different from pointer returned from stream buffer API.
 */
void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBufferAssert( void )
{
    FreeRTOS_Socket_t xSocket;
    BaseType_t xByteCount = 100;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnBadAddress );

    catch_assert( FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, xByteCount ) );
}

/**
 * @brief test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectSizeAssert
 * To validate if FreeRTOS_ReleaseTCPPayloadBuffer triggers assertion when available buffer size
 * is less than input length.
 */
void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectSizeAssert( void )
{
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnIncorrectSize );

    catch_assert( FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, ReleaseTCPPayloadBufferxByteCount ) );
}

/**
 * @brief test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBytesReleasedAssert
 * To validate if FreeRTOS_ReleaseTCPPayloadBuffer triggers assertion when bytes
 * released from FreeRTOS_recv() is different from request.
 */
void test_FreeRTOS_ReleaseTCPPayloadBuffer_IncorrectBytesReleasedAssert( void )
{
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    uxStreamBufferGetPtr_Stub( StubuxStreamBufferGetPtr_ReturnCorrectVals );

    FreeRTOS_recv_ExpectAndReturn( &xSocket, NULL, ReleaseTCPPayloadBufferxByteCount, FREERTOS_MSG_DONTWAIT, ( ReleaseTCPPayloadBufferxByteCount >> 1 ) );

    catch_assert( FreeRTOS_ReleaseTCPPayloadBuffer( &xSocket, ReleaseTCPPayloadBuffer, ReleaseTCPPayloadBufferxByteCount ) );
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
 * @brief test_prvIPTask
 * Check if prvIPTask() initialize functionalities and state variables as expected.
 */
void test_prvIPTask( void )
{
    /* Reset the static variable. */
    xIPTaskInitialised = pdFALSE;

    /* In prvIPTask_Initialise. */
    vNetworkTimerReload_Ignore();

    /* In prvIPTask_Initialise. */
    vTCPTimerReload_ExpectAnyArgs();
    vIPSetARPResolutionTimerEnableState_Expect( pdFALSE );
    vDNSInitialise_Ignore();
    FreeRTOS_dnsclear_Ignore();

    /* In prvIPTask. */
    ipFOREVER_ExpectAndReturn( 0 );

    /* Parameters do not matter here. */
    prvIPTask( NULL );

    TEST_ASSERT_EQUAL( pdTRUE, xIPTaskInitialised );
    TEST_ASSERT_EQUAL( pdFALSE, xNetworkDownEventPending );
}

/**
 * @brief test_prvIPTask_NetworkDown
 * Check if prvIPTask() handles the network down event normally.
 */
void test_prvIPTask_NetworkDown( void )
{
    NetworkInterface_t xNetworkInterface;
    IPStackEvent_t xDownEvent;

    memset( &xNetworkInterface, 0, sizeof( xNetworkInterface ) );
    pxNetworkInterfaces = &xNetworkInterface;

    xDownEvent.eEventType = eNetworkDownEvent;
    xDownEvent.pvData = &xNetworkInterface;

    /* Reset the static variable. */
    xIPTaskInitialised = pdFALSE;

    /* In prvIPTask_Initialise. */
    vNetworkTimerReload_Ignore();

    /* In FreeRTOS_NetworkDown. */
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );
    xQueueGenericSend_ExpectAnyArgsAndReturn( pdPASS );

    /* In prvIPTask_Initialise. */
    vTCPTimerReload_ExpectAnyArgs();
    vIPSetARPResolutionTimerEnableState_Expect( pdFALSE );
    vDNSInitialise_Ignore();
    FreeRTOS_dnsclear_Ignore();

    /* In prvIPTask. */
    ipFOREVER_ExpectAndReturn( pdTRUE );

    /* In prvProcessIPEventsAndTimers. */
    vCheckNetworkTimers_Ignore();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xDownEvent, sizeof( xDownEvent ) );
    prvProcessNetworkDownEvent_Expect( &xNetworkInterface );

    /* In prvIPTask. */
    ipFOREVER_ExpectAndReturn( pdFALSE );

    /* Parameters do not matter here. */
    prvIPTask( NULL );

    TEST_ASSERT_EQUAL( pdTRUE, xIPTaskInitialised );
}

/**
 * @brief test_prvProcessIPEventsAndTimers_NoEventReceived
 * Check if prvProcessIPEventsAndTimers() runs normally without events.
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
 * @brief test_prvProcessIPEventsAndTimers_eNetworkRxEventNULL
 * Check if prvProcessIPEventsAndTimers() triggers assertion when data pointer is NULL in eNetworkRxEvent.
 */
void test_prvProcessIPEventsAndTimers_eNetworkRxEventNULL( void )
{
    IPStackEvent_t xReceivedEvent;

    xReceivedEvent.eEventType = eNetworkRxEvent;
    xReceivedEvent.pvData = NULL;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eNetworkRxEvent
 * Check if prvProcessIPEventsAndTimers() triggers assertion when data pointer is NULL in eNetworkRxEvent.
 */
void test_prvProcessIPEventsAndTimers_eNetworkRxEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t ) - 1;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    xReceivedEvent.eEventType = eNetworkRxEvent;
    xReceivedEvent.pvData = pxNetworkBuffer;

    /* Put an unknown frame type for prvProcessEthernetPacket to release buffer directly. */
    pxEthernetHeader->usFrameType = 0xFF;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    /* prvProcessEthernetPacket */
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eNetworkTxEvent
 * Check if prvProcessIPEventsAndTimers() transmits data through network interface with eNetworkTxEvent.
 */
void test_prvProcessIPEventsAndTimers_eNetworkTxEvent( void )
{
    struct xNetworkInterface xInterface;
    IPStackEvent_t xReceivedEvent;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t ) - 1;
    pxNetworkBuffer->pxInterface = &xInterface;

    NetworkInterfaceOutputFunction_Stub_Called = 0;
    pxNetworkBuffer->pxInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    xReceivedEvent.eEventType = eNetworkTxEvent;
    xReceivedEvent.pvData = pxNetworkBuffer;
    xNetworkDownEventPending = pdFALSE;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    NetworkInterfaceOutputFunction_Stub_Called = 0;

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eNetworkTxEvent_NullInterface
 * Check if prvProcessIPEventsAndTimers() skip transmitting data through network interface
 * when network interface pointer is NULL.
 */
void test_prvProcessIPEventsAndTimers_eNetworkTxEvent_NullInterface( void )
{
    IPStackEvent_t xReceivedEvent;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t ) - 1;
    pxNetworkBuffer->pxInterface = NULL;

    NetworkInterfaceOutputFunction_Stub_Called = 0;

    xReceivedEvent.eEventType = eNetworkTxEvent;
    xReceivedEvent.pvData = ( void * ) pxNetworkBuffer;
    xNetworkDownEventPending = pdFALSE;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eNetworkRxEvent_NullEndPoint
 * Check if prvProcessIPEventsAndTimers() skip receiving data through network interface
 * when network endpoint pointer is NULL.
 */
void test_prvProcessIPEventsAndTimers_eNetworkRxEvent_NullEndPoint( void )
{
    IPStackEvent_t xReceivedEvent;
    NetworkEndPoint_t xEndPoints;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t ) - 1;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = NULL;

    NetworkInterfaceOutputFunction_Stub_Called = 0;

    xReceivedEvent.eEventType = eNetworkRxEvent;
    xReceivedEvent.pvData = pxNetworkBuffer;
    xNetworkDownEventPending = pdFALSE;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eARPTimerEvent
 * Check if prvProcessIPEventsAndTimers() updates the cache for ARP/ND when timeout event triggered.
 */
void test_prvProcessIPEventsAndTimers_eARPTimerEvent( void )
{
    IPStackEvent_t xReceivedEvent;

    xReceivedEvent.eEventType = eARPTimerEvent;
    xReceivedEvent.pvData = NULL;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vARPAgeCache_Expect();
    vNDAgeCache_Expect();

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eSocketBindEvent
 * To validate if prvProcessIPEventsAndTimers() binds IPv4 socket with its address/port successfully
 * with eSocketBindEvent.
 */
void test_prvProcessIPEventsAndTimers_eSocketBindEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    FreeRTOS_Socket_t xSocket;

    xReceivedEvent.eEventType = eSocketBindEvent;
    xReceivedEvent.pvData = &xSocket;

    xSocket.usLocalPort = ( uint16_t ) ~0U;
    xSocket.xEventBits = 0;
    xSocket.bits.bIsIPv6 = pdFALSE_UNSIGNED;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vSocketBind_ExpectAndReturn( &xSocket, NULL, sizeof( struct freertos_sockaddr ), pdFALSE, 0 );
    vSocketBind_IgnoreArg_pxBindAddress();
    vSocketWakeUpUser_Expect( &xSocket );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( 0, xSocket.usLocalPort );
    TEST_ASSERT_EQUAL( eSOCKET_BOUND, xSocket.xEventBits | eSOCKET_BOUND );
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eSocketBindEvent_IPv6
 * To validate if prvProcessIPEventsAndTimers() binds IPv6 socket with its address/port successfully
 * with eSocketBindEvent.
 */
void test_prvProcessIPEventsAndTimers_eSocketBindEvent_IPv6( void )
{
    IPStackEvent_t xReceivedEvent;
    FreeRTOS_Socket_t xSocket;

    xReceivedEvent.eEventType = eSocketBindEvent;
    xReceivedEvent.pvData = &xSocket;

    xSocket.usLocalPort = ( uint16_t ) ~0U;
    xSocket.xEventBits = 0;
    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vSocketBind_ExpectAndReturn( &xSocket, NULL, sizeof( struct freertos_sockaddr ), pdFALSE, 0 );
    vSocketBind_IgnoreArg_pxBindAddress();
    vSocketWakeUpUser_Expect( &xSocket );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( 0, xSocket.usLocalPort );
    TEST_ASSERT_EQUAL( eSOCKET_BOUND, xSocket.xEventBits | eSOCKET_BOUND );
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eSocketCloseEvent
 * To validate if prvProcessIPEventsAndTimers() close socket successfully with eSocketCloseEvent.
 */
void test_prvProcessIPEventsAndTimers_eSocketCloseEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    FreeRTOS_Socket_t xSocket;

    xReceivedEvent.eEventType = eSocketCloseEvent;
    xReceivedEvent.pvData = &xSocket;

    xSocket.usLocalPort = ( uint16_t ) ~0U;
    xSocket.xEventBits = 0;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vSocketClose_ExpectAndReturn( &xSocket, 0 );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eStackTxEvent
 * To validate if prvProcessIPEventsAndTimers() calls vProcessGeneratedUDPPacket() to handle
 * eStackTxEvent for sending UDP/ping.
 */
void test_prvProcessIPEventsAndTimers_eStackTxEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xReceivedEvent.eEventType = eStackTxEvent;
    xReceivedEvent.pvData = &xNetworkBuffer;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vProcessGeneratedUDPPacket_Expect( &xNetworkBuffer );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eDHCPEvent
 * To validate if prvProcessIPEventsAndTimers() calls vDHCPProcess() to handle eDHCPEvent.
 */
void test_prvProcessIPEventsAndTimers_eDHCPEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    uintptr_t ulDHCPEvent = 0x1234;
    NetworkEndPoint_t xEndPoints, * pxEndPoints = &xEndPoints;

    memset( pxEndPoints, 0, sizeof( NetworkEndPoint_t ) );
    pxEndPoints->bits.bWantDHCP = pdTRUE_UNSIGNED;
    pxEndPoints->bits.bIPv6 = pdFALSE_UNSIGNED;

    xReceivedEvent.eEventType = eDHCPEvent;
    xReceivedEvent.pvData = pxEndPoints;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vDHCPProcess_Expect( pdFALSE, pxEndPoints );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eSocketSelectEvent
 * To validate if prvProcessIPEventsAndTimers() calls vSocketSelect() to handle eSocketSelectEvent.
 */
void test_prvProcessIPEventsAndTimers_eSocketSelectEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    uintptr_t ulData = 0x1234;

    xReceivedEvent.eEventType = eSocketSelectEvent;
    xReceivedEvent.pvData = ( void * ) ulData;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vSocketSelect_Expect( ( SocketSelect_t * ) ulData );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eSocketSignalEvent
 * To validate if prvProcessIPEventsAndTimers() calls FreeRTOS_SignalSocket() to handle eSocketSignalEvent.
 */
void test_prvProcessIPEventsAndTimers_eSocketSignalEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    uintptr_t ulData = 0x1234;

    xReceivedEvent.eEventType = eSocketSignalEvent;
    xReceivedEvent.pvData = ( void * ) ulData;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    FreeRTOS_SignalSocket_ExpectAndReturn( ( Socket_t ) ulData, 0 );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eTCPTimerEvent
 * To validate if prvProcessIPEventsAndTimers() calls vIPSetTCPTimerExpiredState() to handle eTCPTimerEvent.
 */
void test_prvProcessIPEventsAndTimers_eTCPTimerEvent( void )
{
    IPStackEvent_t xReceivedEvent;

    xReceivedEvent.eEventType = eTCPTimerEvent;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vIPSetTCPTimerExpiredState_Expect( pdTRUE );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eTCPAcceptEvent_NoNewClient
 * To validate if prvProcessIPEventsAndTimers() calls xTCPCheckNewClient() to handle eTCPAcceptEvent
 * without new client comes.
 */
void test_prvProcessIPEventsAndTimers_eTCPAcceptEvent_NoNewClient( void )
{
    IPStackEvent_t xReceivedEvent;
    FreeRTOS_Socket_t xSocket;

    xReceivedEvent.eEventType = eTCPAcceptEvent;
    xReceivedEvent.pvData = &xSocket;

    xSocket.xEventBits = 0;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    xTCPCheckNewClient_ExpectAndReturn( &xSocket, pdFALSE );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( 0, xSocket.xEventBits );
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eTCPAcceptEvent_NewClient
 * To validate if prvProcessIPEventsAndTimers() calls xTCPCheckNewClient() to handle eTCPAcceptEvent
 * with new client comes.
 */
void test_prvProcessIPEventsAndTimers_eTCPAcceptEvent_NewClient( void )
{
    IPStackEvent_t xReceivedEvent;
    FreeRTOS_Socket_t xSocket;

    xReceivedEvent.eEventType = eTCPAcceptEvent;
    xReceivedEvent.pvData = &xSocket;

    xSocket.xEventBits = 0;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    xTCPCheckNewClient_ExpectAndReturn( &xSocket, pdTRUE );
    vSocketWakeUpUser_Expect( &xSocket );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( eSOCKET_ACCEPT, xSocket.xEventBits | eSOCKET_ACCEPT );
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eTCPNetStat
 * To validate if prvProcessIPEventsAndTimers() calls vTCPNetStat() to handle eTCPNetStat.
 */
void test_prvProcessIPEventsAndTimers_eTCPNetStat( void )
{
    IPStackEvent_t xReceivedEvent;

    xReceivedEvent.eEventType = eTCPNetStat;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vTCPNetStat_Expect();

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eSocketSetDeleteEvent
 * To validate if prvProcessIPEventsAndTimers() calls vEventGroupDelete() to handle eSocketSetDeleteEvent.
 */
void test_prvProcessIPEventsAndTimers_eSocketSetDeleteEvent( void )
{
    IPStackEvent_t xReceivedEvent;
    SocketSelect_t * pxSocketSet = malloc( sizeof( SocketSelect_t ) );

    xReceivedEvent.eEventType = eSocketSetDeleteEvent;
    xReceivedEvent.pvData = pxSocketSet;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vEventGroupDelete_Expect( pxSocketSet->xSelectGroup );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_prvProcessIPEventsAndTimers_eSocketSetDeleteEvent_NetDownPending
 * To validate if prvProcessIPEventsAndTimers() handles pending network down events at the end function.
 */
void test_prvProcessIPEventsAndTimers_eSocketSetDeleteEvent_NetDownPending( void )
{
    IPStackEvent_t xReceivedEvent;
    NetworkInterface_t xNetworkInterface[ 2 ], * pxInterface = &xNetworkInterface[ 1 ];
    SocketSelect_t * pxSocketSet = malloc( sizeof( SocketSelect_t ) );

    xNetworkDownEventPending = pdTRUE;
    xNetworkInterface[ 0 ].bits.bCallDownEvent = pdFALSE_UNSIGNED;
    xNetworkInterface[ 1 ].bits.bCallDownEvent = pdTRUE_UNSIGNED;

    xReceivedEvent.eEventType = eSocketSetDeleteEvent;
    xReceivedEvent.pvData = pxSocketSet;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );
    vEventGroupDelete_Expect( pxSocketSet->xSelectGroup );

    /* prvIPTask_CheckPendingEvents */
    FreeRTOS_FirstNetworkInterface_ExpectAndReturn( &xNetworkInterface[ 0 ] );
    FreeRTOS_NextNetworkInterface_ExpectAndReturn( &xNetworkInterface[ 0 ], pxInterface );
    /* Since network down event is pending, a call to this function should be expected. */
    prvProcessNetworkDownEvent_Expect( pxInterface );
    FreeRTOS_NextNetworkInterface_ExpectAndReturn( pxInterface, NULL );

    prvProcessIPEventsAndTimers();

    TEST_ASSERT_EQUAL( pxInterface->bits.bCallDownEvent, pdFALSE_UNSIGNED );
}

/**
 * @brief test_prvProcessIPEventsAndTimers_Error
 * To validate if prvProcessIPEventsAndTimers() ignores unknown event.
 */
void test_prvProcessIPEventsAndTimers_Error( void )
{
    IPStackEvent_t xReceivedEvent;

    xNetworkDownEventPending = pdFALSE;

    xReceivedEvent.eEventType = eSocketSetDeleteEvent + 1;

    /* prvProcessIPEventsAndTimers */
    vCheckNetworkTimers_Expect();
    xCalculateSleepTime_ExpectAndReturn( 0 );
    xQueueReceive_ExpectAnyArgsAndReturn( pdTRUE );
    xQueueReceive_ReturnMemThruPtr_pvBuffer( &xReceivedEvent, sizeof( xReceivedEvent ) );

    prvProcessIPEventsAndTimers();
}

/**
 * @brief test_FreeRTOS_SendPingRequest_HappyPath
 * To validate if FreeRTOS_SendPingRequest() prepares ping request and send an event to IP task.
 */
void test_FreeRTOS_SendPingRequest_HappyPath( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    /* 32 byte ping to send. */
    size_t uxNumberOfBytesToSend = 32;
    ICMPHeader_t * pxICMPHeader;
    EthernetHeader_t * pxEthernetHeader;

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigNETWORK_MTU - ( sizeof( IPHeader_t ) + sizeof( ICMPHeader_t ) ) ];

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;

    pxICMPHeader = ( ICMPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipIP_PAYLOAD_OFFSET ] );
    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    xIPTaskInitialised = pdTRUE;

    /* FreeRTOS_SendPingRequest */
    /* At least 4 free network buffers must be there to send a ping. */
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNumberOfBytesToSend + sizeof( ICMPPacket_t ), uxBlockTimeTicks, pxNetworkBuffer );

    /* xSendEventStructToIPTask */
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );
    xQueueGenericSend_ExpectAnyArgsAndReturn( pdPASS );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( 1, xReturn );
    TEST_ASSERT_EQUAL( 8 /* ipICMP_ECHO_REQUEST */, pxICMPHeader->ucTypeOfMessage );
    TEST_ASSERT_EQUAL( 0, pxICMPHeader->ucTypeOfService );
    TEST_ASSERT_EQUAL( 1, pxICMPHeader->usIdentifier );
    TEST_ASSERT_EQUAL( 1, pxICMPHeader->usSequenceNumber );
    TEST_ASSERT_EQUAL( ipIPv4_FRAME_TYPE, pxEthernetHeader->usFrameType );
    TEST_ASSERT_EQUAL( FREERTOS_SO_UDPCKSUM_OUT, pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] );
    TEST_ASSERT_EQUAL( ulIPAddress, pxNetworkBuffer->xIPAddress.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( ipPACKET_CONTAINS_ICMP_DATA, pxNetworkBuffer->usPort );
}

/**
 * @brief test_FreeRTOS_SendPingRequest_SendingToIPTaskFails
 * To validate if FreeRTOS_SendPingRequest() release the ping request packet when fail to send event.
 */
void test_FreeRTOS_SendPingRequest_SendingToIPTaskFails( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    /* 32 byte ping to send. */
    size_t uxNumberOfBytesToSend = 32;
    ICMPHeader_t * pxICMPHeader;
    EthernetHeader_t * pxEthernetHeader;

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigNETWORK_MTU - ( sizeof( IPHeader_t ) + sizeof( ICMPHeader_t ) ) ];

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = pucEthernetBuffer;

    pxICMPHeader = ( ICMPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipIP_PAYLOAD_OFFSET ] );
    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    /* FreeRTOS_SendPingRequest */
    /* At least 4 free network buffers must be there to send a ping. */
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNumberOfBytesToSend + sizeof( ICMPPacket_t ), uxBlockTimeTicks, pxNetworkBuffer );

    /* xSendEventStructToIPTask */
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xQueueGenericSend_ExpectAnyArgsAndReturn( pdFAIL );

    /* FreeRTOS_SendPingRequest */
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL( 8 /* ipICMP_ECHO_REQUEST */, pxICMPHeader->ucTypeOfMessage );
    TEST_ASSERT_EQUAL( 0, pxICMPHeader->ucTypeOfService );
    TEST_ASSERT_EQUAL( 1, pxICMPHeader->usIdentifier );
    TEST_ASSERT_EQUAL( 1, pxICMPHeader->usSequenceNumber );
    TEST_ASSERT_EQUAL( ipIPv4_FRAME_TYPE, pxEthernetHeader->usFrameType );
    TEST_ASSERT_EQUAL( FREERTOS_SO_UDPCKSUM_OUT, pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] );
    TEST_ASSERT_EQUAL( ulIPAddress, pxNetworkBuffer->xIPAddress.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( ipPACKET_CONTAINS_ICMP_DATA, pxNetworkBuffer->usPort );
}

/**
 * @brief test_FreeRTOS_SendPingRequest_TooManyBytes
 * To validate if FreeRTOS_SendPingRequest() returns fail when input bytes is too large.
 */
void test_FreeRTOS_SendPingRequest_TooManyBytes( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    size_t uxNumberOfBytesToSend = ipconfigNETWORK_MTU - ( sizeof( IPHeader_t ) + sizeof( ICMPHeader_t ) );

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    /* FreeRTOS_SendPingRequest */
    /* At least 4 free network buffers must be there to send a ping. */
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_FreeRTOS_SendPingRequest_TooLessBytes
 * To validate if FreeRTOS_SendPingRequest() returns fail when input bytes is 0.
 */
void test_FreeRTOS_SendPingRequest_TooLessBytes( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    size_t uxNumberOfBytesToSend = 0;

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    /* FreeRTOS_SendPingRequest */
    /* At least 4 free network buffers must be there to send a ping. */
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_FreeRTOS_SendPingRequest_NotEnoughFreeBuffers
 * To validate if FreeRTOS_SendPingRequest() returns fail when buffer size is not enough for input bytes.
 */
void test_FreeRTOS_SendPingRequest_NotEnoughFreeBuffers( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    /* 32 byte ping to send. */
    size_t uxNumberOfBytesToSend = 32;

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    /* FreeRTOS_SendPingRequest */
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 3U );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_FreeRTOS_SendPingRequest_NetworkBufferFailure
 * To validate if FreeRTOS_SendPingRequest() returns fail to get network buffer descriptor.
 */
void test_FreeRTOS_SendPingRequest_NetworkBufferFailure( void )
{
    BaseType_t xReturn;
    uint32_t ulIPAddress = 0xC0AB0101;
    /* 32 byte ping to send. */
    size_t uxNumberOfBytesToSend = 32;

    /* The value of blocking time doesn't matter since the test doesn't
     * actually block. */
    TickType_t uxBlockTimeTicks = 100;

    /* FreeRTOS_SendPingRequest */
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNumberOfBytesToSend + sizeof( ICMPPacket_t ), uxBlockTimeTicks, NULL );

    xReturn = FreeRTOS_SendPingRequest( ulIPAddress, uxNumberOfBytesToSend, uxBlockTimeTicks );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xSendEventToIPTask
 * To validate if xSendEventToIPTask() returns fail when IP task was not initialized.
 */
void test_xSendEventToIPTask( void )
{
    BaseType_t xReturn;
    eIPEvent_t eEvent = eNetworkRxEvent;

    xIPTaskInitialised = pdFALSE;

    xReturn = xSendEventToIPTask( eEvent );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xSendEventStructToIPTask_IPTaskNotInit_NoNetworkDownEvent
 * To validate if xSendEventToIPTask() returns fail when IP task was not initialized
 * and the event is not eNetworkDownEvent.
 */
void test_xSendEventStructToIPTask_IPTaskNotInit_NoNetworkDownEvent( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout;

    xIPTaskInitialised = pdFALSE;

    xEvent.eEventType = eNetworkDownEvent + 1;

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEvent
 * To validate if xSendEventToIPTask() returns pass when the event is eNetworkDownEvent
 * even though IP task was not initialized.
 */
void test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEvent( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 0;

    xIPTaskInitialised = pdFALSE;
    xEvent.eEventType = eNetworkDownEvent;

    /* xSendEventStructToIPTask */
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );
    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 0, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEventInIPTask
 * To validate if xSendEventToIPTask() changes the timeout value to 0 when it's happening
 * in IP task.
 */
void test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEventInIPTask( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 1;

    xIPTaskInitialised = pdFALSE;
    xEvent.eEventType = eNetworkDownEvent;

    /* xSendEventStructToIPTask */
    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );
    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 0, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEventNotIPTask
 * To validate if xSendEventToIPTask() returns pass when the event is eNetworkDownEvent
 * and it's not happening in IP task.
 */
void test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEventNotIPTask( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 0;

    xIPTaskInitialised = pdFALSE;
    xEvent.eEventType = eNetworkDownEvent;

    /* xSendEventStructToIPTask */
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 0, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEventNotIPTaskTimeout
 * To validate if xSendEventToIPTask() keeps input timeout value to send event when it's
 * not happening in IP task.
 */
void test_xSendEventStructToIPTask_IPTaskNotInit_NetworkDownEventNotIPTaskTimeout( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 10;

    xIPTaskInitialised = pdFALSE;
    xEvent.eEventType = eNetworkDownEvent;

    /* xSendEventStructToIPTask */
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 10, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_xSendEventStructToIPTask_IPTaskInit_NetworkDownEvent
 * To validate if xSendEventToIPTask() sends eNetworkDownEvent to IP task successfully from other tasks.
 */
void test_xSendEventStructToIPTask_IPTaskInit_NetworkDownEvent( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 10;

    xIPTaskInitialised = pdTRUE;
    xEvent.eEventType = eNetworkDownEvent;

    /* xSendEventStructToIPTask */
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 10, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_xSendEventStructToIPTask_IPTaskInit_eTCPTimerEvent
 * To validate if xSendEventToIPTask() sends eTCPTimerEvent to IP task successfully from other tasks
 * when no pending events in queue.
 */
void test_xSendEventStructToIPTask_IPTaskInit_eTCPTimerEvent( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 10;

    xIPTaskInitialised = pdTRUE;
    xEvent.eEventType = eTCPTimerEvent;

    /* xSendEventStructToIPTask */
    vIPSetTCPTimerExpiredState_Expect( pdTRUE );
    uxQueueMessagesWaiting_ExpectAndReturn( xNetworkEventQueue, 0 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 10, 0, pdPASS );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_xSendEventStructToIPTask_IPTaskInit_eTCPTimerEventFail
 * To validate if xSendEventToIPTask() fails to send eTCPTimerEvent to IP task from other tasks.
 */
void test_xSendEventStructToIPTask_IPTaskInit_eTCPTimerEventFail( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 10;

    xIPTaskInitialised = pdTRUE;
    xEvent.eEventType = eTCPTimerEvent;

    /* xSendEventStructToIPTask */
    vIPSetTCPTimerExpiredState_Expect( pdTRUE );
    uxQueueMessagesWaiting_ExpectAndReturn( xNetworkEventQueue, 0 );
    xIsCallingFromIPTask_ExpectAndReturn( pdFALSE );
    xQueueGenericSend_ExpectAndReturn( xNetworkEventQueue, &xEvent, 10, 0, pdFAIL );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief test_xSendEventStructToIPTask_IPTaskInit_eTCPTimerEventWithEventInQueue
 * To validate if xSendEventToIPTask() skip to send eTCPTimerEvent because there are
 * other pending events in queue.
 */
void test_xSendEventStructToIPTask_IPTaskInit_eTCPTimerEventWithEventInQueue( void )
{
    BaseType_t xReturn;
    IPStackEvent_t xEvent;
    TickType_t uxTimeout = 10;

    xIPTaskInitialised = pdTRUE;
    xEvent.eEventType = eTCPTimerEvent;

    /* xSendEventStructToIPTask */
    vIPSetTCPTimerExpiredState_Expect( pdTRUE );
    uxQueueMessagesWaiting_ExpectAndReturn( xNetworkEventQueue, 1 );

    xReturn = xSendEventStructToIPTask( &xEvent, uxTimeout );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/**
 * @brief test_eConsiderFrameForProcessing_NullBufferDescriptor
 * eConsiderFrameForProcessing must return eReleaseBuffer with NULL input.
 */
void test_eConsiderFrameForProcessing_NullBufferDescriptor( void )
{
    eFrameProcessingResult_t eResult;

    eResult = eConsiderFrameForProcessing( NULL );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_eConsiderFrameForProcessing_LocalMACMatch
 * eConsiderFrameForProcessing must return eProcessBuffer when the MAC address in packet
 * matches endpoint's MAC address and the frame type is valid.
 */
void test_eConsiderFrameForProcessing_LocalMACMatch( void )
{
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    /* eConsiderFrameForProcessing */
    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( pxEndPoint );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );

    /* Align endpoint's & packet's MAC address. */
    memset( pxEndPoint->xMACAddress.ucBytes, 0xAA, sizeof( MACAddress_t ) );
    memcpy( pxEthernetHeader->xDestinationAddress.ucBytes, pxEndPoint->xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    pxEthernetHeader->usFrameType = FreeRTOS_htons( 0x0800 );

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_eConsiderFrameForProcessing_LocalMACMatchInvalidFrameType
 * eConsiderFrameForProcessing must return eReleaseBuffer when the frame type is unknown
 * even though the MAC address in packet matches endpoint's MAC address.
 */
void test_eConsiderFrameForProcessing_LocalMACMatchInvalidFrameType( void )
{
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    /* eConsiderFrameForProcessing */
    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( pxEndPoint );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );

    /* Align endpoint's & packet's MAC address. */
    memset( pxEndPoint->xMACAddress.ucBytes, 0xAA, sizeof( MACAddress_t ) );
    memcpy( pxEthernetHeader->xDestinationAddress.ucBytes, pxEndPoint->xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    pxEthernetHeader->usFrameType = FreeRTOS_htons( 0 );

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_eConsiderFrameForProcessing_LocalMACMatchInvalidFrameType1
 * eConsiderFrameForProcessing must return eReleaseBuffer when the frame type is unknown
 * even though the MAC address in packet matches endpoint's MAC address.
 */
void test_eConsiderFrameForProcessing_LocalMACMatchInvalidFrameType1( void )
{
    eFrameProcessingResult_t eResult;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    /* eConsiderFrameForProcessing */
    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( pxEndPoint );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );

    /* Align endpoint's & packet's MAC address. */
    memset( pxEndPoint->xMACAddress.ucBytes, 0xAA, sizeof( MACAddress_t ) );
    memcpy( pxEthernetHeader->xDestinationAddress.ucBytes, pxEndPoint->xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    pxEthernetHeader->usFrameType = 0x0600;

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_eConsiderFrameForProcessing_BroadCastMACMatch
 * eConsiderFrameForProcessing must return eProcessBuffer when the MAC address in packet
 * matches broadcast MAC address and the frame type is valid.
 */
void test_eConsiderFrameForProcessing_BroadCastMACMatch( void )
{
    eFrameProcessingResult_t eResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    /* eConsiderFrameForProcessing */
    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );

    memcpy( pxEthernetHeader->xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );
    pxEthernetHeader->usFrameType = 0xFFFF;

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_eConsiderFrameForProcessing_LLMNR_MACMatch
 * eConsiderFrameForProcessing must return eProcessBuffer when the MAC address in packet
 * matches LLMNR MAC address and the frame type is valid.
 */
void test_eConsiderFrameForProcessing_LLMNR_MACMatch( void )
{
    eFrameProcessingResult_t eResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    /* eConsiderFrameForProcessing */
    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );

    memcpy( pxEthernetHeader->xDestinationAddress.ucBytes, xLLMNR_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    pxEthernetHeader->usFrameType = 0xFFFF;

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_eConsiderFrameForProcessing_NotMatch
 * eConsiderFrameForProcessing must return eReleaseBuffer when the MAC address
 * in packet doesn't match any endpoint.
 */
void test_eConsiderFrameForProcessing_NotMatch( void )
{
    eFrameProcessingResult_t eResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    MACAddress_t xMACAddress = { 0x11, 0x22, 0x33, 0x44, 0x55, 0x66 };

    /* eConsiderFrameForProcessing */
    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );

    memcpy( pxEthernetHeader->xDestinationAddress.ucBytes, &xMACAddress, sizeof( MACAddress_t ) );
    pxEthernetHeader->usFrameType = 0xFFFF;

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_eConsiderFrameForProcessing_IPv6BroadCastMACMatch
 * eConsiderFrameForProcessing must return eProcessBuffer when the MAC address in packet
 * matches IPv6 broadcast MAC address and the frame type is valid.
 */
void test_eConsiderFrameForProcessing_IPv6BroadCastMACMatch( void )
{
    eFrameProcessingResult_t eResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    /* eConsiderFrameForProcessing */
    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );

    pxEthernetHeader->xDestinationAddress.ucBytes[ 0 ] = ipMULTICAST_MAC_ADDRESS_IPv6_0;
    pxEthernetHeader->xDestinationAddress.ucBytes[ 1 ] = ipMULTICAST_MAC_ADDRESS_IPv6_1;
    pxEthernetHeader->usFrameType = 0xFFFF;

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_eConsiderFrameForProcessing_IPv6BroadCastMACPartialMatch
 * eConsiderFrameForProcessing must return eReleaseBuffer when the MAC address in packet
 * doesn't matches IPv6 broadcast MAC address.
 */
void test_eConsiderFrameForProcessing_IPv6BroadCastMACPartialMatch( void )
{
    eFrameProcessingResult_t eResult;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;

    /* eConsiderFrameForProcessing */
    FreeRTOS_FindEndPointOnMAC_ExpectAnyArgsAndReturn( NULL );

    /* Map the buffer onto Ethernet Header struct for easy access to fields. */
    pxEthernetHeader = ( EthernetHeader_t * ) ucEthernetBuffer;

    memset( ucEthernetBuffer, 0x00, ipconfigTCP_MSS );

    pxEthernetHeader->xDestinationAddress.ucBytes[ 0 ] = ipMULTICAST_MAC_ADDRESS_IPv6_0;
    pxEthernetHeader->xDestinationAddress.ucBytes[ 1 ] = 0x00;
    pxEthernetHeader->usFrameType = 0xFFFF;

    eResult = eConsiderFrameForProcessing( ucEthernetBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessEthernetPacket_NoData
 * To validate if prvProcessEthernetPacket calls vReleaseNetworkBufferAndDescriptor
 * to release the network buffer descriptor.
 */
void test_prvProcessEthernetPacket_NoData( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer->xDataLength = 0;
    pxNetworkBuffer->pucEthernetBuffer = NULL;
    pxNetworkBuffer->pxInterface = &xInterface;

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief test_prvProcessEthernetPacket_UnknownFrameType
 * To validate if prvProcessEthernetPacket calls vReleaseNetworkBufferAndDescriptor
 * to release the network buffer descriptor when the ethernet frame type is unknown.
 */
void test_prvProcessEthernetPacket_UnknownFrameType( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;
    pxEthernetHeader = ( EthernetHeader_t * ) ucEtherBuffer;
    pxEthernetHeader->usFrameType = 0xFFFF;
    pxNetworkBuffer->pxInterface = &xInterface;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief test_prvProcessEthernetPacket_ARPFrameType1
 * To validate the flow to handle ARP packets but eARPProcessPacket() returns eReleaseBuffer.
 */
void test_prvProcessEthernetPacket_ARPFrameType1( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;
    struct xNetworkEndPoint xEndPoint;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eReleaseBuffer );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief test_prvProcessEthernetPacket_ARPFrameType2
 * To validate the flow to handle ARP packets but eARPProcessPacket() returns eProcessBuffer.
 */
void test_prvProcessEthernetPacket_ARPFrameType2( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;
    struct xNetworkEndPoint xEndPoint;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eProcessBuffer );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief test_prvProcessEthernetPacket_ARPFrameType_WaitingARPResolution
 * To validate the flow to handle ARP packets but eARPProcessPacket() returns eWaitingARPResolution
 * without pxARPWaitingNetworkBuffer.
 */
void test_prvProcessEthernetPacket_ARPFrameType_WaitingARPResolution( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;
    struct xNetworkEndPoint xEndPoint;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    pxARPWaitingNetworkBuffer = NULL;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eWaitingARPResolution );

    vIPTimerStartARPResolution_ExpectAnyArgs();

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief test_prvProcessEthernetPacket_ARPFrameType_WaitingARPResolution2
 * To validate the flow to handle ARP packets but eARPProcessPacket() returns eWaitingARPResolution
 * with pxARPWaitingNetworkBuffer.
 */
void test_prvProcessEthernetPacket_ARPFrameType_WaitingARPResolution2( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;
    struct xNetworkEndPoint xEndPoint;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    pxARPWaitingNetworkBuffer = ( NetworkBufferDescriptor_t * ) 0x1234ABCD;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eWaitingARPResolution );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief test_prvProcessEthernetPacket_ARPFrameType_eReturnEthernetFrame
 * To validate the flow to handle ARP packets but eARPProcessPacket() returns eReturnEthernetFrame.
 */
void test_prvProcessEthernetPacket_ARPFrameType_eReturnEthernetFrame( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, xARPWaitingBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;
    struct xNetworkEndPoint xEndPoint = { 0 };

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.pxNetworkInterface = xInterfaces;
    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eReturnEthernetFrame );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    prvProcessEthernetPacket( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
}

/**
 * @brief test_prvProcessEthernetPacket_ARPFrameType_eFrameConsumed
 * To validate the flow to handle ARP packets but eARPProcessPacket() returns eFrameConsumed.
 */
void test_prvProcessEthernetPacket_ARPFrameType_eFrameConsumed( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, xARPWaitingBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;
    NetworkEndPoint_t xNetworkEndPoint = { 0 };

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = &xNetworkEndPoint;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    eARPProcessPacket_ExpectAndReturn( pxNetworkBuffer, eFrameConsumed );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief test_prvProcessEthernetPacket_ARPFrameType_SmallerDataLength
 * To validate the flow to handle ARP packets but the data length is smaller than
 * minimum size of ARP packet.
 */
void test_prvProcessEthernetPacket_ARPFrameType_SmallerDataLength( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;
    NetworkEndPoint_t xNetworkEndPoint = { 0 };

    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t );
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = &xNetworkEndPoint;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipARP_FRAME_TYPE;

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief test_prvProcessEthernetPacket_IPv4FrameType_LessData
 * To validate the flow to handle IPv4 packets but the data length is smaller than
 * minimum size of IPv4 packet.
 */
void test_prvProcessEthernetPacket_IPv4FrameType_LessData( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEtherBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;
    NetworkEndPoint_t xNetworkEndPoint = { 0 };

    pxNetworkBuffer->xDataLength = sizeof( EthernetHeader_t );
    pxNetworkBuffer->pucEthernetBuffer = ucEtherBuffer;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = &xNetworkEndPoint;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

    memset( pxNetworkBuffer->pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxEthernetHeader->usFrameType = ipIPv4_FRAME_TYPE;

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief test_prvProcessEthernetPacket_IPv4FrameType_AptData
 * To validate the flow to handle IPv4 packets but the length in IP header is smaller than
 * minimum requirement.
 */
void test_prvProcessEthernetPacket_IPv4FrameType_AptData( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ] = { 0 };
    EthernetHeader_t * pxEthernetHeader;
    IPPacket_t * pxIPPacket;
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;
    NetworkEndPoint_t xNetworkEndPoint = { 0 };

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->pxEndPoint = &xNetworkEndPoint;

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxEthernetHeader->usFrameType = ipIPv4_FRAME_TYPE;

    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPHeader->ucVersionHeaderLength = 0xF0;

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}

/**
 * @brief test_prvProcessEthernetPacket_InterfaceNull
 * To validate the flow to when the interface associated with the
 * network buffer is NULL
 */
void test_prvProcessEthernetPacket_InterfaceNull( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ ipconfigTCP_MSS ] = { 0 };
    EthernetHeader_t * pxEthernetHeader;
    IPPacket_t * pxIPPacket;
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxNetworkBuffer->pxInterface = NULL;

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    prvProcessEthernetPacket( pxNetworkBuffer );
}


/**
 * @brief test_prvProcessIPPacket_HeaderLengthSmaller
 * To validate the flow to handle IPv4 packets but the length in IP header is smaller than
 * minimum requirement.
 */
void test_prvProcessIPPacket_HeaderLengthSmaller( void )
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPPacket_t * pxIPPacket;
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxNetworkBuffer->pxInterface = &xInterface;

    pxIPHeader->ucVersionHeaderLength = 0xF0;

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_HeaderLengthGreater
 * To validate the flow to handle IPv4 packets but the length in IP header is greater than
 * network buffer size.
 */
void test_prvProcessIPPacket_HeaderLengthGreater( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxNetworkBuffer->pxInterface = &xInterface;

    pxIPHeader->ucVersionHeaderLength = 0xFF;

    /* Let the data length be greater than the ethernet header but small
     * enough to make the IP header bigger than the total length. */
    pxNetworkBuffer->xDataLength = 30;

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_UnknownFrameType
 * To validate the flow to handle unknown ethernet frame type.
 */
void test_prvProcessIPPacket_UnknownFrameType( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    memset( ucEthBuffer, 0, ipconfigTCP_MSS );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = 0xFF;
    pxNetworkBuffer->pxInterface = &xInterface;

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_ValidHeader_ARPResolutionReqd
 * To validate the flow to handle a valid IPv4 packet but need ARP resolution.
 */
void test_prvProcessIPPacket_ValidHeader_ARPResolutionReqd( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x45;

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );
    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdTRUE );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eWaitingARPResolution, eResult );
}

/**
 * @brief test_prvProcessIPPacket_ARPResolutionNotReqd_InvalidProt
 * To validate the flow to handle a valid IPv4 packet but invalid protocol.
 */
void test_prvProcessIPPacket_ARPResolutionNotReqd_InvalidProt( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;

    /* Initialize ethernet layer. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x46;
    pxIPHeader->ucProtocol = 0xFF;
    pxNetworkBuffer->pxInterface = &xInterface;

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );
    prvCheckIP4HeaderOptions_ExpectAndReturn( pxNetworkBuffer, eProcessBuffer );
    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_ExpectAnyArgs();

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_ARPResolutionNotReqd_ICMPRelease
 * To validate the flow to handle a valid ICMPv4 packet. Then ProcessICMPPacket() returns eReleaseBuffer.
 */
void test_prvProcessIPPacket_ARPResolutionNotReqd_ICMPRelease( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x46;
    pxIPHeader->ucProtocol = ipPROTOCOL_ICMP;

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );
    prvCheckIP4HeaderOptions_ExpectAndReturn( pxNetworkBuffer, eProcessBuffer );
    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_ExpectAnyArgs();
    ProcessICMPPacket_ExpectAndReturn( pxNetworkBuffer, eReleaseBuffer );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_ARPResolutionNotReqd_ICMPProcess
 * To validate the flow to handle a valid ICMPv4 packet. Then ProcessICMPPacket() returns eProcessBuffer.
 */
void test_prvProcessIPPacket_ARPResolutionNotReqd_ICMPProcess( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x46;
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );
    prvCheckIP4HeaderOptions_ExpectAndReturn( pxNetworkBuffer, eProcessBuffer );
    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_ExpectAnyArgs();
    ProcessICMPPacket_ExpectAndReturn( pxNetworkBuffer, eProcessBuffer );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_ARPResolutionNotReqd_UDPZeroLength
 * To validate the flow to handle a UDPv4 packet with 0 length in UDP header.
 */
void test_prvProcessIPPacket_ARPResolutionNotReqd_UDPZeroLength( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x46;
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    /* Initialize UDP layer. */
    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_htons( 0 );

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );
    prvCheckIP4HeaderOptions_ExpectAndReturn( pxNetworkBuffer, eProcessBuffer );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_ARPResolutionNotReqd_UDPLengthGreaterThanIPHeader
 * To validate the flow to handle a UDPv4 packet when length of UDP header is greater
 * than the length in IP header.
 */
void test_prvProcessIPPacket_ARPResolutionNotReqd_UDPLengthGreaterThanIPHeader( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxUDPPacket = ( ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    /* Initialize UDP layer. */
    /* The length in IP header contains IP header + UDP. So UDP length shouldn't be same as length in IP header. */
    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_htons( ipconfigTCP_MSS );

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_ARPResolutionNotReqd_UDPHappyPath
 * To validate the flow to handle a valid UDPv4 packet.
 */
void test_prvProcessIPPacket_ARPResolutionNotReqd_UDPHappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;
    UDPPacket_t * pxUDPPacket;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    /* Initialize UDP layer. */
    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_ntohs( sizeof( UDPPacket_t ) );

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );
    xProcessReceivedUDPPacket_ExpectAnyArgsAndReturn( pdPASS );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eFrameConsumed, eResult );
}

/**
 * @brief test_prvProcessIPPacket_ARPResolutionNotReqd_UDPProcessFail
 * To validate the flow to handle a valid UDPv4 packet but got failure while calling xProcessReceivedUDPPacket().
 */
void test_prvProcessIPPacket_ARPResolutionNotReqd_UDPProcessFail( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    UDPPacket_t * pxUDPPacket;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    /* Initialize UDP layer. */
    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_ntohs( sizeof( UDPPacket_t ) );

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );

    xProcessReceivedUDPPacket_ExpectAnyArgsAndReturn( pdFAIL );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_ARPResolutionReqd_UDP
 * To validate the flow to handle a valid UDPv4 packet but got failure while calling xProcessReceivedUDPPacket()
 * because of waiting ARP resolution.
 */
void test_prvProcessIPPacket_ARPResolutionReqd_UDP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    UDPPacket_t * pxUDPPacket;
    BaseType_t xReturnValue = pdTRUE;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    /* Initialize UDP layer. */
    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_ntohs( sizeof( UDPPacket_t ) );

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );

    xProcessReceivedUDPPacket_ExpectAndReturn( pxNetworkBuffer, pxUDPPacket->xUDPHeader.usDestinationPort, NULL, pdFAIL );
    xProcessReceivedUDPPacket_IgnoreArg_pxIsWaitingForARPResolution();
    xProcessReceivedUDPPacket_ReturnThruPtr_pxIsWaitingForARPResolution( &xReturnValue );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eWaitingARPResolution, eResult );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) - sizeof( UDPHeader_t ) + sizeof( UDPPacket_t ), pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xIPAddress.ulIP_IPv4, pxUDPPacket->xIPHeader.ulSourceIPAddress );
}

/**
 * @brief test_prvProcessIPPacket_ARPResolutionReqd_UDP1
 * To validate the flow to handle a valid UDPv4 packet but got failure while calling xProcessReceivedUDPPacket()
 * because of waiting ARP resolution. And the network buffer size is small than UDP header.
 */
void test_prvProcessIPPacket_ARPResolutionReqd_UDP1( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    UDPPacket_t * pxUDPPacket;
    BaseType_t xReturnValue = pdTRUE;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t );
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    /* Initialize UDP layer. */
    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_ntohs( sizeof( UDPPacket_t ) );

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );

    xProcessReceivedUDPPacket_ExpectAndReturn( pxNetworkBuffer, pxUDPPacket->xUDPHeader.usDestinationPort, NULL, pdFAIL );
    xProcessReceivedUDPPacket_IgnoreArg_pxIsWaitingForARPResolution();
    xProcessReceivedUDPPacket_ReturnThruPtr_pxIsWaitingForARPResolution( &xReturnValue );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eWaitingARPResolution, eResult );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->usPort, pxUDPPacket->xUDPHeader.usSourcePort );
    TEST_ASSERT_EQUAL( pxNetworkBuffer->xIPAddress.ulIP_IPv4, pxUDPPacket->xIPHeader.ulSourceIPAddress );
}

/**
 * @brief test_prvProcessIPPacket_TCP
 * To validate the flow to handle a valid TCPv4 packet and no ARP resolution needed.
 */
void test_prvProcessIPPacket_TCP( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    BaseType_t xReturnValue = pdTRUE;
    struct xNetworkInterface xInterface;


    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t );
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );
    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_ExpectAnyArgs();
    xProcessReceivedTCPPacket_ExpectAndReturn( pxNetworkBuffer, pdPASS );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eFrameConsumed, eResult );
}

/**
 * @brief test_prvProcessIPPacket_TCPProcessFail
 * To validate the flow to handle a valid TCPv4 packet and no ARP resolution needed.
 * Got failure while calling xProcessReceivedTCPPacket().
 */
void test_prvProcessIPPacket_TCPProcessFail( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    BaseType_t xReturnValue = pdTRUE;
    NetworkEndPoint_t xEndPoint = { 0 };
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t );
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->usLength = FreeRTOS_htons( ipconfigTCP_MSS );
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );
    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );
    vARPRefreshCacheEntryAge_ExpectAnyArgs();
    xProcessReceivedTCPPacket_ExpectAndReturn( pxNetworkBuffer, pdFAIL );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_UDP_ExternalLoopback
 * To validate the flow to handle a UDPv4 packet but the destination IP address
 * is loop-back address.
 */
void test_prvProcessIPPacket_UDP_ExternalLoopback( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_htonl( ipFIRST_LOOPBACK_IPv4 );
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_UDP_GreaterLoopbackAddress
 * To validate the flow to handle a UDPv4 packet but the destination IP address
 * is greater than loop-back address.
 */
void test_prvProcessIPPacket_UDP_GreaterLoopbackAddress( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = 0;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_htonl( ipLAST_LOOPBACK_IPv4 );
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_UDP_LessLoopbackAddress
 * To validate the flow to handle a UDPv4 packet but the destination IP address
 * is less than loop-back address.
 */
void test_prvProcessIPPacket_UDP_LessLoopbackAddress( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = 0;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, xBroadcastMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionHeaderLength = 0x45;
    pxIPHeader->ulDestinationIPAddress = FreeRTOS_htonl( ipFIRST_LOOPBACK_IPv4 - 1 );
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    prvAllowIPPacketIPv4_ExpectAndReturn( pxIPPacket, pxNetworkBuffer, ( pxIPHeader->ucVersionHeaderLength & 0x0FU ) << 2, eProcessBuffer );

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_UDP_IPHeaderLengthTooLarge
 * To validate the flow to handle a UDPv4 packet but the header length in
 * IP header is greater than buffer size.
 */
void test_prvProcessIPPacket_UDP_IPHeaderLengthTooLarge( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_t * pxIPHeader;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxIPPacket = ( IPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    /* Initialize IP layer. */
    /* The length in IP header is larger than buffer size. */
    pxIPHeader->ucVersionHeaderLength = 0x4F;
    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    eResult = prvProcessIPPacket( pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_UDP_IPv6_HappyPath
 * To validate the flow to handle a UDPv6 packet successfully.
 */
void test_prvProcessIPPacket_UDP_IPv6_HappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_IPv6_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_IPv6_t * pxIPHeader;
    UDPPacket_IPv6_t * pxUDPPacket;
    BaseType_t xReturnValue = pdTRUE;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxUDPPacket = ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucMACAddress, sizeof( MACAddress_t ) );

    /* Initialize IP layer. */
    pxIPHeader->ucVersionTrafficClass = 0x60;
    pxIPHeader->usPayloadLength = FreeRTOS_htons( ipconfigTCP_MSS ) - sizeof( IPPacket_IPv6_t );
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_UDP;

    /* Initialize UDP layer. */
    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_ntohs( FreeRTOS_htons( ipconfigTCP_MSS ) - sizeof( UDPPacket_IPv6_t ) );

    prvAllowIPPacketIPv6_ExpectAndReturn( pxIPHeader, pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER, eProcessBuffer );
    xGetExtensionOrder_ExpectAndReturn( ipPROTOCOL_UDP, 0U, 0 );
    xProcessReceivedUDPPacket_ExpectAnyArgsAndReturn( pdPASS );

    eResult = prvProcessIPPacket( ( IPPacket_t * ) pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eFrameConsumed, eResult );
}

/**
 * @brief test_prvProcessIPPacket_UDP_IPv6_ExtensionHappyPath
 * To validate the flow to handle a UDPv6 packet with extension header successfully.
 */
void test_prvProcessIPPacket_UDP_IPv6_ExtensionHappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_IPv6_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_IPv6_t * pxIPHeader;
    UDPPacket_IPv6_t * pxUDPPacket;
    BaseType_t xReturnValue = pdTRUE;
    struct xNetworkInterface xInterface;

    /* Initialize network buffer descriptor. */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    /* Initialize ethernet layer. */
    pxUDPPacket = ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucMACAddress, sizeof( MACAddress_t ) );

    pxIPHeader->ucVersionTrafficClass = 0x60;

    pxIPHeader->usPayloadLength = FreeRTOS_htons( ipconfigTCP_MSS ) - sizeof( IPPacket_IPv6_t );

    /* Packet not meant for this node. */
    memcpy( pxIPHeader->xSourceAddress.ucBytes, xIPAddressTen.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxIPHeader->xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    /* Set the protocol to be IPv6 UDP. */
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_UDP;

    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_ntohs( FreeRTOS_htons( ipconfigTCP_MSS ) - sizeof( UDPPacket_IPv6_t ) );

    prvAllowIPPacketIPv6_ExpectAndReturn( pxIPHeader, pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER, eProcessBuffer );
    xGetExtensionOrder_ExpectAndReturn( ipPROTOCOL_UDP, 0U, 1 );
    eHandleIPv6ExtensionHeaders_ExpectAndReturn( pxNetworkBuffer, pdTRUE, eProcessBuffer );
    xProcessReceivedUDPPacket_ExpectAnyArgsAndReturn( pdPASS );

    eResult = prvProcessIPPacket( ( IPPacket_t * ) pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eFrameConsumed, eResult );
}

/**
 * @brief test_prvProcessIPPacket_UDP_IPv6_ExtensionHandleFail
 * To validate the flow to handle a UDPv6 packet with extension header but got failure
 * while handling extension header.
 */
void test_prvProcessIPPacket_UDP_IPv6_ExtensionHandleFail( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_IPv6_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_IPv6_t * pxIPHeader;
    UDPPacket_IPv6_t * pxUDPPacket;
    BaseType_t xReturnValue = pdTRUE;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    pxUDPPacket = ( UDPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPHeader->ucVersionTrafficClass = 0x60;

    pxIPHeader->usPayloadLength = FreeRTOS_htons( ipconfigTCP_MSS ) - sizeof( IPPacket_IPv6_t );

    /* Packet not meant for this node. */
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucMACAddress, sizeof( MACAddress_t ) );
    memcpy( pxIPHeader->xSourceAddress.ucBytes, xIPAddressTen.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxIPHeader->xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    /* Set the protocol to be IPv6 UDP. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_UDP;

    pxUDPPacket->xUDPHeader.usLength = FreeRTOS_ntohs( FreeRTOS_htons( ipconfigTCP_MSS ) - sizeof( UDPPacket_IPv6_t ) );

    prvAllowIPPacketIPv6_ExpectAndReturn( pxIPHeader, pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER, eProcessBuffer );
    xGetExtensionOrder_ExpectAndReturn( ipPROTOCOL_UDP, 0U, 1 );
    eHandleIPv6ExtensionHeaders_ExpectAndReturn( pxNetworkBuffer, pdTRUE, eReleaseBuffer );

    eResult = prvProcessIPPacket( ( IPPacket_t * ) pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_TCP_IPv6_HappyPath
 * To validate the flow to handle a TCPv6 packet successfully.
 */
void test_prvProcessIPPacket_TCP_IPv6_HappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_IPv6_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_IPv6_t * pxIPHeader;
    TCPPacket_IPv6_t * pxTCPPacket;
    BaseType_t xReturnValue = pdTRUE;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPHeader->ucVersionTrafficClass = 0x60;

    pxIPHeader->usPayloadLength = FreeRTOS_htons( ipconfigTCP_MSS ) - sizeof( IPPacket_IPv6_t );

    /* Packet not meant for this node. */
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucMACAddress, sizeof( MACAddress_t ) );
    memcpy( pxIPHeader->xSourceAddress.ucBytes, xIPAddressTen.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxIPHeader->xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    /* Set the protocol to be IPv6 UDP. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_TCP;

    prvAllowIPPacketIPv6_ExpectAndReturn( pxIPHeader, pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER, eProcessBuffer );
    xGetExtensionOrder_ExpectAndReturn( ipPROTOCOL_TCP, 0U, 0 );
    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    xProcessReceivedTCPPacket_ExpectAnyArgsAndReturn( pdPASS );

    eResult = prvProcessIPPacket( ( IPPacket_t * ) pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eFrameConsumed, eResult );
}

/**
 * @brief test_prvProcessIPPacket_TCP_IPv6_ARPResolution
 * To validate the flow to handle a TCPv6 packet successfully.
 * Then it needs to update ND resolution.
 */
void test_prvProcessIPPacket_TCP_IPv6_ARPResolution( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_IPv6_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_IPv6_t * pxIPHeader;
    TCPPacket_IPv6_t * pxTCPPacket;
    BaseType_t xReturnValue = pdTRUE;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPHeader->ucVersionTrafficClass = 0x60;

    pxIPHeader->usPayloadLength = FreeRTOS_htons( ipconfigTCP_MSS ) - sizeof( IPPacket_IPv6_t );

    /* Packet not meant for this node. */
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucMACAddress, sizeof( MACAddress_t ) );
    memcpy( pxIPHeader->xSourceAddress.ucBytes, xIPAddressTen.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxIPHeader->xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    /* Set the protocol to be IPv6 UDP. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_TCP;

    prvAllowIPPacketIPv6_ExpectAndReturn( pxIPHeader, pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER, eProcessBuffer );
    xGetExtensionOrder_ExpectAndReturn( ipPROTOCOL_TCP, 0U, 0 );
    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdTRUE );

    eResult = prvProcessIPPacket( ( IPPacket_t * ) pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eWaitingARPResolution, eResult );
}

/**
 * @brief test_prvProcessIPPacket_ICMP_IPv6_HappyPath
 * To validate the flow to handle a ICMPv6 packet successfully.
 */
void test_prvProcessIPPacket_ICMP_IPv6_HappyPath( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_IPv6_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_IPv6_t * pxIPHeader;
    ICMPPacket_IPv6_t * pxICMPPacket;
    BaseType_t xReturnValue = pdTRUE;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = ipconfigTCP_MSS;
    pxNetworkBuffer->pxInterface = &xInterface;

    pxICMPPacket = ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPHeader = &( pxIPPacket->xIPHeader );
    pxIPHeader->ucVersionTrafficClass = 0x60;

    pxIPHeader->usPayloadLength = FreeRTOS_htons( ipconfigTCP_MSS ) - sizeof( IPPacket_IPv6_t );

    /* Packet not meant for this node. */
    memcpy( pxIPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucMACAddress, sizeof( MACAddress_t ) );
    memcpy( pxIPHeader->xSourceAddress.ucBytes, xIPAddressTen.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxIPHeader->xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    /* Set the protocol to be IPv6 UDP. */
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;

    prvAllowIPPacketIPv6_ExpectAndReturn( pxIPHeader, pxNetworkBuffer, ipSIZE_OF_IPv6_HEADER, eProcessBuffer );
    xGetExtensionOrder_ExpectAndReturn( ipPROTOCOL_ICMP_IPv6, 0U, 0 );
    xCheckRequiresARPResolution_ExpectAndReturn( pxNetworkBuffer, pdFALSE );
    vNDRefreshCacheEntry_Ignore();
    prvProcessICMPMessage_IPv6_ExpectAnyArgsAndReturn( eReleaseBuffer );

    eResult = prvProcessIPPacket( ( IPPacket_t * ) pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_prvProcessIPPacket_IPv6_LessPacketSize
 *  The packet size is less than IPv6 minimum packet size.
 */
void test_prvProcessIPPacket_IPv6_LessPacketSize( void )
{
    eFrameProcessingResult_t eResult;
    IPPacket_IPv6_t * pxIPPacket;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    UBaseType_t uxHeaderLength = 0;
    uint8_t ucEthBuffer[ ipIP_TYPE_OFFSET + ipconfigTCP_MSS ] = { 0 };
    IPHeader_IPv6_t * pxIPHeader;
    struct xNetworkInterface xInterface;
    BaseType_t xReturnValue = pdTRUE;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer + ipIP_TYPE_OFFSET;
    pxNetworkBuffer->xDataLength = sizeof( IPPacket_IPv6_t ) - 1;
    pxNetworkBuffer->pxInterface = &xInterface;

    pxIPPacket = ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    eResult = prvProcessIPPacket( ( IPPacket_t * ) pxIPPacket, pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief test_vReturnEthernetFrame
 * To validate if vReturnEthernetFrame changes the source/destination MAC addresses correctly
 * and transmits though network interface.
 */
void test_vReturnEthernetFrame( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdFALSE;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pxInterface = &xInterface;

    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;
    xEndPoint.pxNetworkInterface = xInterfaces;
    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    memset( pxEndPoint->xMACAddress.ucBytes, 0x11, sizeof( pxEndPoint->xMACAddress ) );
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10;

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxNetworkBuffer->pxEndPoint );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x11, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
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
    BaseType_t xReleaseAfterSend = pdFALSE;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;
    pxNetworkBuffer->pxInterface = &xInterface;
    xEndPoint.pxNetworkInterface = xInterfaces;
    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;
    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxNetworkBuffer->pxEndPoint );

    xIsCallingFromIPTask_ExpectAndReturn( pdTRUE );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EQUAL( ipconfigETHERNET_MINIMUM_PACKET_BYTES, pxNetworkBuffer->xDataLength );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAA, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
    TEST_ASSERT_EQUAL( 1, NetworkInterfaceOutputFunction_Stub_Called );
}

/**
 * @brief test_vReturnEthernetFrame_ReleaseAfterSend
 * To validate if vReturnEthernetFrame changes the source/destination MAC addresses correctly
 * and send the event to IP task.
 */
void test_vReturnEthernetFrame_ReleaseAfterSend( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdTRUE;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pxInterface = &xInterface;

    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;
    xEndPoint.pxNetworkInterface = xInterfaces;
    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxNetworkBuffer->pxEndPoint );

    xIPTaskInitialised = pdTRUE;
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    xQueueGenericSend_IgnoreAndReturn( pdPASS );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAA, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
    TEST_ASSERT_EQUAL( 0, NetworkInterfaceOutputFunction_Stub_Called );
}

/**
 * @brief test_vReturnEthernetFrame_ReleaseAfterSendFail
 * To validate if vReturnEthernetFrame changes the source/destination MAC addresses correctly
 * but fail to send the event to IP task.
 */
void test_vReturnEthernetFrame_ReleaseAfterSendFail( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdTRUE;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pxInterface = &xInterface;

    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;
    xEndPoint.pxNetworkInterface = xInterfaces;
    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxNetworkBuffer->pxEndPoint );

    xIPTaskInitialised = pdTRUE;
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );
    xQueueGenericSend_IgnoreAndReturn( pdFAIL );
    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );

    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAA, &ucEthBuffer[ ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10 ], 10 );
    TEST_ASSERT_EACH_EQUAL_UINT8( 0x22, &pxEthernetHeader->xDestinationAddress, sizeof( pxEthernetHeader->xDestinationAddress ) );
    TEST_ASSERT_EQUAL_MEMORY( pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes, &pxEthernetHeader->xSourceAddress, sizeof( pxEthernetHeader->xSourceAddress ) );
    TEST_ASSERT_EQUAL( 0, NetworkInterfaceOutputFunction_Stub_Called );
}

/**
 * @brief test_vReturnEthernetFrame_NeitherIPTaskNorReleaseAfterSend
 * To validate if vReturnEthernetFrame triggers assertion when it's neither called from IP task
 * nor ReleaseAfterSend.
 */
void test_vReturnEthernetFrame_NeitherIPTaskNorReleaseAfterSend( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdFALSE;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pxInterface = &xInterface;

    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = pxEndPoint;
    xEndPoint.pxNetworkInterface = xInterfaces;
    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;
    NetworkInterfaceOutputFunction_Stub_Called = 0;

    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES - 10;

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( pxNetworkBuffer->pxEndPoint );

    xIPTaskInitialised = pdTRUE;
    xIsCallingFromIPTask_IgnoreAndReturn( pdFALSE );

    catch_assert( vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend ) );
}

/**
 * @brief test_vReturnEthernetFrame_UnknownFrameType
 * To validate if vReturnEthernetFrame handles unknown ethernet frame type.
 */
void test_vReturnEthernetFrame_UnknownFrameType( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdFALSE;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxNetworkBuffer->pxInterface = &xInterface;

    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;

    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );
    pxEthernetHeader->usFrameType = 0xFF;

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;

    FreeRTOS_FindEndPointOnNetMask_IgnoreAndReturn( NULL );

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );
}

/**
 * @brief test_vReturnEthernetFrame_IPv6NoEndpoint
 * To validate if vReturnEthernetFrame handles IPv6 ethernet frame without endpoint.
 */
void test_vReturnEthernetFrame_IPv6NoEndpoint( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    BaseType_t xReleaseAfterSend = pdFALSE;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    EthernetHeader_t * pxEthernetHeader;
    struct xNetworkInterface xInterface;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;
    pxNetworkBuffer->pxInterface = &xInterface;

    memset( pxNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;

    memset( ucEthBuffer, 0xAA, ipconfigTCP_MSS );

    pxEthernetHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    memset( &pxEthernetHeader->xDestinationAddress, 0x11, sizeof( pxEthernetHeader->xDestinationAddress ) );
    memset( &pxEthernetHeader->xSourceAddress, 0x22, sizeof( pxEthernetHeader->xSourceAddress ) );
    pxEthernetHeader->usFrameType = ipIPv6_FRAME_TYPE;

    pxNetworkBuffer->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;

    vReturnEthernetFrame( pxNetworkBuffer, xReleaseAfterSend );
}

/**
 * @brief test_FreeRTOS_GetIPAddress
 * To validate if FreeRTOS_GetIPAddress returns correct IP address stored in first endpoint.
 */
void test_FreeRTOS_GetIPAddress( void )
{
    uint32_t ulIPAddress;

    NetworkEndPoint_t xEndPoint = { 0 };

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    xEndPoint.ipv4_settings.ulIPAddress = 0xAB12CD34;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );

    ulIPAddress = FreeRTOS_GetIPAddress();

    TEST_ASSERT_EQUAL( 0xAB12CD34, ulIPAddress );
}

/**
 * @brief test_FreeRTOS_GetIPAddress_DefaultSetting
 * To validate if FreeRTOS_GetIPAddress returns correct IP address
 * in ipv4_defaults instead of ipv4_settings.
 */
void test_FreeRTOS_GetIPAddress_DefaultSetting( void )
{
    uint32_t ulIPAddress;

    NetworkEndPoint_t xEndPoint = { 0 };

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    xEndPoint.ipv4_settings.ulIPAddress = 0;
    xEndPoint.ipv4_defaults.ulIPAddress = 0xAB12CD34;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );

    ulIPAddress = FreeRTOS_GetIPAddress();

    TEST_ASSERT_EQUAL( 0xAB12CD34, ulIPAddress );
}

/**
 * @brief test_FreeRTOS_GetIPAddress_NullEndpoint
 * To validate if FreeRTOS_GetIPAddress returns 0 when no endpoint.
 */
void test_FreeRTOS_GetIPAddress_NullEndpoint( void )
{
    uint32_t ulIPAddress;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( NULL );

    ulIPAddress = FreeRTOS_GetIPAddress();

    TEST_ASSERT_EQUAL( 0, ulIPAddress );
}

/**
 * @brief test_FreeRTOS_GetIPAddress_MultipleEndpoints
 * To validate if FreeRTOS_GetIPAddress returns IP address of first IPv4 endpoint.
 */
void test_FreeRTOS_GetIPAddress_MultipleEndpoints( void )
{
    uint32_t ulIPAddress;
    NetworkEndPoint_t xEndPoints[ 2 ]; /* IPv6->IPv4 */

    memset( &xEndPoints[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoints[ 0 ].bits.bIPv6 = pdTRUE;
    memset( &xEndPoints[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoints[ 1 ].bits.bIPv6 = pdFALSE;
    xEndPoints[ 1 ].ipv4_settings.ulIPAddress = 0xAB12CD34;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoints[ 0 ] );
    FreeRTOS_NextEndPoint_ExpectAndReturn( NULL, &xEndPoints[ 0 ], &xEndPoints[ 1 ] );

    ulIPAddress = FreeRTOS_GetIPAddress();

    TEST_ASSERT_EQUAL( 0xAB12CD34, ulIPAddress );
}

/**
 * @brief test_FreeRTOS_GetIPAddress_NoValidEndpoints
 * To validate if FreeRTOS_GetIPAddress returns 0 when no IPv4 endpoint.
 */
void test_FreeRTOS_GetIPAddress_NoValidEndpoints( void )
{
    uint32_t ulIPAddress;
    NetworkEndPoint_t xEndPoints[ 2 ]; /* IPv6->IPv6 */

    memset( &xEndPoints[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoints[ 0 ].bits.bIPv6 = pdTRUE;
    memset( &xEndPoints[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoints[ 1 ].bits.bIPv6 = pdTRUE;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoints[ 0 ] );
    FreeRTOS_NextEndPoint_ExpectAndReturn( NULL, &xEndPoints[ 0 ], &xEndPoints[ 1 ] );
    FreeRTOS_NextEndPoint_ExpectAndReturn( NULL, &xEndPoints[ 1 ], NULL );

    ulIPAddress = FreeRTOS_GetIPAddress();

    TEST_ASSERT_EQUAL( 0, ulIPAddress );
}

/**
 * @brief test_CastingFunctions
 * Casting.
 */
void test_CastingFunctions( void )
{
    void * pvPtr;

    const IPPacket_t * pxIPPacket = ( ( const IPPacket_t * ) pvPtr );
    const IPHeader_t * pxIPHeader = ( ( const IPHeader_t * ) pvPtr );
    const TCPPacket_t * pxConstTCPPacket = ( ( const TCPPacket_t * ) pvPtr );
    TCPPacket_t * pxTCPPacket = ( ( TCPPacket_t * ) pvPtr );
    ProtocolPacket_t * pxProtPacket = ( ( ProtocolPacket_t * ) pvPtr );
    const ProtocolPacket_t * pxConstProtPacket = ( ( const ProtocolPacket_t * ) pvPtr );
    const SocketSelect_t * pxSockSelPtr = ( ( const SocketSelect_t * ) pvPtr );
    const SocketSelectMessage_t * pxConstSockSelMsgPtr = ( ( const SocketSelectMessage_t * ) pvPtr );
    SocketSelectMessage_t * pxSockSelMsgPtr = ( ( SocketSelectMessage_t * ) pvPtr );
    NetworkBufferDescriptor_t * pxNetworkBuffer = ( ( NetworkBufferDescriptor_t * ) pvPtr );
    ListItem_t * pxList = ( ( ListItem_t * ) pvPtr );
    const ListItem_t * pxConstList = ( ( const ListItem_t * ) pvPtr );
    const FreeRTOS_Socket_t * pxSocket = ( ( const FreeRTOS_Socket_t * ) pvPtr );
    const ProtocolHeaders_t * pxConstProtHeader = ( ( const ProtocolHeaders_t * ) pvPtr );
    ProtocolHeaders_t * pxProtHeader = ( ( ProtocolHeaders_t * ) pvPtr );
}

/**
 * @brief test_FreeRTOS_IPInit_Multi_NoInterface
 * To validate if FreeRTOS_IPInit_Multi() triggers assertion when no endpoint.
 */
void test_FreeRTOS_IPInit_Multi_NoInterface( void )
{
    FreeRTOS_FirstNetworkInterface_IgnoreAndReturn( NULL );
    catch_assert( FreeRTOS_IPInit_Multi() );
}

/**
 * @brief test_FreeRTOS_GetEndPointConfiguration_AllSettings
 * To validate if FreeRTOS_GetEndPointConfiguration() returns all settings in endpoint.
 */
void test_FreeRTOS_GetEndPointConfiguration_AllSettings( void )
{
    uint32_t ulIPAddress;
    uint32_t ulNetMask;
    uint32_t ulGatewayAddress;
    uint32_t ulDNSServerAddress;
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xEndPoint.ipv4_settings.ulIPAddress = 1;
    xEndPoint.ipv4_settings.ulNetMask = 2;
    xEndPoint.ipv4_settings.ulGatewayAddress = 3;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] = 4;

    FreeRTOS_GetEndPointConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress, &xEndPoint );
    TEST_ASSERT_EQUAL( 1, ulIPAddress );
    TEST_ASSERT_EQUAL( 2, ulNetMask );
    TEST_ASSERT_EQUAL( 3, ulGatewayAddress );
    TEST_ASSERT_EQUAL( 4, ulDNSServerAddress );
}

/**
 * @brief test_FreeRTOS_GetEndPointConfiguration_AllNull
 * To validate if FreeRTOS_GetEndPointConfiguration() supports NULL pointers in API.
 */
void test_FreeRTOS_GetEndPointConfiguration_AllNull( void )
{
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    xEndPoint.ipv4_settings.ulIPAddress = 1;
    xEndPoint.ipv4_settings.ulNetMask = 2;
    xEndPoint.ipv4_settings.ulGatewayAddress = 3;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] = 4;

    FreeRTOS_GetEndPointConfiguration( NULL, NULL, NULL, NULL, &xEndPoint );
}

/**
 * @brief test_FreeRTOS_GetEndPointConfiguration_IPv6Endpoint
 * To validate if FreeRTOS_GetEndPointConfiguration() skips IPv6 endpoint.
 */
void test_FreeRTOS_GetEndPointConfiguration_IPv6Endpoint( void )
{
    uint32_t ulIPAddress = 0;
    uint32_t ulNetMask = 0;
    uint32_t ulGatewayAddress = 0;
    uint32_t ulDNSServerAddress = 0;
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE;

    FreeRTOS_GetEndPointConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress, &xEndPoint );
    TEST_ASSERT_EQUAL( 0, ulIPAddress );
    TEST_ASSERT_EQUAL( 0, ulNetMask );
    TEST_ASSERT_EQUAL( 0, ulGatewayAddress );
    TEST_ASSERT_EQUAL( 0, ulDNSServerAddress );
}

/**
 * @brief test_FreeRTOS_GetEndPointConfiguration_NullEndpoint
 * To validate if FreeRTOS_GetEndPointConfiguration() supports NULL endpoint.
 */
void test_FreeRTOS_GetEndPointConfiguration_NullEndpoint( void )
{
    uint32_t ulIPAddress = 0;
    uint32_t ulNetMask = 0;
    uint32_t ulGatewayAddress = 0;
    uint32_t ulDNSServerAddress = 0;

    FreeRTOS_GetEndPointConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress, NULL );
    TEST_ASSERT_EQUAL( 0, ulIPAddress );
    TEST_ASSERT_EQUAL( 0, ulNetMask );
    TEST_ASSERT_EQUAL( 0, ulGatewayAddress );
    TEST_ASSERT_EQUAL( 0, ulDNSServerAddress );
}

/**
 * @brief test_FreeRTOS_SetEndPointConfiguration_AllSettings
 * To validate if FreeRTOS_SetEndPointConfiguration() sets all settings in endpoint correctly.
 */
void test_FreeRTOS_SetEndPointConfiguration_AllSettings( void )
{
    uint32_t ulIPAddress = 1;
    uint32_t ulNetMask = 2;
    uint32_t ulGatewayAddress = 3;
    uint32_t ulDNSServerAddress = 4;
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    FreeRTOS_SetEndPointConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress, &xEndPoint );
    TEST_ASSERT_EQUAL( 1, xEndPoint.ipv4_settings.ulIPAddress );
    TEST_ASSERT_EQUAL( 2, xEndPoint.ipv4_settings.ulNetMask );
    TEST_ASSERT_EQUAL( 3, xEndPoint.ipv4_settings.ulGatewayAddress );
    TEST_ASSERT_EQUAL( 4, xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] );
}

/**
 * @brief test_FreeRTOS_SetEndPointConfiguration_AllNull
 * To validate if FreeRTOS_SetEndPointConfiguration() supports NULL input.
 */
void test_FreeRTOS_SetEndPointConfiguration_AllNull( void )
{
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    FreeRTOS_SetEndPointConfiguration( NULL, NULL, NULL, NULL, &xEndPoint );
}

/**
 * @brief test_FreeRTOS_SetEndPointConfiguration_IPv6Endpoint
 * To validate if FreeRTOS_SetEndPointConfiguration() returns 0 when endpoint is not IPv4.
 */
void test_FreeRTOS_SetEndPointConfiguration_IPv6Endpoint( void )
{
    uint32_t ulIPAddress = 1;
    uint32_t ulNetMask = 2;
    uint32_t ulGatewayAddress = 3;
    uint32_t ulDNSServerAddress = 4;
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );
    xEndPoint.bits.bIPv6 = pdTRUE;

    FreeRTOS_SetEndPointConfiguration( &ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress, &xEndPoint );
    TEST_ASSERT_EQUAL( 0, xEndPoint.ipv4_settings.ulIPAddress );
    TEST_ASSERT_EQUAL( 0, xEndPoint.ipv4_settings.ulNetMask );
    TEST_ASSERT_EQUAL( 0, xEndPoint.ipv4_settings.ulGatewayAddress );
    TEST_ASSERT_EQUAL( 0, xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] );
}

/**
 * @brief test_FreeRTOS_SetEndPointConfiguration_NullEndpoint
 * To validate if FreeRTOS_SetEndPointConfiguration() supports NULL endpoint.
 */
void test_FreeRTOS_SetEndPointConfiguration_NullEndpoint( void )
{
    FreeRTOS_SetEndPointConfiguration( NULL, NULL, NULL, NULL, NULL );
}

/**
 * @brief test_FreeRTOS_IsNetworkUp
 * To validate if FreeRTOS_IsNetworkUp() returns pdTRUE when
 * the endpoint in global endpoint list is up.
 */
void test_FreeRTOS_IsNetworkUp()
{
    BaseType_t xReturn;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( pxEndpoint, 0, sizeof( xEndpoint ) );
    pxEndpoint->bits.bEndPointUp = pdTRUE;

    pxNetworkEndPoints = pxEndpoint;

    xReturn = FreeRTOS_IsNetworkUp();

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_FreeRTOS_IsEndPointUp
 * To validate if FreeRTOS_IsEndPointUp() returns pdTRUE when
 * input endpoint is up.
 */
void test_FreeRTOS_IsEndPointUp()
{
    BaseType_t xReturn;
    NetworkEndPoint_t xEndpoint, * pxEndpoint = &xEndpoint;

    memset( pxEndpoint, 0, sizeof( xEndpoint ) );
    pxEndpoint->bits.bEndPointUp = pdTRUE;

    xReturn = FreeRTOS_IsEndPointUp( pxEndpoint );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_FreeRTOS_AllEndPointsUp_NoEndpoints
 * To validate if FreeRTOS_AllEndPointsUp() returns pdTRUE when
 * no endpoint stored in global endpoint list.
 */
void test_FreeRTOS_AllEndPointsUp_NoEndpoints()
{
    BaseType_t xReturn;

    xReturn = FreeRTOS_AllEndPointsUp( NULL );

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_FreeRTOS_AllEndPointsUp_SpecificInterface
 * To validate if FreeRTOS_AllEndPointsUp() returns correctly
 * with input interface pointer.
 */
void test_FreeRTOS_AllEndPointsUp_SpecificInterface()
{
    BaseType_t xReturn;
    NetworkEndPoint_t xEndpoint[ 3 ];
    NetworkInterface_t xInterface[ 2 ];

    /* Three endpoints: e0, e1, e2. And 2 interfaces: i0, i1.
     *  - e0: Attach to i0
     *  - e1: Attach to i1, and it's up.
     *  - e2: Attach to i1, and it's down.
     *  */
    memset( &xInterface[ 0 ], 0, sizeof( NetworkInterface_t ) );
    memset( &xInterface[ 1 ], 0, sizeof( NetworkInterface_t ) );

    memset( &xEndpoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    memset( &xEndpoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    memset( &xEndpoint[ 2 ], 0, sizeof( NetworkEndPoint_t ) );

    xEndpoint[ 0 ].pxNetworkInterface = &xInterface[ 0 ];
    xEndpoint[ 0 ].bits.bEndPointUp = pdTRUE;

    xEndpoint[ 1 ].pxNetworkInterface = &xInterface[ 1 ];
    xEndpoint[ 1 ].bits.bEndPointUp = pdTRUE;

    xEndpoint[ 2 ].pxNetworkInterface = &xInterface[ 1 ];
    xEndpoint[ 2 ].bits.bEndPointUp = pdFALSE;

    /* Append e0~e2 into global endpoint list. */
    pxNetworkEndPoints = &xEndpoint[ 0 ];
    pxNetworkEndPoints->pxNext = &xEndpoint[ 1 ];
    pxNetworkEndPoints->pxNext->pxNext = &xEndpoint[ 2 ];

    xReturn = FreeRTOS_AllEndPointsUp( &xInterface[ 1 ] );

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief test_uxIPHeaderSizeSocket_IPv4
 * To validate if uxIPHeaderSizeSocket() returns ipSIZE_OF_IPv4_HEADER
 * when the socket is an IPv4 socket handler.
 */
void test_uxIPHeaderSizeSocket_IPv4()
{
    size_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.bits.bIsIPv6 = pdFALSE;

    xReturn = uxIPHeaderSizeSocket( &xSocket );
    TEST_ASSERT_EQUAL( ipSIZE_OF_IPv4_HEADER, xReturn );
}

/**
 * @brief test_uxIPHeaderSizeSocket_NullSocket
 * To validate if uxIPHeaderSizeSocket() returns ipSIZE_OF_IPv4_HEADER
 * when input socket is NULL.
 */
void test_uxIPHeaderSizeSocket_NullSocket()
{
    size_t xReturn;

    xReturn = uxIPHeaderSizeSocket( NULL );
    TEST_ASSERT_EQUAL( ipSIZE_OF_IPv4_HEADER, xReturn );
}

/**
 * @brief test_uxIPHeaderSizeSocket_IPv6
 * To validate if uxIPHeaderSizeSocket() returns ipSIZE_OF_IPv6_HEADER
 * when input socket is an IPv6 handler.
 */
void test_uxIPHeaderSizeSocket_IPv6()
{
    size_t xReturn;
    FreeRTOS_Socket_t xSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    xSocket.bits.bIsIPv6 = pdTRUE;

    xReturn = uxIPHeaderSizeSocket( &xSocket );
    TEST_ASSERT_EQUAL( ipSIZE_OF_IPv6_HEADER, xReturn );
}

static void pfAddAllowedMAC( struct xNetworkInterface * pxInterface,
                             const uint8_t * pucMacAddress )
{
    xMACFunctionCalled = pdTRUE;
}

static BaseType_t xNetworkInterfaceInitialise_returnTrue( NetworkInterface_t * xInterface )
{
    return pdTRUE;
}

/**
 * @brief test_prvProcessNetworkDownEvent_Fail
 * To validate if prvProcessNetworkDownEvent skips hook and DHCP
 * when bCallDownHook & bWantDHCP are both disabled.
 */
static void prvIPNetworkUpCalls_Generic( const uint8_t * pucAddress,
                                         IPv6_Type_t eType,
                                         UBaseType_t uxSetMembers )
{
    NetworkInterface_t xInterface = { 0 };
    NetworkEndPoint_t xEndPoint = { 0 };
    BaseType_t xMACAddExpected = pdFALSE;

    xInterfaces[ 0 ].pfInitialise = &xNetworkInterfaceInitialise_returnTrue;
    xInterfaces[ 0 ].pxEndPoint = &xEndPoint;

    xEndPoint.bits.bEndPointUp = pdFALSE;
    xEndPoint.bits.bCallDownHook = pdFALSE_UNSIGNED;
    xEndPoint.bits.bWantDHCP = pdFALSE_UNSIGNED;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, pucAddress, ipSIZE_OF_IPv6_ADDRESS );

    if( ( uxSetMembers & ipHAS_INTERFACE ) != 0U )
    {
        xEndPoint.pxNetworkInterface = &xInterface;
    }

    if( ( uxSetMembers & ipHAS_IPV6 ) != 0U )
    {
        xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    }

    xMACFunctionCalled = pdFALSE;

    if( ( ( eType == eIPv6_LinkLocal ) || ( eType == eIPv6_SiteLocal ) || ( eType == eIPv6_Global ) ) &&
        ( xInterface.pfAddAllowedMAC != NULL ) &&
        ( xEndPoint.pxNetworkInterface != NULL ) &&
        ( xEndPoint.bits.bIPv6 == pdTRUE_UNSIGNED ) )
    {
        xMACAddExpected = pdTRUE;
    }

    if( xEndPoint.bits.bIPv6 == pdTRUE_UNSIGNED )
    {
        /* The vManageSolicitedNodeAddress() function is mocked. */
        vManageSolicitedNodeAddress_Expect( &xEndPoint, pdTRUE );
    }

    vApplicationIPNetworkEventHook_Multi_Expect( eNetworkUp, &xEndPoint );
    vDNSInitialise_Expect();
    vARPTimerReload_Expect( pdMS_TO_TICKS( 10000 ) );

    vIPNetworkUpCalls( &xEndPoint );

    TEST_ASSERT_EQUAL( pdTRUE, xEndPoint.bits.bEndPointUp );
}

void test_prvIPNetworkUpCalls_LinkLocal()
{
    /* Use the local-link address fe80::7009 */
    static const uint8_t ucAddress[ 16 ] =
    {
        0xFEU, 0x80U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x70U, 0x09U
    };

    /* Test all combinations of what might go wrong. */
    prvIPNetworkUpCalls_Generic( ucAddress, eIPv6_LinkLocal, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvIPNetworkUpCalls_Generic( ucAddress, eIPv6_LinkLocal, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvIPNetworkUpCalls_Generic( ucAddress, eIPv6_LinkLocal, ipHAS_IPV6 );
    prvIPNetworkUpCalls_Generic( ucAddress, eIPv6_LinkLocal, ipHAS_INTERFACE );
}

void test_prvIPNetworkUpCalls_Global()
{
    /* Use the local-link address "2001:0470:ed44::7009" */
    static const uint8_t ucAddress[ 16 ] =
    {
        0x20U, 0x01U,
        0x04U, 0x70U,
        0xEDU, 0x44U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x70U, 0x09U
    };

    prvIPNetworkUpCalls_Generic( ucAddress, eIPv6_Global, ipHAS_IPV6 | ipHAS_METHOD | ipHAS_INTERFACE );
    prvIPNetworkUpCalls_Generic( ucAddress, eIPv6_Global, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvIPNetworkUpCalls_Generic( ucAddress, eIPv6_Global, ipHAS_IPV6 | ipHAS_METHOD );
}

void test_prvIPNetworkUpCalls_SiteLocal()
{
    /* Use the local-link address "fec0::7009" */
    static const uint8_t ucAddress[ 16 ] =
    {
        0xFEU, 0xC0U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x70U, 0x09U
    };

    prvIPNetworkUpCalls_Generic( ucAddress, eIPv6_SiteLocal, ipHAS_IPV6 | ipHAS_METHOD | ipHAS_INTERFACE );
    prvIPNetworkUpCalls_Generic( ucAddress, eIPv6_SiteLocal, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvIPNetworkUpCalls_Generic( ucAddress, eIPv6_SiteLocal, ipHAS_IPV6 | ipHAS_METHOD );
}

void test_prvIPNetworkUpCalls_Multicast()
{
    /* Use the multicast address "ff02::fb",
     * just for the coverage of vIPNetworkUpCalls(). */
    static const uint8_t ucAddress[ 16 ] =
    {
        0xFFU, 0x02U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0x00U,
        0x00U, 0xFBU
    };

    prvIPNetworkUpCalls_Generic( ucAddress, eIPv6_Multicast, ipHAS_IPV6 | ipHAS_METHOD | ipHAS_INTERFACE );
}
