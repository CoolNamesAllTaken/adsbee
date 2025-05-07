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
#include "mock_IP_Utils_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_DHCPv6.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_IPv4_Utils.h"
#include "mock_FreeRTOS_IPv6_Utils.h"
#include "mock_NetworkBufferManagement.h"

#include "FreeRTOS_IP_Utils.h"

#include "FreeRTOS_IP_Utils_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* =========================== EXTERN VARIABLES =========================== */

#define TEST_UDP_PAYLOAD_LENGTH    ( 10U )

extern NetworkInterface_t xInterfaces[ 1 ];

#if ( ipconfigUSE_NETWORK_EVENT_HOOK == 1 )
    extern BaseType_t xCallEventHook;
#endif

extern UBaseType_t uxLastMinBufferCount;
extern size_t uxMinLastSize;

extern NetworkBufferDescriptor_t * prvPacketBuffer_to_NetworkBuffer( const void * pvBuffer,
                                                                     size_t uxOffset );
extern uint16_t prvGetChecksumFromPacket( const struct xPacketSummary * pxSet );
extern void prvSetChecksumInPacket( const struct xPacketSummary * pxSet,
                                    uint16_t usChecksum );

/* This variable will be set when pfRemoveAllowedMAC() is called by prvProcessNetworkDownEvent(). */
static BaseType_t xMACFunctionCalled;

/* An implementation of pfRemoveAllowedMAC() */
static void pfRemoveAllowedMAC( struct xNetworkInterface * pxInterface,
                                const uint8_t * pucMacAddress );

/* Testing all situations for prvProcessNetworkDownEvent() to increase coverage. */
#define ipHAS_METHOD       0x01U
#define ipHAS_INTERFACE    0x02U
#define ipHAS_IPV6         0x04U

/* ============================== Test Cases ============================== */

/**
 * @brief test_xSendDHCPEvent
 * To validate if xSendDHCPEvent returns correct result.
 */
void test_xSendDHCPEvent( void )
{
    BaseType_t xReturn, xResult = 0x123;
    struct xNetworkEndPoint xEndPoint = { 0 };

    xEndPoint.xDHCPData.eDHCPState = eInitialWait;

    xSendEventStructToIPTask_ExpectAnyArgsAndReturn( xResult );

    xReturn = xSendDHCPEvent( &xEndPoint );

    TEST_ASSERT_EQUAL( xResult, xReturn );
    TEST_ASSERT_EQUAL( eInitialWait, xEndPoint.xDHCPData.eExpectedState );
}

/**
 * @brief test_pxDuplicateNetworkBufferWithDescriptor_NULLReturned
 * To validate if pxDuplicateNetworkBufferWithDescriptor returns NULL when
 * it's not able to allocate a new network buffer.
 */
void test_pxDuplicateNetworkBufferWithDescriptor_NULLReturned( void )
{
    NetworkBufferDescriptor_t * pxReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    size_t uxNewLength;

    pxNetworkBuffer = &xNetworkBuffer;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNewLength, 0, NULL );

    pxReturn = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, uxNewLength );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief test_pxDuplicateNetworkBufferWithDescriptor_LargerBufferReturned
 * To validate if pxDuplicateNetworkBufferWithDescriptor returns a network buffer
 * with larger content size.
 */
void test_pxDuplicateNetworkBufferWithDescriptor_LargerBufferReturned( void )
{
    NetworkBufferDescriptor_t * pxReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer, xNetworkBuffer2;
    size_t uxNewLength = 0x345;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    uint8_t ucEthBuffer2[ ipconfigTCP_MSS ];

    pxNetworkBuffer = &xNetworkBuffer;
    memset( &xNetworkBuffer2, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAB, ipconfigTCP_MSS );
    xNetworkBuffer2.pucEthernetBuffer = ucEthBuffer2;
    memset( ucEthBuffer2, 0x00, ipconfigTCP_MSS );

    pxNetworkBuffer->xDataLength = 0x123;
    pxNetworkBuffer->xIPAddress.ulIP_IPv4 = 0xABCDEF56;
    pxNetworkBuffer->usPort = 0x1234;
    pxNetworkBuffer->usBoundPort = 0xFFAA;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNewLength, 0, &xNetworkBuffer2 );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    pxReturn = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, uxNewLength );

    TEST_ASSERT_EQUAL( &xNetworkBuffer2, pxReturn );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.xDataLength, uxNewLength );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.xIPAddress.ulIP_IPv4, pxNetworkBuffer->xIPAddress.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.usPort, pxNetworkBuffer->usPort );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.usBoundPort, pxNetworkBuffer->usBoundPort );
    TEST_ASSERT_EQUAL_MEMORY( pxNetworkBuffer->pucEthernetBuffer, xNetworkBuffer2.pucEthernetBuffer, pxNetworkBuffer->xDataLength );
}

/**
 * @brief test_pxDuplicateNetworkBufferWithDescriptor_SmallerBufferReturned
 * To validate if pxDuplicateNetworkBufferWithDescriptor returns a network buffer
 * with smaller content size.
 */
void test_pxDuplicateNetworkBufferWithDescriptor_SmallerBufferReturned( void )
{
    NetworkBufferDescriptor_t * pxReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer, xNetworkBuffer2;
    size_t uxNewLength = 0x34;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    uint8_t ucEthBuffer2[ ipconfigTCP_MSS ];

    pxNetworkBuffer = &xNetworkBuffer;
    memset( &xNetworkBuffer2, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAB, ipconfigTCP_MSS );
    xNetworkBuffer2.pucEthernetBuffer = ucEthBuffer2;
    memset( ucEthBuffer2, 0x00, ipconfigTCP_MSS );

    pxNetworkBuffer->xDataLength = 0x123;
    pxNetworkBuffer->xIPAddress.ulIP_IPv4 = 0xABCDEF56;
    pxNetworkBuffer->usPort = 0x1234;
    pxNetworkBuffer->usBoundPort = 0xFFAA;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNewLength, 0, &xNetworkBuffer2 );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    pxReturn = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, uxNewLength );

    TEST_ASSERT_EQUAL( &xNetworkBuffer2, pxReturn );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.xDataLength, uxNewLength );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.xIPAddress.ulIP_IPv4, pxNetworkBuffer->xIPAddress.ulIP_IPv4 );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.usPort, pxNetworkBuffer->usPort );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.usBoundPort, pxNetworkBuffer->usBoundPort );
    TEST_ASSERT_EQUAL_MEMORY( pxNetworkBuffer->pucEthernetBuffer, xNetworkBuffer2.pucEthernetBuffer, uxNewLength );
}

/**
 * @brief test_pxDuplicateNetworkBufferWithDescriptor_NullBufferReturned
 * To validate if pxDuplicateNetworkBufferWithDescriptor returns a network buffer
 * with NULL content pointer.
 */
void test_pxDuplicateNetworkBufferWithDescriptor_NullBufferReturned( void )
{
    NetworkBufferDescriptor_t * pxReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer, xNetworkBuffer2;
    size_t uxNewLength = 0x34;

    pxNetworkBuffer = &xNetworkBuffer;
    memset( &xNetworkBuffer2, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = NULL;

    pxNetworkBuffer->xDataLength = uxNewLength;
    pxNetworkBuffer->xIPAddress.ulIP_IPv4 = 0xABCDEF56;
    pxNetworkBuffer->usPort = 0x1234;
    pxNetworkBuffer->usBoundPort = 0xFFAA;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNewLength, 0, pxNetworkBuffer );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    catch_assert( pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, uxNewLength ) );
}

/**
 * @brief test_pxDuplicateNetworkBufferWithDescriptor_IPv6
 * To validate if pxDuplicateNetworkBufferWithDescriptor returns a network buffer
 * for IPv6 packet.
 */
void test_pxDuplicateNetworkBufferWithDescriptor_IPv6( void )
{
    NetworkBufferDescriptor_t * pxReturn;
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer, xNetworkBuffer2;
    size_t uxNewLength = ipconfigTCP_MSS;
    uint8_t ucEthBuffer[ ipconfigTCP_MSS ];
    uint8_t ucEthBuffer2[ ipconfigTCP_MSS ];
    IPv6_Address_t xIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

    pxNetworkBuffer = &xNetworkBuffer;
    memset( &xNetworkBuffer2, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer->pucEthernetBuffer = ucEthBuffer;
    memset( ucEthBuffer, 0xAB, ipconfigTCP_MSS );
    xNetworkBuffer2.pucEthernetBuffer = ucEthBuffer2;
    memset( ucEthBuffer2, 0x00, ipconfigTCP_MSS );

    pxNetworkBuffer->xDataLength = uxNewLength;
    memcpy( pxNetworkBuffer->xIPAddress.xIP_IPv6.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    pxNetworkBuffer->usPort = 0x1234;
    pxNetworkBuffer->usBoundPort = 0xFFAA;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( uxNewLength, 0, &xNetworkBuffer2 );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv6_HEADER );

    pxReturn = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, uxNewLength );

    TEST_ASSERT_EQUAL( &xNetworkBuffer2, pxReturn );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.xDataLength, uxNewLength );
    TEST_ASSERT_EQUAL_MEMORY( &xIPv6Address, &pxNetworkBuffer->xIPAddress.xIP_IPv6, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.usPort, pxNetworkBuffer->usPort );
    TEST_ASSERT_EQUAL( xNetworkBuffer2.usBoundPort, pxNetworkBuffer->usBoundPort );
    TEST_ASSERT_EQUAL_MEMORY( pxNetworkBuffer->pucEthernetBuffer, xNetworkBuffer2.pucEthernetBuffer, pxNetworkBuffer->xDataLength );
}

/**
 * @brief test_prvPacketBuffer_to_NetworkBuffer_NULLParam
 * To validate if prvPacketBuffer_to_NetworkBuffer returns NULL
 * when input buffer pointer is NULL.
 */
void test_prvPacketBuffer_to_NetworkBuffer_NULLParam( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;
    const void * pvBuffer = NULL;
    size_t uxOffset;

    pxNetworkBuffer = prvPacketBuffer_to_NetworkBuffer( pvBuffer, uxOffset );

    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
}

/**
 * @brief test_prvPacketBuffer_to_NetworkBuffer_Unaligned
 * To validate if prvPacketBuffer_to_NetworkBuffer returns NULL when byte not aligned.
 */
void test_prvPacketBuffer_to_NetworkBuffer_Unaligned( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetBufferToReturn;
    const void * pvBuffer;
    size_t uxOffset = 12;
    uint8_t ucEthBuf[ ipconfigTCP_MSS ];
    uintptr_t uxAddrOfNetBuffer = ( uintptr_t ) &xNetBufferToReturn;

    memcpy( ucEthBuf, &uxAddrOfNetBuffer, sizeof( uintptr_t ) );
    pvBuffer = ( const void * ) ( uxAddrOfNetBuffer + uxOffset + ipBUFFER_PADDING + 1 );

    pxNetworkBuffer = prvPacketBuffer_to_NetworkBuffer( pvBuffer, uxOffset );

    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
}

/**
 * @brief test_prvPacketBuffer_to_NetworkBuffer_Unaligned
 * To validate if prvPacketBuffer_to_NetworkBuffer moves offset&padding correctly.
 */
void test_prvPacketBuffer_to_NetworkBuffer_Aligned( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetBufferToReturn;
    const void * pvBuffer;
    size_t uxOffset = 20;
    uint8_t ucEthBuf[ ipBUFFER_PADDING + ipconfigTCP_MSS ];
    NetworkBufferDescriptor_t * pxAddrOfNetBuffer = &xNetBufferToReturn;

    pxAddrOfNetBuffer->pucEthernetBuffer = ucEthBuf;

    *( ( NetworkBufferDescriptor_t ** ) pxAddrOfNetBuffer->pucEthernetBuffer ) = pxAddrOfNetBuffer;

    pxAddrOfNetBuffer->pucEthernetBuffer += ( uxOffset + ipBUFFER_PADDING );

    pxNetworkBuffer = prvPacketBuffer_to_NetworkBuffer( pxAddrOfNetBuffer->pucEthernetBuffer, uxOffset );

    TEST_ASSERT_EQUAL_PTR( pxAddrOfNetBuffer, pxNetworkBuffer );
}

/**
 * @brief test_pxUDPPayloadBuffer_to_NetworkBuffer
 * To validate if pxUDPPayloadBuffer_to_NetworkBuffer returns correct network buffer pointer
 * for an IPv4 UDP packet.
 */
void test_pxUDPPayloadBuffer_to_NetworkBuffer( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetBufferToReturn;
    const void * pvBuffer;
    size_t uxOffset = sizeof( UDPPacket_t );
    uint8_t ucEthBuf[ ipBUFFER_PADDING + ipconfigTCP_MSS ];
    uint8_t * pucIPType;
    NetworkBufferDescriptor_t * pxAddrOfNetBuffer = &xNetBufferToReturn;

    pxAddrOfNetBuffer->pucEthernetBuffer = ucEthBuf;

    *( ( NetworkBufferDescriptor_t ** ) pxAddrOfNetBuffer->pucEthernetBuffer ) = pxAddrOfNetBuffer;

    pxAddrOfNetBuffer->pucEthernetBuffer += ( uxOffset + ipBUFFER_PADDING );

    pucIPType = ( pxAddrOfNetBuffer->pucEthernetBuffer ) - ipUDP_PAYLOAD_IP_TYPE_OFFSET;
    *pucIPType = ( uint8_t ) ipTYPE_IPv4;

    pxNetworkBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pxAddrOfNetBuffer->pucEthernetBuffer );

    TEST_ASSERT_EQUAL_PTR( pxAddrOfNetBuffer, pxNetworkBuffer );
}

/**
 * @brief test_pxUDPPayloadBuffer_to_NetworkBuffer_NullInput
 * To validate if pxUDPPayloadBuffer_to_NetworkBuffer returns NULL when input is NULL.
 */
void test_pxUDPPayloadBuffer_to_NetworkBuffer_NullInput( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer;

    pxNetworkBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( NULL );

    TEST_ASSERT_EQUAL( NULL, pxNetworkBuffer );
}

/**
 * @brief test_pxUDPPayloadBuffer_to_NetworkBuffer_UnknownIPType
 * To validate if pxUDPPayloadBuffer_to_NetworkBuffer triggers assertion when IP type of buffer is unknown.
 */
void test_pxUDPPayloadBuffer_to_NetworkBuffer_UnknownIPType( void )
{
    NetworkBufferDescriptor_t * pxNetBufferToReturn, xNetBufferToReturn;
    size_t uxOffset = sizeof( UDPPacket_t );
    uint8_t ucEthBuf[ ipBUFFER_PADDING + ipconfigTCP_MSS ];
    uint8_t * pucIPType;

    memset( ucEthBuf, 0, sizeof( ucEthBuf ) );
    memset( &xNetBufferToReturn, 0, sizeof( xNetBufferToReturn ) );

    pxNetBufferToReturn = &xNetBufferToReturn;

    pxNetBufferToReturn->pucEthernetBuffer = ucEthBuf;

    *( ( NetworkBufferDescriptor_t ** ) pxNetBufferToReturn->pucEthernetBuffer ) = pxNetBufferToReturn;

    pxNetBufferToReturn->pucEthernetBuffer += ( uxOffset + ipBUFFER_PADDING );

    pucIPType = ( pxNetBufferToReturn->pucEthernetBuffer ) - ipUDP_PAYLOAD_IP_TYPE_OFFSET;
    *pucIPType = 0xFF;

    catch_assert( pxUDPPayloadBuffer_to_NetworkBuffer( pxNetBufferToReturn->pucEthernetBuffer ) );
}

/**
 * @brief test_pxUDPPayloadBuffer_to_NetworkBuffer_IPv6
 * To validate if pxUDPPayloadBuffer_to_NetworkBuffer returns correct pointer to the network buffer.
 */
void test_pxUDPPayloadBuffer_to_NetworkBuffer_IPv6( void )
{
    NetworkBufferDescriptor_t * pxNetBufferToReturn, xNetBufferToReturn;
    size_t uxOffset = sizeof( UDPPacket_IPv6_t );
    uint8_t ucEthBuf[ ipBUFFER_PADDING + ipconfigTCP_MSS ];
    uint8_t * pucIPType;
    uint8_t * pucPayloadBuffer;
    NetworkBufferDescriptor_t * pxNetworkBuffer;

    memset( ucEthBuf, 0, sizeof( ucEthBuf ) );
    memset( &xNetBufferToReturn, 0, sizeof( xNetBufferToReturn ) );

    pxNetBufferToReturn = &xNetBufferToReturn;

    pxNetBufferToReturn->pucEthernetBuffer = ucEthBuf;

    *( ( NetworkBufferDescriptor_t ** ) pxNetBufferToReturn->pucEthernetBuffer ) = pxNetBufferToReturn;

    pucPayloadBuffer = &ucEthBuf[ uxOffset + ipBUFFER_PADDING ];

    pucIPType = pucPayloadBuffer - ipUDP_PAYLOAD_IP_TYPE_OFFSET;
    *pucIPType = ipTYPE_IPv6;

    pxNetworkBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pucPayloadBuffer );

    TEST_ASSERT_EQUAL( pxNetBufferToReturn, pxNetworkBuffer );
}

/**
 * @brief test_xIsCallingFromIPTask_NotCallingFromIPTask
 * To validate if xIsCallingFromIPTask returns pdFALSE when task handles are different.
 */
void test_xIsCallingFromIPTask_NotCallingFromIPTask( void )
{
    BaseType_t xReturn;
    TaskHandle_t xHandleOfIPTask = ( TaskHandle_t ) 0xAABBCCDD, xHandleOfNotIPTask = ( TaskHandle_t ) 0xAABBCCDE;

    xTaskGetCurrentTaskHandle_ExpectAndReturn( xHandleOfNotIPTask );
    FreeRTOS_GetIPTaskHandle_ExpectAndReturn( xHandleOfIPTask );

    xReturn = xIsCallingFromIPTask();

    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
}

/**
 * @brief test_xIsCallingFromIPTask_IsCallingFromIPTask
 * To validate if xIsCallingFromIPTask returns pdTRUE when task handles are same.
 */
void test_xIsCallingFromIPTask_IsCallingFromIPTask( void )
{
    BaseType_t xReturn;
    TaskHandle_t xHandleOfIPTask = ( TaskHandle_t ) 0xAABBCCDD;

    xTaskGetCurrentTaskHandle_ExpectAndReturn( xHandleOfIPTask );
    FreeRTOS_GetIPTaskHandle_ExpectAndReturn( xHandleOfIPTask );

    xReturn = xIsCallingFromIPTask();

    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief test_prvProcessNetworkDownEvent_Pass
 * First prvProcessNetworkDownEvent call to validate if network down event reset
 * endpoint's state. And second prvProcessNetworkDownEvent call to validate if it calls
 * user's hook.
 */
void test_prvProcessNetworkDownEvent_Pass( void )
{
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint = { 0 };

    xCallEventHook = pdFALSE;
    xInterfaces[ 0 ].pfInitialise = &xNetworkInterfaceInitialise_returnTrue;
    xEndPoint.bits.bWantDHCP = pdTRUE_UNSIGNED;
    xEndPoint.bits.bCallDownHook = pdFALSE_UNSIGNED;

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    FreeRTOS_ClearARP_ExpectAnyArgs();

    vDHCPStop_Expect( &xEndPoint );

    vDHCPProcess_Expect( pdTRUE, &xEndPoint );

    prvProcessNetworkDownEvent( &xInterfaces[ 0 ] );

    /* Run again to trigger a different path in the code. */

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    vApplicationIPNetworkEventHook_Multi_Expect( eNetworkDown, &xEndPoint );

    FreeRTOS_ClearARP_Expect( &xEndPoint );

    vDHCPStop_Expect( &xEndPoint );

    vDHCPProcess_Expect( pdTRUE, &xEndPoint );

    prvProcessNetworkDownEvent( &xInterfaces[ 0 ] );
}

/**
 * @brief test_prvProcessNetworkDownEvent_Fail
 * To validate if prvProcessNetworkDownEvent skips hook and DHCP
 * when bCallDownHook & bWantDHCP are both disabled.
 */
void test_prvProcessNetworkDownEvent_Fail( void )
{
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint = { 0 };

    xCallEventHook = pdFALSE;
    xInterfaces[ 0 ].pfInitialise = &xNetworkInterfaceInitialise_returnTrue;
    xEndPoint.bits.bCallDownHook = pdFALSE_UNSIGNED;
    xEndPoint.bits.bWantDHCP = pdFALSE_UNSIGNED;

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    FreeRTOS_ClearARP_Expect( &xEndPoint );

    vIPNetworkUpCalls_Expect( &xEndPoint );

    prvProcessNetworkDownEvent( &xInterfaces[ 0 ] );
}

/**
 * @brief test_prvProcessNetworkDownEvent_NullInterface
 * To validate if prvProcessNetworkDownEvent triggers assertion when
 * input interface is NULL pointer.
 */
void test_prvProcessNetworkDownEvent_NullInterface( void )
{
    catch_assert( prvProcessNetworkDownEvent( NULL ) );
}

/**
 * @brief test_prvProcessNetworkDownEvent_NullInitialFunction
 * To validate if prvProcessNetworkDownEvent triggers assertion when
 * initialize function pointer of input interface is NULL.
 */
void test_prvProcessNetworkDownEvent_NullInitialFunction( void )
{
    NetworkInterface_t xInterface;

    xInterface.pfInitialise = NULL;

    catch_assert( prvProcessNetworkDownEvent( &xInterface ) );
}

/**
 * @brief test_prvProcessNetworkDownEvent_InterfaceInitFail
 * To validate if prvProcessNetworkDownEvent skips the following calls
 * after interface initialization when it returns false.
 */
void test_prvProcessNetworkDownEvent_InterfaceInitFail( void )
{
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint = { 0 };

    xCallEventHook = pdFALSE;
    xInterface.pfInitialise = &xNetworkInterfaceInitialise_returnFalse;
    xEndPoint.bits.bWantDHCP = pdTRUE_UNSIGNED;
    xEndPoint.bits.bCallDownHook = pdFALSE_UNSIGNED;

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    FreeRTOS_ClearARP_ExpectAnyArgs();

    vDHCPStop_Expect( &xEndPoint );

    vSetAllNetworksUp_Expect( pdFALSE );

    prvProcessNetworkDownEvent( &xInterface );
}

/**
 * @brief test_prvProcessNetworkDownEvent_PassDHCPv6
 * To validate if prvProcessNetworkDownEvent runs DHCPv6 flow when
 * the endpoint is configured for it.
 */
void test_prvProcessNetworkDownEvent_PassDHCPv6( void )
{
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint = { 0 };

    xCallEventHook = pdFALSE;
    xInterface.pfInitialise = &xNetworkInterfaceInitialise_returnTrue;
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xEndPoint.bits.bWantDHCP = pdTRUE_UNSIGNED;
    xEndPoint.bits.bCallDownHook = pdFALSE_UNSIGNED;

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );

    if( xEndPoint.bits.bIPv6 == pdTRUE_UNSIGNED )
    {
        /* The vManageSolicitedNodeAddress() function is mocked. */
        vManageSolicitedNodeAddress_Expect( &xEndPoint, pdFALSE );
    }

    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    FreeRTOS_ClearARP_ExpectAnyArgs();

    vDHCPv6Stop_Expect( &xEndPoint );

    vDHCPv6Process_Expect( pdTRUE, &xEndPoint );

    prvProcessNetworkDownEvent( &xInterface );
}

/**
 * @brief test_prvProcessNetworkDownEvent_PassRA
 * To validate if prvProcessNetworkDownEvent runs RA flow when
 * the endpoint is configured for it.
 */
void test_prvProcessNetworkDownEvent_PassRA( void )
{
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint = { 0 };

    xCallEventHook = pdFALSE;
    xInterface.pfInitialise = &xNetworkInterfaceInitialise_returnTrue;
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xEndPoint.bits.bWantRA = pdTRUE_UNSIGNED;
    xEndPoint.bits.bCallDownHook = pdFALSE_UNSIGNED;

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );

    if( xEndPoint.bits.bIPv6 == pdTRUE_UNSIGNED )
    {
        /* The vManageSolicitedNodeAddress() function is mocked. */
        vManageSolicitedNodeAddress_Expect( &xEndPoint, pdFALSE );
    }

    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    FreeRTOS_ClearARP_ExpectAnyArgs();

    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );

    vRAProcess_Expect( pdTRUE, &xEndPoint );

    prvProcessNetworkDownEvent( &xInterface );
}

/**
 * @brief test_prvProcessNetworkDownEvent_PassStaticIP
 * To validate if prvProcessNetworkDownEvent sets static IP address to endpoint.
 */
void test_prvProcessNetworkDownEvent_PassStaticIP( void )
{
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint = { 0 };
    IPv6_Address_t xIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

    xCallEventHook = pdFALSE;
    xInterface.pfInitialise = &xNetworkInterfaceInitialise_returnTrue;
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xEndPoint.bits.bWantRA = pdFALSE_UNSIGNED;
    xEndPoint.bits.bWantDHCP = pdFALSE_UNSIGNED;
    xEndPoint.bits.bCallDownHook = pdFALSE_UNSIGNED;
    memcpy( xEndPoint.ipv6_defaults.xIPAddress.ucBytes, xIPv6Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );

    if( xEndPoint.bits.bIPv6 == pdTRUE_UNSIGNED )
    {
        /* The vManageSolicitedNodeAddress() function is mocked. */
        vManageSolicitedNodeAddress_Expect( &xEndPoint, pdFALSE );
    }

    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    FreeRTOS_ClearARP_ExpectAnyArgs();

    vIPNetworkUpCalls_Expect( &xEndPoint );

    prvProcessNetworkDownEvent( &xInterface );

    TEST_ASSERT_EQUAL_MEMORY( xIPv6Address.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief test_vPreCheckConfigs_CatchAssertTaskNotReady
 * To validate if vPreCheckConfigs triggers assertion when IP task is not ready.
 */
void test_vPreCheckConfigs_CatchAssertTaskNotReady( void )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdTRUE );

    catch_assert( vPreCheckConfigs() );
}

/**
 * @brief test_vPreCheckConfigs_CatchAssertNonEmptyEventQueue
 * To validate if vPreCheckConfigs triggers assertion when network event queue is not NULL.
 */
void test_vPreCheckConfigs_CatchAssertNonEmptyEventQueue( void )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );
    xNetworkEventQueue = ( QueueHandle_t ) 0xAABBCCDD;

    catch_assert( vPreCheckConfigs() );
}

/**
 * @brief test_vPreCheckConfigs_CatchAssertNonNullTaskHandle
 * To validate if vPreCheckConfigs triggers assertion when task handle is not NULL.
 */
void test_vPreCheckConfigs_CatchAssertNonNullTaskHandle( void )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );
    xNetworkEventQueue = NULL;
    FreeRTOS_GetIPTaskHandle_ExpectAndReturn( ( TaskHandle_t ) 0xAABBCCDD );

    catch_assert( vPreCheckConfigs() );
}

/**
 * @brief test_vPreCheckConfigs
 * To validate vPreCheckConfigs pass path.
 */
void test_vPreCheckConfigs( void )
{
    xIPIsNetworkTaskReady_ExpectAndReturn( pdFALSE );
    xNetworkEventQueue = NULL;
    FreeRTOS_GetIPTaskHandle_ExpectAndReturn( ( TaskHandle_t ) 0x00 );

    vPreCheckConfigs();
}

/**
 * @brief test_usGenerateProtocolChecksum_UnknownProtocol
 * To validate usGenerateProtocolChecksum returns ipUNHANDLED_PROTOCOL if no valid protocol in IP header.
 */
void test_usGenerateProtocolChecksum_UnknownProtocol( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );
    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;

    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xTCPPacket.xTCPHeader.ucTCPOffset = 0x50;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_UnknownProtocol );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipUNHANDLED_PROTOCOL, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_InvalidLength
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if prvChecksumIPv4Checks returns non-zero.
 */
void test_usGenerateProtocolChecksum_InvalidLength( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = sizeof( IPPacket_t ) - 1;
    BaseType_t xOutgoingPacket;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );
    ( ( IPPacket_t * ) pucEthernetBuffer )->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_InvalidLength );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( usReturn, ipINVALID_LENGTH );
}

/**
 * @brief test_usGenerateProtocolChecksum_UDPInvalidLength
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * length in IP header is less than UDP header size.
 */
void test_usGenerateProtocolChecksum_UDPInvalidLength( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER - 1;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_UDPWrongCRCIncomingPacket
 * To validate usGenerateProtocolChecksum returns ipWRONG_CRC if
 * UDP checksum is zero and ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS is 0.
 */
void test_usGenerateProtocolChecksum_UDPWrongCRCIncomingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength + ipSIZE_OF_UDP_HEADER + TEST_UDP_PAYLOAD_LENGTH;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_UDPOutgoingPacketLessProtocolLength
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * length in IP header is less than UDP header size.
 */
void test_usGenerateProtocolChecksum_UDPOutgoingPacketLessProtocolLength( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 10;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_UDPNonZeroChecksum
 * To validate usGenerateProtocolChecksum returns ipWRONG_CRC if
 * CRC in UDP header is wrong.
 */
void test_usGenerateProtocolChecksum_UDPNonZeroChecksum( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength + ipSIZE_OF_UDP_HEADER + TEST_UDP_PAYLOAD_LENGTH;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x1234;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_UDPCorrectCRCOutgoingPacket
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC if
 * it's a outgoing packet. And set the checksum to 0xFFFF because the calculated checksum was zero.
 */
void test_usGenerateProtocolChecksum_UDPCorrectCRCOutgoingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    /* This is the checksum with zeroed out data. Fill it in to make the checksum 0. */
    *( ( uint32_t * ) &pucEthernetBuffer[ usLength - sizeof( uint32_t ) ] ) = FreeRTOS_htonl( 0xFF9E );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x00;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
    TEST_ASSERT_EQUAL( 0xFFFF, pxProtPack->xUDPPacket.xUDPHeader.usChecksum );
}

/**
 * @brief test_usGenerateProtocolChecksum_UDPLessBufferSizeOutgoingPacket
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * buffer size is less than minimum requirement.
 */
void test_usGenerateProtocolChecksum_UDPLessBufferSizeOutgoingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ucVersionHeaderLength + ipSIZE_OF_UDP_HEADER - 1;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x00;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_UDPCorrectCRC
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC if
 * it's a incoming packet.
 */
void test_usGenerateProtocolChecksum_UDPCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x9EFF;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_UDPIncorrectCRC
 * To validate usGenerateProtocolChecksum returns ipWRONG_CRC if
 * checksum in UDP header is wrong.
 */
void test_usGenerateProtocolChecksum_UDPIncorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_UDP;

    pxProtPack->xUDPPacket.xUDPHeader.usChecksum = 0x01;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPCorrectCRC
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC if
 * checksum in TCP header is correct.
 */
void test_usGenerateProtocolChecksum_TCPCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xTCPPacket.xTCPHeader.ucTCPOffset = 0x50;
    pxProtPack->xTCPPacket.xTCPHeader.usChecksum = 0xA9AF;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPCorrectCRCOutgoingPacket
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC when it
 * generates correct CRC in TCP checksum.
 */
void test_usGenerateProtocolChecksum_TCPCorrectCRCOutgoingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    /* This is the checksum with zeroed out data. Fill it in to make the checksum 0. */
    *( ( uint32_t * ) &pucEthernetBuffer[ usLength - sizeof( uint32_t ) ] ) = FreeRTOS_htonl( 0xFFA9 );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xTCPPacket.xTCPHeader.ucTCPOffset = 0x50;
    pxProtPack->xTCPPacket.xTCPHeader.usChecksum = 0x0000;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPCorrectCRCOutgoingPacketZeroChecksum
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC if
 * it's a TCP outgoing packet. And the checksum is zero.
 */
void test_usGenerateProtocolChecksum_TCPCorrectCRCOutgoingPacketZeroChecksum( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    /* This is the checksum with zeroed out data. Fill it in to make the checksum 0. */
    *( ( uint32_t * ) &pucEthernetBuffer[ usLength - sizeof( uint32_t ) ] ) = FreeRTOS_htonl( 0xAFA9 );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xTCPPacket.xTCPHeader.ucTCPOffset = 0x50;
    pxProtPack->xTCPPacket.xTCPHeader.usChecksum = 0x00;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
    TEST_ASSERT_EQUAL( 0, pxProtPack->xTCPPacket.xTCPHeader.usChecksum );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPIncorrectCRC_IncomingPacket
 * To validate usGenerateProtocolChecksum returns ipWRONG_CRC if
 * checksum in TCP header is incorrect.
 */
void test_usGenerateProtocolChecksum_TCPIncorrectCRC_IncomingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xTCPPacket.xTCPHeader.ucTCPOffset = 0x50;
    pxProtPack->xTCPPacket.xTCPHeader.usChecksum = 0x0000;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPLessBufferSize_OutgoingPacket
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * buffer size is less than TCP minimum requirement.
 */
void test_usGenerateProtocolChecksum_TCPLessBufferSize_OutgoingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ucVersionHeaderLength + ipSIZE_OF_TCP_HEADER - 1;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xTCPPacket.xTCPHeader.ucTCPOffset = 0x50;
    pxProtPack->xTCPPacket.xTCPHeader.usChecksum = 0x0000;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPLessOffset_OutgoingPacket
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * offset in TCP header is less than minimum requirement.
 */
void test_usGenerateProtocolChecksum_TCPLessOffset_OutgoingPacket( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xTCPPacket.xTCPHeader.ucTCPOffset = 0x40;
    pxProtPack->xTCPPacket.xTCPHeader.usChecksum = 0x0000;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPLessBufferSize
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * buffer size is less than TCP minimum requirement.
 */
void test_usGenerateProtocolChecksum_TCPLessBufferSize( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength + ipSIZE_OF_TCP_HEADER - 1;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_TCP_HEADER - 1;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xTCPPacket.xTCPHeader.ucTCPOffset = 0x50;
    pxProtPack->xTCPPacket.xTCPHeader.usChecksum = 0x0000;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPLessHeaderLength
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * length in IP header is less than TCP minimum requirement.
 */
void test_usGenerateProtocolChecksum_TCPLessHeaderLength( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_TCP_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xTCPPacket.xTCPHeader.ucTCPOffset = 0x50;
    pxProtPack->xTCPPacket.xTCPHeader.usChecksum = 0x0000;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPLargeBufferSize
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * buffer size is larger than MTU.
 */
void test_usGenerateProtocolChecksum_TCPLargeBufferSize( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ipconfigNETWORK_MTU * 2;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + usLength;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    pxProtPack->xTCPPacket.xTCPHeader.ucTCPOffset = 0x50;
    pxProtPack->xTCPPacket.xTCPHeader.usChecksum = 0x0000;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_ICMPLargeBufferSize
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * buffer size is larger than MTU.
 */
void test_usGenerateProtocolChecksum_ICMPLargeBufferSize( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ipconfigNETWORK_MTU * 2;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + usLength;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    pxProtPack->xICMPPacket.xICMPHeader.usChecksum = 0x0000;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_ICMPLessBufferSize
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * buffer size is less than ICMP minimum requirement.
 */
void test_usGenerateProtocolChecksum_ICMPLessBufferSize( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength + ipSIZE_OF_ICMPv4_HEADER;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMPv4_HEADER - 1;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    pxProtPack->xICMPPacket.xICMPHeader.usChecksum = 0x0000;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_ICMPOutgoingChecksum
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC when it
 * generates correct CRC in ICMP checksum.
 */
void test_usGenerateProtocolChecksum_ICMPOutgoingChecksum( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    pxProtPack->xICMPPacket.xICMPHeader.usChecksum = 0x0000;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
    TEST_ASSERT_EQUAL( 65535, pxProtPack->xICMPPacket.xICMPHeader.usChecksum );
}

/**
 * @brief test_usGenerateProtocolChecksum_ICMPIncomingIncorrectCRC
 * To validate usGenerateProtocolChecksum returns ipWRONG_CRC if
 * checksum in ICMP header is incorrect.
 */
void test_usGenerateProtocolChecksum_ICMPIncomingIncorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    pxProtPack->xICMPPacket.xICMPHeader.usChecksum = 0x0000;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
    TEST_ASSERT_EQUAL( 0, pxProtPack->xICMPPacket.xICMPHeader.usChecksum );
}

/**
 * @brief test_usGenerateProtocolChecksum_ICMPIncomingCorrectCRC
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC if
 * checksum in ICMP header is correct.
 */
void test_usGenerateProtocolChecksum_ICMPIncomingCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_ICMP;

    /* Fill in the checksum. */
    pxProtPack->xICMPPacket.xICMPHeader.usChecksum = FreeRTOS_htons( 0xFFFF );

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_IGMPLargeBufferSize
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * buffer size is larger than MTU.
 */
void test_usGenerateProtocolChecksum_IGMPLargeBufferSize( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ipconfigNETWORK_MTU * 2;
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + usLength;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_IGMP;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_IGMPLessBufferSize
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * buffer size is less than IGMP minimum requirement.
 */
void test_usGenerateProtocolChecksum_IGMPLessBufferSize( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = ucVersionHeaderLength;
    size_t uxBufferLength = ucVersionHeaderLength + ipSIZE_OF_ETH_HEADER + ipSIZE_OF_ICMPv4_HEADER - 1;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_IGMP;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_IGMPOutgoingChecksum
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * buffer size is less than IGMP minimum requirement.
 */
void test_usGenerateProtocolChecksum_IGMPOutgoingChecksum( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_IGMP;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
    TEST_ASSERT_EQUAL( 65535, pxProtPack->xICMPPacket.xICMPHeader.usChecksum );
}

/**
 * @brief test_usGenerateProtocolChecksum_IGMPIncomingIncorrectCRC
 * To validate usGenerateProtocolChecksum returns ipWRONG_CRC if
 * checksum in IGMP header is incorrect.
 */
void test_usGenerateProtocolChecksum_IGMPIncomingIncorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_IGMP;
    pxProtPack->xICMPPacket.xICMPHeader.usChecksum = 0U;

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
    TEST_ASSERT_EQUAL( 0, pxProtPack->xICMPPacket.xICMPHeader.usChecksum );
}

/**
 * @brief test_usGenerateProtocolChecksum_IGMPIncomingCorrectCRC
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC if
 * checksum in IGMP header is correct.
 */
void test_usGenerateProtocolChecksum_IGMPIncomingCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    uint8_t ucVersionHeaderLength = 20;
    IPPacket_t * pxIPPacket;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) &( pucEthernetBuffer[ ucVersionHeaderLength - ipSIZE_OF_IPv4_HEADER ] );

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    pxIPPacket->xIPHeader.usLength = FreeRTOS_htons( usLength );

    pxIPPacket->xIPHeader.ucProtocol = ipPROTOCOL_IGMP;

    /* Fill in the checksum. */
    pxProtPack->xICMPPacket.xICMPHeader.usChecksum = FreeRTOS_htons( 0xFFFF );

    prvChecksumIPv4Checks_Stub( prvChecksumIPv4Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_UnknownEthernetType
 * To validate usGenerateProtocolChecksum triggers assertion when frame type in
 * ethernet header is unknown.
 */
void test_usGenerateProtocolChecksum_UnknownEthernetType( void )
{
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    IPPacket_t * pxIPPacket;
    ProtocolPacket_t * pxProtPack;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxProtPack = ( ProtocolPacket_t * ) pucEthernetBuffer;

    pxIPPacket = ( IPPacket_t * ) pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = 0xFF;

    catch_assert( usGenerateProtocolChecksum( pucEthernetBuffer, ipconfigTCP_MSS, xOutgoingPacket ) );
}

/**
 * @brief test_usGenerateProtocolChecksum_ICMPv6IncomingCorrectCRC
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC if
 * checksum in ICMPv6 header is correct.
 */
void test_usGenerateProtocolChecksum_ICMPv6IncomingCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    IPPacket_IPv6_t * pxIPPacket;
    ICMPPacket_IPv6_t * pxICMPv6Packet;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxICMPv6Packet = ( ICMPPacket_IPv6_t * ) pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( usLength - ipSIZE_OF_IPv6_HEADER );
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
    pxICMPv6Packet->xICMPHeaderIPv6.usChecksum = 0x89FF;

    prvChecksumIPv6Checks_Stub( prvChecksumIPv6Checks_Valid );
    prvChecksumICMPv6Checks_Stub( prvChecksumICMPv6Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_ICMPv6IncomingIncorrectCRC
 * To validate usGenerateProtocolChecksum returns ipWRONG_CRC if
 * checksum in ICMPv6 header is incorrect.
 */
void test_usGenerateProtocolChecksum_ICMPv6IncomingIncorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    IPPacket_IPv6_t * pxIPPacket;
    ICMPPacket_IPv6_t * pxICMPv6Packet;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxICMPv6Packet = ( ICMPPacket_IPv6_t * ) pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( usLength - ipSIZE_OF_IPv6_HEADER );
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
    pxICMPv6Packet->xICMPHeaderIPv6.usChecksum = 0;

    prvChecksumIPv6Checks_Stub( prvChecksumIPv6Checks_Valid );
    prvChecksumICMPv6Checks_Stub( prvChecksumICMPv6Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
    TEST_ASSERT_EQUAL( 0, pxICMPv6Packet->xICMPHeaderIPv6.usChecksum );
}

/**
 * @brief test_usGenerateProtocolChecksum_UDPv6IncomingCorrectCRC
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC if
 * checksum in UDPv6 header is correct.
 */
void test_usGenerateProtocolChecksum_UDPv6IncomingCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    IPPacket_IPv6_t * pxIPPacket;
    UDPPacket_IPv6_t * pxUDPv6Packet;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( usLength - ipSIZE_OF_IPv6_HEADER );
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_UDP;
    pxUDPv6Packet->xUDPHeader.usChecksum = 0xB2FF;

    prvChecksumIPv6Checks_Stub( prvChecksumIPv6Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_UDPv6IncomingIncorrectCRC
 * To validate usGenerateProtocolChecksum returns ipWRONG_CRC if
 * checksum in UDPv6 header is incorrect.
 */
void test_usGenerateProtocolChecksum_UDPv6IncomingIncorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    IPPacket_IPv6_t * pxIPPacket;
    UDPPacket_IPv6_t * pxUDPv6Packet;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxUDPv6Packet = ( UDPPacket_IPv6_t * ) pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( usLength - ipSIZE_OF_IPv6_HEADER );
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_UDP;
    pxUDPv6Packet->xUDPHeader.usChecksum = 0x1111;

    prvChecksumIPv6Checks_Stub( prvChecksumIPv6Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
    TEST_ASSERT_EQUAL( 0x1111, pxUDPv6Packet->xUDPHeader.usChecksum );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPv6IncomingCorrectCRC
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC if
 * checksum in TCPv6 header is correct.
 */
void test_usGenerateProtocolChecksum_TCPv6IncomingCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    IPPacket_IPv6_t * pxIPPacket;
    TCPPacket_IPv6_t * pxTCPv6Packet;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxTCPv6Packet = ( TCPPacket_IPv6_t * ) pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( usLength - ipSIZE_OF_IPv6_HEADER );
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_TCP;
    pxTCPv6Packet->xTCPHeader.ucTCPOffset = 0x50;
    pxTCPv6Packet->xTCPHeader.usChecksum = 0xBDAF;

    prvChecksumIPv6Checks_Stub( prvChecksumIPv6Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPv6IncomingIncorrectCRC
 * To validate usGenerateProtocolChecksum returns ipWRONG_CRC if
 * checksum in UDPv6 header is incorrect.
 */
void test_usGenerateProtocolChecksum_TCPv6IncomingIncorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    IPPacket_IPv6_t * pxIPPacket;
    TCPPacket_IPv6_t * pxTCPv6Packet;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxTCPv6Packet = ( TCPPacket_IPv6_t * ) pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( usLength - ipSIZE_OF_IPv6_HEADER );
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_TCP;
    pxTCPv6Packet->xTCPHeader.ucTCPOffset = 0x50;
    pxTCPv6Packet->xTCPHeader.usChecksum = 0x1111;

    prvChecksumIPv6Checks_Stub( prvChecksumIPv6Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipWRONG_CRC, usReturn );
    TEST_ASSERT_EQUAL( 0x1111, pxTCPv6Packet->xTCPHeader.usChecksum );
}

/**
 * @brief test_usGenerateProtocolChecksum_TCPv6OutgoingCorrectCRC
 * To validate usGenerateProtocolChecksum returns ipCORRECT_CRC when it
 * generates correct CRC in TCP checksum.
 */
void test_usGenerateProtocolChecksum_TCPv6OutgoingCorrectCRC( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    IPPacket_IPv6_t * pxIPPacket;
    TCPPacket_IPv6_t * pxTCPv6Packet;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxTCPv6Packet = ( TCPPacket_IPv6_t * ) pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( usLength - ipSIZE_OF_IPv6_HEADER );
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_TCP;
    pxTCPv6Packet->xTCPHeader.ucTCPOffset = 0x50;

    prvChecksumIPv6Checks_Stub( prvChecksumIPv6Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipCORRECT_CRC, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_IPv6UnknownProtocol
 * To validate usGenerateProtocolChecksum returns ipUNHANDLED_PROTOCOL when
 * the protocol is unknown in IPv6 packet.
 */
void test_usGenerateProtocolChecksum_IPv6UnknownProtocol( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdFALSE;
    IPPacket_IPv6_t * pxIPPacket;
    TCPPacket_IPv6_t * pxTCPv6Packet;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxTCPv6Packet = ( TCPPacket_IPv6_t * ) pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( usLength - ipSIZE_OF_IPv6_HEADER );
    pxIPPacket->xIPHeader.ucNextHeader = 0xFF;

    prvChecksumIPv6Checks_Stub( prvChecksumIPv6Checks_Valid );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipUNHANDLED_PROTOCOL, usReturn );
}

/**
 * @brief test_usGenerateProtocolChecksum_ICMPv6LessHeaderLength
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * remaining bytes in packets is less than header size.
 */
void test_usGenerateProtocolChecksum_ICMPv6LessHeaderLength( void )
{
    uint16_t usReturn;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    BaseType_t xOutgoingPacket = pdTRUE;
    IPPacket_IPv6_t * pxIPPacket;
    ICMPPacket_IPv6_t * pxICMPv6Packet;
    uint16_t usLength = 100;
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;

    memset( pucEthernetBuffer, 0, ipconfigTCP_MSS );

    pxICMPv6Packet = ( ICMPPacket_IPv6_t * ) pucEthernetBuffer;

    pxIPPacket = ( IPPacket_IPv6_t * ) pucEthernetBuffer;
    pxIPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    pxIPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( usLength - ipSIZE_OF_IPv6_HEADER );
    pxIPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
    pxICMPv6Packet->xICMPHeaderIPv6.usChecksum = 0;

    prvChecksumIPv6Checks_Stub( prvChecksumIPv6Checks_Valid );
    prvChecksumICMPv6Checks_Stub( prvChecksumICMPv6Checks_BigHeaderLength );

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_usGenerateChecksum_UnalignedAccess
 * To toggle address that is not aligned in usGenerateChecksum.
 */
void test_usGenerateChecksum_UnalignedAccess( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 10;
    size_t uxUnaligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnaligned = 0; uxUnaligned < 4; uxUnaligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnaligned ] ) & 0x01U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnaligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 0x5A5A, usResult );
}

/**
 * @brief test_usGenerateChecksum_OneByteToChecksum
 * To toggle address that is not aligned in usGenerateChecksum with one byte length.
 */
void test_usGenerateChecksum_OneByteToChecksum( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 1;
    size_t uxUnaligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnaligned = 0; uxUnaligned < 4; uxUnaligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnaligned ] ) & 0x01U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnaligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 0xAB00, usResult );
}

/**
 * @brief test_usGenerateChecksum_OneByteAlignedButZeroLength
 * To validate usGenerateChecksum with one byte align but zero length.
 */
void test_usGenerateChecksum_OneByteAlignedButZeroLength( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 0;
    size_t uxUnaligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnaligned = 0; uxUnaligned < 4; uxUnaligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnaligned ] ) & 0x01U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnaligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 0, usResult );
}

/**
 * @brief test_usGenerateChecksum_TwoByteAligned
 * To validate usGenerateChecksum with two byte align and 1 length.
 */
void test_usGenerateChecksum_TwoByteAligned( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 1;
    size_t uxUnaligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnaligned = 0; uxUnaligned < 4; uxUnaligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnaligned ] ) & 0x02U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnaligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 43776, usResult );
}

/**
 * @brief test_usGenerateChecksum_TwoByteAlignedTwoLength
 * To validate usGenerateChecksum with two byte align and 2 length.
 */
void test_usGenerateChecksum_TwoByteAlignedTwoLength( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 2;
    size_t uxUnaligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnaligned = 0; uxUnaligned < 4; uxUnaligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnaligned ] ) & 0x02U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnaligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 43947, usResult );
}

/**
 * @brief test_usGenerateChecksum_FourByteAligned
 * To validate usGenerateChecksum with four byte align and 2 length.
 */
void test_usGenerateChecksum_FourByteAligned( void )
{
    uint16_t usResult;
    uint16_t usSum = 0;
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 2;
    size_t uxUnaligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnaligned = 0; uxUnaligned < 4; uxUnaligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnaligned ] ) & 0x04U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnaligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 43947, usResult );
}

/**
 * @brief test_usGenerateChecksum_FourByteAlignedSumOverflow
 * To validate usGenerateChecksum with four byte align and sum overflow.
 */
void test_usGenerateChecksum_FourByteAlignedSumOverflow( void )
{
    uint16_t usResult;
    uint16_t usSum = FreeRTOS_htons( 0xFFFF - 0xAB );
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 20;
    size_t uxUnaligned = 0;

    memset( pucNextData, 0xAB, ipconfigTCP_MSS );

    for( uxUnaligned = 0; uxUnaligned < 4; uxUnaligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnaligned ] ) & 0x04U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnaligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 2484, usResult );
}

/**
 * @brief test_usGenerateChecksum_FourByteAlignedSumOverflow2
 * To validate usGenerateChecksum with four byte align and sum overflow.
 */
void test_usGenerateChecksum_FourByteAlignedSumOverflow2( void )
{
    uint16_t usResult;
    uint16_t usSum = FreeRTOS_htons( 0xFFFF - 0xAB );
    uint8_t pucNextData[ ipconfigTCP_MSS ];
    size_t uxByteCount = 20;
    size_t uxUnaligned = 0;

    memset( pucNextData, 0xFF, ipconfigTCP_MSS );

    for( uxUnaligned = 0; uxUnaligned < 4; uxUnaligned++ )
    {
        if( ( ( uintptr_t ) &pucNextData[ uxUnaligned ] ) & 0x04U )
        {
            break;
        }
    }

    usResult = usGenerateChecksum( usSum, &pucNextData[ uxUnaligned ], uxByteCount );

    TEST_ASSERT_EQUAL( 21759, usResult );
}

/**
 * @brief test_vPrintResourceStats_BufferCountMore
 * To validate vPrintResourceStats when minimum free network buffer
 * is greater than last record.
 */
void test_vPrintResourceStats_BufferCountMore( void )
{
    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS + 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 2 );

    vPrintResourceStats();
}

/**
 * @brief test_vPrintResourceStats_BufferCountMore
 * To validate vPrintResourceStats when minimum free network buffer
 * is less than last record.
 */
void test_vPrintResourceStats_BufferCountLess( void )
{
    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 2 );

    vPrintResourceStats();
    TEST_ASSERT_EQUAL( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 2, uxLastMinBufferCount );
}

/**
 * @brief test_vPrintResourceStats_LastBuffer_NE_0
 * To validate vPrintResourceStats when minimum ever free heap size
 * is less than last record.
 */
void test_vPrintResourceStats_LastBuffer_NE_0( void )
{
    uxLastMinBufferCount = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
    uxMinLastSize = 10u;

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 2 );

    vPrintResourceStats();

    TEST_ASSERT_EQUAL( 2, uxMinLastSize );
}

/**
 * @brief test_vPrintResourceStats_LastBuffer_NE_0
 * To validate vPrintResourceStats when minimum ever free heap size
 * is greater than last record.
 */
void test_vPrintResourceStats_MinSizeIsBigger( void )
{
    uxLastMinBufferCount = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
    uxMinLastSize = 10u;

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 1024U * 1025U );

    vPrintResourceStats();

    TEST_ASSERT_EQUAL( 10, uxMinLastSize );
}

/**
 * @brief test_FreeRTOS_strerror_r_Invalid
 * To validate FreeRTOS_strerror_r with invalid errno.
 */
void test_FreeRTOS_strerror_r_Invalid( void )
{
    const char * pucResult;
    BaseType_t xErrnum = 0;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "Errno 0x0", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_EADDRINUSE
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_EADDRINUSE.
 */
void test_FreeRTOS_strerror_r_EADDRINUSE( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EADDRINUSE;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EADDRINUSE", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_ENOMEM
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_ENOMEM.
 */
void test_FreeRTOS_strerror_r_ENOMEM( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ENOMEM;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ENOMEM", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_EADDRNOTAVAIL
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_EADDRNOTAVAIL.
 */
void test_FreeRTOS_strerror_r_EADDRNOTAVAIL( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EADDRNOTAVAIL;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EADDRNOTAVAIL", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_ENOPROTOOPT
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_ENOPROTOOPT.
 */
void test_FreeRTOS_strerror_r_ENOPROTOOPT( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ENOPROTOOPT;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ENOPROTOOPT", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_EBADF
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_EBADF.
 */
void test_FreeRTOS_strerror_r_EBADF( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EBADF;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EBADF", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_ENOSPC
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_ENOSPC.
 */
void test_FreeRTOS_strerror_r_ENOSPC( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ENOSPC;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ENOSPC", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_ECANCELED
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_ECANCELED.
 */
void test_FreeRTOS_strerror_r_ECANCELED( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ECANCELED;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ECANCELED", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_ENOTCONN
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_ENOTCONN.
 */
void test_FreeRTOS_strerror_r_ENOTCONN( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ENOTCONN;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ENOTCONN", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_EINPROGRESS
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_EINPROGRESS.
 */
void test_FreeRTOS_strerror_r_EINPROGRESS( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EINPROGRESS;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EINPROGRESS", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_EOPNOTSUPP
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_EOPNOTSUPP.
 */
void test_FreeRTOS_strerror_r_EOPNOTSUPP( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EOPNOTSUPP;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EOPNOTSUPP", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_EINTR
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_EINTR.
 */
void test_FreeRTOS_strerror_r_EINTR( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EINTR;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EINTR", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_ETIMEDOUT
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_ETIMEDOUT.
 */
void test_FreeRTOS_strerror_r_ETIMEDOUT( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_ETIMEDOUT;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "ETIMEDOUT", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_EINVAL
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_EINVAL.
 */
void test_FreeRTOS_strerror_r_EINVAL( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EINVAL;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EINVAL", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_EWOULDBLOCK
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_EWOULDBLOCK.
 */
void test_FreeRTOS_strerror_r_EWOULDBLOCK( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EWOULDBLOCK;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EWOULDBLOCK", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_EISCONN
 * To validate FreeRTOS_strerror_r with pdFREERTOS_ERRNO_EISCONN.
 */
void test_FreeRTOS_strerror_r_EISCONN( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EISCONN;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EISCONN", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_ZeroLengthBuffer
 * To validate FreeRTOS_strerror_r with zero length buffer.
 */
void test_FreeRTOS_strerror_r_ZeroLengthBuffer( void )
{
    const char * pucResult;
    BaseType_t xErrnum = pdFREERTOS_ERRNO_EISCONN;
    char pcBuffer[ 100 ];
    size_t uxLength = 0;

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "", pcBuffer );
}

/**
 * @brief test_FreeRTOS_strerror_r_NegativeErrno
 * To validate FreeRTOS_strerror_r with negative errno.
 */
void test_FreeRTOS_strerror_r_NegativeErrno( void )
{
    const char * pucResult;
    BaseType_t xErrnum = -pdFREERTOS_ERRNO_EISCONN;
    char pcBuffer[ 100 ];
    size_t uxLength = sizeof( pcBuffer );

    memset( pcBuffer, 0, sizeof( pcBuffer ) );

    pucResult = FreeRTOS_strerror_r( xErrnum, pcBuffer, uxLength );

    TEST_ASSERT_EQUAL( pcBuffer, pucResult );
    TEST_ASSERT_EQUAL_STRING( "EISCONN", pcBuffer );
}

/**
 * @brief test_FreeRTOS_max_int32
 * To validate FreeRTOS_max_int32.
 */
void test_FreeRTOS_max_int32( void )
{
    int32_t lResult;
    int i, j;

    for( i = -100; i < 100; i++ )
    {
        for( j = -100; j <= i; j++ )
        {
            lResult = FreeRTOS_max_int32( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }

    for( i = ( 0x6FFFFFFF - 100 ); i < ( 0x6FFFFFFF + 100 ); i++ )
    {
        for( j = ( 0x6FFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_max_int32( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }
}

/**
 * @brief test_FreeRTOS_max_uint32
 * To validate FreeRTOS_max_uint32.
 */
void test_FreeRTOS_max_uint32( void )
{
    uint32_t lResult;
    uint32_t i, j;

    for( i = 0; i < 100; i++ )
    {
        for( j = 0; j <= i; j++ )
        {
            lResult = FreeRTOS_max_uint32( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }

    for( i = ( 0xDFFFFFFF - 100 ); i < ( 0xDFFFFFFF + 100 ); i++ )
    {
        for( j = ( 0xDFFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_max_uint32( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }
}

/**
 * @brief test_FreeRTOS_max_size_t
 * To validate FreeRTOS_max_size_t.
 */
void test_FreeRTOS_max_size_t( void )
{
    uint32_t lResult;
    uint32_t i, j;

    for( i = 0; i < 100; i++ )
    {
        for( j = 0; j <= i; j++ )
        {
            lResult = FreeRTOS_max_size_t( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }

    for( i = ( 0xDFFFFFFF - 100 ); i < ( 0xDFFFFFFF + 100 ); i++ )
    {
        for( j = ( 0xDFFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_max_size_t( i, j );
            TEST_ASSERT_EQUAL( i, lResult );
        }
    }
}

/**
 * @brief test_FreeRTOS_min_int32
 * To validate FreeRTOS_min_int32.
 */
void test_FreeRTOS_min_int32( void )
{
    int32_t lResult;
    int i, j;

    for( i = -100; i < 100; i++ )
    {
        for( j = -100; j <= i; j++ )
        {
            lResult = FreeRTOS_min_int32( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }

    for( i = ( 0x6FFFFFFF - 100 ); i < ( 0x6FFFFFFF + 100 ); i++ )
    {
        for( j = ( 0x6FFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_min_int32( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }
}

/**
 * @brief test_FreeRTOS_min_uint32
 * To validate FreeRTOS_min_uint32.
 */
void test_FreeRTOS_min_uint32( void )
{
    uint32_t lResult;
    uint32_t i, j;

    for( i = 0; i < 100; i++ )
    {
        for( j = 0; j <= i; j++ )
        {
            lResult = FreeRTOS_min_uint32( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }

    for( i = ( 0xDFFFFFFF - 100 ); i < ( 0xDFFFFFFF + 100 ); i++ )
    {
        for( j = ( 0xDFFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_min_uint32( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }
}

/**
 * @brief test_FreeRTOS_min_size_t
 * To validate FreeRTOS_min_size_t.
 */
void test_FreeRTOS_min_size_t( void )
{
    uint32_t lResult;
    uint32_t i, j;

    for( i = 0; i < 100; i++ )
    {
        for( j = 0; j <= i; j++ )
        {
            lResult = FreeRTOS_min_size_t( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }

    for( i = ( 0xDFFFFFFF - 100 ); i < ( 0xDFFFFFFF + 100 ); i++ )
    {
        for( j = ( 0xDFFFFFFF - 100 ); j <= i; j++ )
        {
            lResult = FreeRTOS_min_size_t( i, j );
            TEST_ASSERT_EQUAL( j, lResult );
        }
    }
}

/**
 * @brief test_FreeRTOS_round_up
 * To validate FreeRTOS_round_up.
 */
void test_FreeRTOS_round_up( void )
{
    uint32_t ulResult;
    uint32_t a, d;

    a = 0;
    d = 0;
    catch_assert( FreeRTOS_round_up( a, d ) );

    a = 32;
    d = 5;
    ulResult = FreeRTOS_round_up( a, d );
    TEST_ASSERT_EQUAL( 35, ulResult );

    a = 0xFFFFFFF7;
    d = 3;
    ulResult = FreeRTOS_round_up( a, d );
    TEST_ASSERT_EQUAL( 0xFFFFFFF9, ulResult );

    a = 0x123AB;
    d = 7;
    ulResult = FreeRTOS_round_up( a, d );
    TEST_ASSERT_EQUAL( 0x123AD, ulResult );

    a = 0x123AD;
    d = 7;
    ulResult = FreeRTOS_round_up( a, d );
    TEST_ASSERT_EQUAL( 0x123AD, ulResult );
}

/**
 * @brief test_FreeRTOS_round_down
 * To validate FreeRTOS_round_down.
 */
void test_FreeRTOS_round_down( void )
{
    uint32_t ulResult;
    uint32_t a, d;

    a = 0;
    d = 0;
    catch_assert( FreeRTOS_round_down( a, d ) );

    a = 32;
    d = 5;
    ulResult = FreeRTOS_round_down( a, d );
    TEST_ASSERT_EQUAL( 30, ulResult );

    a = 0xFFFFFFF7;
    d = 3;
    ulResult = FreeRTOS_round_down( a, d );
    TEST_ASSERT_EQUAL( 0xFFFFFFF6, ulResult );

    a = 0x123AB;
    d = 7;
    ulResult = FreeRTOS_round_down( a, d );
    TEST_ASSERT_EQUAL( 0x123A6, ulResult );

    a = 0x123AD;
    d = 7;
    ulResult = FreeRTOS_round_down( a, d );
    TEST_ASSERT_EQUAL( 0x123AD, ulResult );
}

/**
 * @brief test_ulChar2u32
 * To validate ulChar2u32.
 */
void test_ulChar2u32( void )
{
    uint32_t ulResult;
    uint8_t pucPtr[] = { 0xAA, 0x00, 0x12, 0xEF };

    ulResult = ulChar2u32( pucPtr );

    TEST_ASSERT_EQUAL_UINT32( 0xAA0012EF, ulResult );
}

/**
 * @brief test_usChar2u16
 * To validate usChar2u16.
 */
void test_usChar2u16( void )
{
    uint16_t usResult;
    uint8_t pucPtr[] = { 0xAA, 0x00, 0x12, 0xEF };

    usResult = usChar2u16( pucPtr );

    TEST_ASSERT_EQUAL_UINT16( 0xAA00, usResult );

    usResult = usChar2u16( &pucPtr[ 2 ] );

    TEST_ASSERT_EQUAL_UINT16( 0x12EF, usResult );
}

/**
 * @brief test_prvGetChecksumFromPacket_UnhandledProtocol
 * To validate prvGetChecksumFromPacket returns ipUNHANDLED_PROTOCOL when
 * input set has unknown protocol.
 */
void test_prvGetChecksumFromPacket_UnhandledProtocol()
{
    struct xPacketSummary xSet;
    uint16_t usReturn;

    memset( &xSet, 0, sizeof( xSet ) );

    xSet.ucProtocol = 0xFF;

    usReturn = prvGetChecksumFromPacket( &xSet );
    TEST_ASSERT_EQUAL( ipUNHANDLED_PROTOCOL, usReturn );
}

/**
 * @brief test_prvGetChecksumFromPacket_IPv6UnhandledProtocol
 * To validate prvGetChecksumFromPacket returns ipUNHANDLED_PROTOCOL when
 * input set has unknown protocol.
 */
void test_prvGetChecksumFromPacket_IPv6UnhandledProtocol()
{
    struct xPacketSummary xSet;
    uint16_t usReturn;

    memset( &xSet, 0, sizeof( xSet ) );

    xSet.xIsIPv6 = pdTRUE;
    xSet.ucProtocol = 0xFF;

    usReturn = prvGetChecksumFromPacket( &xSet );
    TEST_ASSERT_EQUAL( ipUNHANDLED_PROTOCOL, usReturn );
}

/**
 * @brief test_prvSetChecksumInPacket_UnhandledProtocol
 * To validate prvSetChecksumInPacket returns ipUNHANDLED_PROTOCOL when
 * input set has unknown protocol.
 */
void test_prvSetChecksumInPacket_UnhandledProtocol()
{
    struct xPacketSummary xSet;

    memset( &xSet, 0, sizeof( xSet ) );

    xSet.ucProtocol = 0xFF;

    prvSetChecksumInPacket( &xSet, 0 );
}

/**
 * @brief test_prvSetChecksumInPacket_IPv6UnhandledProtocol
 * To validate prvSetChecksumInPacket returns ipUNHANDLED_PROTOCOL when
 * input set has unknown protocol.
 */
void test_prvSetChecksumInPacket_IPv6UnhandledProtocol()
{
    struct xPacketSummary xSet;
    uint16_t usReturn;

    memset( &xSet, 0, sizeof( xSet ) );

    xSet.xIsIPv6 = pdTRUE;
    xSet.ucProtocol = 0xFF;

    prvSetChecksumInPacket( &xSet, 0 );
}

static void pfRemoveAllowedMAC( struct xNetworkInterface * pxInterface,
                                const uint8_t * pucMacAddress )
{
    xMACFunctionCalled = pdTRUE;
}

/**
 * @brief test_prvProcessNetworkDownEvent_Fail
 * To validate if prvProcessNetworkDownEvent skips hook and DHCP
 * when bCallDownHook & bWantDHCP are both disabled.
 */
static void prvProcessNetworkDownEvent_Generic( const uint8_t * pucAddress,
                                                IPv6_Type_t eType,
                                                UBaseType_t uxSetMembers )
{
    NetworkInterface_t xInterface = { 0 };
    NetworkEndPoint_t xEndPoint = { 0 };
    BaseType_t xMACRemoveExpected = pdFALSE;

    xCallEventHook = pdFALSE;
    xInterfaces[ 0 ].pfInitialise = &xNetworkInterfaceInitialise_returnTrue;
    xInterfaces[ 0 ].pxEndPoint = &xEndPoint;

    xEndPoint.bits.bEndPointUp = pdTRUE;
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
        ( xInterface.pfRemoveAllowedMAC != NULL ) &&
        ( xEndPoint.pxNetworkInterface != NULL ) &&
        ( xEndPoint.bits.bIPv6 == pdTRUE_UNSIGNED ) )
    {
        xMACRemoveExpected = pdTRUE;
    }

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );

    if( xEndPoint.bits.bIPv6 == pdTRUE_UNSIGNED )
    {
        /* The vManageSolicitedNodeAddress() function is mocked. */
        vManageSolicitedNodeAddress_Expect( &xEndPoint, pdFALSE );
    }

    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );


    FreeRTOS_ClearARP_Expect( &xEndPoint );

    vIPNetworkUpCalls_Expect( &xEndPoint );

    prvProcessNetworkDownEvent( &xInterfaces[ 0 ] );

    /* See if pfRemoveAllowedMAC() was called when it has to. */
    TEST_ASSERT_EQUAL( xMACRemoveExpected, xMACFunctionCalled );
}

void test_prvProcessNetworkDownEvent_LinkLocal()
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
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_LinkLocal, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_LinkLocal, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_LinkLocal, ipHAS_IPV6 );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_LinkLocal, ipHAS_INTERFACE );
}

void test_prvProcessNetworkDownEvent_Global()
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

    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_Global, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_Global, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_Global, ipHAS_IPV6 );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_Global, ipHAS_INTERFACE );
}

void test_prvProcessNetworkDownEvent_SiteLocal()
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

    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_SiteLocal, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_SiteLocal, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_SiteLocal, ipHAS_IPV6 );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_SiteLocal, ipHAS_INTERFACE );
}

void test_prvProcessNetworkDownEvent_Multicast()
{
    /* Use the multicast address "ff02::fb",
     * just for the coverage of prvProcessNetworkDownEvent(). */
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

    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_Multicast, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_Multicast, ipHAS_IPV6 | ipHAS_INTERFACE );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_Multicast, ipHAS_IPV6 );
    prvProcessNetworkDownEvent_Generic( ucAddress, eIPv6_Multicast, ipHAS_INTERFACE );
}

/**
 * @brief test_eGetDHCPState
 * To validate if eGetDHCPState returns expected
 * DHCP state.
 */
void test_eGetDHCPState( void )
{
    DHCPData_t xTestData;
    eDHCPState_t eReturn;
    int i;
    struct xNetworkEndPoint xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    for( i = 0; i < sizeof( xTestData.eDHCPState ); i++ )
    {
        /* Modify the global state. */
        pxEndPoint->xDHCPData.eDHCPState = i;
        eReturn = eGetDHCPState( &xEndPoint );
        TEST_ASSERT_EQUAL( i, eReturn );
    }
}
