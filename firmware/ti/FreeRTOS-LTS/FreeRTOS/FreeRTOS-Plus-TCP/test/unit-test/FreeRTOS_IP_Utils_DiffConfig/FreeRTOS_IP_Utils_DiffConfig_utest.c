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
#include "mock_IP_Utils_DiffConfig_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "FreeRTOSIPConfig.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_IPv4_Utils.h"

#include "FreeRTOS_IP_Utils.h"
#include "FreeRTOS_IP_Utils_DiffConfig_stubs.c"

#include "catch_assert.h"

/* =========================== EXTERN VARIABLES =========================== */

#if ( ipconfigUSE_NETWORK_EVENT_HOOK == 1 )
    extern BaseType_t xCallEventHook;
#endif

extern UBaseType_t uxLastMinBufferCount;
extern size_t uxMinLastSize;
extern UBaseType_t uxLastMinQueueSpace;

extern NetworkInterface_t xInterfaces[ 1 ];

/* ============================== Test Cases ============================== */

/**
 * @brief test_pxPacketBuffer_to_NetworkBuffer
 * To validate if pxPacketBuffer_to_NetworkBuffer returns NULL when input is NULL.
 */
void test_pxPacketBuffer_to_NetworkBuffer( void )
{
    NetworkBufferDescriptor_t * pxReturn;

    pxReturn = pxPacketBuffer_to_NetworkBuffer( NULL );

    TEST_ASSERT_EQUAL( NULL, pxReturn );
}

/**
 * @brief test_prvProcessNetworkDownEvent_Pass_DHCP_Enabled
 * To validate if prvProcessNetworkDownEvent runs DHCP flow when it's enabled for that endpoint.
 */
void test_prvProcessNetworkDownEvent_Pass_DHCP_Enabled( void )
{
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint = { 0 };

    xCallEventHook = pdFALSE;

    xInterface.pfInitialise = xNetworkInterfaceInitialise_test;

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_FirstEndPoint_ExpectAndReturn( &xInterface, &xEndPoint );

    FreeRTOS_ClearARP_Expect( &xEndPoint );

    vDHCPStop_Expect( &xEndPoint );

    FreeRTOS_NextEndPoint_ExpectAndReturn( &xInterface, &xEndPoint, NULL );

    xInterface.pfInitialise = xNetworkInterfaceInitialise_test;

    FreeRTOS_FirstEndPoint_ExpectAndReturn( &xInterface, &xEndPoint );

    xEndPoint.bits.bWantDHCP = pdTRUE;

    vDHCPProcess_Expect( pdTRUE, &xEndPoint );

    FreeRTOS_NextEndPoint_ExpectAndReturn( &xInterface, &xEndPoint, NULL );

    prvProcessNetworkDownEvent( &xInterface );
}

/**
 * @brief test_FreeRTOS_round_up
 * To validate if FreeRTOS_round_up doesn't trigger assertion when configASSERT is not enabled.
 */
void test_FreeRTOS_round_up( void )
{
    uint32_t ulReturn;
    uint32_t a = 10;

    ulReturn = FreeRTOS_round_up( a, 0 );

    TEST_ASSERT_EQUAL( 10, ulReturn );
}

/**
 * @brief test_FreeRTOS_round_down
 * To validate if FreeRTOS_round_down doesn't trigger assertion when configASSERT is not enabled.
 */
void test_FreeRTOS_round_down( void )
{
    uint32_t ulReturn;
    uint32_t a = 10;

    ulReturn = FreeRTOS_round_down( a, 0 );

    TEST_ASSERT_EQUAL( 0, ulReturn );
}

/**
 * @brief test_vPrintResourceStats_MinSizeIsBigger
 * To validate if vPrintResourceStats updates uxLastMinQueueSpace when
 * ipconfigCHECK_IP_QUEUE_SPACE is enabled.
 */
void test_vPrintResourceStats_MinSizeIsBigger( void )
{
    uxLastMinBufferCount = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
    uxMinLastSize = 10u;
    uxLastMinQueueSpace = 0;

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 1024U * 1025U );

    uxGetMinimumIPQueueSpace_ExpectAndReturn( 0 );

    vPrintResourceStats();

    TEST_ASSERT_EQUAL( 10, uxMinLastSize );
    TEST_ASSERT_EQUAL( 0, uxLastMinQueueSpace );
}

/**
 * @brief test_vPrintResourceStats_LastQueueNECurrentQueue
 * To validate if vPrintResourceStats updates uxLastMinQueueSpace when
 * ipconfigCHECK_IP_QUEUE_SPACE is enabled.
 */
void test_vPrintResourceStats_LastQueueNECurrentQueue( void )
{
    uxLastMinBufferCount = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
    uxMinLastSize = 10u;
    uxLastMinQueueSpace = 0;

    uxGetMinimumFreeNetworkBuffers_ExpectAndReturn( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS - 2 );
    xPortGetMinimumEverFreeHeapSize_ExpectAndReturn( 1024U * 1025U );

    uxGetMinimumIPQueueSpace_ExpectAndReturn( 10 );

    vPrintResourceStats();

    TEST_ASSERT_EQUAL( 10, uxMinLastSize );
    TEST_ASSERT_EQUAL( 10, uxLastMinQueueSpace );
}

/**
 * @brief test_vPrintResourceStats_LastQueueNECurrentQueue
 * To validate if prvProcessNetworkDownEvent skip DHCP flow when
 * DHCP is disabled for that endpoint.
 */
void test_prvProcessNetworkDownEvent_Pass_DHCP_Disabled( void )
{
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint = { 0 };

    xCallEventHook = pdFALSE;
    xEndPoint.bits.bCallDownHook = 1;

    xInterface.pfInitialise = xNetworkInterfaceInitialise_test;

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_FirstEndPoint_ExpectAndReturn( &xInterface, &xEndPoint );

    vApplicationIPNetworkEventHook_Expect( eNetworkDown );
    FreeRTOS_ClearARP_Expect( &xEndPoint );

    FreeRTOS_NextEndPoint_ExpectAndReturn( &xInterface, &xEndPoint, NULL );

    xInterface.pfInitialise = xNetworkInterfaceInitialise_test;

    FreeRTOS_FirstEndPoint_ExpectAndReturn( &xInterface, &xEndPoint );

    xEndPoint.bits.bWantDHCP = pdFALSE;
    xEndPoint.bits.bWantRA = pdFALSE;

    vIPNetworkUpCalls_Expect( &xEndPoint );

    FreeRTOS_NextEndPoint_ExpectAndReturn( &xInterface, &xEndPoint, NULL );

    prvProcessNetworkDownEvent( &xInterface );
}

/**
 * @brief test_prvProcessNetworkDownEvent_PassIPv6
 * To validate if prvProcessNetworkDownEvent skip setting IPv6 address to
 * endpoint when IPv6 is disabled.
 */
void test_prvProcessNetworkDownEvent_PassIPv6( void )
{
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint = { 0 };

    xCallEventHook = pdFALSE;
    xEndPoint.bits.bCallDownHook = 1;

    xInterface.pfInitialise = xNetworkInterfaceInitialise_test;

    vIPSetARPTimerEnableState_Expect( pdFALSE );

    FreeRTOS_FirstEndPoint_ExpectAndReturn( &xInterface, &xEndPoint );

    vApplicationIPNetworkEventHook_Expect( eNetworkDown );
    FreeRTOS_ClearARP_Expect( &xEndPoint );

    FreeRTOS_NextEndPoint_ExpectAndReturn( &xInterface, &xEndPoint, NULL );

    xInterface.pfInitialise = xNetworkInterfaceInitialise_test;

    FreeRTOS_FirstEndPoint_ExpectAndReturn( &xInterface, &xEndPoint );

    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdFALSE;
    xEndPoint.bits.bWantRA = pdFALSE;

    vIPNetworkUpCalls_Expect( &xEndPoint );

    FreeRTOS_NextEndPoint_ExpectAndReturn( &xInterface, &xEndPoint, NULL );

    prvProcessNetworkDownEvent( &xInterface );
}

/**
 * @brief test_usGenerateProtocolChecksum_UDPv6IncomingPacket
 * To validate usGenerateProtocolChecksum returns ipINVALID_LENGTH if
 * checksum if IPv6 is not supported.
 */
void test_usGenerateProtocolChecksum_UDPv6IncomingPacket( void )
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

    usReturn = usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, xOutgoingPacket );

    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, usReturn );
}

/**
 * @brief test_pxUDPPayloadBuffer_to_NetworkBuffer_IPv6
 * Though the packet is marked as IPv6, we count it as IPv4 packet when
 * IPv6 is disabled.
 */
void test_pxUDPPayloadBuffer_to_NetworkBuffer_IPv6( void )
{
    NetworkBufferDescriptor_t * pxNetBufferToReturn, xNetBufferToReturn;
    size_t uxOffset = sizeof( UDPPacket_t );
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
