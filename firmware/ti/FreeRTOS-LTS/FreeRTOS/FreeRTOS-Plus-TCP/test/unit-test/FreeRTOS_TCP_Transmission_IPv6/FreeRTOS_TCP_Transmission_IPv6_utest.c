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

#include "FreeRTOSIPConfig.h"

#include "mock_task.h"
#include "mock_list.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_TCP_Utils.h"
#include "mock_FreeRTOS_TCP_State_Handling.h"
#include "mock_FreeRTOS_ND.h"
#include "mock_TCP_Transmission_IPv6_list_macros.h"


#include "FreeRTOS_TCP_Transmission.h"
#include "FreeRTOS_TCP_Transmission_IPv6_stubs.c"

#include "catch_assert.h"

/* ===========================  EXTERN VARIABLES  =========================== */

#define PACKET_LENGTH    50

uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];

/* =============================== Test Cases =============================== */

/**
 * @brief This function verify handling when both
 *        'pxNetworkBuffer' or 'pxSocket' is not defined.
 *         while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_BufferSocketNULL( void )
{
    FreeRTOS_Socket_t * pxSocket = NULL;
    NetworkBufferDescriptor_t * pxDescriptor = NULL;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdFALSE;

    prvTCPReturnPacket_IPV6( pxSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify handling case when
 *        only pxNetworkBuffer is NULL while
 *        returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_BufferNULL( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t * pxDescriptor = NULL;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdFALSE;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify asserting when
 *        ethernet buffer is not initialized.
 */
void test_prvTCPReturnPacket_IPV6_pucEthernetBuffer_Assert( void )
{
    FreeRTOS_Socket_t * pxSocket = NULL;
    NetworkBufferDescriptor_t xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdFALSE;
    NetworkEndPoint_t xEndPoint;

    memset( &xDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xDescriptor.pxEndPoint = &xEndPoint;
    xDescriptor.pucEthernetBuffer = NULL;

    catch_assert( prvTCPReturnPacket_IPV6( pxSocket, &xDescriptor, ulLen, xReleaseAfterSend ) );
}

/**
 * @brief This function verify handling case when
 *        only xSocket is NULL while
 *        returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_SocketNULL( void )
{
    FreeRTOS_Socket_t * pxSocket = NULL;
    NetworkBufferDescriptor_t xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdFALSE;
    NetworkEndPoint_t xEndPoint;
    NetworkInterface_t xNetworkInterfaces;

    memset( &xDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    xDescriptor.pxEndPoint = &xEndPoint;
    xDescriptor.pucEthernetBuffer = ucEthernetBuffer;
    xDescriptor.pxEndPoint->pxNetworkInterface = &xNetworkInterfaces;
    xDescriptor.pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    prvTCPReturnPacket_IPV6( pxSocket, &xDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point is NULL while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_NoEP_Found( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdFALSE;
    TCPPacket_IPv6_t * pxTCPPacket;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );

    xDescriptor.pucEthernetBuffer = ucEthernetBuffer;
    pxTCPPacket = ( ( TCPPacket_IPv6_t * ) xDescriptor.pucEthernetBuffer );
    xDescriptor.pxEndPoint = NULL;
    xSocket.pxEndPoint = NULL;

    prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket & set EndPoint is
 *        not able to find an Endpoint .
 */
void test_prvTCPReturnPacket_IPV6_NoEP_ReleaseAfterSend( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdTRUE;
    TCPPacket_IPv6_t * pxTCPPacket;

    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );

    xDescriptor.pucEthernetBuffer = ucEthernetBuffer;
    pxTCPPacket = ( ( TCPPacket_IPv6_t * ) xDescriptor.pucEthernetBuffer );
    xDescriptor.pxEndPoint = NULL;

    vReleaseNetworkBufferAndDescriptor_ExpectAnyArgs();

    prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point does not have a valid NetworkInterface
 *        while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_Assert1( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdTRUE;
    NetworkEndPoint_t xEndPoint;
    TCPPacket_IPv6_t * pxTCPPacket;


    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    xDescriptor.pucEthernetBuffer = ucEthernetBuffer;
    pxTCPPacket = ( ( TCPPacket_IPv6_t * ) xDescriptor.pucEthernetBuffer );
    pxDescriptor->pxEndPoint = NULL;
    pxDescriptor->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    xSocket.pxEndPoint = &xEndPoint;
    xSocket.pxEndPoint->pxNetworkInterface = NULL;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    catch_assert( prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend ) );
}


/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point does not have a valid NetworkInterface
 *        while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_Assert2( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdTRUE;
    NetworkEndPoint_t xEndPoint;
    TCPPacket_IPv6_t * pxTCPPacket;
    IPHeader_IPv6_t * pxIPHeader;
    TCPWindow_t * pxTCPWindow = &( xSocket.u.xTCP.xTCPWindow );


    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxDescriptor->pucEthernetBuffer = ucEthernetBuffer;
    pxDescriptor->pxEndPoint = &xEndPoint;
    pxDescriptor->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    pxDescriptor->pxEndPoint->pxNetworkInterface = NULL;
    pxTCPPacket = ( ( TCPPacket_IPv6_t * ) pxDescriptor->pucEthernetBuffer );
    pxIPHeader = &pxTCPPacket->xIPHeader;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );

    catch_assert( prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend ) );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point does not have a valid NetworkInterface output
 *        function, while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_Assert3( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdTRUE;
    NetworkEndPoint_t xEndPoint;
    TCPPacket_IPv6_t * pxTCPPacket;
    IPHeader_IPv6_t * pxIPHeader;
    TCPWindow_t * pxTCPWindow = &( xSocket.u.xTCP.xTCPWindow );
    NetworkInterface_t xNetworkInterfaces;


    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxDescriptor->pucEthernetBuffer = ucEthernetBuffer;
    pxDescriptor->pxEndPoint = &xEndPoint;
    pxDescriptor->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    pxDescriptor->pxEndPoint->pxNetworkInterface = &xNetworkInterfaces;
    pxDescriptor->pxEndPoint->pxNetworkInterface->pfOutput = NULL;
    pxTCPPacket = ( ( TCPPacket_IPv6_t * ) pxDescriptor->pucEthernetBuffer );
    pxIPHeader = &pxTCPPacket->xIPHeader;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    catch_assert( prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend ) );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point does not have a valid NetworkInterface,
 *        while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_HappyPath_ReleaseAfterSend( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    BaseType_t xReleaseAfterSend = pdTRUE;
    NetworkEndPoint_t xEndPoint;
    TCPPacket_IPv6_t * pxTCPPacket;
    NetworkInterface_t xNetworkInterfaces;


    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xNetworkInterfaces, 0, sizeof( NetworkInterface_t ) );

    xDescriptor.pucEthernetBuffer = ucEthernetBuffer;
    pxTCPPacket = ( ( TCPPacket_IPv6_t * ) xDescriptor.pucEthernetBuffer );
    pxDescriptor->pxEndPoint = &xEndPoint;
    pxDescriptor->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    pxDescriptor->pxEndPoint->pxNetworkInterface = &xNetworkInterfaces;
    pxDescriptor->pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function verify handling case with valid
 *        pxNetworkBuffer and pxSocket where as network end
 *        point does not have a valid NetworkInterface,
 *        while returning a packet.
 */
void test_prvTCPReturnPacket_IPV6_HappyPath_NoReleaseAfterSend( void )
{
    FreeRTOS_Socket_t xSocket;
    NetworkBufferDescriptor_t xDescriptor, * pxDescriptor = &xDescriptor;
    uint32_t ulLen = PACKET_LENGTH;
    BaseType_t xReleaseAfterSend = pdFALSE;
    NetworkEndPoint_t xEndPoint;
    NetworkInterface_t xNetworkInterfaces;
    uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ];



    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    memset( pxDescriptor, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xNetworkInterfaces, 0, sizeof( NetworkInterface_t ) );

    pxDescriptor->pucEthernetBuffer = ucEthernetBuffer;
    pxDescriptor->pxEndPoint = &xEndPoint;
    pxDescriptor->xDataLength = ipconfigETHERNET_MINIMUM_PACKET_BYTES;
    pxDescriptor->pxEndPoint->pxNetworkInterface = &xNetworkInterfaces;
    pxDescriptor->pxEndPoint->pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    prvTCPReturnPacket_IPV6( &xSocket, pxDescriptor, ulLen, xReleaseAfterSend );
}

/**
 * @brief This function validates failure in creating a packet
 *        as failed to get ND Cache Entry and the End point
 *        was found to be NULL.
 *
 */
void test_prvTCPPrepareConnect_IPV6_CacheMiss_NULLEP( void )
{
    FreeRTOS_Socket_t xSocket, * pxSocket = &xSocket;
    BaseType_t xReturn = pdFALSE;

    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv6_HEADER );

    xReturn = prvTCPPrepareConnect_IPV6( pxSocket );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief This function validates failure in creating a packet
 *        as after getting the ND Cache Entry, the
 *        End point was found to be NULL.
 *
 */
void test_prvTCPPrepareConnect_IPV6_CacheHit_NULLEP( void )
{
    FreeRTOS_Socket_t xSocket, * pxSocket = &xSocket;
    BaseType_t xReturn = pdFALSE;

    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv6_HEADER );
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 0 );

    xReturn = prvTCPPrepareConnect_IPV6( pxSocket );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief This function validates failure in creating a packet
 *        as after getting the ND Cache Entry, but there
 *        was random number generation error.
 *
 */
void test_prvTCPPrepareConnect_IPV6_CacheHit_RandNumFail( void )
{
    FreeRTOS_Socket_t xSocket, * pxSocket = &xSocket;
    BaseType_t xReturn = pdFALSE;

    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv6_HEADER );
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 10 );

    xReturn = prvTCPPrepareConnect_IPV6( pxSocket );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}


/**
 * @brief This function validates failure in creating a packet
 *        as there is no IP address, or an ARP is still in progress.
 */
void test_prvTCPPrepareConnect_IPV6_CantSendPacket_NULLEP( void )
{
    FreeRTOS_Socket_t xSocket, * pxSocket = &xSocket;
    BaseType_t xReturn = pdFALSE;

    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eCantSendPacket );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv6_HEADER );

    xReturn = prvTCPPrepareConnect_IPV6( pxSocket );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief This function validates failure in creating a packet
 *        as there is a cache miss but a valid Endpoint is found.
 */
void test_prvTCPPrepareConnect_IPV6_CacheMiss_ValidEP( void )
{
    FreeRTOS_Socket_t xSocket, * pxSocket = &xSocket;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    BaseType_t xReturn = pdFALSE;

    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheMiss );
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv6_HEADER );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdPASS );

    xReturn = prvTCPPrepareConnect_IPV6( pxSocket );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL_MEMORY( pxSocket->pxEndPoint, pxEndPoint, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function validates failure in creating a packet
 *        as cache get entry returns an unknown return value.
 */
void test_prvTCPPrepareConnect_IPV6_DefaultCase_ValidEP( void )
{
    FreeRTOS_Socket_t xSocket, * pxSocket = &xSocket;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;
    BaseType_t xReturn = pdFALSE;

    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eCantSendPacket + 1 ); /* Default case */
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv6_HEADER );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    vNDSendNeighbourSolicitation_ExpectAnyArgs();

    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdPASS );

    xReturn = prvTCPPrepareConnect_IPV6( pxSocket );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL_MEMORY( pxSocket->pxEndPoint, pxEndPoint, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function validates successfully created a
 *        packet and sending the first SYN with IPv4 frame type.
 */
void test_prvTCPPrepareConnect_IPV6_HappyPath_IPv4( void )
{
    FreeRTOS_Socket_t xSocket, * pxSocket = &xSocket;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;
    BaseType_t xReturn = pdFALSE;

    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    pxSocket->bits.bIsIPv6 = 0;

    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 10 );

    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdPASS );

    xReturn = prvTCPPrepareConnect_IPV6( pxSocket );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL_MEMORY( pxSocket->pxEndPoint, pxEndPoint, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function validates successfully created a
 *        packet and sending the first SYN with IPv6 frame type.
 */
void test_prvTCPPrepareConnect_IPV6_HappyPath_IPv6( void )
{
    FreeRTOS_Socket_t xSocket, * pxSocket = &xSocket;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;
    BaseType_t xReturn = pdFALSE;

    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    pxSocket->bits.bIsIPv6 = 1;
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv6_HEADER );
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 10 );

    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdPASS );

    xReturn = prvTCPPrepareConnect_IPV6( pxSocket );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL_MEMORY( pxSocket->pxEndPoint, pxEndPoint, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function validates successfully created a
 *        packet but the TCP window creation fails.
 */
void test_prvTCPPrepareConnect_IPV6_CreateTCPWindowFails( void )
{
    FreeRTOS_Socket_t xSocket, * pxSocket = &xSocket;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;
    BaseType_t xReturn = pdFALSE;

    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    pxSocket->bits.bIsIPv6 = 1;
    eNDGetCacheEntry_ExpectAnyArgsAndReturn( eARPCacheHit );
    eNDGetCacheEntry_ReturnThruPtr_ppxEndPoint( &pxEndPoint );

    uxIPHeaderSizeSocket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv6_HEADER );
    ulApplicationGetNextSequenceNumber_ExpectAnyArgsAndReturn( 10 );

    prvSocketSetMSS_ExpectAnyArgs();
    prvTCPCreateWindow_ExpectAnyArgsAndReturn( pdFAIL );

    xReturn = prvTCPPrepareConnect_IPV6( pxSocket );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief This function validates sending a TCP protocol control packet,
 *        when an un synchronised packet is received.
 */
void test_prvTCPSendSpecialPktHelper_IPV6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    TCPPacket_IPv6_t * pxTCPPacket;
    uint8_t ucTCPFlags = tcpTCP_FLAG_RST;
    BaseType_t xReturn;

    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    pxTCPPacket = ( ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxTCPPacket->xTCPHeader.ucTCPFlags = 0;

    xReturn = prvTCPSendSpecialPktHelper_IPV6( pxNetworkBuffer, ucTCPFlags );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL( ucTCPFlags, pxTCPPacket->xTCPHeader.ucTCPFlags );
    TEST_ASSERT_EQUAL( ( ipSIZE_OF_TCP_HEADER ) << 2, pxTCPPacket->xTCPHeader.ucTCPOffset );
}

/**
 * @brief This function validates sending a TCP protocol control packet,
 *        when an synchronize packet is received.
 */
void test_prvTCPSendSpecialPktHelper_IPV6_Syn( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    TCPPacket_IPv6_t * pxTCPPacket;
    uint8_t ucTCPFlags = tcpTCP_FLAG_RST;
    BaseType_t xReturn;

    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    pxTCPPacket = ( ( TCPPacket_IPv6_t * ) xNetworkBuffer.pucEthernetBuffer );
    pxTCPPacket->xTCPHeader.ucTCPFlags = tcpTCP_FLAG_SYN;

    xReturn = prvTCPSendSpecialPktHelper_IPV6( pxNetworkBuffer, ucTCPFlags );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
    TEST_ASSERT_EQUAL( ucTCPFlags, pxTCPPacket->xTCPHeader.ucTCPFlags );
    TEST_ASSERT_EQUAL( ( ipSIZE_OF_TCP_HEADER ) << 2, pxTCPPacket->xTCPHeader.ucTCPOffset );
}
