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

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_DNS_Networking.h"
#include "mock_task.h"
#include "mock_list.h"
#include "mock_queue.h"

#include "mock_FreeRTOS_DNS_Cache.h"
#include "mock_FreeRTOS_DNS_Parser.h"
#include "mock_FreeRTOS_DNS_Networking.h"
#include "mock_NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"


#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"
#include "FreeRTOS_DNS_ConfigNoCallback_stubs.c"

/* ===========================  EXTERN VARIABLES  =========================== */

#define LLMNR_ADDRESS                 "freertos"
#define LOCAL_ADDRESS                 "freertos.local"
#define GOOD_ADDRESS                  "www.freertos.org"
#define BAD_ADDRESS                   "this is a bad address"
#define DOTTED_IPV4_ADDRESS           "192.168.0.1"
#define DOTTED_IPV4_ADDRESS_UINT32    ( 0x0100A8C0 )
#define DOTTED_IPv6_ADDRESS           "2001::1"

IPv6_Address_t xIPv6Address = { { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 } };

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                struct freertos_addrinfo * /* pxAddressInfo */ );

extern IPPreference_t xDNS_IP_Preference;

/* ============================  Unity Fixtures  ============================ */

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
    xDNS_IP_Preference = xPreferenceIPv4;
    isMallocFail = false;
}

/* ============================== Test Cases ============================== */

/**
 * @brief IP address found with IPv4 address input
 */
void test_FreeRTOS_getaddrinfo_IPv4AddressFound( void )
{
    BaseType_t xReturn;
    struct freertos_addrinfo * pxAddress;
    struct freertos_addrinfo xHint, * pxHint = &xHint;

    memset( &xHint, 0, sizeof( struct freertos_addrinfo ) );

    xHint.ai_family = FREERTOS_AF_INET4;

    FreeRTOS_inet_addr_ExpectAndReturn( DOTTED_IPV4_ADDRESS, DOTTED_IPV4_ADDRESS_UINT32 );
    ulChar2u32_IgnoreAndReturn( DOTTED_IPV4_ADDRESS_UINT32 );

    xReturn = FreeRTOS_getaddrinfo( DOTTED_IPV4_ADDRESS, "Service", pxHint, &pxAddress );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET4, pxAddress->ai_family );
    TEST_ASSERT_EQUAL( DOTTED_IPV4_ADDRESS_UINT32, FreeRTOS_htonl( pxAddress->ai_addr->sin_address.ulIP_IPv4 ) );
    TEST_ASSERT_EQUAL( ipSIZE_OF_IPv4_ADDRESS, pxAddress->ai_addrlen );

    vPortFree( pxAddress ); /* Make LeakSanitizer happy. */
}

/**
 * @brief Ensures that when the supplied address is in the dotted format, it is
 *        translated to the numerical form and no lookup is performed
 */
void test_FreeRTOS_gethostbyname_SuccessDotAddress( void )
{
    uint32_t ret;

    FreeRTOS_inet_addr_ExpectAndReturn( DOTTED_IPV4_ADDRESS, 12345 );

    xApplicationGetRandomNumber_IgnoreAndReturn( pdTRUE );
    ulChar2u32_IgnoreAndReturn( 12345 );
    ret = FreeRTOS_gethostbyname( DOTTED_IPV4_ADDRESS );
    TEST_ASSERT_EQUAL( 12345, ret );
}

/**
 * @brief Ensures that if the address is not in the dotted form and found in the cache,
 *        it is returned to the caller
 */
void test_FreeRTOS_gethostbyname_SuccessAddressInCache( void )
{
    uint32_t ret;

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 12345 );

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );
    TEST_ASSERT_EQUAL( 12345, ret );
}

/**
 * @brief The identifier is different between DNS request and reply.
 */
void test_FreeRTOS_gethostbyname_DifferentIdentifier( void )
{
    uint32_t ret;
    uint32_t ulNumber = 34;
    int pvSearchID = 32;
    NetworkEndPoint_t xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct xDNSBuffer xReceiveBuffer;
    struct xSOCKET xDNSSocket;
    size_t uxBytesNeeded = sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t );
    int i;

    xNetworkBuffer.pucEthernetBuffer = malloc( uxBytesNeeded + ipBUFFER_PADDING );
    xNetworkBuffer.pucEthernetBuffer += ipBUFFER_PADDING;
    xNetworkBuffer.xDataLength = uxBytesNeeded;
    xReceiveBuffer.pucPayloadBuffer = malloc( 300 );
    xReceiveBuffer.uxPayloadLength = 300;
    ( void ) memset( xNetworkBuffer.pucEthernetBuffer, 0x00, uxBytesNeeded );
    ( void ) memset( xReceiveBuffer.pucPayloadBuffer, 0x00, 300 );
    DNSMessage_t * header = ( DNSMessage_t * ) xReceiveBuffer.pucPayloadBuffer;

    header->usIdentifier = 12;
    xDNSSocket.usLocalPort = 0;
    xEndPoint.bits.bIPv6 = pdFALSE;
    xEndPoint.ipv4_settings.ucDNSIndex = 0;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] = 0xC0C0C0C0;

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnThruPtr_pulNumber( &ulNumber );

    /* in prvGetHostByName */
    DNS_CreateSocket_ExpectAnyArgsAndReturn( &xDNSSocket );
    /* prvGetHostByNameOp */
    /* prvFillSockAddress */
    /* in prvSendBuffer */
    /* in prvGetPayloadBuffer */

    for( i = 0; i < ipconfigDNS_REQUEST_ATTEMPTS; i++ )
    {
        FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );
        DNS_BindSocket_ExpectAnyArgsAndReturn( 0 );

        pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );

        /* back in prvSendBuffer */
        DNS_SendRequest_ExpectAnyArgsAndReturn( pdPASS );

        /* back in prvGetHostByNameOp */
        DNS_ReadReply_ExpectAnyArgsAndReturn( 4 );
        DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
        /* prvDNSReply */
        FreeRTOS_ReleaseUDPPayloadBuffer_ExpectAnyArgs();
    }

    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );

    TEST_ASSERT_EQUAL( 0, ret );

    free( xNetworkBuffer.pucEthernetBuffer - ipBUFFER_PADDING );
    free( xReceiveBuffer.pucPayloadBuffer );
}

/**
 * @brief The identifier is same between DNS request and reply.
 */
void test_FreeRTOS_gethostbyname_SameIdentifier( void )
{
    uint32_t ret;
    uint32_t ulNumber = 34;
    int pvSearchID = 32;
    NetworkEndPoint_t xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct xDNSBuffer xReceiveBuffer;
    struct xSOCKET xDNSSocket;
    size_t uxBytesNeeded = sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t );
    int i;

    xNetworkBuffer.pucEthernetBuffer = malloc( uxBytesNeeded + ipBUFFER_PADDING );
    xNetworkBuffer.pucEthernetBuffer += ipBUFFER_PADDING;
    xNetworkBuffer.xDataLength = uxBytesNeeded;
    xReceiveBuffer.pucPayloadBuffer = malloc( 300 );
    xReceiveBuffer.uxPayloadLength = 300;
    ( void ) memset( xNetworkBuffer.pucEthernetBuffer, 0x00, uxBytesNeeded );
    ( void ) memset( xReceiveBuffer.pucPayloadBuffer, 0x00, 300 );
    DNSMessage_t * header = ( DNSMessage_t * ) xReceiveBuffer.pucPayloadBuffer;

    header->usIdentifier = ulNumber;
    xDNSSocket.usLocalPort = 0;
    xEndPoint.bits.bIPv6 = pdFALSE;
    xEndPoint.ipv4_settings.ucDNSIndex = 0;
    xEndPoint.ipv4_settings.ulDNSServerAddresses[ 0 ] = 0xC0C0C0C0;

    FreeRTOS_inet_addr_ExpectAndReturn( GOOD_ADDRESS, 0 );
    Prepare_CacheLookup_ExpectAnyArgsAndReturn( 0 );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ReturnThruPtr_pulNumber( &ulNumber );

    /* in prvGetHostByName */
    DNS_CreateSocket_ExpectAnyArgsAndReturn( &xDNSSocket );
    /* prvGetHostByNameOp */
    /* prvFillSockAddress */
    /* in prvSendBuffer */
    /* in prvGetPayloadBuffer */

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );
    DNS_BindSocket_ExpectAnyArgsAndReturn( 0 );

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );

    /* back in prvSendBuffer */
    DNS_SendRequest_ExpectAnyArgsAndReturn( pdPASS );

    /* back in prvGetHostByNameOp */
    DNS_ReadReply_ExpectAnyArgsAndReturn( 4 );
    DNS_ReadReply_ReturnThruPtr_pxReceiveBuffer( &xReceiveBuffer );
    /* prvDNSReply */
    DNS_ParseDNSReply_ExpectAnyArgsAndReturn( 12345 );
    FreeRTOS_ReleaseUDPPayloadBuffer_ExpectAnyArgs();

    /* back in prvGetHostByName */
    DNS_CloseSocket_ExpectAnyArgs();

    ret = FreeRTOS_gethostbyname( GOOD_ADDRESS );

    TEST_ASSERT_EQUAL( 12345, ret );

    free( xNetworkBuffer.pucEthernetBuffer - ipBUFFER_PADDING );
    free( xReceiveBuffer.pucPayloadBuffer );
}
