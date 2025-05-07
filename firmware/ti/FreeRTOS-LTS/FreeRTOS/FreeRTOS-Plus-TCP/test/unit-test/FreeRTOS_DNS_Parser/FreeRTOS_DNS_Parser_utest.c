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

#include "FreeRTOS.h"
#include "FreeRTOS_IP.h"

#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_task.h"
#include "mock_list.h"
#include "mock_queue.h"
#include "mock_FreeRTOS_DNS_Callback.h"
#include "mock_FreeRTOS_DNS_Cache.h"
#include "mock_FreeRTOS_DNS_Networking.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_DNS.h"

#include "catch_assert.h"
#include "FreeRTOSIPConfig.h"
#include "FreeRTOS_DNS_Parser.h"

#define LLMNR_ADDRESS     "freertos"
#define GOOD_ADDRESS      "www.freertos.org"
#define BAD_ADDRESS       "this is a bad address"
#define DOTTED_ADDRESS    "192.268.0.1"

#define prvROUND_UP_TO( SIZE, ALIGNMENT )    ( ( ( SIZE ) + ( ALIGNMENT ) -1 ) / ( ALIGNMENT ) *( ALIGNMENT ) )

#define prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4    prvROUND_UP_TO( ipUDP_PAYLOAD_OFFSET_IPv4, sizeof( void * ) )

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                struct freertos_addrinfo * /* pxAddressInfo */ );

/* ===========================   GLOBAL VARIABLES =========================== */
static int callback_called = 0;
static BaseType_t hook_return = pdFALSE;
static BaseType_t hook_called = pdFALSE;



/* ===========================  STATIC FUNCTIONS  =========================== */
static void dns_callback( const char * pcName,
                          void * pvSearchID,
                          struct freertos_addrinfo * pxAddressInfo )
{
    callback_called = 1;
}

/* ===========================  EXTERN VARIABLES  =========================== */

extern BaseType_t xBufferAllocFixedSize;

extern struct freertos_addrinfo pucAddrBuffer[ 2 ];
extern struct freertos_sockaddr pucSockAddrBuffer[ 1 ];

/* ============================  TEST FIXTURES  ============================= */

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
    xBufferAllocFixedSize = pdFALSE;
    callback_called = 0;
}

/**
 * @brief calls at the end of each test case
 */
void tearDown( void )
{
    hook_return = pdFALSE;
    hook_called = pdFALSE;
}

/* =============================  TEST MACROS  =============================== */
#define ASSERT_DNS_QUERY_HOOK_CALLED()            \
    do {                                          \
        TEST_ASSERT_EQUAL( pdTRUE, hook_called ); \
    } while( 0 )

#define ASSERT_DNS_QUERY_HOOK_NOT_CALLED()         \
    do {                                           \
        TEST_ASSERT_EQUAL( pdFALSE, hook_called ); \
    } while( 0 )

/* =============================  TEST CASES  =============================== */

/**
 * @brief ensures when there is no empty spots in the  pucByte buffer zero is
 *        returned
 */
void test_DNS_ReadNameField_success_empty_uxRemainingBytes( void )
{
    uint8_t pucByte[ 300 ];
    size_t ret;
    ParseSet_t xSet = { 0 };
    size_t uxDestLen;

    memset( pucByte, 0x00, 300 );
    ret = DNS_ReadNameField( &xSet, uxDestLen );
    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures that if the dns name is dnsNAME_IS_OFFSET  and the source
 *        length is less than 2 bytes zero is returned
 */
void test_DNS_ReadNameField_fail_offset_dns_name( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    size_t ret;
    ParseSet_t xSet = { 0 };
    size_t uxDestLen;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;

    ret = DNS_ReadNameField( &xSet, uxDestLen );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures that if the dns name is dnsNAME_IS_OFFSET  and the source
 *        length is greater than 2 bytes 2 is returned (sizeof (uint16_t)
 */
void test_DNS_ReadNameField_success_fully_coded_gt_uint16( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    size_t ret;
    ParseSet_t xSet = { 0 };

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = 8;

    ret = DNS_ReadNameField( &xSet, 234 );

    TEST_ASSERT_EQUAL( sizeof( uint16_t ), ret );
}

/**
 * @brief ensures that if the dns name is dnsNAME_IS_OFFSET  and the source
 *        length is equal to 2 bytes 0 is returned
 */
void test_DNS_ReadNameField_success_half_coded_gt_uint16( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    size_t ret;
    ParseSet_t xSet = { 0 };

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = 2;

    ret = DNS_ReadNameField( &xSet, 234 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures when the next name field size is zero, zero is returned
 */
void test_DNS_ReadNameField_zero_size_walk_over_nothing_to_do( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    size_t ret;
    ParseSet_t xSet = { 0 };

    memset( pucByte, 0x00, 300 );
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = 300;

    pucByte[ 0 ] = 0;

    ret = DNS_ReadNameField( &xSet, 234 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures when the name is 8 bytes 10 is returned . + '\0', and the name
 *        field is copied to pcName
 */
void test_DNS_ReadNameField_walk_over_copy_name( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    size_t ret;
    ParseSet_t xSet = { 0 };

    memset( pucByte, 0x00, 300 );
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = 300;
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );

    ret = DNS_ReadNameField( &xSet, 254 );

    TEST_ASSERT_EQUAL( 10, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS", xSet.pcName );
}

/**
 * @brief ensures when the name is 8 bytes and the size passed is smaller
 *        zero is returned and field id copied to pcName
 */
void test_DNS_ReadNameField_walk_over_exact_source_length( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    size_t ret;
    ParseSet_t xSet = { 0 };
    size_t uxDestLen;

    memset( pucByte, 0x00, 300 );
    memset( xSet.pcName, 0x00, sizeof( xSet.pcName ) );
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = 9;
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );

    ret = DNS_ReadNameField( &xSet, 254 );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS", xSet.pcName );
    TEST_ASSERT_EQUAL( 0, xSet.pcName[ 8 ] );
    TEST_ASSERT_EQUAL( 0, xSet.pcName[ 9 ] );
    TEST_ASSERT_EQUAL( 0, xSet.pcName[ 10 ] );
}

/**
 * @brief ensures when we have 2 names fields
 *        their total + 2(dot, and \0) are returned
 *        and the result string in pcName
 */
void test_DNS_ReadNameField_walk_over_copy_2_names( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    ParseSet_t xSet = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 300 );
    memset( xSet.pcName, 0x00, sizeof( xSet.pcName ) );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = 300;

    ret = DNS_ReadNameField( &xSet, 254 );

    TEST_ASSERT_EQUAL( 18, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.PlusTCP", xSet.pcName );
}

/**
 * @brief ensures that when the destination buffer (pcName) is shorter than the
 *        total string name field, zero is returned and the string is truncated i
 *        pcName
 */
void test_DNS_ReadNameField_short_destination( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    ParseSet_t xSet = { 0 };

    memset( pucByte, 0x00, 300 );
    memset( xSet.pcName, 0x00, sizeof( xSet.pcName ) );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );
    size_t ret;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = 300;

    ret = DNS_ReadNameField( &xSet, 12 );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.", xSet.pcName );
}

/**
 * @brief ensures that when the source buffer (pucByte) is shorter than the size
 *        of the name field, zero is returned, and the resulting string (pcName)
 *        is truncated
 */
void test_DNS_ReadNameField_short_source( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    char pcName[ 300 ] = { 0 };
    ParseSet_t xSet = { 0 };

    memset( pucByte, 0x00, 300 );
    memset( xSet.pcName, 0x00, sizeof( xSet.pcName ) );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );
    size_t ret;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = 10;

    ret = DNS_ReadNameField( &xSet, 254 );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.", xSet.pcName );
}

/**
 * @brief ensures when the second name does not fit the destination zero is
 *        returned and only the first string is returned
 */
void test_DNS_ReadNameField_fail_name_len_gt_destlen( void )
{
    uint8_t pucByte[ 15 ] = { 0 };
    char pcName[ 10 ] = { 0 };
    ParseSet_t xSet = { 0 };
    size_t uxDestLen;

    memset( pucByte, 0x00, 15 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 1;
    size_t ret;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = 15;

    ret = DNS_ReadNameField( &xSet, 10 );
    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL_STRING( "FreeRTOS.", xSet.pcName );
}


/* ==================== Testing  DNS_SkipNameField ===========================*/

/**
 * @brief ensures that if pucByte has a size of zero, zero is returned
 */
void test_DNS_SkipNameField_failed_zero_length()
{
    size_t ret;
    uint8_t pucByte[ 20 ];

    memset( pucByte, 0x00, 20 );

    ret = DNS_SkipNameField( pucByte, 0 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures that the appropriate size is returned + dot, dot, and \0
 */
void test_DNS_SkipNameField_failed_()
{
    uint8_t pucByte[ 300 ] = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );

    ret = DNS_SkipNameField( pucByte, 300 );

    TEST_ASSERT_EQUAL( 18, ret );
}


/**
 * @brief ensures that when it is an offset packet and the size is less than 2
 *        bytes, zero is returned
 */
void test_DNS_SkipNameField_fail_fully_coded( void )
{
    uint8_t pucByte[ 2 ] = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 2 );
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;

    ret = DNS_SkipNameField( pucByte, 2 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures that when it is an offset packet and the size is greater
 *        than 2, 2 is returned
 */
void test_DNS_SkipNameField_success_fully_coded_gt_uint16( void )
{
    uint8_t pucByte[ 300 ] = { 0 };
    size_t ret;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = dnsNAME_IS_OFFSET;

    ret = DNS_SkipNameField( pucByte, 84 );

    TEST_ASSERT_EQUAL( sizeof( uint16_t ), ret );
}

/**
 * @brief ensures that when the source is shorter than the size markings
 *        zero is returned
 */
void test_DNS_SkipNameField_short_source( void )
{
    uint8_t pucByte[ 300 ] = { 0 };

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );
    size_t ret;

    ret = DNS_SkipNameField( pucByte, 10 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/**
 * @brief ensures that when the last name field is less than the buffer
 *        remaining size, zero is returned
 */
void test_DNS_SkipNameField_small_buffer( void )
{
    uint8_t pucByte[ 300 ] = { 0 };

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 8;
    strcpy( pucByte + 1, "FreeRTOS" );
    pucByte[ 9 ] = 7;
    strcpy( pucByte + 10, "PlusTCP" );
    size_t ret;

    ret = DNS_SkipNameField( pucByte, 6 );

    TEST_ASSERT_EQUAL( 0, ret );
}

/* =================== test prepare Reply DNS Message ======================= */

/**
 * @brief Send a DNS message successfully : IPv4
 */
void test_prepareReplyDNSMessage_success( void )
{
    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    uint8_t ether_buffer[ 300 ] = { 0 };
    size_t uxDataLength;
    NetworkEndPoint_t xEndPoint = { 0 };

    pxNetworkBuffer.pucEthernetBuffer = ether_buffer;
    pxNetworkBuffer.xDataLength = 300;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;


    BaseType_t lNetLength = 50;
    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;
    UDPHeader_t * pxUDPHeader;

    pxUDPPacket = ( ( UDPPacket_t * )
                    pxNetworkBuffer.pucEthernetBuffer );
    pxIPHeader = &pxUDPPacket->xIPHeader;
    pxIPHeader->ucVersionHeaderLength = 0x0;
    pxUDPHeader = &pxUDPPacket->xUDPHeader;
    IPPacket_t * xIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer.pucEthernetBuffer );

    pxIPHeader->ulSourceIPAddress = 1234;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    usGenerateChecksum_ExpectAnyArgsAndReturn( 555 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 444 );

    prepareReplyDNSMessage( &pxNetworkBuffer,
                            lNetLength );

    uxDataLength = ( ( size_t ) lNetLength ) + ipSIZE_OF_IPv4_HEADER +
                   ipSIZE_OF_UDP_HEADER + ipSIZE_OF_ETH_HEADER;

    TEST_ASSERT_EQUAL( pxNetworkBuffer.xDataLength, uxDataLength );
    TEST_ASSERT_EQUAL( pxIPHeader->ucTimeToLive, ipconfigUDP_TIME_TO_LIVE );
}

/**
 * @brief Send a DNS message used in MDNS successfully : IPv4
 */
void test_prepareReplyDNSMessage_success_MDNS( void )
{
    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    uint8_t ether_buffer[ 300 ] = { 0 };
    size_t uxDataLength;
    NetworkEndPoint_t xEndPoint = { 0 };

    pxNetworkBuffer.pucEthernetBuffer = ether_buffer;
    pxNetworkBuffer.xDataLength = 300;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;

    BaseType_t lNetLength = 50;
    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;
    UDPHeader_t * pxUDPHeader;

    pxUDPPacket = ( ( UDPPacket_t * )
                    pxNetworkBuffer.pucEthernetBuffer );
    pxIPHeader = &pxUDPPacket->xIPHeader;
    pxIPHeader->ucVersionHeaderLength = 0x0;
    pxUDPHeader = &pxUDPPacket->xUDPHeader;
    IPPacket_t * xIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer.pucEthernetBuffer );

    pxIPHeader->ulSourceIPAddress = 1234;
    pxIPHeader->ulDestinationIPAddress = ipMDNS_IP_ADDRESS;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    usGenerateChecksum_ExpectAnyArgsAndReturn( 555 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 444 );

    prepareReplyDNSMessage( &pxNetworkBuffer,
                            lNetLength );

    uxDataLength = ( ( size_t ) lNetLength ) + ipSIZE_OF_IPv4_HEADER +
                   ipSIZE_OF_UDP_HEADER + ipSIZE_OF_ETH_HEADER;

    TEST_ASSERT_EQUAL( pxNetworkBuffer.xDataLength, uxDataLength );
    TEST_ASSERT_EQUAL( pxIPHeader->ucTimeToLive, ipMDNS_TIME_TO_LIVE );
}

/**
 * @brief Send a DNS message , but end point on NetMask is NULL : IPv4
 */
void test_prepareReplyDNSMessage_NullEndPoint( void )
{
    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    uint8_t ether_buffer[ 300 ] = { 0 };
    size_t uxDataLength;
    NetworkEndPoint_t xEndPoint = { 0 };

    pxNetworkBuffer.pucEthernetBuffer = ether_buffer;
    pxNetworkBuffer.xDataLength = 300;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;


    BaseType_t lNetLength = 50;
    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;
    UDPHeader_t * pxUDPHeader;

    pxUDPPacket = ( ( UDPPacket_t * )
                    pxNetworkBuffer.pucEthernetBuffer );
    pxIPHeader = &pxUDPPacket->xIPHeader;
    pxIPHeader->ucVersionHeaderLength = 0x0;
    pxUDPHeader = &pxUDPPacket->xUDPHeader;
    IPPacket_t * xIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer.pucEthernetBuffer );

    pxIPHeader->ulSourceIPAddress = 1234;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    usGenerateChecksum_ExpectAnyArgsAndReturn( 555 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 444 );

    prepareReplyDNSMessage( &pxNetworkBuffer,
                            lNetLength );

    uxDataLength = ( ( size_t ) lNetLength ) + ipSIZE_OF_IPv4_HEADER +
                   ipSIZE_OF_UDP_HEADER + ipSIZE_OF_ETH_HEADER;

    TEST_ASSERT_EQUAL( pxNetworkBuffer.xDataLength, uxDataLength );
}

/**
 * @brief Send a DNS message successfully , when frame type is IPv6
 */
void test_prepareReplyDNSMessage_IPv6success( void )
{
    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    uint8_t ether_buffer[ 300 ] = { 0 };
    size_t uxDataLength;
    NetworkEndPoint_t xEndPoint = { 0 };

    pxNetworkBuffer.pucEthernetBuffer = ether_buffer;
    pxNetworkBuffer.xDataLength = 300;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;

    BaseType_t lNetLength = 50;

    IPPacket_IPv6_t * xIPPacket_IPv6 = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer.pucEthernetBuffer );
    xIPPacket_IPv6->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;
    UDPHeader_t * pxUDPHeader;

    pxUDPPacket = ( ( UDPPacket_t * )
                    pxNetworkBuffer.pucEthernetBuffer );
    pxIPHeader = &pxUDPPacket->xIPHeader;
    pxUDPHeader = &pxUDPPacket->xUDPHeader;
    IPPacket_t * xIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer.pucEthernetBuffer );

    pxIPHeader->ulSourceIPAddress = 1234;
    pxIPHeader->ucVersionHeaderLength = 0x60U;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv6_HEADER );

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 444 );

    prepareReplyDNSMessage( &pxNetworkBuffer,
                            lNetLength );

    uxDataLength = ( ( size_t ) lNetLength ) + ipSIZE_OF_IPv6_HEADER +
                   ipSIZE_OF_UDP_HEADER + ipSIZE_OF_ETH_HEADER;

    TEST_ASSERT_EQUAL( pxNetworkBuffer.xDataLength, uxDataLength );
}

/**
 * @brief Send a DNS message fail , when frame type is IPv6
 */
void test_prepareReplyDNSMessage_IPv6Fail( void )
{
    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    uint8_t ether_buffer[ 300 ] = { 0 };
    size_t uxDataLength;
    NetworkEndPoint_t xEndPoint = { 0 };

    pxNetworkBuffer.pucEthernetBuffer = ether_buffer;
    pxNetworkBuffer.xDataLength = 300;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;

    BaseType_t lNetLength = 50;
    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;
    UDPHeader_t * pxUDPHeader;

    pxUDPPacket = ( ( UDPPacket_t * )
                    pxNetworkBuffer.pucEthernetBuffer );
    pxIPHeader = &pxUDPPacket->xIPHeader;
    pxIPHeader->ucVersionHeaderLength = 0x0;
    pxUDPHeader = &pxUDPPacket->xUDPHeader;
    IPPacket_t * xIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer.pucEthernetBuffer );

    pxIPHeader->ulSourceIPAddress = 1234;
    pxIPHeader->ucVersionHeaderLength = 0x0U;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv6_HEADER );

    usGenerateChecksum_ExpectAnyArgsAndReturn( 555 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 444 );

    prepareReplyDNSMessage( &pxNetworkBuffer,
                            lNetLength );

    uxDataLength = ( ( size_t ) lNetLength ) + ipSIZE_OF_IPv6_HEADER +
                   ipSIZE_OF_UDP_HEADER + ipSIZE_OF_ETH_HEADER;

    TEST_ASSERT_EQUAL( pxNetworkBuffer.xDataLength, uxDataLength );
    TEST_ASSERT_EQUAL( pxIPHeader->ucTimeToLive, ipconfigUDP_TIME_TO_LIVE );
}

/* / * =========================== test DNS_TreatNBNS  ========================== * / */

/**
 * @brief ensures that when buffer with size less than 92 bytes is passed,
 *        vReturnEthernetFrame is not called
 */
void test_DNS_TreatNBNS_Fail_MinimumBufferSize( void )
{
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength;
    uint32_t ulIPAddress;
    struct xNetworkEndPoint xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint16_t * pusFlags, offset_of_uc = offsetof( NBNSRequest_t, usFlags );

    xNetworkBuffer.pxEndPoint = &xEndPoint;

    DNS_TreatNBNS( pucPayload,
                   91, /*minimum buffer size: 92 bytes*/
                   1234 );
}

/**
 * @brief ensures that when Payload of the message passed is NULL,
 *        vReturnEthernetFrame is not called
 */
void test_DNS_TreatNBNS_Fail_NullPayload( void )
{
    uint8_t * pucPayload = NULL;
    size_t uxBufferLength;
    uint32_t ulIPAddress;
    struct xNetworkEndPoint xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint16_t * pusFlags, offset_of_uc = offsetof( NBNSRequest_t, usFlags );

    xNetworkBuffer.pxEndPoint = &xEndPoint;

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief ensures that when a random payload is passed, vReturnEthernetFrame is
 *        not called
 */
void test_DNS_TreatNBNS_success( void )
{
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength;
    uint32_t ulIPAddress;
    struct xNetworkEndPoint xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint16_t * pusFlags, offset_of_uc = offsetof( NBNSRequest_t, usFlags );

    xNetworkBuffer.pxEndPoint = &xEndPoint;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( NULL );

/*
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
 */
    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief ensures that when a NULL payload is passed, no API is called
 *
 */
void test_DNS_TreatNBNS_FailNullPayload( void )
{
    uint8_t * pucPayload = NULL;
    size_t uxBufferLength;
    uint32_t ulIPAddress;
    struct xNetworkEndPoint xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint16_t * pusFlags, offset_of_uc = offsetof( NBNSRequest_t, usFlags );

    xNetworkBuffer.pxEndPoint = &xEndPoint;

/*
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
 */
    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief ensures that when a Length of the buffer is lesser than uxBytesNeeded , no API is called
 *
 */
void test_DNS_TreatNBNS_FailLessBufferSize( void )
{
    uint8_t * pucPayload = NULL;
    size_t uxBufferLength;
    uint32_t ulIPAddress;
    struct xNetworkEndPoint xEndPoint = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint16_t * pusFlags, offset_of_uc = offsetof( NBNSRequest_t, usFlags );

    xNetworkBuffer.pxEndPoint = &xEndPoint;

/*
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
 */
    DNS_TreatNBNS( pucPayload,
                   ( sizeof( UDPPacket_t ) + sizeof( NBNSRequest_t ) - 1 ),
                   1234 );
}

/**
 * @brief ensures that when a random payload is passed, vReturnEthernetFrame is
 *        not called
 */
void test_DNS_TreatNBNS_success_nbns_mask( void )
{
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength;
    uint32_t ulIPAddress;
    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };

    pxNetworkBuffer.pucEthernetBuffer = pucPayload;

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );

    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_MASK );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief ensures that when new buffer is NULL, vReturnEthernetFrame is not
 *        called
 */
void test_DNS_TreatNBNS_success_nbns_query_trailing_space( void )
{
    uint8_t pucPayload[ 300 ] = { 0 };
    uint8_t ether_buffer[ 300 ] = { 0 };
    size_t uxBufferLength;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };

    pxNetworkBuffer.pucEthernetBuffer = ether_buffer;

    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
    ASSERT_DNS_QUERY_HOOK_NOT_CALLED();
}

/**
 * @brief ensures that when buffer is NULL, vReturnEthernetFrame is not
 *        called
 */
void test_DNS_TreatNBNS_success_nbns_query( void )
{
    uint8_t pucPayload[ 300 ] = { 0 };
    uint8_t ether_buffer[ 300 ] = { 0 };
    size_t uxBufferLength;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };

    pxNetworkBuffer.pucEthernetBuffer = ether_buffer;

    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
/*  FreeRTOS_FindEndPointOnNetMask_ExpectAnyArgsAndReturn( NULL ); */
/*  pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL ); */

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
    ASSERT_DNS_QUERY_HOOK_NOT_CALLED();
}

/**
 * @brief ensures that when new buffer is NULL, vReturnEthernetFrame is not
 *        called
 */
void test_DNS_TreatNBNS_success_nbns_query_network_buffer_null( void )
{
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;


    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( NULL );

/*
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
 *  usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
 */

    DNS_TreatNBNS( pucPayload,
                   uxBufferLength,
                   1234 );
    /*ASSERT_DNS_QUERY_HOOK_CALLED(); */
}

/**
 * @brief success path, formed packet is sent over the network with
 *        vReturnEthernetFrame
 */
void test_DNS_TreatNBNS_success_nbns_non_fixed_size_buffer( void )
{
/*	XXX */
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    struct xNetworkEndPoint xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;
    pxNetworkBuffer.pucEthernetBuffer = pucPayload;
    pxNetworkBuffer.xDataLength = 300;

    NetworkBufferDescriptor_t pxNewBuffer = { 0 };
    pxNewBuffer.pxEndPoint = &xEndPoint;
    pxNewBuffer.pucEthernetBuffer = pucPayload;
    pxNewBuffer.xDataLength = 300;

    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usFlags */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );      /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxResizeNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &pxNewBuffer );

    usGenerateChecksum_ExpectAnyArgsAndReturn( 4 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 4 );
    vReturnEthernetFrame_Expect( &pxNetworkBuffer, pdFALSE ); /* goal */


    DNS_TreatNBNS( pucPayload,
                   uxBufferLength,
                   1234 );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief success path, BufferAllocation_1.c is used, the Network Buffers can contain at least
 *  ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER.
 */
void test_DNS_TreatNBNS_Fail_BufferAllocation1( void )
{
/*	XXX */
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    struct xNetworkEndPoint xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;
    pxNetworkBuffer.pucEthernetBuffer = pucPayload;
    pxNetworkBuffer.xDataLength = 3000;

    hook_return = pdTRUE;
    xBufferAllocFixedSize = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usFlags */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );      /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );

    catch_assert( DNS_TreatNBNS( pucPayload, uxBufferLength, 1234 ) );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief success path, BufferAllocation_1.c is used, the Network Buffers can contain at least
 *  ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER.
 */
void test_DNS_TreatNBNS_success_BufferAllocation1( void )
{
/*	XXX */
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    struct xNetworkEndPoint xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;
    pxNetworkBuffer.pucEthernetBuffer = pucPayload;
    pxNetworkBuffer.xDataLength = 300;

    hook_return = pdTRUE;
    xBufferAllocFixedSize = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usFlags */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );      /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );

    usGenerateChecksum_ExpectAnyArgsAndReturn( 4 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 4 );
    vReturnEthernetFrame_Expect( &pxNetworkBuffer, pdFALSE ); /* goal */

    DNS_TreatNBNS( pucPayload, uxBufferLength, 1234 );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief fail path : application informs that the name in 'ucNBNSName' does not refer to this host.
 */
void test_DNS_TreatNBNS_fail_DNSHookFail( void )
{
/*	XXX */
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    struct xNetworkEndPoint xEndPoint = { 0 };

    pxNetworkBuffer.pxEndPoint = &xEndPoint;
    pxNetworkBuffer.pucEthernetBuffer = pucPayload;
    pxNetworkBuffer.xDataLength = 300;

    hook_return = pdFALSE;

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usFlags */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );      /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );

    DNS_TreatNBNS( pucPayload, uxBufferLength, 1234 );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when pxResizeNetworkBufferWithDescriptor() fails to allocate buffer
 *        we break out of the loop and nothing is sent over the network
 */
void test_DNS_TreatNBNS_success_nbns_null_buffer( void )
{
/*	XXX */
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    struct xNetworkEndPoint xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;
    pxNetworkBuffer.pucEthernetBuffer = pucPayload;
    pxNetworkBuffer.xDataLength = 300;

    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usFlags */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );      /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxResizeNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    DNS_TreatNBNS( pucPayload,
                   uxBufferLength,
                   1234 );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief success path, formed packet is sent over the network with
 *        vReturnEthernetFrame
 */
void test_DNS_TreatNBNS_success_nbns_non_fixed_size_buffer2( void )
{
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;

    xBufferAllocFixedSize = pdFALSE;
    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    struct xNetworkEndPoint xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;
    pxNetworkBuffer.pucEthernetBuffer = pucPayload;
    pxNetworkBuffer.xDataLength = 300;

    hook_return = pdTRUE;
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usFlags */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );      /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    pxResizeNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &pxNetworkBuffer );

    usGenerateChecksum_ExpectAnyArgsAndReturn( 4 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 4 );
    vReturnEthernetFrame_Expect( &pxNetworkBuffer, pdFALSE ); /* goal */

    DNS_TreatNBNS( pucPayload,
                   uxBufferLength,
                   1234 );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief success path, formed packet is sent over the network with
 *        vReturnEthernetFrame
 */
void test_DNS_TreatNBNS_success_nbns_non_fixed_size_buffer3( void )
{
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t xNetworkBuffer;
    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    struct xNetworkEndPoint xEndPoint = { 0 };

    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    uint8_t buffer[ 300 ];

    pxNetworkBuffer.pucEthernetBuffer = buffer;
    pxNetworkBuffer.xDataLength = 300;

    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usFlags */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_CLASS_IN );           /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );

    DNS_TreatNBNS( pucPayload,
                   uxBufferLength,
                   1234 );
}

/**
 * @brief Endpoint is not fully up (invalid IP)
 */
void test_DNS_TreatNBNS_EndpointHasNoValidIP( void )
{
    uint8_t pucPayload[ 300 ] = { 0 };
    size_t uxBufferLength = 300;
    uint32_t ulIPAddress;

    NetworkBufferDescriptor_t xNetworkBuffer = { 0 };
    struct xNetworkEndPoint xEndPoint = { 0 };

    xNetworkBuffer.pxEndPoint = &xEndPoint;
    uint8_t buffer[ 300 ];

    xNetworkBuffer.pucEthernetBuffer = buffer;
    xNetworkBuffer.xDataLength = 300;
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usFlags */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );      /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );

    DNS_TreatNBNS( pucPayload,
                   uxBufferLength,
                   1234 );
}

/**
 * @brief ensures that when pucPayload + dnsNBNS_ENCODED_NAME_LENGTH = 41U = 'A'
 *        we break out of the loop and nothing is sent over the network if the
 *        whole name if not in capital letters and terminated with '\0'
 */
void test_DNS_TreatNBNS_success_empty_char_nbns_name( void )
{
    uint8_t pucPayload[ 300 ] = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct xNetworkEndPoint xEndPoint = { 0 };

    xNetworkBuffer.pxEndPoint = &xEndPoint;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) +
                offsetof( NBNSRequest_t, ucName ) ] = 2 + 0x41U;
    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) +
                offsetof( NBNSRequest_t, ucName ) + 1 ] = ' ' + 0x41U;

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY | dnsNBNS_FLAGS_RESPONSE );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( 1 );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}

/**
 * @brief ensures that when pucPayload + dnsNBNS_ENCODED_NAME_LENGTH = 41U = 'A'
 *        we break out of the loop and nothing is sent over the network if the
 *        whole name if not in capital letters and terminated with '\0'
 */
void test_DNS_TreatNBNS_success_empty_char_nbns_name2( void )
{
    uint8_t pucPayload[ 300 ] = { 0 };
    NetworkBufferDescriptor_t xNetworkBuffer;
    struct xNetworkEndPoint xEndPoint = { 0 };

    xNetworkBuffer.pxEndPoint = &xEndPoint;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) +
                offsetof( NBNSRequest_t, ucName ) ] = 2 + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) + 1 ] = ' ' + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 1 ] = ' ' + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 2 ] = ' ' + 0x42U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 3 ] = ' ' + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 4 ] = ' ' + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 5 ] = ' ' + 0x41U;

    pucPayload[ ( dnsNBNS_ENCODED_NAME_LENGTH - 2 ) + /* 32 - 2 */
                offsetof( NBNSRequest_t, ucName ) - 6 ] = ' ' + 0x41U;

    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY | dnsNBNS_FLAGS_RESPONSE );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_TYPE_NET_BIOS );
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( 1 );

    DNS_TreatNBNS( pucPayload,
                   300,
                   1234 );
}
/* ======================== test DNS_ParseDNSReply ========================== */

/**
 * @brief ensures that when the passed buffer is smaller than DNS_Message_t
 *        false is returned
 */
void test_DNS_ParseDNSReply_fail_small_buffer( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ sizeof( DNSMessage_t ) - 2 ];
    size_t uxBufferLength = sizeof( DNSMessage_t ) - 2;
    BaseType_t xExpected = pdFALSE;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief ensures that when the buffer is empty false is returned
 */
void test_DNS_ParseDNSReply_fail_no_namefield( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 300 ] = { 0 };
    size_t uxBufferLength = 300;
    BaseType_t xExpected = pdFALSE;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}


/**
 * @brief
 */
void test_DNS_ParseDNSReply_fail( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 300 ];
    size_t uxBufferLength = 300;
    BaseType_t xExpected = pdFALSE;
    int beg = sizeof( DNSMessage_t );
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;

    memset( pucUDPPayloadBuffer, 0x00, 300 );

    pucUDPPayloadBuffer[ beg++ ] = 8;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS" );


    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief
 */
void test_DNS_ParseDNSReply_fail_empty_namefield( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 300 ];
    size_t uxBufferLength = 300;
    BaseType_t xExpected = pdFALSE;
    uint8_t beg = sizeof( DNSMessage_t );
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );
    pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usQuestions ) ] = 4;

    pucUDPPayloadBuffer[ beg++ ] = 8;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS" );

    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usClass */

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief
 */
void test_DNS_ParseDNSReply_fail_not_enough_space_lt_32( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ];
    size_t uxBufferLength = 250;
    char dns[ 64 ];
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usQuestions ) ] = 4;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOS111111111111111111111111111111" );
    beg += 38;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief
 */
void test_DNS_ParseDNSReply_answer_record_no_answers( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ];
    size_t uxBufferLength = 250;
    char dns[ 64 ];
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    const uint16_t usFlags = ( dnsRX_FLAGS_MASK | dnsEXPECTED_RX_FLAGS );

    memset( dns, 'a', 64 );
    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usQuestions ) ] = 0;
    pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usAnswers ) ] = 0;

    memcpy( &pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usFlags ) ], &usFlags, sizeof( uint16_t ) );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief Check the case when the DNS answer record
 * doesn't have any answers.
 */
void test_DNS_ParseDNSReply_answer_record_no_answers2( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ];
    size_t uxBufferLength = 250;
    char dns[ 64 ];
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    const uint16_t usFlags = dnsEXPECTED_RX_FLAGS;

    memset( dns, 'a', 64 );
    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usQuestions ) ] = 0;
    pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usAnswers ) ] = 0;

    memcpy( &pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usFlags ) ], &usFlags, sizeof( uint16_t ) );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief Check the case when the DNS answer record
 * doesn't have any questions.
 */
void test_DNS_ParseDNSReply_answer_record_no_questions( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ];
    size_t uxBufferLength = 250;
    char dns[ 64 ];
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    const uint16_t usFlags = dnsEXPECTED_RX_FLAGS;

    memset( dns, 'a', 64 );
    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 0 );
    dns_header->usAnswers = FreeRTOS_htons( 1 );

    memcpy( &pucUDPPayloadBuffer[ offsetof( DNSMessage_t, usFlags ) ], &usFlags, sizeof( uint16_t ) );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */

    hook_return = pdTRUE;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief Test DNS_ParseDNSReply when the endpoint has an invalid IP (0)
 */
void test_DNS_ParseDNSReply_InvalidEndpointIP( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;

    xBufferAllocFixedSize = pdTRUE;
    uint8_t * nullAddress = NULL;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer;
    pxNewBuffer.xDataLength = uxBufferLength;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdTRUE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
    LLMNRAnswer_t * pxAnswer = ( LLMNRAnswer_t * ) &( pucNewBuffer[ 56 ] ); /* xOffset1 = 56 */

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );                    /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );                       /* usClass */

    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief Test DNS_ParseDNSReply when the endpoint is non matching (IPv6)
 */
void test_DNS_ParseDNSReply_InvalidEndpointType( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4 + 250 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = udp_buffer + prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;

    xBufferAllocFixedSize = pdTRUE;
    uint8_t * nullAddress = NULL;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer + prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4 - ipUDP_PAYLOAD_OFFSET_IPv4;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer + prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4 - ipUDP_PAYLOAD_OFFSET_IPv4;
    pxNewBuffer.xDataLength = uxBufferLength;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdTRUE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
    LLMNRAnswer_t * pxAnswer = ( LLMNRAnswer_t * ) &( pucNewBuffer[ 56 ] ); /* xOffset1 = 56 */

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );                    /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );                       /* usClass */

    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usGenerateChecksum_ExpectAnyArgsAndReturn( 555 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 444 );
    vReturnEthernetFrame_Expect( &pxNetworkBuffer, pdFALSE );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );
    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief
 */
void test_DNS_ParseDNSReply_answer_record_too_many_answers( void )
{
    uint32_t ret;
    uint8_t pucUDPPayloadBuffer[ 250 ] = { 0 };
    size_t uxBufferLength = 250;
    char dns[ 64 ];
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;

    memset( dns, 'a', 64 );
    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) &pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsEXPECTED_RX_FLAGS;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usClass */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY ); /* usType */

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply_xBufferAllocFixedsize( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4 + 250 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = udp_buffer + prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;

    xBufferAllocFixedSize = pdTRUE;
    uint8_t * nullAddress = NULL;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer + prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4 - ipUDP_PAYLOAD_OFFSET_IPv4;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer + prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4 - ipUDP_PAYLOAD_OFFSET_IPv4;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdTRUE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
    LLMNRAnswer_t * pxAnswer = ( LLMNRAnswer_t * ) &( pucNewBuffer[ 56 ] ); /* xOffset1 = 56 */

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );                    /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );                       /* usClass */

    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );


    TEST_ASSERT_EQUAL( dnsPARSE_ERROR, ret );
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4 + 250 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = udp_buffer + prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer + prvALIGNED_UDP_PAYLOAD_OFFSET_IPv4 - ipUDP_PAYLOAD_OFFSET_IPv4;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ 0 ] );
    LLMNRAnswer_t * pxAnswer = ( LLMNRAnswer_t * ) &( pucNewBuffer[ 56 ] ); /* xOffset1 = 56 */

    xEndPoint.ipv4_settings.ulIPAddress = 11;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );    /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_NOT_CALLED();
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame : uxUDPOffset = ipUDP_PAYLOAD_OFFSET_IPv6
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply2( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv6 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv6;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ 0 ] );
    LLMNRAnswer_t * pxAnswer = ( LLMNRAnswer_t * ) &( pucNewBuffer[ 56 ] ); /* xOffset1 = 56 */

    xEndPoint.ipv4_settings.ulIPAddress = 11;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );    /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_NOT_CALLED();
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame : uxUDPOffset != ipUDP_PAYLOAD_OFFSET_IPv4 || uxUDPOffset != ipUDP_PAYLOAD_OFFSET_IPv6
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply3( void )
{
    uint32_t ret = 0xDEADC0DE;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4 - 1;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ 0 ] );
    LLMNRAnswer_t * pxAnswer = ( LLMNRAnswer_t * ) &( pucNewBuffer[ 56 ] ); /* xOffset1 = 56 */

    xEndPoint.ipv4_settings.ulIPAddress = 11;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );    /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    catch_assert( ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                                           uxBufferLength,
                                           &pxAddressInfo,
                                           xExpected,
                                           usPort ) );

    /* ret is not reassigned, because the function asserts. */
    TEST_ASSERT_EQUAL( 0xDEADC0DE, ret );
    ASSERT_DNS_QUERY_HOOK_NOT_CALLED();
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame : usType = dnsTYPE_AAAA_HOST
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply_diffUsType( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ 0 ] );
    LLMNRAnswer_t * pxAnswer = ( LLMNRAnswer_t * ) &( pucNewBuffer[ 56 ] ); /* xOffset1 = 56 */

    xEndPoint.ipv4_settings.ulIPAddress = 11;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_AAAA_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );       /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_NOT_CALLED();
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame : pxNetworkBuffer = NULL
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply_NullNetworkBuffer( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ 0 ] );
    LLMNRAnswer_t * pxAnswer = ( LLMNRAnswer_t * ) &( pucNewBuffer[ 56 ] ); /* xOffset1 = 56 */

    xEndPoint.ipv4_settings.ulIPAddress = 11;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_AAAA_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );       /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( NULL );
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_NOT_CALLED();
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame : usType = 0
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply4( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 ); /* 0000000100000000 */
    dns_header->usAnswers = FreeRTOS_htons( 2 );   /* 0000001000000000 */
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
    LLMNRAnswer_t * pxAnswer = ( LLMNRAnswer_t * ) &( pucNewBuffer[ 56 ] ); /* xOffset1 = 56 */

    usChar2u16_ExpectAnyArgsAndReturn( 0 );                                 /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );                       /* usClass */
    hook_return = pdTRUE;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief ensures that the ip set in Setup is passed to the network with
 *        vReturnEthernetFrame : usClass != dnsCLASS_IN
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply5( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uint8_t * pucNewBuffer = NULL;
    pucNewBuffer = &( pucUDPPayloadBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
    LLMNRAnswer_t * pxAnswer = ( LLMNRAnswer_t * ) &( pucNewBuffer[ 56 ] ); /* xOffset1 = 56 */

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );                    /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsNBNS_FLAGS_OPCODE_QUERY );        /* usClass */
    hook_return = pdTRUE;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );


    TEST_ASSERT_EQUAL( pdFALSE, ret );
}

/**
 * @brief ensures that when the dns query hook returns pdFALSE, the ip is not
 *        set and no packet is sent over the network
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply_query_hook_false( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4;
    struct freertos_addrinfo * pxAddressInfo;
    struct xNetworkEndPoint xEndPoint = { 0 };
    uint16_t usPort;

    memset( pucUDPPayloadBuffer, 0x0, 250 );
    size_t uxBufferLength = 250;

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );    /* usClass */
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );

    hook_return = pdFALSE;

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when the duplicated network buffer is null, no packet is
 *        sent over the network
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply_null_new_netbuffer( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );    /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when the duplicated network buffer is null, no packet is
 *        sent over the network
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply_null_new_netbuffer2( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_AAAA_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );       /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when the duplicated network buffer is valid, packet is
 *        sent over the network
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply_valid_new_netbuffer( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;

    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;
    UDPHeader_t * pxUDPHeader;

    pxUDPPacket = ( ( UDPPacket_t * )
                    pxNetworkBuffer.pucEthernetBuffer );
    pxIPHeader = &pxUDPPacket->xIPHeader;
    pxIPHeader->ucVersionHeaderLength = 0x0;
    pxUDPHeader = &pxUDPPacket->xUDPHeader;
    IPPacket_t * xIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer.pucEthernetBuffer );

    pxIPHeader->ulSourceIPAddress = 1234;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );    /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &pxNetworkBuffer );

    usGenerateChecksum_ExpectAnyArgsAndReturn( 555 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 444 );
    vReturnEthernetFrame_Expect( &pxNetworkBuffer, pdFALSE );
    vReleaseNetworkBufferAndDescriptor_Expect( &pxNetworkBuffer );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when the duplicated network buffer is valid, packet is
 *        sent over the network
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply_valid_new_netbuffer2( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;

    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;
    UDPHeader_t * pxUDPHeader;

    pxUDPPacket = ( ( UDPPacket_t * )
                    pxNetworkBuffer.pucEthernetBuffer );
    pxIPHeader = &pxUDPPacket->xIPHeader;
    pxIPHeader->ucVersionHeaderLength = 0x0;
    pxUDPHeader = &pxUDPPacket->xUDPHeader;
    IPPacket_t * xIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer.pucEthernetBuffer );

    pxIPHeader->ulSourceIPAddress = 1234;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_AAAA_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );       /* usClass */
    hook_return = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &pxNetworkBuffer );

    usGenerateChecksum_ExpectAnyArgsAndReturn( 555 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 444 );
    vReturnEthernetFrame_Expect( &pxNetworkBuffer, pdFALSE );
    vReleaseNetworkBufferAndDescriptor_Expect( &pxNetworkBuffer );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when the duplicated network buffer is valid, packet is
 *        sent over the network, buffer allocation 1 scheme is used
 */
void test_DNS_ParseDNSReply_answer_lmmnr_reply_valid_new_netbuffer3( void )
{
    uint32_t ret;
    uint8_t udp_buffer[ 250 + ipUDP_PAYLOAD_OFFSET_IPv4 ] = { 0 };
    uint8_t * pucUDPPayloadBuffer = ( ( uint8_t * ) udp_buffer ) + ipUDP_PAYLOAD_OFFSET_IPv4;
    size_t uxBufferLength = 250;
    struct freertos_addrinfo * pxAddressInfo;
    uint16_t usPort;
    NetworkEndPoint_t xEndPoint = { 0 };

    memset( pucUDPPayloadBuffer, 0x00, uxBufferLength );

    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    xEndPoint.ipv4_settings.ulIPAddress = 0xABCD1234;
    pxNetworkBuffer.pucEthernetBuffer = udp_buffer;
    pxNetworkBuffer.xDataLength = uxBufferLength;
    pxNetworkBuffer.pxEndPoint = &xEndPoint;

    UDPPacket_t * pxUDPPacket;
    IPHeader_t * pxIPHeader;
    UDPHeader_t * pxUDPHeader;

    pxUDPPacket = ( ( UDPPacket_t * )
                    pxNetworkBuffer.pucEthernetBuffer );
    pxIPHeader = &pxUDPPacket->xIPHeader;
    pxIPHeader->ucVersionHeaderLength = 0x0;
    pxUDPHeader = &pxUDPPacket->xUDPHeader;
    IPPacket_t * xIPPacket = ( ( IPPacket_t * ) pxNetworkBuffer.pucEthernetBuffer );

    pxIPHeader->ulSourceIPAddress = 1234;

    NetworkBufferDescriptor_t pxNewBuffer;
    pxNewBuffer.pucEthernetBuffer = udp_buffer;
    pxNewBuffer.xDataLength = uxBufferLength;

    char dns[ 64 ];
    memset( dns, 'a', 64 );
    dns[ 63 ] = 0;
    BaseType_t xExpected = pdFALSE;
    size_t beg = sizeof( DNSMessage_t );

    DNSMessage_t * dns_header;

    dns_header = ( DNSMessage_t * ) pucUDPPayloadBuffer;

    dns_header->usQuestions = FreeRTOS_htons( 1 );
    dns_header->usAnswers = FreeRTOS_htons( 2 );
    dns_header->usFlags = dnsDNS_PORT;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    beg += sizeof( uint32_t );

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    pucUDPPayloadBuffer[ beg ] = 38;
    beg++;
    strcpy( pucUDPPayloadBuffer + beg, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    beg += 38;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_AAAA_HOST ); /* usType */
    usChar2u16_ExpectAnyArgsAndReturn( dnsCLASS_IN );       /* usClass */
    hook_return = pdTRUE;
    xBufferAllocFixedSize = pdTRUE;
    pxUDPPayloadBuffer_to_NetworkBuffer_ExpectAnyArgsAndReturn( &pxNetworkBuffer );

    usGenerateChecksum_ExpectAnyArgsAndReturn( 555 );
    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( 444 );
    vReturnEthernetFrame_Expect( &pxNetworkBuffer, pdFALSE );

    ret = DNS_ParseDNSReply( pucUDPPayloadBuffer,
                             uxBufferLength,
                             &pxAddressInfo,
                             xExpected,
                             usPort );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    ASSERT_DNS_QUERY_HOOK_CALLED();
}

/**
 * @brief ensures that when the number of answers is zero no packet is sent over
 *        the network
 */
void test_parseDNSAnswer_no_answers( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo;

    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = pdFALSE;
    memset( pucByte, 0x00, uxsourceBytesRemaining );

    pxDNSMessageHeader.usAnswers = 0;

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );
    TEST_ASSERT_FALSE( ret );
    TEST_ASSERT_EQUAL( 0, uxBytesRead );
}

/**
 * @brief ensures that when the total bytes is zero no packet is sent over
 *        the network
 */
void test_parseDNSAnswer_null_bytes( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    ParseSet_t xSet = { 0 };
    IPv46_Address_t ip_address;

    ip_address.xIPAddress.ulIP_IPv4 = 1234;
    ip_address.xIs_IPv6 = pdFALSE;
    struct freertos_addrinfo * pxAddressInfo, * pxAddressInfo_2;

    DNSAnswerRecord_t * pxDNSAnswerRecord;

    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.pucByte = pucByte;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = pdTRUE;
    xSet.usNumARecordsStored = 0;
    xSet.ppxLastAddress = &pxAddressInfo_2;
    memset( pucByte, 0x00, uxsourceBytesRemaining );

    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );
    pxDNSMessageHeader.usAnswers = 1;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, NULL );
    TEST_ASSERT_FALSE( ret );
    TEST_ASSERT_EQUAL( 0, uxBytesRead );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned
 */
void test_parseDNSAnswer_recordstored_gt_count( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    IPv46_Address_t ip_address;
    const uint32_t ulTestAddress = 0xABCD1234;

    ip_address.xIPAddress.ulIP_IPv4 = 1234;
    ip_address.xIs_IPv6 = pdFALSE;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo, * pxAddressInfo_2;

    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = pdTRUE;
    xSet.usNumARecordsStored = 0;
    xSet.ppxLastAddress = &pxAddressInfo_2;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    memset( pucByte, 0x00, uxsourceBytesRemaining );


    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    memcpy( ( ( uint8_t * ) pxDNSAnswerRecord ) + sizeof( DNSAnswerRecord_t ), &ulTestAddress, sizeof( ulTestAddress ) );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    pxNew_AddrInfo_ExpectAnyArgsAndReturn( pxAddressInfo );
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ReturnThruPtr_pxIP( &ip_address );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( ( const char * ) &( xSet.ulIPAddress ) );

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned : usType: dnsTYPE_AAAA_HOST
 */
void test_parseDNSAnswer_recordstored_gt_count_diffUsType( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    uint32_t ip_address = 1234;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo, * pxAddressInfo_2;

    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = pdTRUE;
    xSet.usNumARecordsStored = 0;
    xSet.ppxLastAddress = &pxAddressInfo_2;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;

    memset( pucByte, 0x00, uxsourceBytesRemaining );


    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_AAAA_HOST );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_AAAA_HOST ); /* usType */

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned : usType: dnsTYPE_AAAA_HOST
 * uxSourceBytesRemaining is lesser than size of the DNS message
 */
void test_parseDNSAnswer_recordNOTstored_gt_count_diffUsType( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 30;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    uint32_t ip_address = 1234;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo, * pxAddressInfo_2;

    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = pdTRUE;
    xSet.usNumARecordsStored = 0;
    xSet.ppxLastAddress = &pxAddressInfo_2;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;

    memset( pucByte, 0x00, uxsourceBytesRemaining );


    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_AAAA_HOST );

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 0, uxBytesRead );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned when address is of type IPv6,
 *  usType is NOT dnsTYPE_AAAA_HOST
 */
void test_parseDNSAnswer_recordstored_gt_count_IPv6_fail1( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    uint32_t ip_address = 1234;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo, * pxAddressInfo_2;

    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = pdTRUE;
    xSet.usNumARecordsStored = 0;
    xSet.ppxLastAddress = &pxAddressInfo_2;
    xSet.uxAddressLength = ipSIZE_OF_IPv6_ADDRESS;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;

    memset( pucByte, 0x00, uxsourceBytesRemaining );


    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv6_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_ANY_HOST );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_ANY_HOST ); /* usType */

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned when address is of type IPv6,
 *  usType is NOT dnsTYPE_AAAA_HOST
 */
void test_parseDNSAnswer_recordstored_gt_count_IPv6_fail2( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    uint32_t ip_address = 1234;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo, * pxAddressInfo_2;

    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = pdTRUE;
    xSet.usNumARecordsStored = 0;
    xSet.uxAddressLength = ipSIZE_OF_IPv6_ADDRESS;
    xSet.ppxLastAddress = &pxAddressInfo_2;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;

    memset( pucByte, 0x00, uxsourceBytesRemaining );


    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv6_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned when address is of type IPv6,
 *  usType is dnsTYPE_AAAA_HOST
 */
void test_parseDNSAnswer_recordstored_gt_count_IPv6_success( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    IPv46_Address_t ip_address;

    memset( &( ip_address.xIPAddress.xIP_IPv6 ), 1, ipSIZE_OF_IPv6_ADDRESS );
    ip_address.xIs_IPv6 = pdTRUE;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo xAddressInfo = { 0 }, * pxAddressInfo, * pxAddressInfo_2;

    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = pdTRUE;
    xSet.usNumARecordsStored = 0;
    xSet.ppxLastAddress = &pxAddressInfo_2;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;

    memset( pucByte, 0x00, uxsourceBytesRemaining );


    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv6_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_AAAA_HOST );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_AAAA_HOST ); /* usType */
    pxNew_AddrInfo_ExpectAnyArgsAndReturn( &xAddressInfo );
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ReturnThruPtr_pxIP( &ip_address );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( ( const char * ) &( xSet.ulIPAddress ) );

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned when address is of type IPv6,
 *  usType is dnsTYPE_AAAA_HOST
 */
void test_parseDNSAnswer_recordstored_gt_count_IPv6_success2( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    IPv46_Address_t ip_address;

    memset( &( ip_address.xIPAddress.xIP_IPv6 ), 1, ipSIZE_OF_IPv6_ADDRESS );
    ip_address.xIs_IPv6 = pdTRUE;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo, * pxAddressInfo_2;

    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = pdTRUE;
    xSet.usNumARecordsStored = 0;
    xSet.ppxLastAddress = &pxAddressInfo_2;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;

    memset( pucByte, 0x00, uxsourceBytesRemaining );


    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv6_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_AAAA_HOST );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_AAAA_HOST ); /* usType */
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ReturnThruPtr_pxIP( &ip_address );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( ( const char * ) &( xSet.ulIPAddress ) );

    ret = parseDNSAnswer( &xSet, NULL, &uxBytesRead );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned when address is of type IPv6,
 *  usType is dnsTYPE_AAAA_HOST
 *  xDoAccept = FALSE
 */
void test_parseDNSAnswer_recordstored_gt_count_IPv6_success3( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 56;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    IPv46_Address_t ip_address;

    memset( &( ip_address.xIPAddress.xIP_IPv6 ), 1, ipSIZE_OF_IPv6_ADDRESS );
    ip_address.xIs_IPv6 = pdTRUE;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo, * pxAddressInfo_2;

    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = pdTRUE;
    xSet.usNumARecordsStored = 0;
    xSet.ppxLastAddress = &pxAddressInfo_2;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;

    memset( pucByte, 0x00, uxsourceBytesRemaining );


    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv6_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_AAAA_HOST );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_AAAA_HOST ); /* usType */

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}


/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned when address is of type IPv6,
 *  usType is dnsTYPE_AAAA_HOST
 */
void test_parseDNSAnswer_recordstored_gt_count_IPv6_fail_nullLinkedListForDNSAns( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    IPv46_Address_t ip_address;
    const uint32_t ulTestAddress = 0xABCD1234;

    memset( &( ip_address.xIPAddress.xIP_IPv6 ), 1, ipSIZE_OF_IPv6_ADDRESS );
    ip_address.xIs_IPv6 = pdTRUE;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo, * pxAddressInfo_2;

    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.pucByte = pucByte;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = pdTRUE;
    xSet.usNumARecordsStored = 0;
    xSet.ppxLastAddress = &pxAddressInfo_2;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;

    memset( pucByte, 0x00, uxsourceBytesRemaining );


    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    memcpy( ( ( uint8_t * ) pxDNSAnswerRecord ) + sizeof( DNSAnswerRecord_t ), &ulTestAddress, sizeof( ulTestAddress ) );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ReturnThruPtr_pxIP( &ip_address );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( ( const char * ) &( xSet.ulIPAddress ) );

    ret = parseDNSAnswer( &xSet, NULL, &uxBytesRead );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when more records are stored than allowed by
 * ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY true is returned
 */
void test_parseDNSAnswer_recordstored_gt_count2( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char * pcName = "FreeRTOS+TCP";
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    DNSAnswerRecord_t * pxDNSAnswerRecord2;
    uint32_t ip_address = 1234;
    uint32_t ip_address2 = 2345;
    int index = 0;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo = NULL;

    memset( pucByte, 0x00, uxsourceBytesRemaining );

    pucByte[ index ] = 38;
    index += 1;
    strcpy( pucByte + index, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );
    index += 39; /* String + \0 */
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + index );
    index += sizeof( DNSAnswerRecord_t );
    memcpy( pucByte + index, &ip_address, 4 );
    index += 4;

    pucByte[ index ] = 38;
    index += 1;
    strcpy( pucByte + index, "FreeRTOSaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" );
    index += 39; /* String + \0 */
    pxDNSAnswerRecord2 = ( DNSAnswerRecord_t * ) ( pucByte + index );
    index += sizeof( DNSAnswerRecord_t );
    memcpy( pucByte + index, &ip_address2, 4 );
    index += 4;
    pucByte[ index ] = 0;

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );
    pxDNSAnswerRecord->ulTTL = 23;
    pxDNSAnswerRecord->usClass = 45;

    pxDNSAnswerRecord2->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord2->usType = ( dnsTYPE_A_HOST );
    pxDNSAnswerRecord2->ulTTL = 67;
    pxDNSAnswerRecord2->usClass = 89;

    xSet.pucByte = pucByte;
    xSet.usNumARecordsStored = 0;
    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    strcpy( xSet.pcName, pcName );
    xSet.xDoStore = xDoStore;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    pxNew_AddrInfo_ExpectAnyArgsAndReturn( pxAddressInfo );
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( ( const char * ) &( xSet.ulIPAddress ) );

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    pxNew_AddrInfo_ExpectAnyArgsAndReturn( pxAddressInfo );
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( ( const char * ) &( xSet.ulIPAddress ) );


    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( 1234, ret );
    TEST_ASSERT_EQUAL( 80, uxBytesRead );
}

/**
 * @brief ensures that when the number of entries is larger than the configured
 *        cache address entries, not packet is sent over the network
 */
void test_parseDNSAnswer_dns_nocallback_false( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    IPv46_Address_t ip_address;
    const uint32_t ulTestAddress = 0xABCD1234;

    ip_address.xIPAddress.ulIP_IPv4 = 5678;
    ip_address.xIs_IPv6 = pdFALSE;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo xAddressInfo = { 0 };
    struct freertos_addrinfo ** ppxAddressInfo = ( struct freertos_addrinfo ** ) &pucAddrBuffer;

    *ppxAddressInfo = NULL;

    memset( pucByte, 0x00, uxsourceBytesRemaining );

    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;
    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    memcpy( ( ( uint8_t * ) pxDNSAnswerRecord ) + sizeof( DNSAnswerRecord_t ), &ulTestAddress, sizeof( ulTestAddress ) );

    xSet.pucByte = pucByte;
    xSet.usNumARecordsStored = 0;
    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = xDoStore;
    xSet.ppxLastAddress = ppxAddressInfo;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    pxNew_AddrInfo_ExpectAnyArgsAndReturn( &xAddressInfo );
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdFALSE );
    FreeRTOS_dns_update_ExpectAnyArgsAndReturn( pdTRUE );
    FreeRTOS_dns_update_ReturnThruPtr_pxIP( &ip_address );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( "ignored" );

    ret = parseDNSAnswer( &xSet, ppxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( 0, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when the number of entries is larger than the configured
 *        cache address entries, not packet is sent over the network
 */
void test_parseDNSAnswer_do_store_false( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdFALSE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo;
    struct freertos_addrinfo ** ppxAddressInfo = ( struct freertos_addrinfo ** ) &pucAddrBuffer;
    const uint32_t ulTestAddress = 0xABCD1234;

    memset( pucByte, 0x00, 300 );
    memset( pcName, 0x00, 300 );
    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    memset( &pxDNSMessageHeader, 0x00, sizeof( DNSMessage_t ) );
    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    xSet.pucByte = pucByte;
    xSet.usNumARecordsStored = 0;
    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = xDoStore;
    xSet.ppxLastAddress = ppxAddressInfo;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */
    pxNew_AddrInfo_ExpectAnyArgsAndReturn( NULL );
    xDNSDoCallback_ExpectAnyArgsAndReturn( pdFALSE );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( "ignored" );

    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    memcpy( ( ( uint8_t * ) pxDNSAnswerRecord ) + sizeof( DNSAnswerRecord_t ), &ulTestAddress, sizeof( ulTestAddress ) );

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when the number of entries is larger than the configured
 *        cache address entries, not packet is sent over the network
 *
 */
void test_parseDNSAnswer_dnsanswerrecord_datalength_ne_addresslength( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 300;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo;

    memset( pucByte, 0x00, uxsourceBytesRemaining );
    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    xSet.pucByte = pucByte;
    xSet.usNumARecordsStored = 0;
    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = xDoStore;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */

    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS + 2 );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when the number of entries is larger than the configured
 *        cache address entries, not packet is sent over the network
 *
 */
void test_parseDNSAnswer_remaining_gt_datalength( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 40 + sizeof( DNSAnswerRecord_t ) + 2;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo;

    memset( pucByte, 0x00, 300 );

    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    xSet.pucByte = pucByte;
    xSet.usNumARecordsStored = 0;
    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = xDoStore;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST ); /* usType */

    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when source bytes remaining int pucByte are
 *        less than 16bytes processing is stopped and false is returned
 */
void test_parseDNSAnswer_remaining_lt_uint16( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = 40 + 1;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST );

    xSet.pucByte = pucByte;
    xSet.usNumARecordsStored = 0;
    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = xDoStore;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    TEST_ASSERT_EQUAL( 40, uxBytesRead );
}

/**
 * @brief ensures that when the number of entries is larger than the configured
 *        cache address entries, not packet is sent over the network
 *
 */
void test_parseDNSAnswer_remaining_lt_dnsanswerrecord( void )
{
    BaseType_t ret;
    DNSMessage_t pxDNSMessageHeader;
    char pucByte[ 300 ];
    size_t uxsourceBytesRemaining = sizeof( DNSAnswerRecord_t ) + 38;
    size_t uxBytesRead = 0;
    char pcName[ 300 ];
    BaseType_t xDoStore = pdTRUE;
    DNSAnswerRecord_t * pxDNSAnswerRecord;
    ParseSet_t xSet = { 0 };
    struct freertos_addrinfo * pxAddressInfo;

    memset( pucByte, 0x00, 300 );
    pucByte[ 0 ] = 38;
    strcpy( pucByte + 1, "FreeRTOSbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" );

    pxDNSMessageHeader.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    pxDNSAnswerRecord = ( DNSAnswerRecord_t * ) ( pucByte + 40 );
    pxDNSAnswerRecord->usDataLength = FreeRTOS_htons( ipSIZE_OF_IPv4_ADDRESS );
    pxDNSAnswerRecord->usType = ( dnsTYPE_A_HOST + 1 );

    xSet.pucByte = pucByte;
    xSet.usNumARecordsStored = 0;
    xSet.pxDNSMessageHeader = &pxDNSMessageHeader;
    xSet.uxSourceBytesRemaining = uxsourceBytesRemaining;
    xSet.xDoStore = xDoStore;
    xSet.usAnswers = ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1;

    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST + 1 );
    usChar2u16_ExpectAnyArgsAndReturn( dnsTYPE_A_HOST );

    ret = parseDNSAnswer( &xSet, &pxAddressInfo, &uxBytesRead );

    TEST_ASSERT_EQUAL( pdFALSE, ret );
    TEST_ASSERT_EQUAL( 44, uxBytesRead );
}

BaseType_t xApplicationDNSQueryHook_Multi( struct xNetworkEndPoint * pxEndPoint,
                                           const char * pcName )
{
    hook_called = pdTRUE;
    return hook_return;
}

void test_prepareReplyDNSMessage_null_pointer( void )
{
    NetworkBufferDescriptor_t pxNetworkBuffer = { 0 };
    uint8_t ether_buffer[ 300 ] = { 0 };
    size_t uxDataLength;
    BaseType_t lNetLength = 54;
    NetworkEndPoint_t xEndPoint = { 0 };

    pxNetworkBuffer.pucEthernetBuffer = ether_buffer;
    pxNetworkBuffer.xDataLength = 300;
    /* This will cause an assert(). */
    pxNetworkBuffer.pxEndPoint = NULL;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );
    catch_assert( prepareReplyDNSMessage( &pxNetworkBuffer, lNetLength ) );
}
