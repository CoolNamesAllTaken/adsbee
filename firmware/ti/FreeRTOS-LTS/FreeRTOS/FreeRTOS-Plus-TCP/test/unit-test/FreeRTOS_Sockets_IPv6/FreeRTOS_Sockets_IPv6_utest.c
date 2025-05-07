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
#include "mock_Sockets_IPv6_list_macros.h"
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_portable.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_DHCP.h"
#include "mock_FreeRTOS_DNS.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"

#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IPv6_Sockets.h"

#include "FreeRTOS_Sockets_IPv6_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* ===========================  EXTERN VARIABLES  =========================== */

extern BaseType_t prv_ntop6_write_zeros( char * pcDestination,
                                         size_t uxSize,
                                         struct sNTOP6_Set * pxSet );
extern BaseType_t prv_ntop6_write_short( char * pcDestination,
                                         size_t uxSize,
                                         struct sNTOP6_Set * pxSet );
extern BaseType_t prv_inet_pton6_add_nibble( struct sPTON6_Set * pxSet,
                                             uint8_t ucNew,
                                             char ch );
extern void prv_inet_pton6_set_zeros( struct sPTON6_Set * pxSet );

#define SAMPLE_IPv4_ADDR               0xABCD1234
#define NTOP_CHAR_BUFFER_SIZE          41
#define NTOP_CHAR_BUFFER_LAST_INDEX    39

/* The maximum segment size used by TCP, it is the maximum size of
 * the TCP payload per packet.
 * For IPv4: when MTU equals 1500, the MSS equals 1460.
 * It is recommended to use the default value defined here.
 *
 * In FreeRTOS_TCP_IP.c, there is a local macro called 'tcpREDUCED_MSS_THROUGH_INTERNET'.
 * When a TCP connection is made outside the local network, the MSS
 * will be reduced to 'tcpREDUCED_MSS_THROUGH_INTERNET' before the connection
 * is made.
 */
#ifndef ipconfigTCP_MSS
    #define ipconfigTCP_MSS    ( ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER ) )
#endif

static const IPv6_Address_t xSampleAddress_IPv6_1 = { { 0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x70, 0x08 } };
static const IPv6_Address_t xSampleAddress_IPv6_2 = { { 0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x74, 0x08 } };
static const IPv6_Address_t xSampleAddress_IPv6_3 = { { 0xfe, 0x80, 0, 0, 0, 0xde, 0, 0, 0, 0, 0, 0, 0, 0, 0x70, 0x08 } };
static const IPv6_Address_t xSampleAddress_IPv6_4 = { { 0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0, 0, 0, 0x74, 0x08 } };
static const IPv6_Address_t xSampleAddress_IPv6_5 = { { 0xfe, 0x80, 0, 0xde, 0, 0xde, 0, 0xde, 0, 0xde, 0xff, 0, 0xde, 0, 0x74, 0x08 } };
static const IPv6_Address_t xSampleAddress_IPv6_6 = { { 0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 } };

/* =============================== Test Cases =============================== */

/**
 * @brief Test with NULL socket handler
 */
void test_pxTCPSocketLookup_IPv6_NullSocket( void )
{
    IPv46_Address_t xAddress;
    FreeRTOS_Socket_t * pxRetSocket;

    memset( &xAddress, 0, sizeof( xAddress ) );

    pxRetSocket = pxTCPSocketLookup_IPv6( NULL, &xAddress );

    TEST_ASSERT_EQUAL( NULL, pxRetSocket );
}

/**
 * @brief Test with NULL IP address pointer
 */
void test_pxTCPSocketLookup_IPv6_NullIPPointer( void )
{
    FreeRTOS_Socket_t xSocket;
    FreeRTOS_Socket_t * pxRetSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );

    xSocket.bits.bIsIPv6 = pdFALSE_UNSIGNED;

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, NULL );

    TEST_ASSERT_EQUAL( NULL, pxRetSocket );
}

/**
 * @brief Address is IPv6 but socket is not an IPv6 socket
 */
void test_pxTCPSocketLookup_IPv6_NotIPv6Socket_IPv6Address( void )
{
    FreeRTOS_Socket_t xSocket;
    IPv46_Address_t xAddress;
    FreeRTOS_Socket_t * pxRetSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.bits.bIsIPv6 = pdFALSE_UNSIGNED;
    xAddress.xIs_IPv6 = pdTRUE;

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( NULL, pxRetSocket );
}

/**
 * @brief IPv4 address pointer passed and socket is not an IPv6 socket, but a matching IPv4 address is passed
 */
void test_pxTCPSocketLookup_IPv6_NotIPv6Socket_NotIPv6Address_MatchingIPv4Address( void )
{
    FreeRTOS_Socket_t xSocket, * pxRetSocket = NULL;
    IPv46_Address_t xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.bits.bIsIPv6 = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = SAMPLE_IPv4_ADDR;
    xAddress.xIs_IPv6 = pdFALSE;
    xAddress.xIPAddress.ulIP_IPv4 = SAMPLE_IPv4_ADDR;

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( &xSocket, pxRetSocket );
}

/**
 * @brief IPv4 address pointer passed and socket is not an IPv6 socket, but a non matching IPv4 address is passed
 */
void test_pxTCPSocketLookup_IPv6_NotIPv6Socket_NotIPv6Address_NonMatchingIPv4Address( void )
{
    FreeRTOS_Socket_t xSocket, * pxRetSocket = NULL;
    IPv46_Address_t xAddress;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.bits.bIsIPv6 = pdFALSE_UNSIGNED;
    xSocket.u.xTCP.xRemoteIP.ulIP_IPv4 = 0xDBCD1235;
    xAddress.xIs_IPv6 = pdFALSE;
    xAddress.xIPAddress.ulIP_IPv4 = SAMPLE_IPv4_ADDR;

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( NULL, pxRetSocket );
}

/**
 * @brief NULL IPv6 address pointer passed and socket is an IPv6 socket
 */
void test_pxTCPSocketLookup_IPv6_IPv6Socket_NotIPv6Address( void )
{
    FreeRTOS_Socket_t xSocket;
    IPv46_Address_t xAddress;
    FreeRTOS_Socket_t * pxRetSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;
    xAddress.xIs_IPv6 = pdFALSE;

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( NULL, pxRetSocket );
}

/**
 * @brief Valid IPv6 address pointer passed and socket is an IPv6 socket, but the IPv6 addresses match
 */
void test_pxTCPSocketLookup_IPv6_IPv6Socket_NonNullIPv6Address_MatchingIPv6Address( void )
{
    FreeRTOS_Socket_t xSocket;
    IPv46_Address_t xAddress;
    FreeRTOS_Socket_t * pxRetSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;
    memcpy( xSocket.u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, xSampleAddress_IPv6_1.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xAddress.xIs_IPv6 = pdTRUE;
    memcpy( xAddress.xIPAddress.xIP_IPv6.ucBytes, xSampleAddress_IPv6_1.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( &xSocket, pxRetSocket );
}

/**
 * @brief Valid IPv6 address pointer passed and socket is an IPv6 socket, but the IPv6 addresses doesn't match
 */
void test_pxTCPSocketLookup_IPv6_IPv6Socket_NonNullIPv6Address_NonMatchingIPv6Address( void )
{
    FreeRTOS_Socket_t xSocket;
    IPv46_Address_t xAddress;
    FreeRTOS_Socket_t * pxRetSocket;

    memset( &xSocket, 0, sizeof( xSocket ) );
    memset( &xAddress, 0, sizeof( xAddress ) );

    xSocket.bits.bIsIPv6 = pdTRUE_UNSIGNED;
    memcpy( xSocket.u.xTCP.xRemoteIP.xIP_IPv6.ucBytes, xSampleAddress_IPv6_2.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xAddress.xIs_IPv6 = pdTRUE;
    memcpy( xAddress.xIPAddress.xIP_IPv6.ucBytes, xSampleAddress_IPv6_1.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxRetSocket = pxTCPSocketLookup_IPv6( &xSocket, &xAddress );

    TEST_ASSERT_EQUAL( NULL, pxRetSocket );
}

/**
 * @brief Catch configASSERT in case NULL pxDestinationAddress is passed
 */
void test_xSend_UDP_Update_IPv6_NullDestinationAddr( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;

    catch_assert( xSend_UDP_Update_IPv6( &xNetworkBuffer, NULL ) );
}

/**
 * @brief Valid network buffer and destination addresses are passed and the output is compared
 */
void test_xSend_UDP_Update_IPv6( void )
{
    struct freertos_sockaddr xDestinationAddress;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPPacket_IPv6;
    void * pvReturn;

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) xNetworkBuffer.pucEthernetBuffer );

    ( void ) memcpy( xDestinationAddress.sin_address.xIP_IPv6.ucBytes, xSampleAddress_IPv6_1.ucBytes, sizeof( IPv6_Address_t ) );

    pvReturn = xSend_UDP_Update_IPv6( &xNetworkBuffer, &xDestinationAddress );

    TEST_ASSERT_EQUAL_MEMORY( pxUDPPacket_IPv6->xIPHeader.xDestinationAddress.ucBytes, xDestinationAddress.sin_address.xIP_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    TEST_ASSERT_EQUAL_MEMORY( xNetworkBuffer.xIPAddress.xIP_IPv6.ucBytes, xDestinationAddress.sin_address.xIP_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    TEST_ASSERT_EQUAL( pxUDPPacket_IPv6->xEthernetHeader.usFrameType, ipIPv6_FRAME_TYPE );
    TEST_ASSERT_EQUAL( NULL, pvReturn );
}

/**
 * @brief Test for invalid IP frame type
 */
void test_xRecv_Update_IPv6_InvalidFrame( void )
{
    struct freertos_sockaddr xSourceAddress;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPPacket_IPv6;
    void * pvReturn;
    size_t xRetVal;

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) xNetworkBuffer.pucEthernetBuffer );

    pxUDPPacket_IPv6->xEthernetHeader.usFrameType = 0xCAFE;

    xRetVal = xRecv_Update_IPv6( &xNetworkBuffer, &xSourceAddress );

    TEST_ASSERT_EQUAL( 0, xRetVal );
}

/**
 * @brief NULL source address pointer
 */
void test_xRecv_Update_IPv6_InvalidFrame_NullSourceAddress( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPPacket_IPv6;
    void * pvReturn;
    size_t xRetVal;

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) xNetworkBuffer.pucEthernetBuffer );

    pxUDPPacket_IPv6->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    xRetVal = xRecv_Update_IPv6( &xNetworkBuffer, NULL );

    TEST_ASSERT_EQUAL( ipUDP_PAYLOAD_OFFSET_IPv6, xRetVal );
}

/**
 * @brief Test for invalid IP frame type
 */
void test_xRecv_Update_IPv6_InvalidFrame_ValidSourceAddress( void )
{
    struct freertos_sockaddr xSourceAddress;
    NetworkBufferDescriptor_t xNetworkBuffer;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    UDPPacket_IPv6_t * pxUDPPacket_IPv6;
    void * pvReturn;
    size_t xRetVal;

    xNetworkBuffer.pucEthernetBuffer = pucEthernetBuffer;
    pxUDPPacket_IPv6 = ( ( UDPPacket_IPv6_t * ) xNetworkBuffer.pucEthernetBuffer );

    ( void ) memcpy( pxUDPPacket_IPv6->xIPHeader.xSourceAddress.ucBytes, xSampleAddress_IPv6_1.ucBytes, sizeof( IPv6_Address_t ) );
    xNetworkBuffer.usPort = 1234;

    pxUDPPacket_IPv6->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

    xRetVal = xRecv_Update_IPv6( &xNetworkBuffer, &xSourceAddress );

    TEST_ASSERT_EQUAL( ipUDP_PAYLOAD_OFFSET_IPv6, xRetVal );
    TEST_ASSERT_EQUAL_MEMORY( xSourceAddress.sin_address.xIP_IPv6.ucBytes, xSampleAddress_IPv6_1.ucBytes, sizeof( IPv6_Address_t ) );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, xSourceAddress.sin_family );
    TEST_ASSERT_EQUAL( 1234, xSourceAddress.sin_port );
}

/**
 * @brief Test for the branch when in the nibble is less than or equal to 9
 */
void test_cHexToChar_LessThanEqNine( void )
{
    char cRetVal;

    cRetVal = cHexToChar( 8 );

    TEST_ASSERT_EQUAL( '8', cRetVal );
}

/**
 * @brief Test for the branch when in the nibble is greater than or equal to 9
 */
void test_cHexToChar_GreaterThanNine( void )
{
    char cRetVal;

    cRetVal = cHexToChar( 10 );

    TEST_ASSERT_EQUAL( 'a', cRetVal );
}

/**
 * @brief Test for the branch when in the nibble is greater than or equal to 15
 */
void test_cHexToChar_GreaterThanFifteen( void )
{
    char cRetVal;

    catch_assert( cHexToChar( 16 ) );
}

/**
 * @brief uxHexPrintShort happy path.
 */
void test_uxHexPrintShort( void )
{
    char cBuffer[ 5 ] = { '\0' };
    size_t xCBuffLen;
    char * pcExpOp = "cafe";

    xCBuffLen = uxHexPrintShort( cBuffer, 5, 0xCAFE );

    TEST_ASSERT_EQUAL( 4, xCBuffLen );
    TEST_ASSERT_EQUAL_MEMORY( pcExpOp, cBuffer, xCBuffLen );
}

/**
 * @brief Test when buffer size is bigger than 4
 */
void test_uxHexPrintShort_LongerBuffer( void )
{
    char cBuffer[ 7 ] = { '\0' };
    size_t xCBuffLen;
    char * pcExpOp = "cafe";

    xCBuffLen = uxHexPrintShort( cBuffer, 7, 0xCAFE );

    TEST_ASSERT_EQUAL( 4, xCBuffLen );
    TEST_ASSERT_EQUAL_MEMORY( pcExpOp, cBuffer, xCBuffLen );
}

/**
 * @brief Test when input is just 2 nibbles / 1 byte
 */
void test_uxHexPrintShort_OneByteInput( void )
{
    char cBuffer[ 5 ] = { '\0' };
    size_t xCBuffLen;
    char * pcExpOp = "cafe";

    xCBuffLen = uxHexPrintShort( cBuffer, 5, 0xCA );

    TEST_ASSERT_EQUAL( 2, xCBuffLen );
    TEST_ASSERT_EQUAL_MEMORY( pcExpOp, cBuffer, xCBuffLen );
}

/**
 * @brief Test when input is just 3 nibbles
 */
void test_uxHexPrintShort_OneByteAndNibbleInput( void )
{
    char cBuffer[ 5 ] = { '\0' };
    size_t xCBuffLen;
    char * pcExpOp = "cafe";

    xCBuffLen = uxHexPrintShort( cBuffer, 5, 0xCAF );

    TEST_ASSERT_EQUAL( 3, xCBuffLen );
    TEST_ASSERT_EQUAL_MEMORY( pcExpOp, cBuffer, xCBuffLen );
}

/**
 * @brief Test when input is just 1 nibbles
 */
void test_uxHexPrintShort_NibbleInput( void )
{
    char cBuffer[ 5 ] = { '\0' };
    size_t xCBuffLen;
    char * pcExpOp = "cafe";

    xCBuffLen = uxHexPrintShort( cBuffer, 5, 0xC );

    TEST_ASSERT_EQUAL( 1, xCBuffLen );
    TEST_ASSERT_EQUAL_MEMORY( pcExpOp, cBuffer, xCBuffLen );
}

/**
 * @brief Test when buffer overflows
 */
void test_uxHexPrintShort_BufferOverflow( void )
{
    char cBuffer[ 5 ] = { '\0' };
    size_t xCBuffLen;
    char * pcExpOp = "cafe";

    xCBuffLen = uxHexPrintShort( cBuffer, 3, 0xCAF );

    TEST_ASSERT_EQUAL( 2, xCBuffLen );
    TEST_ASSERT_EQUAL_MEMORY( pcExpOp, cBuffer, xCBuffLen );
}

/**
 * @brief Test when input is fe80::7008
 */
void test_prv_ntop6_search_zeros( void )
{
    struct sNTOP6_Set xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_1.ucBytes;

    prv_ntop6_search_zeros( &( xSet ) );

    TEST_ASSERT_EQUAL( 6, xSet.xZeroLength );
    TEST_ASSERT_EQUAL( 1, xSet.xZeroStart );
}

/**
 * @brief Test when input is fe80:0:de::7008
 */
void test_prv_ntop6_search_zeros_2( void )
{
    struct sNTOP6_Set xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_3.ucBytes;

    prv_ntop6_search_zeros( &( xSet ) );

    TEST_ASSERT_EQUAL( 4, xSet.xZeroLength );
    TEST_ASSERT_EQUAL( 3, xSet.xZeroStart );
}

/**
 * @brief Test when input is fe80::ff00:0:7008
 */
void test_prv_ntop6_search_zeros_3( void )
{
    struct sNTOP6_Set xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_4.ucBytes;

    prv_ntop6_search_zeros( &( xSet ) );

    TEST_ASSERT_EQUAL( 4, xSet.xZeroLength );
    TEST_ASSERT_EQUAL( 1, xSet.xZeroStart );
}

/**
 * @brief Test when input is fe80::
 */
void test_prv_ntop6_search_zeros_4( void )
{
    struct sNTOP6_Set xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_6.ucBytes;

    prv_ntop6_search_zeros( &( xSet ) );

    TEST_ASSERT_EQUAL( 7, xSet.xZeroLength );
    TEST_ASSERT_EQUAL( 1, xSet.xZeroStart );
}

/**
 * @brief Test when input doesn't have any zero shorts
 */
void test_prv_ntop6_search_zeros_NoZeroes( void )
{
    struct sNTOP6_Set xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_5.ucBytes;

    prv_ntop6_search_zeros( &( xSet ) );

    TEST_ASSERT_EQUAL( 0, xSet.xZeroLength );
    TEST_ASSERT_EQUAL( -1, xSet.xZeroStart );
}

/**
 * @brief xZeroLength is already set to correct value
 */
void test_prv_ntop6_search_zeros_ZeroLengthIsAlreadySet( void )
{
    struct sNTOP6_Set xSet;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_4.ucBytes;
    xSet.xZeroLength = 4;
    xSet.xZeroStart = 2;

    prv_ntop6_search_zeros( &( xSet ) );

    TEST_ASSERT_EQUAL( 4, xSet.xZeroLength );
    TEST_ASSERT_EQUAL( -1, xSet.xZeroStart );
}

/**
 * @brief Case were there is non zero data after the longest train of zeroes
 */
void test_prv_ntop6_write_zeros( void )
{
    struct sNTOP6_Set xSet;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };
    BaseType_t xReturn;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_1.ucBytes;
    xSet.xZeroLength = 6;
    xSet.xZeroStart = 1;
    xSet.xIndex = xSet.xZeroStart;
    xSet.uxTargetIndex = xSet.xZeroStart * 5; /* Assuming all the previous shorts have 4 chars + 1 colon */

    xReturn = prv_ntop6_write_zeros( cDestination, 40, &( xSet ) );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL_MEMORY( &cDestination[ xSet.xZeroStart * 5 ], ":", 1 );
}

/**
 * @brief Case were there is no non zero data after the longest train of zeroes
 */
void test_prv_ntop6_write_zeros_AddressEndsInZeroes( void )
{
    struct sNTOP6_Set xSet;
    BaseType_t xReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_1.ucBytes;
    xSet.xZeroLength = 7;
    xSet.xZeroStart = 1;
    xSet.xIndex = xSet.xZeroStart;
    xSet.uxTargetIndex = xSet.xZeroStart * 5; /* Assuming all the previous shorts have 4 chars + 1 colon */

    xReturn = prv_ntop6_write_zeros( cDestination, 40, &( xSet ) );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL_MEMORY( &cDestination[ xSet.xZeroStart * 5 ], "::", 2 );
}

/**
 * @brief Case were there is not enough space in the input buffer.
 */
void test_prv_ntop6_write_zeros_NotEnoughSpaceInBuffer( void )
{
    struct sNTOP6_Set xSet;
    BaseType_t xReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_1.ucBytes;
    xSet.xZeroLength = 7;
    xSet.xZeroStart = 1;
    xSet.xIndex = xSet.xZeroStart;
    xSet.uxTargetIndex = NTOP_CHAR_BUFFER_LAST_INDEX;

    xReturn = prv_ntop6_write_zeros( cDestination, 40, &( xSet ) );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief Case were there is not enough space in the input buffer after first insertion to the buffer
 */
void test_prv_ntop6_write_zeros_NotEnoughSpaceInBuffer_2( void )
{
    struct sNTOP6_Set xSet;
    BaseType_t xReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_1.ucBytes;
    xSet.xZeroLength = 7;
    xSet.xZeroStart = 1;
    xSet.xIndex = 1;
    xSet.uxTargetIndex = NTOP_CHAR_BUFFER_LAST_INDEX;

    xReturn = prv_ntop6_write_zeros( cDestination, 40, &( xSet ) );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief Case were target index is greater than size of the destination buffer.
 */
void test_prv_ntop6_write_zeros_TargetIndexGreater( void )
{
    struct sNTOP6_Set xSet;
    BaseType_t xReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_1.ucBytes;
    xSet.xZeroLength = 7;
    xSet.xZeroStart = 1;
    xSet.xIndex = 1;
    xSet.uxTargetIndex = NTOP_CHAR_BUFFER_LAST_INDEX;

    xReturn = prv_ntop6_write_zeros( cDestination, NTOP_CHAR_BUFFER_LAST_INDEX, &( xSet ) );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief Output size greater than buffer length
 */
void test_prv_ntop6_write_short_SmallerBuffer( void )
{
    struct sNTOP6_Set xSet;
    BaseType_t xReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_1.ucBytes;
    xSet.xIndex = 8;
    xSet.uxTargetIndex = NTOP_CHAR_BUFFER_LAST_INDEX;

    xReturn = prv_ntop6_write_short( cDestination, 40, &( xSet ) );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief Output size less is enough to fit in the buffer, starts
 * from beginning of IPv6 address.
 */
void test_prv_ntop6_write_short_EnoughBuffer( void )
{
    struct sNTOP6_Set xSet;
    BaseType_t xReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_1.ucBytes;
    xSet.xIndex = 0;
    xSet.uxTargetIndex = 0;

    xReturn = prv_ntop6_write_short( cDestination, 40, &( xSet ) );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL_MEMORY( &cDestination[ 0 ], "fe80", 4 );
    TEST_ASSERT_EQUAL( 4, xSet.uxTargetIndex );
}

/**
 * @brief Output size less is enough to fit in the buffer, starts
 * after beginning of IPv6 address.
 */
void test_prv_ntop6_write_short_EnoughBuffer_StartAfterBeginning( void )
{
    struct sNTOP6_Set xSet;
    BaseType_t xReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_5.ucBytes;
    xSet.xIndex = 1;
    xSet.uxTargetIndex = 4;

    xReturn = prv_ntop6_write_short( cDestination, 40, &( xSet ) );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL_MEMORY( &cDestination[ 4 ], ":de", 3 );
    TEST_ASSERT_EQUAL( 7, xSet.uxTargetIndex );
}

/**
 * @brief Not enough space to write a short.
 */
void test_prv_ntop6_write_short_NotEnoughSpaceForShort( void )
{
    struct sNTOP6_Set xSet;
    BaseType_t xReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.pusAddress = ( const uint16_t * ) xSampleAddress_IPv6_5.ucBytes;
    xSet.xIndex = 1;
    xSet.uxTargetIndex = 37;

    xReturn = prv_ntop6_write_short( cDestination, 40, &( xSet ) );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief Buffer size is less than the minimum 3 required.
 */
void test_FreeRTOS_inet_ntop6_LowBufferSize( void )
{
    const char * pcReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    pcReturn = FreeRTOS_inet_ntop6( xSampleAddress_IPv6_1.ucBytes, cDestination, 2 );

    TEST_ASSERT_EQUAL( NULL, pcReturn );
}

/**
 * @brief Test for fe80::7008.
 */
void test_FreeRTOS_inet_ntop6_HappyPath( void )
{
    const char * pcReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    pcReturn = FreeRTOS_inet_ntop6( xSampleAddress_IPv6_1.ucBytes, cDestination, 40 );

    TEST_ASSERT_EQUAL_MEMORY( "fe80::7008", pcReturn, 10 );
}

/**
 * @brief Test for fe80:0:de::7008.
 */
void test_FreeRTOS_inet_ntop6_HappyPath2( void )
{
    const char * pcReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    pcReturn = FreeRTOS_inet_ntop6( xSampleAddress_IPv6_3.ucBytes, cDestination, 40 );

    TEST_ASSERT_EQUAL_MEMORY( "fe80:0:de::7008", pcReturn, 16 );
}

/**
 * @brief Test for fe80:de:de:de:de:ff00:de00:7408.
 */
void test_FreeRTOS_inet_ntop6_HappyPath3( void )
{
    const char * pcReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    pcReturn = FreeRTOS_inet_ntop6( xSampleAddress_IPv6_5.ucBytes, cDestination, 40 );

    TEST_ASSERT_EQUAL_MEMORY( "fe80:de:de:de:de:ff00:de00:7408", pcReturn, 32 );
}

/**
 * @brief Test for fe80::.
 */
void test_FreeRTOS_inet_ntop6_HappyPath4( void )
{
    const char * pcReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    pcReturn = FreeRTOS_inet_ntop6( xSampleAddress_IPv6_6.ucBytes, cDestination, 40 );

    TEST_ASSERT_EQUAL_MEMORY( "fe80::", pcReturn, 7 );
}

/**
 * @brief Case where the destination buffer size is lesser than required
 *        when writing zeroes..
 */
void test_FreeRTOS_inet_ntop6_LesserBufferSize( void )
{
    const char * pcReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    pcReturn = FreeRTOS_inet_ntop6( xSampleAddress_IPv6_6.ucBytes, cDestination, 5 );

    TEST_ASSERT_EQUAL( NULL, pcReturn );
}

/**
 * @brief Case where the destination buffer size is lesser than required
 *        when writing non zero data.
 */
void test_FreeRTOS_inet_ntop6_LesserBufferSizeNonZero( void )
{
    const char * pcReturn;
    char cDestination[ NTOP_CHAR_BUFFER_SIZE ] = { '\0' };

    pcReturn = FreeRTOS_inet_ntop6( xSampleAddress_IPv6_5.ucBytes, cDestination, 24 );

    TEST_ASSERT_EQUAL( NULL, pcReturn );
}

/**
 * @brief Test for the case when the incoming character is not a colon.
 */
void test_prv_inet_pton6_add_nibble_NotColon( void )
{
    struct sPTON6_Set xSet;
    BaseType_t xReturn;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );

    xReturn = prv_inet_pton6_add_nibble( &xSet, 15, 'f' );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSet.xHadDigit );
    TEST_ASSERT_EQUAL( 15, xSet.ulValue );
}

/**
 * @brief Test for the case when the incoming character is not a colon and the accumulator
 *        is non zero
 */
void test_prv_inet_pton6_add_nibble_NotColon_AccumulatorNonZero( void )
{
    struct sPTON6_Set xSet;
    BaseType_t xReturn;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.ulValue = 0xFFF;

    xReturn = prv_inet_pton6_add_nibble( &xSet, 15, 'f' );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL( pdTRUE, xSet.xHadDigit );
    TEST_ASSERT_EQUAL( 0xFFFF, xSet.ulValue );
}

/**
 * @brief Test for the case when the incoming character is not a colon and the accumulator
 *        overflows.
 */
void test_prv_inet_pton6_add_nibble_NotColon_AccumulatorOverflow( void )
{
    struct sPTON6_Set xSet;
    BaseType_t xReturn;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.ulValue = 0xFFFF;

    xReturn = prv_inet_pton6_add_nibble( &xSet, 15, 'f' );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief Test for the case when the incoming character is a colon and there is a valid digit in the set.
 */
void test_prv_inet_pton6_add_nibble_InvalidHexChar_ValidDigit( void )
{
    struct sPTON6_Set xSet;
    BaseType_t xReturn, xTargetIndex = 5;
    uint8_t uIPv6Address[ ipSIZE_OF_IPv6_ADDRESS ] = { 0 };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.xHadDigit = pdTRUE;
    xSet.xTargetIndex = xTargetIndex;
    xSet.xHighestIndex = ipSIZE_OF_IPv6_ADDRESS - 2;
    xSet.pucTarget = uIPv6Address;
    xSet.ulValue = 0xFE80;

    xReturn = prv_inet_pton6_add_nibble( &xSet, socketINVALID_HEX_CHAR, ':' );

    TEST_ASSERT_EQUAL( pdPASS, xReturn );
    TEST_ASSERT_EQUAL( 0xFE, uIPv6Address[ xTargetIndex ] );
    TEST_ASSERT_EQUAL( 0x80, uIPv6Address[ xTargetIndex + 1 ] );
    TEST_ASSERT_EQUAL( xTargetIndex + 2, xSet.xTargetIndex );
    TEST_ASSERT_EQUAL( pdFALSE, xSet.xHadDigit );
    TEST_ASSERT_EQUAL( 0, xSet.ulValue );
}

/**
 * @brief Test for the case when the incoming character is a colon and there is a valid digit in the set
 *        but buffer overflow
 */
void test_prv_inet_pton6_add_nibble_InvalidHexChar_ValidDigit_BufferOverflow( void )
{
    struct sPTON6_Set xSet;
    BaseType_t xReturn, xTargetIndex = ipSIZE_OF_IPv6_ADDRESS - 1;
    uint8_t uIPv6Address[ ipSIZE_OF_IPv6_ADDRESS ] = { 0 };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.xHadDigit = pdTRUE;
    xSet.xTargetIndex = xTargetIndex;
    xSet.xHighestIndex = ipSIZE_OF_IPv6_ADDRESS - 2;
    xSet.pucTarget = uIPv6Address;
    xSet.ulValue = 0xFE80;

    xReturn = prv_inet_pton6_add_nibble( &xSet, socketINVALID_HEX_CHAR, ':' );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief Test for the case when the incoming character is a colon and there isn't a valid digit, but
 *        receives 2nd colon
 */
void test_prv_inet_pton6_add_nibble_InvalidHexChar_InValidDigit( void )
{
    struct sPTON6_Set xSet;
    BaseType_t xReturn, xTargetIndex = 5;
    uint8_t uIPv6Address[ ipSIZE_OF_IPv6_ADDRESS ] = { 0 };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.xHadDigit = pdFALSE;
    xSet.xColon = -1;
    xSet.xTargetIndex = xTargetIndex;
    xSet.xHighestIndex = ipSIZE_OF_IPv6_ADDRESS - 2;
    xSet.pucTarget = uIPv6Address;
    xSet.ulValue = 0xFE80;

    xReturn = prv_inet_pton6_add_nibble( &xSet, socketINVALID_HEX_CHAR, ':' );

    TEST_ASSERT_EQUAL( xTargetIndex, xSet.xColon );
}

/**
 * @brief Test for the case when the incoming character is a colon and there isn't a valid digit, but
 *        receives 3nd colon
 */
void test_prv_inet_pton6_add_nibble_InvalidHexChar_InValidDigit_3rdColon( void )
{
    struct sPTON6_Set xSet;
    BaseType_t xReturn, xTargetIndex = 5;
    uint8_t uIPv6Address[ ipSIZE_OF_IPv6_ADDRESS ] = { 0 };

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.xHadDigit = pdFALSE;
    xSet.xColon = 5;
    xSet.xTargetIndex = xTargetIndex;
    xSet.xHighestIndex = ipSIZE_OF_IPv6_ADDRESS - 2;
    xSet.pucTarget = uIPv6Address;
    xSet.ulValue = 0xFE80;

    xReturn = prv_inet_pton6_add_nibble( &xSet, socketINVALID_HEX_CHAR, ':' );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief Test for the case when the input is invalid input
 */
void test_prv_inet_pton6_add_nibble_InvalidInput( void )
{
    struct sPTON6_Set xSet;
    BaseType_t xReturn, xTargetIndex = 5;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );

    xReturn = prv_inet_pton6_add_nibble( &xSet, socketINVALID_HEX_CHAR, '-' );

    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/**
 * @brief Check if the double colons in the string are filled
 *        with correct
 */
void test_prv_inet_pton6_set_zeros( void )
{
    struct sPTON6_Set xSet;
    BaseType_t xReturn, xTargetIndex = 4;
    uint8_t uIPv6Address[ ipSIZE_OF_IPv6_ADDRESS ] = { 0 };
    uint8_t uIPv6AddressExpected[ ipSIZE_OF_IPv6_ADDRESS ] = { 0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2 };

    uIPv6Address[ 0 ] = 0xFE;
    uIPv6Address[ 1 ] = 0x80;
    uIPv6Address[ 2 ] = 0x0;
    uIPv6Address[ 3 ] = 0x2;

    ( void ) memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.xColon = 2;
    xSet.xTargetIndex = 4;
    xSet.xHighestIndex = ipSIZE_OF_IPv6_ADDRESS - 2;
    xSet.pucTarget = uIPv6Address;
    xSet.ulValue = 0xFE80;

    prv_inet_pton6_set_zeros( &xSet );

    TEST_ASSERT_EQUAL_MEMORY( uIPv6AddressExpected, uIPv6Address, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief Normal string IPv6 address conversion
 */
void test_FreeRTOS_inet_pton6( void )
{
    const char * pcSource = "fe80::2";
    uint8_t uIPv6AddressDstn[ ipSIZE_OF_IPv6_ADDRESS ];
    uint8_t uIPv6AddressExpected[ ipSIZE_OF_IPv6_ADDRESS ] = { 0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x2 };
    BaseType_t xResult;


    xResult = FreeRTOS_inet_pton6( pcSource, uIPv6AddressDstn );

    TEST_ASSERT_EQUAL( 1, xResult );
    TEST_ASSERT_EQUAL_MEMORY( uIPv6AddressExpected, uIPv6AddressDstn, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief IPv6 address conversion when input is ::
 */
void test_FreeRTOS_inet_pton6_DoubleColonInput( void )
{
    const char * pcSource = "::";
    uint8_t uIPv6AddressDstn[ ipSIZE_OF_IPv6_ADDRESS ];
    uint8_t uIPv6AddressExpected[ ipSIZE_OF_IPv6_ADDRESS ] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    BaseType_t xResult;


    xResult = FreeRTOS_inet_pton6( pcSource, uIPv6AddressDstn );

    TEST_ASSERT_EQUAL( 1, xResult );
    TEST_ASSERT_EQUAL_MEMORY( uIPv6AddressExpected, uIPv6AddressDstn, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief IPv6 address conversion when input starts with ::
 */
void test_FreeRTOS_inet_pton6_StartsWithSingleColon( void )
{
    const char * pcSource = "::fe80:2";
    uint8_t uIPv6AddressDstn[ ipSIZE_OF_IPv6_ADDRESS ];
    uint8_t uIPv6AddressExpected[ ipSIZE_OF_IPv6_ADDRESS ] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xfe, 0x80, 0, 0x2 };
    BaseType_t xResult;


    xResult = FreeRTOS_inet_pton6( pcSource, uIPv6AddressDstn );

    TEST_ASSERT_EQUAL( 1, xResult );
    TEST_ASSERT_EQUAL_MEMORY( uIPv6AddressExpected, uIPv6AddressDstn, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief IPv6 address conversion with no shorthand notation
 */
void test_FreeRTOS_inet_pton6_NoShortHand( void )
{
    const char * pcSource = "fe80:de:de:de:de:ff00:de00:7408";
    uint8_t uIPv6AddressDstn[ ipSIZE_OF_IPv6_ADDRESS ];
    uint8_t uIPv6AddressExpected[ ipSIZE_OF_IPv6_ADDRESS ] = { 0xfe, 0x80, 0, 0xde, 0, 0xde, 0, 0xde, 0, 0xde, 0xff, 0, 0xde, 0, 0x74, 0x08 };
    BaseType_t xResult;


    xResult = FreeRTOS_inet_pton6( pcSource, uIPv6AddressDstn );

    TEST_ASSERT_EQUAL( 1, xResult );
    TEST_ASSERT_EQUAL_MEMORY( uIPv6AddressExpected, uIPv6AddressDstn, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief IPv6 address conversion with longer input
 */
void test_FreeRTOS_inet_pton6_LongerInput( void )
{
    const char * pcSource = "fe80:de:de:de:de:ff00:de00:7408:7409";
    uint8_t uIPv6AddressDstn[ ipSIZE_OF_IPv6_ADDRESS + 2 ] = { 0 };
    uint8_t uIPv6AddressExpected[ ipSIZE_OF_IPv6_ADDRESS + 2 ] = { 0xfe, 0x80, 0, 0xde, 0, 0xde, 0, 0xde, 0, 0xde, 0xff, 0, 0xde, 0, 0x74, 0x08, 0x74, 0x08 };
    BaseType_t xResult;


    xResult = FreeRTOS_inet_pton6( pcSource, uIPv6AddressDstn );

    TEST_ASSERT_EQUAL( 1, xResult );
    TEST_ASSERT_EQUAL_MEMORY( uIPv6AddressExpected, uIPv6AddressDstn, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief Input string IPv6 address terminates in double colon.
 */
void test_FreeRTOS_inet_pton6_InputTermintatesInDoubleColon( void )
{
    const char * pcSource = "fe80::";
    uint8_t uIPv6AddressDstn[ ipSIZE_OF_IPv6_ADDRESS ] = { 0 };
    uint8_t uIPv6AddressExpected[ ipSIZE_OF_IPv6_ADDRESS ] = { 0xfe, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    BaseType_t xResult;


    xResult = FreeRTOS_inet_pton6( pcSource, uIPv6AddressDstn );

    TEST_ASSERT_EQUAL( 1, xResult );
    TEST_ASSERT_EQUAL_MEMORY( uIPv6AddressExpected, uIPv6AddressDstn, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief Input string IPv6 address has invalid character.
 */
void test_FreeRTOS_inet_pton6_InputHasInvalidChars( void )
{
    const char * pcSource = "fe8k::";
    uint8_t uIPv6AddressDstn[ ipSIZE_OF_IPv6_ADDRESS ];
    BaseType_t xResult;


    xResult = FreeRTOS_inet_pton6( pcSource, uIPv6AddressDstn );

    TEST_ASSERT_EQUAL( 0, xResult );
}
