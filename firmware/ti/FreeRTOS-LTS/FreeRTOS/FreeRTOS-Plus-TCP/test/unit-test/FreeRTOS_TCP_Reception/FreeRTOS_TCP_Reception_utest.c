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
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_NetworkInterface.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_Stream_Buffer.h"
#include "mock_FreeRTOS_TCP_WIN.h"
#include "mock_FreeRTOS_TCP_Transmission.h"

#include "FreeRTOS_TCP_IP.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_TCP_Reception_stubs.c"
#include "FreeRTOS_TCP_Reception.h"


int32_t prvSingleStepTCPHeaderOptions( const uint8_t * const pucPtr,
                                       size_t uxTotalLength,
                                       FreeRTOS_Socket_t * const pxSocket,
                                       BaseType_t xHasSYNFlag );

void prvReadSackOption( const uint8_t * const pucPtr,
                        size_t uxIndex,
                        FreeRTOS_Socket_t * const pxSocket );

FreeRTOS_Socket_t xSocket, * pxSocket;
NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer;
uint8_t ucEthernetBuffer[ ipconfigNETWORK_MTU ] =
{
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x08, 0x00, 0x45, 0x00,
    0x00, 0x34, 0x15, 0xc2, 0x40, 0x00, 0x40, 0x06, 0xa8, 0x8e, 0xc0, 0xa8, 0x00, 0x08, 0xac, 0xd9,
    0x0e, 0xea, 0xea, 0xfe, 0x01, 0xbb, 0x8b, 0xaf, 0x8a, 0x24, 0xdc, 0x96, 0x95, 0x7a, 0x80, 0x10,
    0x01, 0xf5, 0x7c, 0x9a, 0x00, 0x00, 0x01, 0x01, 0x08, 0x0a, 0xb8, 0x53, 0x57, 0x27, 0xb2, 0xce,
    0xc3, 0x17
};


const uint8_t ucTCPOptions_good_MSS_WSF[ ipSIZE_TCP_OPTIONS ] =
{
    0x02, 0x04, 0x12, 0x34, /* MSS */
    0x01,                   /* noop */
    0x03, 0x03, 0x10,       /* WSF */
    0x01,                   /* noop */
    0x04, 0x02,             /* SACKP */
    0x00                    /* EOL */
};

const uint8_t ucTCPOptions_bad_MSS_WSF[ ipSIZE_TCP_OPTIONS ] =
{
    0x02, 0x04, 0x12, 0x34, /* MSS */
    0x01,                   /* noop */
    0x03, 0x03, 0x10,       /* WSF */
    0x01,                   /* noop */
    0x08, 0x0a, 0x01        /* bad TS */
};

const uint8_t ucTCPOptions_good_MSS_WSF_woEND[ ipSIZE_TCP_OPTIONS ] =
{
    0x02, 0x04, 0x12, 0x34, /* MSS */
    0x01,                   /* noop */
    0x03, 0x03, 0x10,       /* WSF */
    0x01,                   /* noop */
    0x04, 0x02,             /* SACKP */
    0x01                    /* noop */
};

const uint8_t ucTCPOptions_good_SACK[ ipSIZE_TCP_OPTIONS ] =
{
    0x05, 0x0A, 0x10, 0x00, 0x05, 0x00, 0x11, 0x11, 0x22, 0x22,
    0x00,
    0x00
};

const uint8_t ucTCPOptions_good_TS[ ipSIZE_TCP_OPTIONS ] =
{
    0x08, 0x0A, 0x12, 0x34, 0x56, 0x78, 0x11, 0x22, 0x33, 0x44,
    0x00,
    0x00
};

/* Test for prvCheckOptions function. */
void test_prvCheckOptions_No_Option( void )
{
    BaseType_t xReturn;

    /* Setup TCP option for tests */
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 64;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    xReturn = prvCheckOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/* Test for prvCheckOptions function. */
void test_prvCheckOptions_Invalid_Data_Length( void )
{
    BaseType_t xReturn;

    /* Setup TCP option for tests */
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 50;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    xReturn = prvCheckOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/* Test for prvCheckOptions function. */
void test_prvCheckOptions_Invalid_Option_Length( void )
{
    BaseType_t xReturn;

    /* Setup TCP option for tests */
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 60;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    xReturn = prvCheckOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/* Test for prvCheckOptions function. */
void test_prvCheckOptions_MSS_WSF( void )
{
    BaseType_t xReturn;

    /* Setup TCP option for tests */
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) ucTCPOptions_good_MSS_WSF, sizeof( ucTCPOptions_good_MSS_WSF ) );

    TCPWindow_t tcpWindow;
    tcpWindow.usMSS = 536;
    pxSocket->u.xTCP.usMSS = 1400;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( 500 );

    xReturn = prvCheckOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/* Test for prvCheckOptions function. */
void test_prvCheckOptions_MSS_WSF_Bad_Option( void )
{
    BaseType_t xReturn;

    /* Setup TCP option for tests */
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) ucTCPOptions_bad_MSS_WSF, sizeof( ucTCPOptions_bad_MSS_WSF ) );

    TCPWindow_t tcpWindow;
    tcpWindow.usMSS = 536;
    pxSocket->u.xTCP.usMSS = 1400;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( 500 );

    xReturn = prvCheckOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, xReturn );
}

/* Test for prvCheckOptions function. */
void test_prvCheckOptions_MSS_WSF_Without_END( void )
{
    BaseType_t xReturn;

    /* Setup TCP option for tests */
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) ucTCPOptions_good_MSS_WSF_woEND, sizeof( ucTCPOptions_good_MSS_WSF_woEND ) );

    TCPWindow_t tcpWindow;
    tcpWindow.usMSS = 536;
    pxSocket->u.xTCP.usMSS = 1400;
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( 500 );
    xReturn = prvCheckOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/* Test for prvCheckOptions function. */
void test_prvCheckOptions_MSS_WSF_SYN_on( void )
{
    BaseType_t xReturn;

    /* Setup TCP option for tests */
    pxSocket = &xSocket;
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    pxTCPHeader->ucTCPFlags |= tcpTCP_FLAG_SYN;
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) ucTCPOptions_good_MSS_WSF, sizeof( ucTCPOptions_good_MSS_WSF ) );

    TCPWindow_t tcpWindow;
    tcpWindow.usMSS = 536;
    pxSocket->u.xTCP.usMSS = 1400;
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    usChar2u16_ExpectAnyArgsAndReturn( 500 );
    xReturn = prvCheckOptions( pxSocket, pxNetworkBuffer );
    TEST_ASSERT_EQUAL( pdPASS, xReturn );
}

/* Test for prvSingleStepTCPHeaderOptions function. */
void test_prvSingleStepTCPHeaderOptions_SACK( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ uxTCPHeaderOffset ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    const uint8_t ucTCPOptions_good_SACK[ ipSIZE_TCP_OPTIONS ] =
    {
        0x05, 0x0A, 0x10, 0x00, 0x05, 0x00, 0x11, 0x11, 0x22, 0x22
    };
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) ucTCPOptions_good_SACK, sizeof( ucTCPOptions_good_SACK ) );

    ulChar2u32_ExpectAnyArgsAndReturn( 0x12345678 );
    ulChar2u32_ExpectAnyArgsAndReturn( 0x12345678 );
    ulTCPWindowTxSack_ExpectAnyArgsAndReturn( 5 );
    result = prvSingleStepTCPHeaderOptions(
        pxTCPHeader->ucOptdata,
        10,
        pxSocket,
        pdTRUE );

    TEST_ASSERT_EQUAL( 10, result );
}

/* Test for prvSingleStepTCPHeaderOptions function. */
void test_prvSingleStepTCPHeaderOptions_TS( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ uxTCPHeaderOffset ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    const uint8_t ucTCPOptions_good_SACK[ ipSIZE_TCP_OPTIONS ] =
    {
        0x08, 0x01, 0x10, 0x00, 0x05, 0x00, 0x11, 0x11, 0x22, 0x22
    };
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) ucTCPOptions_good_SACK, sizeof( ucTCPOptions_good_SACK ) );


    result = prvSingleStepTCPHeaderOptions(
        pxTCPHeader->ucOptdata,
        10,
        pxSocket,
        pdTRUE );

    TEST_ASSERT_EQUAL( -1, result );
}

/* Test for prvSingleStepTCPHeaderOptions function. */
void test_prvSingleStepTCPHeaderOptions_END_NOOP( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    uint8_t ucTCPOptions = 0x00;
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) &ucTCPOptions, sizeof( ucTCPOptions ) );


    result = prvSingleStepTCPHeaderOptions(
        ( const uint8_t * const ) pxTCPHeader->ucOptdata,
        1,
        pxSocket,
        pdTRUE );

    TEST_ASSERT_EQUAL( 0, result );

    ucTCPOptions = 0x01;
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) &ucTCPOptions, sizeof( ucTCPOptions ) );


    result = prvSingleStepTCPHeaderOptions(
        ( const uint8_t * const ) pxTCPHeader->ucOptdata,
        1,
        pxSocket,
        pdTRUE );

    TEST_ASSERT_EQUAL( 1, result );
}

/* Test for prvSingleStepTCPHeaderOptions function. */
void test_prvSingleStepTCPHeaderOptions_MSS_Invalid_Length( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    uint8_t ucTCPOptions[] = { 0x02, 0x04, 0x12, 0x34 };
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) &ucTCPOptions, sizeof( ucTCPOptions ) );


    result = prvSingleStepTCPHeaderOptions(
        pxTCPHeader->ucOptdata,
        1,
        pxSocket,
        pdTRUE );

    TEST_ASSERT_EQUAL( -1, result );

    result = prvSingleStepTCPHeaderOptions(
        pxTCPHeader->ucOptdata,
        3,
        pxSocket,
        pdTRUE );

    TEST_ASSERT_EQUAL( -1, result );

    ucTCPOptions[ 1 ] = 0x03;
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) &ucTCPOptions, sizeof( ucTCPOptions ) );
    result = prvSingleStepTCPHeaderOptions(
        ( const uint8_t * const ) pxTCPHeader->ucOptdata,
        4,
        pxSocket,
        pdTRUE );

    TEST_ASSERT_EQUAL( -1, result );
}

/* Test for prvSingleStepTCPHeaderOptions function. */
void test_prvSingleStepTCPHeaderOptions_Zero_Length_MSS( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    const uint8_t ucTCPOptions[] = { 0x02, 0x04, 0x0, 0x0 };
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) &ucTCPOptions, sizeof( ucTCPOptions ) );
    usChar2u16_ExpectAnyArgsAndReturn( 0 );

    result = prvSingleStepTCPHeaderOptions(
        pxTCPHeader->ucOptdata,
        4,
        pxSocket,
        pdTRUE );

    TEST_ASSERT_EQUAL( -1, result );
}

/* Test for prvSingleStepTCPHeaderOptions function. */
void test_prvSingleStepTCPHeaderOptions_Same_MSS( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;
    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    const uint8_t ucTCPOptions[] = { 0x02, 0x04, 0x0, 0x0 };
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) &ucTCPOptions, sizeof( ucTCPOptions ) );

    TCPWindow_t tcpWindow;
    tcpWindow.usMSS = 536;
    pxSocket->u.xTCP.usMSS = 536;
    usChar2u16_ExpectAnyArgsAndReturn( 536 );

    result = prvSingleStepTCPHeaderOptions(
        pxTCPHeader->ucOptdata,
        4,
        pxSocket,
        pdTRUE );

    TEST_ASSERT_EQUAL( 4, result );
}

/* Test for prvSingleStepTCPHeaderOptions function. */
void test_prvSingleStepTCPHeaderOptions_Invalid_Length_WS( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ucEthernetBuffer;
    size_t uxTCPHeaderOffset = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER;

    ProtocolHeaders_t * pxProtocolHeader = ( ( ProtocolHeaders_t * )
                                             &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &( pxProtocolHeader->xTCPHeader );

    pxTCPHeader->ucTCPOffset = 0x80;
    pxNetworkBuffer->xDataLength = 0x50;
    uint8_t ucTCPOptions[] = { 0x03, 0x03, 0x10 };
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) &ucTCPOptions, sizeof( ucTCPOptions ) );


    result = prvSingleStepTCPHeaderOptions(
        pxTCPHeader->ucOptdata,
        2,
        pxSocket,
        pdTRUE );

    TEST_ASSERT_EQUAL( -1, result );

    ucTCPOptions[ 1 ] = 0x02;
    memcpy( ( void * ) pxTCPHeader->ucOptdata, ( void * ) &ucTCPOptions, sizeof( ucTCPOptions ) );
    result = prvSingleStepTCPHeaderOptions(
        ( const uint8_t * const ) pxTCPHeader->ucOptdata,
        3,
        pxSocket,
        pdTRUE );

    TEST_ASSERT_EQUAL( -1, result );
}

static uint32_t ulCalled = 0;
static void xLocalFunctionPointer( Socket_t xSocket,
                                   size_t xLength )
{
    ulCalled++;
}

/* Test for prvReadSackOption function */
void test_prvReadSackOption( void )
{
    pxSocket = &xSocket;
    ulCalled = 0;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    ulChar2u32_ExpectAnyArgsAndReturn( 0x12345678 );
    ulChar2u32_ExpectAnyArgsAndReturn( 0x12346678 );
    ulTCPWindowTxSack_ExpectAnyArgsAndReturn( 0x1000 );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 0x1000 );
    pxSocket->xSelectBits |= eSELECT_WRITE;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;

    const uint8_t ucTCPOptions[] =
    {
        0x05, 0x0A, 0x10, 0x00, 0x05, 0x00, 0x11, 0x11, 0x22, 0x22
    };

    prvReadSackOption( ( const uint8_t * const ) &ucTCPOptions, 2, pxSocket );

    TEST_ASSERT_NOT_EQUAL( pxSocket->xEventBits & ( ( ( EventBits_t ) eSELECT_WRITE ) << SOCKET_EVENT_BIT_COUNT ), 0 );
    TEST_ASSERT_EQUAL( 1, ulCalled );
}

/* Test for prvReadSackOption function */
void test_prvReadSackOption_Zero_Length_Block( void )
{
    pxSocket = &xSocket;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    ulChar2u32_ExpectAnyArgsAndReturn( 0x12345678 );
    ulChar2u32_ExpectAnyArgsAndReturn( 0x12346678 );
    ulTCPWindowTxSack_ExpectAnyArgsAndReturn( 0 );
    pxSocket->xEventBits = 0;

    const uint8_t ucTCPOptions[] =
    {
        0x05, 0x0A, 0x10, 0x00, 0x05, 0x00, 0x11, 0x11, 0x22, 0x22
    };

    prvReadSackOption( ( const uint8_t * const ) &ucTCPOptions, 2, pxSocket );

    TEST_ASSERT_NOT_EQUAL( 0, pxSocket->xEventBits ^ ( EventBits_t ) eSOCKET_SEND );
}

/* Test for prvReadSackOption function */
void test_prvReadSackOption_Selectbits_On( void )
{
    pxSocket = &xSocket;
    ulCalled = 0;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    ulChar2u32_ExpectAnyArgsAndReturn( 0x12345678 );
    ulChar2u32_ExpectAnyArgsAndReturn( 0x12346678 );
    ulTCPWindowTxSack_ExpectAnyArgsAndReturn( 0x1000 );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 0x1000 );
    pxSocket->xEventBits = 0;
    pxSocket->xSelectBits = 0;
    pxSocket->u.xTCP.pxHandleSent = xLocalFunctionPointer;


    const uint8_t ucTCPOptions[] =
    {
        0x05, 0x0A, 0x10, 0x00, 0x05, 0x00, 0x11, 0x11, 0x22, 0x22
    };

    prvReadSackOption( ( const uint8_t * const ) &ucTCPOptions, 2, pxSocket );

    TEST_ASSERT_EQUAL( 0, pxSocket->xEventBits & ( ( ( EventBits_t ) eSELECT_WRITE ) << SOCKET_EVENT_BIT_COUNT ) );
}


/* Test for prvReadSackOption function */
void test_prvReadSackOption_No_Handler( void )
{
    pxSocket = &xSocket;
    ulCalled = 0;

    pxSocket->u.xTCP.txStream = ( StreamBuffer_t * ) 0x12345678;
    ulChar2u32_ExpectAnyArgsAndReturn( 0x12345678 );
    ulChar2u32_ExpectAnyArgsAndReturn( 0x12346678 );
    ulTCPWindowTxSack_ExpectAnyArgsAndReturn( 0x1000 );
    uxStreamBufferGet_ExpectAnyArgsAndReturn( 0x1000 );
    pxSocket->xSelectBits = 0;
    pxSocket->u.xTCP.pxHandleSent = NULL;

    const uint8_t ucTCPOptions[] =
    {
        0x05, 0x0A, 0x10, 0x00, 0x05, 0x00, 0x11, 0x11, 0x22, 0x22
    };

    prvReadSackOption( ( const uint8_t * const ) &ucTCPOptions, 2, pxSocket );

    TEST_ASSERT_EQUAL( 0, pxSocket->xEventBits & ( ( ( EventBits_t ) eSELECT_WRITE ) << SOCKET_EVENT_BIT_COUNT ) );
    TEST_ASSERT_EQUAL( 0, ulCalled );
}

uint8_t EthernetBuffer[ ipconfigNETWORK_MTU ] =
{
    0x8c, 0xdc, 0xd4, 0x4a, 0xea, 0x02, 0xa0, 0x40, 0xa0, 0x3a, 0x21, 0xea, 0x08, 0x00, 0x45, 0x20,
    0x00, 0x5b, 0xd2, 0xe9, 0x00, 0x00, 0x39, 0x06, 0x32, 0x47, 0xac, 0xd9, 0x0e, 0xc3, 0xc0, 0xa8,
    0x00, 0x08, 0x01, 0xbb, 0xdc, 0x44, 0xe2, 0x34, 0xd4, 0x84, 0xa7, 0xa9, 0xc1, 0xd8, 0x80, 0x18,
    0x01, 0x15, 0x2c, 0xed, 0x00, 0x00, 0x01, 0x01, 0x08, 0x0a, 0x7c, 0x17, 0x05, 0xb6, 0x9e, 0x62,
    0x6f, 0x27, 0x17, 0x03, 0x03, 0x00, 0x22, 0x1c, 0xeb, 0x68, 0x29, 0xea, 0x20, 0x2d, 0xb2, 0x6f,
    0x97, 0xdf, 0x26, 0xf5, 0x70, 0x9c, 0x09, 0xe0, 0x0d, 0xda, 0xf5, 0xf9, 0xd5, 0x37, 0x92, 0x4f,
    0x81, 0xe7, 0x65, 0x1e, 0xb1, 0x77, 0xcc, 0x72, 0x11
};

/**
 * @brief This function validates getting the TCP payload data
 *        and check the length of this data when frame type is IPv4.
 */
void test_prvCheckRxData_IPv4( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    uint8_t * pData;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    result = prvCheckRxData( pxNetworkBuffer, &pData );

    TEST_ASSERT_EQUAL( 14, result );
}

/**
 * @brief This function validates getting the TCP payload data
 *        and check the length of this data when frame type is IPv6.
 */
void test_prvCheckRxData_IPv6( void )
{
    int32_t result;
    uint8_t EthernetBuffer[ ipconfigNETWORK_MTU ];
    EthernetHeader_t * px_ethHeader;
    uint8_t * pData;
    IPHeader_IPv6_t * pxIPHeader;

    /* Setup TCP option for tests */
    memset( EthernetBuffer, 0, sizeof( EthernetBuffer ) );
    pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    pxNetworkBuffer->xDataLength = 0x50;
    px_ethHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    px_ethHeader->usFrameType = ipIPv6_FRAME_TYPE;
    pxIPHeader = ( IPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] );
    pxIPHeader->usPayloadLength = FreeRTOS_htons( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ) );

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv6_HEADER );
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv6_HEADER );

    result = prvCheckRxData( pxNetworkBuffer, &pData );

    TEST_ASSERT_EQUAL( ( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ) ), result );
}

/**
 * @brief This function validates getting the TCP payload data
 *        and check the length of this data when frame type is incorrect.
 */
void test_prvCheckRxData_IncorrectFrameType( void )
{
    int32_t result;
    uint8_t EthernetBuffer[ ipconfigNETWORK_MTU ];
    EthernetHeader_t * px_ethHeader;
    uint8_t * pData;

    /* Setup TCP option for tests */
    memset( EthernetBuffer, 0, sizeof( EthernetBuffer ) );
    pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    px_ethHeader = ( EthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;
    px_ethHeader->usFrameType = 0;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( 0 );
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( 0 );

    result = prvCheckRxData( pxNetworkBuffer, &pData );

    TEST_ASSERT_EQUAL( 0, result );
}


/* Test for prvCheckRxData function. */
void test_prvCheckRxData_URG_On( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    /* Set TCP Flag URG */
    uint8_t EthernetBuffer_urg[ ipconfigNETWORK_MTU ] =
    {
        0x8c, 0xdc, 0xd4, 0x4a, 0xea, 0x02, 0xa0, 0x40, 0xa0, 0x3a, 0x21, 0xea, 0x08, 0x00, 0x45, 0x20,
        0x00, 0x5b, 0xd2, 0xe9, 0x00, 0x00, 0x39, 0x06, 0x32, 0x47, 0xac, 0xd9, 0x0e, 0xc3, 0xc0, 0xa8,
        0x00, 0x08, 0x01, 0xbb, 0xdc, 0x44, 0xe2, 0x34, 0xd4, 0x84, 0xa7, 0xa9, 0xc1, 0xd8, 0x80, 0x38,
        0x01, 0x15, 0x2c, 0xed, 0x00, 0x10, 0x01, 0x01, 0x08, 0x0a, 0x7c, 0x17, 0x05, 0xb6, 0x9e, 0x62,
        0x6f, 0x27, 0x17, 0x03, 0x03, 0x00, 0x22, 0x1c, 0xeb, 0x68, 0x29, 0xea, 0x20, 0x2d, 0xb2, 0x6f,
        0x97, 0xdf, 0x26, 0xf5, 0x70, 0x9c, 0x09, 0xe0, 0x0d, 0xda, 0xf5, 0xf9, 0xd5, 0x37, 0x92, 0x4f,
        0x81, 0xe7, 0x65, 0x1e, 0xb1, 0x77, 0xcc, 0x72, 0x11
    };


    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_urg;
    uint8_t * pData;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    FreeRTOS_min_int32_ExpectAnyArgsAndReturn( 10 );

    result = prvCheckRxData( pxNetworkBuffer, &pData );

    TEST_ASSERT_EQUAL( 4, result );
}

/* Test for prvStorexData function. */
void test_prvStoreRxData_Happy_Path( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    uint8_t * pData;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    result = prvCheckRxData( pxNetworkBuffer, &pData );

    TEST_ASSERT_EQUAL( 14, result );

    BaseType_t xResult = 0;
    xSocket.u.xTCP.uxRxStreamSize = 39;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.rxStream = ( StreamBuffer_t * ) 0x12345678;
    pxSocket = &xSocket;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    pxTCPWindow->ulUserDataLength = 14;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxStreamBufferGetSpace_ExpectAnyArgsAndReturn( 100 );
    lTCPWindowRxCheck_ExpectAnyArgsAndReturn( 20 );
    lTCPAddRxdata_ExpectAnyArgsAndReturn( 14 );
    lTCPAddRxdata_ExpectAnyArgsAndReturn( 14 );


    xResult = prvStoreRxData( pxSocket,
                              pData,
                              pxNetworkBuffer,
                              14 );

    TEST_ASSERT_EQUAL( 0, xResult );
}

/* Test for prvStorexData function. */
void test_prvStoreRxData_Wrong_State( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    uint8_t * pData;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    result = prvCheckRxData( pxNetworkBuffer, &pData );

    TEST_ASSERT_EQUAL( 14, result );

    BaseType_t xResult = 0;
    xSocket.u.xTCP.eTCPState = eCONNECT_SYN;
    pxSocket = &xSocket;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    xResult = prvStoreRxData( pxSocket,
                              pData,
                              pxNetworkBuffer,
                              105 );

    TEST_ASSERT_EQUAL( 0, xResult );
}

/* Test for prvStorexData function. */
void test_prvStoreRxData_Zero_Length( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    /* zero-length packet */
    uint8_t EthernetBuffer_zl[ ipconfigNETWORK_MTU ] =
    {
        0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x08, 0x00, 0x45, 0x00,
        0x00, 0x34, 0x15, 0xc2, 0x40, 0x00, 0x40, 0x06, 0xa8, 0x8e, 0xc0, 0xa8, 0x00, 0x08, 0xac, 0xd9,
        0x0e, 0xea, 0xea, 0xfe, 0x01, 0xbb, 0x8b, 0xaf, 0x8a, 0x24, 0xdc, 0x96, 0x95, 0x7a, 0x80, 0x10,
        0x01, 0xf5, 0x7c, 0x9a, 0x00, 0x00, 0x01, 0x01, 0x08, 0x0a, 0xb8, 0x53, 0x57, 0x27, 0xb2, 0xce,
        0xc3, 0x17
    };

    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer_zl;
    uint8_t * pData;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    result = prvCheckRxData( pxNetworkBuffer, &pData );

    TEST_ASSERT_EQUAL( 0, result );

    BaseType_t xResult = 0;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    pxSocket = &xSocket;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    xResult = prvStoreRxData( pxSocket,
                              pData,
                              pxNetworkBuffer,
                              0 );

    TEST_ASSERT_EQUAL( 0, xResult );
}


/* Test for prvStorexData function. */
void test_prvStoreRxData_Null_RxStream( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    uint8_t * pData;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    result = prvCheckRxData( pxNetworkBuffer, &pData );

    TEST_ASSERT_EQUAL( 14, result );

    BaseType_t xResult = 0;
    xSocket.u.xTCP.uxRxStreamSize = 39;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.rxStream = NULL;
    pxSocket = &xSocket;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    lTCPWindowRxCheck_ExpectAnyArgsAndReturn( 20 );
    lTCPAddRxdata_ExpectAnyArgsAndReturn( 14 );
    prvTCPSendReset_IgnoreAndReturn( pdTRUE );

    xResult = prvStoreRxData( pxSocket,
                              pData,
                              pxNetworkBuffer,
                              105 );

    TEST_ASSERT_EQUAL( -1, xResult );
}

/* Test for prvStorexData function. */
void test_prvStoreRxData_Negative_Offset( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;
    uint8_t * pData;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    result = prvCheckRxData( pxNetworkBuffer, &pData );

    TEST_ASSERT_EQUAL( 14, result );

    BaseType_t xResult = 0;
    xSocket.u.xTCP.uxRxStreamSize = 39;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.rxStream = NULL;
    pxSocket = &xSocket;
    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    pxTCPWindow->ulUserDataLength = 0;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    lTCPWindowRxCheck_ExpectAnyArgsAndReturn( -1 );

    xResult = prvStoreRxData( pxSocket,
                              pData,
                              pxNetworkBuffer,
                              105 );

    TEST_ASSERT_EQUAL( 0, xResult );
}

/* Test for prvStorexData function. */
void test_prvStoreRxData_None_Zero_Skipcount( void )
{
    int32_t result;

    /* Setup TCP option for tests */
    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = EthernetBuffer;

    ProtocolHeaders_t * pxProtocolHeaders = ( ( ProtocolHeaders_t * )
                                              &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ] ) );
    TCPHeader_t * pxTCPHeader = &pxProtocolHeaders->xTCPHeader;
    uint8_t * pData;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );

    result = prvCheckRxData( pxNetworkBuffer, &pData );

    TEST_ASSERT_EQUAL( 14, result );

    BaseType_t xResult = 0;
    xSocket.u.xTCP.uxRxStreamSize = 39;
    xSocket.u.xTCP.eTCPState = eESTABLISHED;
    xSocket.u.xTCP.rxStream = NULL;
    pxSocket = &xSocket;

    TCPWindow_t * pxTCPWindow = &pxSocket->u.xTCP.xTCPWindow;
    pxTCPWindow->ulUserDataLength = 0;
    uint32_t SkipCount;
    uint32_t * pSkipCount = &SkipCount;
    *( pSkipCount ) = 10;

    uxIPHeaderSizePacket_ExpectAnyArgsAndReturn( ipSIZE_OF_IPv4_HEADER );
    lTCPWindowRxCheck_ExpectAndReturn(
        pxTCPWindow,
        FreeRTOS_ntohl( pxTCPHeader->ulSequenceNumber ),
        14,
        pxSocket->u.xTCP.uxRxStreamSize,
        NULL,
        20 );
    lTCPWindowRxCheck_IgnoreArg_pulSkipCount();
    lTCPWindowRxCheck_ReturnThruPtr_pulSkipCount( pSkipCount );
    lTCPAddRxdata_ExpectAnyArgsAndReturn( 4 );
    prvTCPSendReset_IgnoreAndReturn( pdTRUE );

    xResult = prvStoreRxData( pxSocket,
                              pData,
                              pxNetworkBuffer,
                              14 );

    TEST_ASSERT_EQUAL( 0, xResult );
}
