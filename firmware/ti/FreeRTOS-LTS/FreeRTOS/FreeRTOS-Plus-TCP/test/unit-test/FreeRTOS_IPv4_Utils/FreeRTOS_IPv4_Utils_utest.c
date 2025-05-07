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

#include "FreeRTOS_IPv4_Utils.h"

#include "catch_assert.h"

/* ============================== Test Cases ============================== */

/**
 * @brief test_vSetMultiCastIPv4MacAddress
 * To validate if vSetMultiCastIPv4MacAddress sets IPv4 multicast MAC address correctly
 * into input pointer.
 */
void test_vSetMultiCastIPv4MacAddress( void )
{
    uint32_t ulIP = 0xABCDEF12;
    MACAddress_t xMACAddress;

    vSetMultiCastIPv4MacAddress( ulIP, &xMACAddress );

    TEST_ASSERT_EQUAL( ( uint8_t ) 0x01U, xMACAddress.ucBytes[ 0 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) 0x00U, xMACAddress.ucBytes[ 1 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) 0x5EU, xMACAddress.ucBytes[ 2 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) ( ( FreeRTOS_ntohl( ulIP ) >> 16 ) & 0x7fU ), xMACAddress.ucBytes[ 3 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) ( ( FreeRTOS_ntohl( ulIP ) >> 8 ) & 0xffU ), xMACAddress.ucBytes[ 4 ] );
    TEST_ASSERT_EQUAL( ( uint8_t ) ( ( FreeRTOS_ntohl( ulIP ) ) & 0xffU ), xMACAddress.ucBytes[ 5 ] );
}

/**
 * @brief test_prvChecksumIPv4Checks_IPLengthLessThanHeaderLength
 * To validate if prvChecksumIPv4Checks sets ipINVALID_LENGTH in checksum field when
 * length in IPv4 header is less than ucVersionHeaderLength.
 */
void test_prvChecksumIPv4Checks_IPLengthLessThanHeaderLength()
{
    BaseType_t xReturn;
    IPPacket_t xIPPacket;
    struct xPacketSummary xSet;
    uint8_t ucVersionHeaderLength = 20;
    uint16_t usLength = ucVersionHeaderLength - 1;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = usLength + ipSIZE_OF_ETH_HEADER;

    memset( &xIPPacket, 0, sizeof( xIPPacket ) );
    memset( &xSet, 0, sizeof( xSet ) );

    xSet.pxIPPacket = &xIPPacket;
    xIPPacket.xIPHeader.usLength = FreeRTOS_htons( usLength );
    xIPPacket.xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    xReturn = prvChecksumIPv4Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( 3, xReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief test_prvChecksumIPv4Checks_BufferLessIPPacket
 * To validate if prvChecksumIPv4Checks sets ipINVALID_LENGTH in checksum field when
 * buffer size is less than IPv4 packet minimum requirement.
 */
void test_prvChecksumIPv4Checks_BufferLessIPPacket()
{
    BaseType_t xReturn;
    IPPacket_t xIPPacket;
    struct xPacketSummary xSet;
    uint8_t ucVersionHeaderLength = 20;
    uint16_t usLength = ucVersionHeaderLength;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER - 1;

    memset( &xIPPacket, 0, sizeof( xIPPacket ) );
    memset( &xSet, 0, sizeof( xSet ) );

    xSet.pxIPPacket = &xIPPacket;
    xIPPacket.xIPHeader.usLength = FreeRTOS_htons( usLength );
    xIPPacket.xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    xReturn = prvChecksumIPv4Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( 4, xReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief test_prvChecksumIPv4Checks_BufferLessIPHeaderLength
 * To validate if prvChecksumIPv4Checks sets ipINVALID_LENGTH in checksum field when
 * buffer size is less than IPv4 header length.
 */
void test_prvChecksumIPv4Checks_BufferLessIPHeaderLength()
{
    BaseType_t xReturn;
    IPPacket_t xIPPacket;
    struct xPacketSummary xSet;
    uint8_t ucVersionHeaderLength = 24;
    uint16_t usLength = ucVersionHeaderLength;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + ucVersionHeaderLength - 1;

    memset( &xIPPacket, 0, sizeof( xIPPacket ) );
    memset( &xSet, 0, sizeof( xSet ) );

    xSet.pxIPPacket = &xIPPacket;
    xIPPacket.xIPHeader.usLength = FreeRTOS_htons( usLength );
    xIPPacket.xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    xReturn = prvChecksumIPv4Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( 5, xReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief test_prvChecksumIPv4Checks_BufferLessIPPayloadLength
 * To validate if prvChecksumIPv4Checks sets ipINVALID_LENGTH in checksum field when
 * buffer size is less than IPv4 header payload length.
 */
void test_prvChecksumIPv4Checks_BufferLessIPPayloadLength()
{
    BaseType_t xReturn;
    IPPacket_t xIPPacket;
    struct xPacketSummary xSet;
    uint8_t ucVersionHeaderLength = 20;
    uint16_t usLength = ucVersionHeaderLength + ipSIZE_OF_TCP_HEADER;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + usLength - 1;

    memset( &xIPPacket, 0, sizeof( xIPPacket ) );
    memset( &xSet, 0, sizeof( xSet ) );

    xSet.pxIPPacket = &xIPPacket;
    xIPPacket.xIPHeader.usLength = FreeRTOS_htons( usLength );
    xIPPacket.xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );

    xReturn = prvChecksumIPv4Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( 6, xReturn );
    TEST_ASSERT_EQUAL( ipINVALID_LENGTH, xSet.usChecksum );
}

/**
 * @brief test_prvChecksumIPv4Checks_Pass
 * To validate if prvChecksumIPv4Checks returns 0 when pass.
 */
void test_prvChecksumIPv4Checks_Pass()
{
    BaseType_t xReturn;
    IPPacket_t xIPPacket;
    struct xPacketSummary xSet;
    uint8_t ucVersionHeaderLength = 20;
    uint16_t usLength = ucVersionHeaderLength + ipSIZE_OF_TCP_HEADER;
    uint8_t pucEthernetBuffer[ ipconfigTCP_MSS ];
    size_t uxBufferLength = ipSIZE_OF_ETH_HEADER + usLength;

    memset( &xIPPacket, 0, sizeof( xIPPacket ) );
    memset( &xSet, 0, sizeof( xSet ) );

    xSet.pxIPPacket = &xIPPacket;
    xIPPacket.xIPHeader.usLength = FreeRTOS_htons( usLength );
    xIPPacket.xIPHeader.ucVersionHeaderLength = ( ucVersionHeaderLength >> 2 );
    xIPPacket.xIPHeader.ucProtocol = ipPROTOCOL_TCP;

    xReturn = prvChecksumIPv4Checks( pucEthernetBuffer, uxBufferLength, &xSet );

    TEST_ASSERT_EQUAL( 0, xReturn );
    TEST_ASSERT_EQUAL( ipPROTOCOL_TCP, xSet.ucProtocol );
    TEST_ASSERT_EQUAL( &pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ucVersionHeaderLength ], xSet.pxProtocolHeaders );
    TEST_ASSERT_EQUAL( ipSIZE_OF_TCP_HEADER, xSet.usProtocolBytes );
}
