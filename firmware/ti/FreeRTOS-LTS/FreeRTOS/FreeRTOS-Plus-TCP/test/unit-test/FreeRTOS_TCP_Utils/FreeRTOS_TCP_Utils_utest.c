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
#include "mock_FreeRTOS_TCP_IP.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_TCP_Utils_stubs.c"
#include "FreeRTOS_TCP_Utils.h"

/* =========================== EXTERN VARIABLES =========================== */

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

/* ============================== Test Cases ============================== */

/**
 * @brief This function Print out the value of flags
 *        in a human readable manner.
 */
void test_prvTCPFlagMeaning_FlagGroup1( void )
{
    char ReturnString[ 10 ];
    size_t Flags = tcpTCP_FLAG_FIN | tcpTCP_FLAG_RST | tcpTCP_FLAG_ACK | tcpTCP_FLAG_ECN;

    strncpy( ReturnString, prvTCPFlagMeaning( Flags ), sizeof( ReturnString ) );
    TEST_ASSERT_EQUAL_STRING( "F.R.A.E.", ReturnString );
}

/**
 * @brief This function Print out the value of flags
 *        in a human readable manner.
 */
void test_prvTCPFlagMeaning_FlagGroup2( void )
{
    char ReturnString[ 10 ];
    size_t Flags = tcpTCP_FLAG_SYN | tcpTCP_FLAG_PSH | tcpTCP_FLAG_URG | tcpTCP_FLAG_CWR;

    strncpy( ReturnString, prvTCPFlagMeaning( Flags ), sizeof( ReturnString ) );
    TEST_ASSERT_EQUAL_STRING( ".S.P.U.C", ReturnString );
}

/**
 * @brief This function sets the maximum segment size for
 *        IPv4 packet with NULL endpoint.
 */
void test_prvSocketSetMSS_NULL_EP( void )
{
    NetworkEndPoint_t * pxEndPoint = NULL;

    pxSocket = &xSocket;

    pxSocket->bits.bIsIPv6 = pdFALSE_UNSIGNED;
    pxSocket->pxEndPoint = pxEndPoint;
    pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4 = 0xC0C0C0C0;

    prvSocketSetMSS( pxSocket );

    TEST_ASSERT_EQUAL( ipconfigTCP_MSS, pxSocket->u.xTCP.usMSS );
}

/**
 * @brief This function sets the maximum segment size for
 *        IPv4 packet with valid endpoint.
 */
void test_prvSocketSetMSS_Reduced( void )
{
    NetworkEndPoint_t xEndPoint;

    pxSocket = &xSocket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxSocket->bits.bIsIPv6 = pdFALSE_UNSIGNED;
    pxSocket->pxEndPoint = &xEndPoint;
    pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4 = 0xC0C0C0C0;
    xEndPoint.ipv4_settings.ulIPAddress = 0xC1C1C1C1;
    xEndPoint.ipv4_settings.ulNetMask = 0xFFFFFF00;

    FreeRTOS_min_uint32_ExpectAnyArgsAndReturn( 1400 );
    prvSocketSetMSS( pxSocket );
    TEST_ASSERT_EQUAL( 1400, pxSocket->u.xTCP.usMSS );
}

/**
 * @brief This function sets the maximum segment size for
 *        IPv6 packet with valid endpoint.
 */
void test_prvSocketSetMSS_Normal( void )
{
    NetworkEndPoint_t xEndPoint = { 0 };

    pxSocket = &xSocket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxSocket->bits.bIsIPv6 = pdFALSE_UNSIGNED;
    xEndPoint.ipv4_settings.ulIPAddress = 0;
    xEndPoint.ipv4_settings.ulNetMask = 0xFFFFFF00;
    pxSocket->pxEndPoint = &xEndPoint;
    pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4 = 0x0;

    prvSocketSetMSS( pxSocket );
    TEST_ASSERT_EQUAL( ipconfigNETWORK_MTU - 40U, pxSocket->u.xTCP.usMSS );
}

/**
 * @brief This function sets the maximum segment size for
 *        IPv6 packet.
 */
void test_prvSocketSetMSS_Normal_IPv6( void )
{
    NetworkEndPoint_t xEndPoint = { 0 };

    pxSocket = &xSocket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxSocket->bits.bIsIPv6 = 1;

    prvSocketSetMSS( pxSocket );
}
