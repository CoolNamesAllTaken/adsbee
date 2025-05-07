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

#include "FreeRTOS_IP.h"

#include "FreeRTOS_Sockets.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/* ============================ EXTERN VARIABLES ============================ */

#define TEST_MAX_UDPV4_PAYLOAD_LENGTH    ipconfigNETWORK_MTU - ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_UDP_HEADER )

BaseType_t xTCPWindowLoggingLevel = 0;

/* =============================== Test Cases =============================== */

/**
 * @brief Sending more than maximum allowed data in one go.
 * And the family of destination address is set as invalid value.
 */
void test_FreeRTOS_sendto_MoreDataThanUDPPayload_UseTempDestinationAddress( void )
{
    int32_t lResult;
    Socket_t xSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH + 1;
    BaseType_t xFlags;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;

    xDestinationAddress.sin_family = FREERTOS_AF_INET + 1;

    lResult = FreeRTOS_sendto( xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
}

/**
 * @brief Sending more than maximum allowed data in one go.
 * And the family of destination address is set as FREERTOS_AF_INET6.
 */
void test_FreeRTOS_sendto_MoreDataThanUDPPayload_IPv6DestinationAddress( void )
{
    int32_t lResult;
    Socket_t xSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH + 1;
    BaseType_t xFlags;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;

    xDestinationAddress.sin_family = FREERTOS_AF_INET6;

    lResult = FreeRTOS_sendto( xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( -pdFREERTOS_ERRNO_EINVAL, lResult );
}

/**
 * @brief Sending more than maximum allowed data in one go.
 * And the family of destination address is set as FREERTOS_AF_INET.
 */
void test_FreeRTOS_sendto_MoreDataThanUDPPayload_IPv4DestinationAddress( void )
{
    int32_t lResult;
    Socket_t xSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH + 1;
    BaseType_t xFlags;
    struct freertos_sockaddr xDestinationAddress;
    socklen_t xDestinationAddressLength;

    xDestinationAddress.sin_family = FREERTOS_AF_INET;

    lResult = FreeRTOS_sendto( xSocket, pvBuffer, uxTotalDataLength, xFlags, &xDestinationAddress, xDestinationAddressLength );

    TEST_ASSERT_EQUAL( 0, lResult );
}

/**
 * @brief Sending more than maximum allowed data in one go.
 * And the destination address is NULL.
 */
void test_FreeRTOS_sendto_MoreDataThanUDPPayload_NullDestinationAddress( void )
{
    int32_t lResult;
    Socket_t xSocket;
    char pvBuffer[ ipconfigTCP_MSS ];
    size_t uxTotalDataLength = TEST_MAX_UDPV4_PAYLOAD_LENGTH + 1;
    BaseType_t xFlags;
    socklen_t xDestinationAddressLength;

    catch_assert( FreeRTOS_sendto( xSocket, pvBuffer, uxTotalDataLength, xFlags, NULL, xDestinationAddressLength ) );
}
