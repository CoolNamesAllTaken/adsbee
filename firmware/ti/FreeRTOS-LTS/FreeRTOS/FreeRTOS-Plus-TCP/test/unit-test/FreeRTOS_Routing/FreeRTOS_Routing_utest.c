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
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IPv6.h"
#include "mock_FreeRTOS_Sockets.h"

#include "FreeRTOS_Routing.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_Routing_stubs.c"

/* ===========================  EXTERN VARIABLES  =========================== */

/* Default IPv4 address is 192.168.123.223, which is 0xDF7BA8C0. */
#define IPV4_DEFAULT_ADDRESS       ( 0xDF7BA8C0 )
/* Default IPv4 netmask is 255.255.255.0, which is 0x00FFFFFF. */
#define IPV4_DEFAULT_NETMASK       ( 0x00FFFFFF )
/* Default IPv4 netmask is 192.168.123.254, which is 0xFE7BA8C0. */
#define IPV4_DEFAULT_GATEWAY       ( 0xFE7BA8C0 )
/* Default IPv4 netmask is 192.168.123.1, which is 0x017BA8C0. */
#define IPV4_DEFAULT_DNS_SERVER    ( 0x017BA8C0 )

extern RoutingStats_t xRoutingStatistics;
const struct xIPv6_Address FreeRTOS_in6addr_any;
const struct xIPv6_Address FreeRTOS_in6addr_loopback;

const uint8_t ucDefaultIPAddress_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 192, 168, 123, 223 };
const uint8_t ucDefaultNetMask_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 255, 255, 255, 0 };
const uint8_t ucDefaultGatewayAddress_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 192, 168, 123, 254 };
const uint8_t ucDefaultDNSServerAddress_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 192, 168, 123, 1 };
const uint8_t ucDefaultMACAddress_IPv4[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };

/* Default IPv6 address is set to 2001::1 */
const IPv6_Address_t xDefaultIPAddress_IPv6 = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
/* Default IPv6 address is set to 2001:: */
const IPv6_Address_t xDefaultNetPrefix_IPv6 = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
const size_t xDefaultPrefixLength = 64U;
/* Default IPv6 address is set to 2001::fffe */
const IPv6_Address_t xDefaultGatewayAddress_IPv6 = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xfe };
/* Default IPv6 address is set to 2001::ffee */
const IPv6_Address_t xDefaultDNSServerAddress_IPv6 = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xee };

const uint8_t ucDefaultMACAddress_IPv6[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x22, 0x33, 0xab, 0xcd, 0xef };

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
    pxNetworkEndPoints = NULL;
    pxNetworkInterfaces = NULL;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint when all input parameters
 * are valid IPv4 default setting.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint.
 *  - Check if pxNetworkEndPoints is same as input endpoint.
 *  - Check if all setting are correctly stored in endpoint.
 */
void test_FreeRTOS_FillEndPoint_HappyPath( void )
{
    NetworkInterface_t xInterfaces;
    NetworkEndPoint_t xEndPoint;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    printf( "test_FreeRTOS_FillEndPoint_happy_path: xEndPoint=%p\n", &xEndPoint );

    FreeRTOS_FillEndPoint( &xInterfaces,
                           &xEndPoint,
                           ucDefaultIPAddress_IPv4,
                           ucDefaultNetMask_IPv4,
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultDNSServerAddress_IPv4,
                           ucDefaultMACAddress_IPv4 );

    TEST_ASSERT_EQUAL( &xEndPoint, pxNetworkEndPoints );
    TEST_ASSERT_EQUAL( &xEndPoint, xInterfaces.pxEndPoint );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_ADDRESS, xEndPoint.ipv4_defaults.ulIPAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_NETMASK, xEndPoint.ipv4_defaults.ulNetMask );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_GATEWAY, xEndPoint.ipv4_defaults.ulGatewayAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_DNS_SERVER, xEndPoint.ipv4_defaults.ulDNSServerAddresses[ 0 ] );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xEndPoint.bits.bIPv6 );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint when network interface is NULL.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint with NULL network interface.
 *  - Check if pxNetworkEndPoints is NULL.
 */
void test_FreeRTOS_FillEndPoint_NullInterface( void )
{
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    FreeRTOS_FillEndPoint( NULL,
                           &xEndPoint,
                           ucDefaultIPAddress_IPv4,
                           ucDefaultNetMask_IPv4,
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultDNSServerAddress_IPv4,
                           ucDefaultMACAddress_IPv4 );

    TEST_ASSERT_EQUAL( NULL, pxNetworkEndPoints );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint when endpoint is NULL.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint with NULL endpoint.
 *  - Check if pxNetworkEndPoints is NULL.
 */
void test_FreeRTOS_FillEndPoint_NullEndpoint( void )
{
    NetworkInterface_t xInterfaces;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );

    FreeRTOS_FillEndPoint( &xInterfaces,
                           NULL,
                           ucDefaultIPAddress_IPv4,
                           ucDefaultNetMask_IPv4,
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultDNSServerAddress_IPv4,
                           ucDefaultMACAddress_IPv4 );

    TEST_ASSERT_EQUAL( NULL, pxNetworkEndPoints );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint when all input parameters
 * are valid IPv4 default setting.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint.
 *  - Check if pxNetworkEndPoints is same as input endpoint.
 *  - Check if all setting are correctly stored in endpoint.
 *  - Loop steps up here three times.
 */
void test_FreeRTOS_FillEndPoint_MultipleEndpoints( void )
{
    NetworkInterface_t xInterfaces;
    NetworkEndPoint_t xEndPoint[ 3 ];

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    memset( &xEndPoint[ 2 ], 0, sizeof( NetworkEndPoint_t ) );

    FreeRTOS_FillEndPoint( &xInterfaces,
                           &xEndPoint[ 0 ],
                           ucDefaultIPAddress_IPv4,
                           ucDefaultNetMask_IPv4,
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultDNSServerAddress_IPv4,
                           ucDefaultMACAddress_IPv4 );

    TEST_ASSERT_EQUAL( &xEndPoint[ 0 ], pxNetworkEndPoints );
    TEST_ASSERT_EQUAL( &xEndPoint[ 0 ], xInterfaces.pxEndPoint );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_ADDRESS, xEndPoint[ 0 ].ipv4_defaults.ulIPAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_NETMASK, xEndPoint[ 0 ].ipv4_defaults.ulNetMask );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_GATEWAY, xEndPoint[ 0 ].ipv4_defaults.ulGatewayAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_DNS_SERVER, xEndPoint[ 0 ].ipv4_defaults.ulDNSServerAddresses[ 0 ] );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint[ 0 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xEndPoint[ 0 ].bits.bIPv6 );
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );

    FreeRTOS_FillEndPoint( &xInterfaces,
                           &xEndPoint[ 1 ],
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultNetMask_IPv4,
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultDNSServerAddress_IPv4,
                           ucDefaultMACAddress_IPv4 );

    TEST_ASSERT_EQUAL( &xEndPoint[ 1 ], pxNetworkEndPoints->pxNext );
    TEST_ASSERT_EQUAL( &xEndPoint[ 1 ], xInterfaces.pxEndPoint->pxNext );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_GATEWAY, xEndPoint[ 1 ].ipv4_defaults.ulIPAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_NETMASK, xEndPoint[ 1 ].ipv4_defaults.ulNetMask );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_GATEWAY, xEndPoint[ 1 ].ipv4_defaults.ulGatewayAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_DNS_SERVER, xEndPoint[ 1 ].ipv4_defaults.ulDNSServerAddresses[ 0 ] );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint[ 1 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xEndPoint[ 1 ].bits.bIPv6 );

    FreeRTOS_FillEndPoint( &xInterfaces,
                           &xEndPoint[ 2 ],
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultNetMask_IPv4,
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultDNSServerAddress_IPv4,
                           ucDefaultMACAddress_IPv4 );

    TEST_ASSERT_EQUAL( &xEndPoint[ 2 ], pxNetworkEndPoints->pxNext->pxNext );
    TEST_ASSERT_EQUAL( &xEndPoint[ 2 ], xInterfaces.pxEndPoint->pxNext->pxNext );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_GATEWAY, xEndPoint[ 2 ].ipv4_defaults.ulIPAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_NETMASK, xEndPoint[ 2 ].ipv4_defaults.ulNetMask );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_GATEWAY, xEndPoint[ 2 ].ipv4_defaults.ulGatewayAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_DNS_SERVER, xEndPoint[ 2 ].ipv4_defaults.ulDNSServerAddresses[ 0 ] );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint[ 2 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xEndPoint[ 2 ].bits.bIPv6 );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint when all input parameters
 * are valid IPv6 default setting.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint.
 *  - Check if pxNetworkEndPoints is same as input endpoint.
 *  - Check if all setting are correctly stored in endpoint.
 *  - Call FreeRTOS_FillEndPoint to fill with same endpoint.
 *  - Check if endpoint is not attached.
 */
void test_FreeRTOS_FillEndPoint_SameEndpoint( void )
{
    NetworkInterface_t xInterfaces;
    NetworkEndPoint_t xEndPoint;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    FreeRTOS_FillEndPoint( &xInterfaces,
                           &xEndPoint,
                           ucDefaultIPAddress_IPv4,
                           ucDefaultNetMask_IPv4,
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultDNSServerAddress_IPv4,
                           ucDefaultMACAddress_IPv4 );

    TEST_ASSERT_EQUAL( &xEndPoint, pxNetworkEndPoints );
    TEST_ASSERT_EQUAL( &xEndPoint, xInterfaces.pxEndPoint );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_ADDRESS, xEndPoint.ipv4_defaults.ulIPAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_NETMASK, xEndPoint.ipv4_defaults.ulNetMask );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_GATEWAY, xEndPoint.ipv4_defaults.ulGatewayAddress );
    TEST_ASSERT_EQUAL( IPV4_DEFAULT_DNS_SERVER, xEndPoint.ipv4_defaults.ulDNSServerAddresses[ 0 ] );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, xEndPoint.bits.bIPv6 );

    FreeRTOS_FillEndPoint( &xInterfaces,
                           &xEndPoint,
                           ucDefaultIPAddress_IPv4,
                           ucDefaultNetMask_IPv4,
                           ucDefaultGatewayAddress_IPv4,
                           ucDefaultDNSServerAddress_IPv4,
                           ucDefaultMACAddress_IPv4 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxNetworkEndPoints );
    TEST_ASSERT_EQUAL( NULL, pxNetworkEndPoints->pxNext );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint_IPv6 when all input parameters
 * are valid IPv6 default setting.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint_IPv6 to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint.
 *  - Check if pxNetworkEndPoints is same as input endpoint.
 *  - Check if all setting are correctly stored in endpoint.
 */
void test_FreeRTOS_FillEndPoint_IPv6_HappyPath( void )
{
    NetworkInterface_t xInterfaces;
    NetworkEndPoint_t xEndPoint;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                &xEndPoint,
                                &xDefaultIPAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );

    TEST_ASSERT_EQUAL( &xEndPoint, pxNetworkEndPoints );
    TEST_ASSERT_EQUAL( &xEndPoint, xInterfaces.pxEndPoint );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultIPAddress_IPv6, xEndPoint.ipv6_defaults.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultNetPrefix_IPv6, xEndPoint.ipv6_defaults.xPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( xDefaultPrefixLength, xEndPoint.ipv6_defaults.uxPrefixLength );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultGatewayAddress_IPv6, xEndPoint.ipv6_defaults.xGatewayAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultDNSServerAddress_IPv6, xEndPoint.ipv6_defaults.xDNSServerAddresses[ 0 ].ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xEndPoint.bits.bIPv6 );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint when network interface is NULL.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint_IPv6 to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint with NULL network interface.
 *  - Check if pxNetworkEndPoints is NULL.
 */
void test_FreeRTOS_FillEndPoint_IPv6_NullInterface( void )
{
    NetworkEndPoint_t xEndPoint;

    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    FreeRTOS_FillEndPoint_IPv6( NULL,
                                &xEndPoint,
                                &xDefaultIPAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );

    TEST_ASSERT_EQUAL( NULL, pxNetworkEndPoints );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint_IPv6 when endpoint is NULL.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint_IPv6 to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint with NULL endpoint.
 *  - Check if pxNetworkEndPoints is NULL.
 */
void test_FreeRTOS_FillEndPoint_IPv6_NullEndpoint( void )
{
    NetworkInterface_t xInterfaces;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                NULL,
                                &xDefaultIPAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );

    TEST_ASSERT_EQUAL( NULL, pxNetworkEndPoints );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint_IPv6 when input IP address is NULL.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint_IPv6 with NULL IP address pointer.
 */
void test_FreeRTOS_FillEndPoint_IPv6_NullIP( void )
{
    NetworkInterface_t xInterfaces;
    NetworkEndPoint_t xEndPoint;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                &xEndPoint,
                                NULL,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint_IPv6 when input MAC address is NULL.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint_IPv6 with NULL MAC address pointer.
 */
void test_FreeRTOS_FillEndPoint_IPv6_NullMAC( void )
{
    NetworkInterface_t xInterfaces;
    NetworkEndPoint_t xEndPoint;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                &xEndPoint,
                                &xDefaultIPAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                NULL );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint_IPv6 when some input parameters
 * are NULL (gateway, DNS and prefix).
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint_IPv6 to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint.
 *  - Check if pxNetworkEndPoints is same as input endpoint.
 *  - Check if all setting are correctly stored in endpoint.
 */
void test_FreeRTOS_FillEndPoint_IPv6_NullGatewayDNSPrefix( void )
{
    NetworkInterface_t xInterfaces;
    NetworkEndPoint_t xEndPoint;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( xEndPoint ) );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                &xEndPoint,
                                &xDefaultIPAddress_IPv6,
                                NULL,
                                0,
                                NULL,
                                NULL,
                                ucDefaultMACAddress_IPv6 );

    TEST_ASSERT_EQUAL( &xEndPoint, pxNetworkEndPoints );
    TEST_ASSERT_EQUAL( &xEndPoint, xInterfaces.pxEndPoint );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultIPAddress_IPv6, xEndPoint.ipv6_defaults.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( 0, xEndPoint.ipv6_defaults.uxPrefixLength );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xEndPoint.bits.bIPv6 );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint_IPv6 when all input parameters
 * are valid IPv6 default setting.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint_IPv6 to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint.
 *  - Check if pxNetworkEndPoints is same as input endpoint.
 *  - Check if all setting are correctly stored in endpoint.
 *  - Loop steps up here three times.
 */
void test_FreeRTOS_FillEndPoint_IPv6_MultipleEndpoints( void )
{
    NetworkInterface_t xInterfaces;
    NetworkEndPoint_t xEndPoint[ 3 ];

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    memset( &xEndPoint[ 2 ], 0, sizeof( NetworkEndPoint_t ) );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                &xEndPoint[ 0 ],
                                &xDefaultIPAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );

    TEST_ASSERT_EQUAL( &xEndPoint[ 0 ], pxNetworkEndPoints );
    TEST_ASSERT_EQUAL( &xEndPoint[ 0 ], xInterfaces.pxEndPoint );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultIPAddress_IPv6, xEndPoint[ 0 ].ipv6_defaults.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultNetPrefix_IPv6, xEndPoint[ 0 ].ipv6_defaults.xPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( xDefaultPrefixLength, xEndPoint[ 0 ].ipv6_defaults.uxPrefixLength );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultGatewayAddress_IPv6, xEndPoint[ 0 ].ipv6_defaults.xGatewayAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultDNSServerAddress_IPv6, xEndPoint[ 0 ].ipv6_defaults.xDNSServerAddresses[ 0 ].ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint[ 0 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xEndPoint[ 0 ].bits.bIPv6 );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                &xEndPoint[ 1 ],
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );

    TEST_ASSERT_EQUAL( &xEndPoint[ 1 ], pxNetworkEndPoints->pxNext );
    TEST_ASSERT_EQUAL( &xEndPoint[ 1 ], xInterfaces.pxEndPoint->pxNext );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultGatewayAddress_IPv6, xEndPoint[ 1 ].ipv6_defaults.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultNetPrefix_IPv6, xEndPoint[ 1 ].ipv6_defaults.xPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( xDefaultPrefixLength, xEndPoint[ 1 ].ipv6_defaults.uxPrefixLength );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultGatewayAddress_IPv6, xEndPoint[ 1 ].ipv6_defaults.xGatewayAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultDNSServerAddress_IPv6, xEndPoint[ 1 ].ipv6_defaults.xDNSServerAddresses[ 0 ].ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint[ 1 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xEndPoint[ 1 ].bits.bIPv6 );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                &xEndPoint[ 2 ],
                                &xDefaultDNSServerAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );

    TEST_ASSERT_EQUAL( &xEndPoint[ 2 ], pxNetworkEndPoints->pxNext->pxNext );
    TEST_ASSERT_EQUAL( &xEndPoint[ 2 ], xInterfaces.pxEndPoint->pxNext->pxNext );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultDNSServerAddress_IPv6, xEndPoint[ 2 ].ipv6_defaults.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultNetPrefix_IPv6, xEndPoint[ 2 ].ipv6_defaults.xPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( xDefaultPrefixLength, xEndPoint[ 2 ].ipv6_defaults.uxPrefixLength );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultGatewayAddress_IPv6, xEndPoint[ 2 ].ipv6_defaults.xGatewayAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultDNSServerAddress_IPv6, xEndPoint[ 2 ].ipv6_defaults.xDNSServerAddresses[ 0 ].ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint[ 2 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xEndPoint[ 2 ].bits.bIPv6 );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_FillEndPoint_IPv6 when all input parameters
 * are valid IPv6 default setting.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FillEndPoint_IPv6 to fill IP address, netmask, gateway address,
 *    DNS server address, and MAC address into endpoint.
 *  - Check if pxNetworkEndPoints is same as input endpoint.
 *  - Check if all setting are correctly stored in endpoint.
 *  - Call FreeRTOS_FillEndPoint_IPv6 to fill with same endpoint.
 *  - Check if endpoint is not attached.
 */
void test_FreeRTOS_FillEndPoint_IPv6_SameEndpoint( void )
{
    NetworkInterface_t xInterfaces;
    NetworkEndPoint_t xEndPoint;

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                &xEndPoint,
                                &xDefaultIPAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );

    TEST_ASSERT_EQUAL( &xEndPoint, pxNetworkEndPoints );
    TEST_ASSERT_EQUAL( &xEndPoint, xInterfaces.pxEndPoint );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultIPAddress_IPv6, xEndPoint.ipv6_defaults.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultNetPrefix_IPv6, xEndPoint.ipv6_defaults.xPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL( xDefaultPrefixLength, xEndPoint.ipv6_defaults.uxPrefixLength );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultGatewayAddress_IPv6, xEndPoint.ipv6_defaults.xGatewayAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( &xDefaultDNSServerAddress_IPv6, xEndPoint.ipv6_defaults.xDNSServerAddresses[ 0 ].ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, ipMAC_ADDRESS_LENGTH_BYTES );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, xEndPoint.bits.bIPv6 );

    FreeRTOS_FillEndPoint_IPv6( &xInterfaces,
                                &xEndPoint,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultNetPrefix_IPv6,
                                xDefaultPrefixLength,
                                &xDefaultGatewayAddress_IPv6,
                                &xDefaultDNSServerAddress_IPv6,
                                ucDefaultMACAddress_IPv6 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxNetworkEndPoints );
    TEST_ASSERT_EQUAL( NULL, pxNetworkEndPoints->pxNext );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_AddNetworkInterface when input parameter
 * is not NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_AddNetworkInterface with one valid network interface.
 *  - Check if the input network interface is stored into pxNetworkInterfaces.
 */
void test_FreeRTOS_AddNetworkInterface_HappyPath( void )
{
    NetworkInterface_t xNetworkInterface;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );

    ( void ) FreeRTOS_AddNetworkInterface( &xNetworkInterface );

    TEST_ASSERT_EQUAL( &xNetworkInterface, pxNetworkInterfaces );
    TEST_ASSERT_EQUAL( NULL, pxNetworkInterfaces->pxNext );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_AddNetworkInterface three times with
 * different valid input parameters.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_AddNetworkInterface three times with three different network interfaces.
 *  - Check if all input network interfaces are stored into pxNetworkInterfaces.
 */
void test_FreeRTOS_AddNetworkInterface_ThreeInARow( void )
{
    NetworkInterface_t xNetworkInterface[ 3 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    int i = 0;

    for( i = 0; i < 3; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );

        ( void ) FreeRTOS_AddNetworkInterface( &( xNetworkInterface[ i ] ) );
    }

    pxNetworkInterface = pxNetworkInterfaces;

    for( i = 0; i < 3; i++ )
    {
        TEST_ASSERT_EQUAL( &( xNetworkInterface[ i ] ), pxNetworkInterface );
        pxNetworkInterface = pxNetworkInterface->pxNext;
    }

    TEST_ASSERT_EQUAL( NULL, pxNetworkInterface );
}

/**
 * @brief The purpose of this test is to verify FreeRTOS_AddNetworkInterface when input parameter
 * is NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_AddNetworkInterface with input NULL.
 *  - Check if pxNetworkInterfaces is still NULL.
 */
void test_FreeRTOS_AddNetworkInterface_Null( void )
{
    ( void ) FreeRTOS_AddNetworkInterface( NULL );
    TEST_ASSERT_EQUAL( NULL, pxNetworkInterfaces );
}

/**
 * @brief FreeRTOS_AddNetworkInterface should only add same interface once into
 * the pxNetworkInterfaces.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_AddNetworkInterface with same input twice.
 *  - Check if pxNetworkInterfaces is same as input.
 *  - Check if pxNetworkInterfaces->pxNext is NULL.
 */
void test_FreeRTOS_AddNetworkInterface_DuplicateInterface( void )
{
    NetworkInterface_t xNetworkInterface;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );

    ( void ) FreeRTOS_AddNetworkInterface( &xNetworkInterface );
    ( void ) FreeRTOS_AddNetworkInterface( &xNetworkInterface );

    TEST_ASSERT_EQUAL( &xNetworkInterface, pxNetworkInterfaces );
    TEST_ASSERT_EQUAL( NULL, pxNetworkInterfaces->pxNext );
}

/**
 * @brief FreeRTOS_FirstNetworkInterface should be able to find the first network interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Assign a network interface into pxNetworkInterfaces.
 *  - Call FreeRTOS_FirstNetworkInterface to get first network interface.
 *  - Check if the return is same as the input.
 */
void test_FreeRTOS_FirstNetworkInterface_HappyPath( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    pxNetworkInterface = FreeRTOS_FirstNetworkInterface();

    TEST_ASSERT_EQUAL( &xNetworkInterface, pxNetworkInterface );
}

/**
 * @brief FreeRTOS_FirstNetworkInterface should be able to return NULL if there is no network interface available.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_FirstNetworkInterface to get first network interface.
 *  - Check if the return is NULL.
 */
void test_FreeRTOS_FirstNetworkInterface_Null( void )
{
    NetworkInterface_t * pxNetworkInterface = NULL;

    pxNetworkInterface = FreeRTOS_FirstNetworkInterface();

    TEST_ASSERT_EQUAL( NULL, pxNetworkInterface );
}

/**
 * @brief FreeRTOS_NextNetworkInterface returns next network interface correctly.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Create 3 network interfaces and attach them into pxNetworkInterfaces.
 *  - Check if pxNetworkInterfaces is same as first input.
 *  - Check if we can query next two network interfaces correctly by calling FreeRTOS_NextNetworkInterface.
 */
void test_FreeRTOS_NextNetworkInterface_HappyPath( void )
{
    NetworkInterface_t xNetworkInterface[ 3 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    int i = 0;

    for( i = 0; i < 3; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );

        if( pxNetworkInterfaces == NULL )
        {
            pxNetworkInterfaces = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterfaces;
        }
        else
        {
            pxNetworkInterface->pxNext = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterface->pxNext;
        }
    }

    pxNetworkInterface = pxNetworkInterfaces;

    for( i = 0; i < 3; i++ )
    {
        TEST_ASSERT_EQUAL( &( xNetworkInterface[ i ] ), pxNetworkInterface );
        pxNetworkInterface = FreeRTOS_NextNetworkInterface( pxNetworkInterface );
    }

    TEST_ASSERT_EQUAL( NULL, pxNetworkInterface );
}

/**
 * @brief FreeRTOS_NextNetworkInterface returns NULL if the input is NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_NextNetworkInterface with NULL input.
 *  - Check if return is NULL.
 */
void test_FreeRTOS_NextNetworkInterface_Null( void )
{
    NetworkInterface_t * pxNetworkInterface = NULL;

    pxNetworkInterface = FreeRTOS_NextNetworkInterface( NULL );

    TEST_ASSERT_EQUAL( NULL, pxNetworkInterface );
}

/**
 * @brief FreeRTOS_FirstEndPoint should return endpoint attached on the input network interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Set a network interface into pxNetworkInterfaces.
 *  - Attach an endpoint to the network interface.
 *  - Call FreeRTOS_FirstEndPoint to get attached endpoint.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_HappyPath( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    xEndPoint.pxNetworkInterface = pxNetworkInterfaces;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FirstEndPoint( pxNetworkInterfaces );

    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FirstEndPoint should return first endpoint in the list if input is NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Set a network interface into pxNetworkInterfaces.
 *  - Attach an endpoint to the network interface.
 *  - Call FreeRTOS_FirstEndPoint to get attached endpoint with NULL input.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_Null( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    xEndPoint.pxNetworkInterface = pxNetworkInterfaces;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FirstEndPoint( NULL );

    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FirstEndPoint should return NULL if no endpoint available in the list.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Set a network interface into pxNetworkInterfaces.
 *  - Attach an endpoint to the network interface.
 *  - Call FreeRTOS_FirstEndPoint to get attached endpoint with NULL input.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_NoEndpoints( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    xEndPoint.pxNetworkInterface = pxNetworkInterfaces;

    pxEndPoint = FreeRTOS_FirstEndPoint( &xNetworkInterface );

    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FirstEndPoint should return first endpoint with specified interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 3 network interfaces and 3 endpoints.
 *  - Attach one endpoint each network interface.
 *  - Put interfaces & endpoints into the list.
 *  - Loop to call FreeRTOS_FirstEndPoint to get attached endpoint with each network interface.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_AnotherInterface( void )
{
    /* Attach one endpoint to one network interface. Check if we can get correct endpoint by API. */
    NetworkInterface_t xNetworkInterface[ 3 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint[ 3 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    int i = 0;

    for( i = 0; i < 3; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );
        memset( &( xEndPoint[ i ] ), 0, sizeof( NetworkEndPoint_t ) );

        if( pxNetworkInterfaces == NULL )
        {
            pxNetworkInterfaces = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterfaces;

            pxNetworkEndPoints = &( xEndPoint[ i ] );
            pxEndPoint = pxNetworkEndPoints;
        }
        else
        {
            pxNetworkInterface->pxNext = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterface->pxNext;

            pxEndPoint->pxNext = &( xEndPoint[ i ] );
            pxEndPoint = pxEndPoint->pxNext;
        }

        xEndPoint[ i ].pxNetworkInterface = pxNetworkInterface;
    }

    for( i = 0; i < 3; i++ )
    {
        pxEndPoint = FreeRTOS_FirstEndPoint( &( xNetworkInterface[ i ] ) );
        TEST_ASSERT_EQUAL( &( xEndPoint[ i ] ), pxEndPoint );
    }
}

/**
 * @brief FreeRTOS_FirstEndPoint_IPv6 should return an IPv6 endpoint attached on the input network interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Set a network interface into pxNetworkInterfaces.
 *  - Attach an endpoint to the network interface.
 *     - Set IPv6 bit in endpoint.
 *  - Call FreeRTOS_FirstEndPoint to get attached endpoint.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_IPv6_HappyPath( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.pxNetworkInterface = pxNetworkInterfaces;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FirstEndPoint_IPv6( pxNetworkInterfaces );

    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FirstEndPoint_IPv6 should return first endpoint in the list if input is NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Set a network interface into pxNetworkInterfaces.
 *  - Attach an endpoint to the network interface.
 *     - Set IPv6 bit in endpoint.
 *  - Call FreeRTOS_FirstEndPoint_IPv6 to get attached endpoint with NULL input.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_IPv6_Null( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.pxNetworkInterface = pxNetworkInterfaces;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FirstEndPoint_IPv6( NULL );

    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FirstEndPoint_IPv6 should return NULL if no IPv6 endpoint in the list.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Set a network interface into pxNetworkInterfaces.
 *  - Attach an IPv4 endpoint to the network interface.
 *  - Call FreeRTOS_FirstEndPoint_IPv6 to get attached endpoint with NULL input.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_IPv6_NotFound( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.pxNetworkInterface = pxNetworkInterfaces;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FirstEndPoint_IPv6( &xNetworkInterface );

    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FirstEndPoint_IPv6 should return first endpoint with specified interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 3 network interfaces and 6 endpoints (e0~e5).
 *  - Attach 2 endpoints each network interface.
 *     - One endpoint with IPv6 bit set.
 *     - The other endpoint with IPv6 bit clear.
 *     - The other endpoint with IPv6 bit clear.
 *       - Network interface 0: endpoint e0(IPv4)/e3(IPv6)
 *       - Network interface 1: endpoint e1(IPv4)/e4(IPv6)
 *       - Network interface 2: endpoint e2(IPv4)/e5(IPv6)
 *  - Put interfaces & endpoints into the list.
 *  - Loop to call FreeRTOS_FirstEndPoint_IPv6 to get attached IPv6 endpoint with each network interface.
 *  - Check if returned endpoint is same as attached one.
 */
void test_FreeRTOS_FirstEndPoint_IPv6_AnotherInterface( void )
{
    /* Attach one endpoint to one network interface. Check if we can get correct endpoint by API. */
    NetworkInterface_t xNetworkInterface[ 3 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint[ 6 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    int i = 0;

    for( i = 0; i < 3; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );

        if( pxNetworkInterfaces == NULL )
        {
            pxNetworkInterfaces = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterfaces;
        }
        else
        {
            pxNetworkInterface->pxNext = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterface->pxNext;
        }
    }

    for( i = 0; i < 6; i++ )
    {
        bool bShouldBeIPv6 = i >= 3 ? true : false;
        memset( &( xEndPoint[ i ] ), 0, sizeof( NetworkEndPoint_t ) );

        if( pxNetworkEndPoints == NULL )
        {
            pxNetworkEndPoints = &( xEndPoint[ i ] );
            pxEndPoint = pxNetworkEndPoints;
        }
        else
        {
            pxEndPoint->pxNext = &( xEndPoint[ i ] );
            pxEndPoint = pxEndPoint->pxNext;
        }

        if( bShouldBeIPv6 )
        {
            xEndPoint[ i ].pxNetworkInterface = &( xNetworkInterface[ i - 3 ] );
            xEndPoint[ i ].bits.bIPv6 = pdTRUE;
        }
        else
        {
            xEndPoint[ i ].pxNetworkInterface = &( xNetworkInterface[ i ] );
            xEndPoint[ i ].bits.bIPv6 = pdFALSE;
        }
    }

    for( i = 0; i < 3; i++ )
    {
        pxEndPoint = FreeRTOS_FirstEndPoint_IPv6( &( xNetworkInterface[ i ] ) );
        TEST_ASSERT_EQUAL( &( xEndPoint[ i + 3 ] ), pxEndPoint );
    }
}

/**
 * @brief FreeRTOS_NextEndPoint should return next endpoint with specified endpoint.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 3 endpoints and stored then into pxNetworkEndPoints.
 *  - Loop to call FreeRTOS_NextEndPoint to get endpoints.
 *  - Check if endpoints are returned in correct order.
 */
void test_FreeRTOS_NextEndPoint_HappyPath( void )
{
    NetworkEndPoint_t xEndPoint[ 3 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    int i = 0;

    for( i = 0; i < 3; i++ )
    {
        memset( &( xEndPoint[ i ] ), 0, sizeof( NetworkEndPoint_t ) );

        if( pxNetworkEndPoints == NULL )
        {
            pxNetworkEndPoints = &( xEndPoint[ i ] );
            pxEndPoint = pxNetworkEndPoints;
        }
        else
        {
            pxEndPoint->pxNext = &( xEndPoint[ i ] );
            pxEndPoint = pxEndPoint->pxNext;
        }
    }

    pxEndPoint = pxNetworkEndPoints;

    for( i = 0; i < 3; i++ )
    {
        TEST_ASSERT_EQUAL( &( xEndPoint[ i ] ), pxEndPoint );
        pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint );
    }

    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_NextEndPoint should return next endpoint with specified interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 3 interfaces and 9 endpoints (e0~e8).
 *  - Put interfaces & endpoints into the list.
 *     - Attach 3 endpoints into each network interface
 *       - Network interface 0: endpoint e0/e1/e2
 *       - Network interface 1: endpoint e3/e4/e5
 *       - Network interface 2: endpoint e6/e7/e8
 *     - Stored endpoints in below order.
 *       - e0,e3,e6,e1,e4,e7,e2,e5,e8
 *  - Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 0.
 *  - Check if returned endpoints are e0 -> e1 -> e2.
 *  - Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 1.
 *  - Check if returned endpoints are e3 -> e4 -> e5.
 *  - Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 2.
 *  - Check if returned endpoints are e6 -> e7 -> e8.
 */
void test_FreeRTOS_NextEndPoint_AnotherInterface( void )
{
    NetworkInterface_t xNetworkInterface[ 3 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    NetworkEndPoint_t xEndPoint[ 9 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    int i = 0;
    const int specifiedEndpointOrder[ 9 ][ 2 ] = \
        /* {network_interface_index, endpoint_index} */
    {
        { 0, 0 },
        { 1, 3 },
        { 2, 6 },
        { 0, 1 },
        { 1, 4 },
        { 2, 7 },
        { 0, 2 },
        { 1, 5 },
        { 2, 8 }
    };

    /* Initialize network interface list. */
    for( i = 0; i < 3; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );

        if( pxNetworkInterfaces == NULL )
        {
            pxNetworkInterfaces = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterfaces;
        }
        else
        {
            pxNetworkInterface->pxNext = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterface->pxNext;
        }
    }

    /* Initialize endpoint list. */
    for( i = 0; i < 9; i++ )
    {
        memset( &( xEndPoint[ specifiedEndpointOrder[ i ][ 1 ] ] ), 0, sizeof( NetworkEndPoint_t ) );

        if( pxNetworkEndPoints == NULL )
        {
            pxNetworkEndPoints = &( xEndPoint[ specifiedEndpointOrder[ i ][ 1 ] ] );
            pxEndPoint = pxNetworkEndPoints;
        }
        else
        {
            pxEndPoint->pxNext = &( xEndPoint[ specifiedEndpointOrder[ i ][ 1 ] ] );
            pxEndPoint = pxEndPoint->pxNext;
        }

        pxEndPoint->pxNetworkInterface = &( xNetworkInterface[ specifiedEndpointOrder[ i ][ 0 ] ] );
    }

    /* Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 0. */
    /* Check if returned endpoints are e0 -> e1 -> e2. */
    pxEndPoint = NULL;
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 0 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 0 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 0 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 1 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 0 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 2 ] ), pxEndPoint );

    /* Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 1. */
    /* Check if returned endpoints are e3 -> e4 -> e5. */
    pxEndPoint = NULL;
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 1 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 3 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 1 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 4 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 1 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 5 ] ), pxEndPoint );

    /* Loop to call FreeRTOS_NextEndPoint to get endpoints for interface 2. */
    /* Check if returned endpoints are e6 -> e7 -> e8. */
    pxEndPoint = NULL;
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 2 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 6 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 2 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 7 ] ), pxEndPoint );
    pxEndPoint = FreeRTOS_NextEndPoint( &( xNetworkInterface[ 2 ] ), pxEndPoint );
    TEST_ASSERT_EQUAL( &( xEndPoint[ 8 ] ), pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnIP_IPv4 should return the endpoint with specified IPv4 address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query with same IP address stored in endpoint.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv4_HappyPath( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;

    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( IPV4_DEFAULT_ADDRESS, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnIP_IPv4 should return NULL if no matched endpoint found.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 2 endpoints (e0, e1) and add them to the list.
 *     - Set e0 IP address to 192.168.123.223 (IPV4_DEFAULT_ADDRESS).
 *     - Set e1 IP address to 2001::1 (xDefaultIPAddress_IPv6).
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query different IP address.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv4_NotFound( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint32_t ulWhere;

    /* Initialize e0. */
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 0 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    /* Initialize e1. */
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint[ 1 ].ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint[ 1 ].bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    /* Set ulWhere to boundary of array size to toggle corner case. */
    ulWhere = sizeof( xRoutingStatistics.ulLocationsIP ) / sizeof( xRoutingStatistics.ulLocationsIP[ 0 ] );
    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( IPV4_DEFAULT_GATEWAY, ulWhere );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnIP_IPv4 should return the endpoint with specified IPv4 address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 2 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query with xDefaultIPAddress_IPv4 address stored in endpoint.
 *  - Check if returned endpoint is same.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query with xDefaultGatewayAddress_IPv4 address stored in endpoint.
 *  - Check if returned endpoint is same.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query with xDefaultDNSServerAddress_IPv4 address stored in endpoint.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv4_MultipleEndpoints( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 0 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 1 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_GATEWAY;
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( IPV4_DEFAULT_ADDRESS, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint[ 0 ], pxEndPoint );

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( IPV4_DEFAULT_GATEWAY, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint[ 1 ], pxEndPoint );

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( IPV4_DEFAULT_DNS_SERVER, 0 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnIP_IPv4 should return first endpoint in the list when query IP address is 0.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 2 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query with 0 address.
 *  - Check if returned endpoint is the first endpoint.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv4_AnyEndpoint( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 0 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 1 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_GATEWAY;
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( 0, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint[ 0 ], pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnIP_IPv4 should return first endpoint in the list when query IP address is 0.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint with IP address 0 and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query with IPV4_DEFAULT_ADDRESS.
 *  - Check if returned endpoint is same.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query with IPV4_DEFAULT_GATEWAY.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv4_ZeroAddressEndpoint( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = 0;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( IPV4_DEFAULT_ADDRESS, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( IPV4_DEFAULT_GATEWAY, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnIP_IPv6 should return the endpoint with specified IPv6 address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv6 to query with same IP address stored in endpoint.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv6_HappyPath( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    pxNetworkEndPoints = &xEndPoint;

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint.ipv6_settings.xIPAddress ), &xDefaultIPAddress_IPv6, xEndPoint.ipv6_settings.uxPrefixLength, 0 );

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( &xDefaultIPAddress_IPv6 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnIP_IPv6 should return the endpoint with specified IPv6 address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 2 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv6 to query with xDefaultIPAddress_IPv6 address stored in endpoint.
 *  - Check if returned endpoint is same.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv6 to query with xDefaultGatewayAddress_IPv6 address stored in endpoint.
 *  - Check if returned endpoint is same.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv6 to query with xDefaultDNSServerAddress_IPv6 address stored in endpoint.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv6_MultipleEndpoints( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint[ 0 ].ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint[ 0 ].bits.bIPv6 = pdTRUE;
    xEndPoint[ 0 ].ipv6_settings.uxPrefixLength = 64;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint[ 1 ].ipv6_settings.xIPAddress.ucBytes, &xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint[ 1 ].bits.bIPv6 = pdTRUE;
    xEndPoint[ 1 ].ipv6_settings.uxPrefixLength = 64;
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint[ 0 ].ipv6_settings.xIPAddress ), &xDefaultIPAddress_IPv6, xEndPoint[ 0 ].ipv6_settings.uxPrefixLength, 0 );
    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( &xDefaultIPAddress_IPv6 );
    TEST_ASSERT_EQUAL( &xEndPoint[ 0 ], pxEndPoint );

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint[ 0 ].ipv6_settings.xIPAddress ), &xDefaultGatewayAddress_IPv6, xEndPoint[ 0 ].ipv6_settings.uxPrefixLength, 1 );
    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint[ 1 ].ipv6_settings.xIPAddress ), &xDefaultGatewayAddress_IPv6, xEndPoint[ 1 ].ipv6_settings.uxPrefixLength, 0 );
    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( &xDefaultGatewayAddress_IPv6 );
    TEST_ASSERT_EQUAL( &xEndPoint[ 1 ], pxEndPoint );

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint[ 0 ].ipv6_settings.xIPAddress ), &xDefaultDNSServerAddress_IPv6, xEndPoint[ 0 ].ipv6_settings.uxPrefixLength, 1 );
    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint[ 1 ].ipv6_settings.xIPAddress ), &xDefaultDNSServerAddress_IPv6, xEndPoint[ 1 ].ipv6_settings.uxPrefixLength, 1 );
    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( &xDefaultDNSServerAddress_IPv6 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnIP_IPv6 should return NULL if no matched endpoint found.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 2 endpoint and add it to the list.
 *     - 1 IPv4 endpoint.
 *     - 1 IPv6 endpoint, with xDefaultIPAddress_IPv6 address.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv6 to query with xDefaultIPAddress_IPv6.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv6_NotFound( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 0 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint[ 1 ].ipv6_settings.xIPAddress.ucBytes, &xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint[ 1 ].bits.bIPv6 = pdTRUE;
    xEndPoint[ 1 ].ipv6_settings.uxPrefixLength = 64;
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint[ 1 ].ipv6_settings.xIPAddress ), &xDefaultGatewayAddress_IPv6, xEndPoint[ 1 ].ipv6_settings.uxPrefixLength, 1 );

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( &xDefaultGatewayAddress_IPv6 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnMAC should return the endpoint with specified MAC address & network interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 network interface and add it to the list.
 *  - Create 1 endpoint, attach to the interface, and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnMAC to query with same MAC address stored in endpoint.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnMAC_HappyPath( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    /* MAC address:  */
    const MACAddress_t xMACAddress = { 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc };
    NetworkInterface_t xNetworkInterface;

    /* Initialize network interface and add it to the list. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnMAC( &xMACAddress, &xNetworkInterface );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnMAC should return the endpoint with specified MAC address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnMAC to query with same MAC address stored in endpoint.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnMAC_NullInterface( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    /* MAC address:  */
    const MACAddress_t xMACAddress = { 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc };

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnMAC( &xMACAddress, NULL );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnMAC should return the endpoint with NULL pointer as MAC address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnMAC to query with NULL pointer as MAC address.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnMAC_NullMAC( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    /* MAC address:  */
    const MACAddress_t xMACAddress = { 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc };

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnMAC( NULL, NULL );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnMAC should return the endpoint attached to the specified interface.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 2 interfaces and add them to the list.
 *  - Create 2 endpoints with same MAC address, attach to each interface, and add them to the list.
 *  - Call FreeRTOS_FindEndPointOnMAC to query attached in first interface.
 *  - Check if returned endpoint is same as first endpoint.
 *  - Call FreeRTOS_FindEndPointOnMAC to query attached in second interface.
 *  - Check if returned endpoint is same as second endpoint.
 */
void test_FreeRTOS_FindEndPointOnMAC_MultipleInterface( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    NetworkInterface_t xNetworkInterface[ 2 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    /* MAC address:  */
    const MACAddress_t xMACAddress = { 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc };
    int i = 0;

    /* Initialize network interfaces and add them to the list. */
    for( i = 0; i < 2; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );

        if( pxNetworkInterfaces == NULL )
        {
            pxNetworkInterfaces = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterfaces;
        }
        else
        {
            pxNetworkInterface->pxNext = &( xNetworkInterface[ i ] );
            pxNetworkInterface = pxNetworkInterface->pxNext;
        }
    }

    /* Initialize network endpoints and add them to the list. */
    for( i = 0; i < 2; i++ )
    {
        memset( &( xEndPoint[ i ] ), 0, sizeof( NetworkEndPoint_t ) );

        if( pxNetworkEndPoints == NULL )
        {
            pxNetworkEndPoints = &( xEndPoint[ i ] );
            pxEndPoint = pxNetworkEndPoints;
        }
        else
        {
            pxEndPoint->pxNext = &( xEndPoint[ i ] );
            pxEndPoint = pxEndPoint->pxNext;
        }

        pxEndPoint->pxNetworkInterface = &xNetworkInterface[ i ];
        memcpy( pxEndPoint->xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    }

    /* Check if we can get correct endpoint by specified network interface. */
    for( i = 0; i < 2; i++ )
    {
        pxEndPoint = FreeRTOS_FindEndPointOnMAC( &xMACAddress, &xNetworkInterface[ i ] );
        TEST_ASSERT_EQUAL( &( xEndPoint[ i ] ), pxEndPoint );
    }
}

/**
 * @brief FreeRTOS_FindEndPointOnMAC should return NULL if no endpoint matches.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 network interface and add it to the list.
 *  - Create 1 endpoint, attach to the interface, and add it to the list.
 *     - Use ucDefaultMACAddress_IPv4 as MAC address.
 *  - Call FreeRTOS_FindEndPointOnMAC to query with different MAC address.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnMAC_NotFound( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    /* MAC address:  */
    const MACAddress_t xMACAddress = { 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc };
    NetworkInterface_t xNetworkInterface;
    MACAddress_t * pxQueryMACAddress = NULL;

    /* Initialize network interface and add it to the list. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    pxQueryMACAddress = ( MACAddress_t * ) ( &ucDefaultMACAddress_IPv4 );
    pxEndPoint = FreeRTOS_FindEndPointOnMAC( pxQueryMACAddress, &xNetworkInterface );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnNetMask should be able to find the endpoint within same network region.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *     - Set the IP address to 192.168.123.223.
 *     - Set the netmask to 255.255.255.0.
 *  - Call FreeRTOS_FindEndPointOnNetMask to query for IP address 192.168.123.1.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnNetMask_HappyPath( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    xEndPoint.ipv4_settings.ulNetMask = IPV4_DEFAULT_NETMASK;
    pxNetworkEndPoints = &xEndPoint;

    /* IPV4_DEFAULT_DNS_SERVER is 192.168.123.1 within the network region. */
    pxEndPoint = FreeRTOS_FindEndPointOnNetMask( IPV4_DEFAULT_DNS_SERVER, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnNetMask should be able to return NULL if no endpoint is in same network region.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *     - Set the netmask to 255.255.255.0.
 *     - Set the IP address to 192.168.123.223.
 *  - Call FreeRTOS_FindEndPointOnNetMask to query for IP address 192.168.1.1.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnNetMask_NotFound( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    xEndPoint.ipv4_settings.ulNetMask = IPV4_DEFAULT_NETMASK;
    pxNetworkEndPoints = &xEndPoint;

    /* 192.168.1.1 is 0x0101A8C0. */
    pxEndPoint = FreeRTOS_FindEndPointOnNetMask( 0x0101A8C0, 0 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnNetMask_IPv6 should be able to find the endpoint within same network region.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *     - Set the IP address to 2001::1.
 *     - Set the prefix address to 2001::.
 *     - Set the prefix length to 64.
 *  - Call FreeRTOS_FindEndPointOnNetMask to query for IP address 2001::fffe.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnNetMask_IPv6_HappyPath( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = xDefaultPrefixLength;
    xEndPoint.bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints = &xEndPoint;

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint.ipv6_settings.xIPAddress ), &xDefaultGatewayAddress_IPv6, xDefaultPrefixLength, 0 );

    /* xDefaultGatewayAddress_IPv6 is 2001::fffe within the network region. */
    pxEndPoint = FreeRTOS_FindEndPointOnNetMask_IPv6( &xDefaultGatewayAddress_IPv6 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnNetMask_IPv6 should be able to return NULL if no endpoint is in same network region.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 2 endpoint (e0, e1) and add it to the list.
 *     - Set e0 IP address to 2001::1.
 *     - Set e0 prefix address to 2001::.
 *     - Set e0 prefix length to 64.
 *     - Set e1 IP address to 192.168.124.223.
 *     - Set e1 netmask to 255.255.255.0.
 *  - Call FreeRTOS_FindEndPointOnNetMask to query for IP address 2002::fffe.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnNetMask_IPv6_NotFound( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    const IPv6_Address_t xTargetAddress = { 0x20, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xfe };

    /* Initialize e0. */
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint[ 0 ].ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint[ 0 ].ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint[ 0 ].ipv6_settings.uxPrefixLength = xDefaultPrefixLength;
    xEndPoint[ 0 ].bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    /* Initialize e1. */
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 1 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    xEndPoint[ 1 ].ipv4_settings.ulNetMask = IPV4_DEFAULT_NETMASK;
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint[ 0 ].ipv6_settings.xIPAddress ), &xTargetAddress, xDefaultPrefixLength, 1 );

    pxEndPoint = FreeRTOS_FindEndPointOnNetMask_IPv6( &xTargetAddress );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_InterfaceEndPointOnNetMask should be able to find the endpoint within same network region.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *     - Set the IP address to 192.168.123.223 (IPV4_DEFAULT_ADDRESS).
 *     - Set the netmask to 255.255.255.0.
 *  - Call FreeRTOS_InterfaceEndPointOnNetMask to query for IP address 192.168.123.1.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_InterfaceEndPointOnNetMask_HappyPath( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    NetworkInterface_t xNetworkInterface;
    uint32_t ulWhere;

    /* Initialize network interface and add it to the list. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    xEndPoint.ipv4_settings.ulNetMask = IPV4_DEFAULT_NETMASK;
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Set ulWhere to boundary of array size to toggle corner case. */
    ulWhere = sizeof( xRoutingStatistics.ulLocations ) / sizeof( xRoutingStatistics.ulLocations[ 0 ] );
    /* IPV4_DEFAULT_ADDRESS is 192.168.123.1 within the network region. */
    pxEndPoint = FreeRTOS_InterfaceEndPointOnNetMask( &xNetworkInterface, IPV4_DEFAULT_DNS_SERVER, ulWhere );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_InterfaceEndPointOnNetMask should be able to find the endpoint within same network region.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 2 network interfaces and add them to the list.
 *  - Create 2 endpoints (e0, e1).
 *     - Set e0 IP address to 192.168.123.223 (IPV4_DEFAULT_ADDRESS).
 *     - Set e0 netmask to 255.255.255.0.
 *     - Attach e0 to first interface.
 *     - Set e1 IP address to 192.168.124.223.
 *     - Set e1 netmask to 255.255.255.0.
 *     - Attach e0 to second interface.
 *  - Call FreeRTOS_InterfaceEndPointOnNetMask to query for IP address 192.168.124.1.
 *  - Check if returned endpoint is e1.
 */
void test_FreeRTOS_InterfaceEndPointOnNetMask_DifferentInterface( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    NetworkInterface_t xNetworkInterface[ 2 ];
    uint32_t ulWhere;
    /* 192.168.124.223 is 0xDF7CA8C0. */
    uint32_t ulE1IPAddress = 0xDF7CA8C0;
    /* 192.168.124.1 is 0x017CA8C0. */
    uint32_t ulQueryIPAddress = 0x017CA8C0;

    /* Create 2 network interfaces and add them to the list. */
    memset( &xNetworkInterface[ 0 ], 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface[ 0 ];
    memset( &xNetworkInterface[ 1 ], 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces->pxNext = &xNetworkInterface[ 1 ];

    /* Initialize e0. */
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 0 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    xEndPoint[ 0 ].ipv4_settings.ulNetMask = IPV4_DEFAULT_NETMASK;
    xEndPoint[ 0 ].pxNetworkInterface = &xNetworkInterface[ 0 ];
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    /* Initialize e1. */
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 1 ].ipv4_settings.ulIPAddress = ulE1IPAddress;
    xEndPoint[ 1 ].ipv4_settings.ulNetMask = IPV4_DEFAULT_NETMASK;
    xEndPoint[ 1 ].pxNetworkInterface = &xNetworkInterface[ 1 ];
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    /* Set ulWhere to boundary of array size to toggle corner case. */
    ulWhere = sizeof( xRoutingStatistics.ulLocations ) / sizeof( xRoutingStatistics.ulLocations[ 0 ] );
    /* IPV4_DEFAULT_ADDRESS is 192.168.123.1 within the network region. */
    pxEndPoint = FreeRTOS_InterfaceEndPointOnNetMask( &xNetworkInterface[ 1 ], ulQueryIPAddress, ulWhere );
    TEST_ASSERT_EQUAL( &xEndPoint[ 1 ], pxEndPoint );
}

/**
 * @brief FreeRTOS_InterfaceEndPointOnNetMask returns NULL when there is no endpoint matches.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv6 endpoint and add it to the list.
 *     - Set the IP address to 2001::1.
 *     - Set the prefix address to 2001::.
 *     - Set the prefix length to 64.
 *  - Call FreeRTOS_InterfaceEndPointOnNetMask to query for IP address 192.168.123.1.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_InterfaceEndPointOnNetMask_NotFound( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    NetworkInterface_t xNetworkInterface;

    /* Initialize network interface and add it to the list. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = xDefaultPrefixLength;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* IPV4_DEFAULT_ADDRESS is 192.168.123.1 within the network region. */
    pxEndPoint = FreeRTOS_InterfaceEndPointOnNetMask( &xNetworkInterface, IPV4_DEFAULT_DNS_SERVER, 0 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_InterfaceEndPointOnNetMask returns first IPv4 endpoint when querying with IP address 0xFFFFFFFF.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 2 endpoint (e0, e1) and add them to the list.
 *     - Set e0 IP address to 2001::1 (xDefaultIPAddress_IPv6).
 *     - Set e0 prefix address to 2001::.
 *     - Set e0 prefix length to 64.
 *     - Set e1 IP address to 192.168.123.223 (IPV4_DEFAULT_ADDRESS).
 *     - Set e1 netmask to 255.255.255.0.
 *  - Call FreeRTOS_InterfaceEndPointOnNetMask to query for IP address 0xFFFFFFFF.
 *  - Check if returned endpoint is e1.
 */
void test_FreeRTOS_InterfaceEndPointOnNetMask_Broadcast( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    NetworkInterface_t xNetworkInterface;

    /* Initialize network interface and add it to the list. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize e0. */
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint[ 0 ].ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint[ 0 ].ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint[ 0 ].ipv6_settings.uxPrefixLength = xDefaultPrefixLength;
    xEndPoint[ 0 ].bits.bIPv6 = pdTRUE;
    xEndPoint[ 0 ].pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    /* Initialize e1. */
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 1 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    xEndPoint[ 1 ].ipv4_settings.ulNetMask = IPV4_DEFAULT_NETMASK;
    xEndPoint[ 1 ].pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    /* IPV4_DEFAULT_ADDRESS is 192.168.123.1 within the network region. */
    pxEndPoint = FreeRTOS_InterfaceEndPointOnNetMask( &xNetworkInterface, 0xFFFFFFFF, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint[ 1 ], pxEndPoint );
}

/**
 * @brief FreeRTOS_FindGateWay should be able to find the endpoint with valid IPv4 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv4 endpoint and add it to the list.
 *     - Set the gateway address to 192.168.123.254 (IPV4_DEFAULT_GATEWAY).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv4.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindGateWay_IPv4_HappyPath( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulGatewayAddress = IPV4_DEFAULT_GATEWAY;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv4 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindGateWay should be able to return NULL if no valid IPv4 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv6 endpoint and add it to the list.
 *     - Set the gateway address to 2001::fffe (xDefaultGatewayAddress_IPv6).
 *  - Create 1 IPv4 endpoint and add it to the list.
 *     - Set the gateway address to 0 (invalid address).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv4.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindGateWay_IPv4_NotFound( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint[ 0 ].ipv6_settings.xGatewayAddress.ucBytes, &xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint[ 0 ].bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv4 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindGateWay should be able to return the endpoint with valid IPv4 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv6 endpoint and add it to the list.
 *     - Set the gateway address to 2001::fffe (xDefaultGatewayAddress_IPv6).
 *  - Create 1 IPv4 endpoint and add it to the list.
 *     - Set the gateway address to 192.168.123.254 (IPV4_DEFAULT_GATEWAY).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv4.
 *  - Check if returned endpoint is same as second endpoint.
 */
void test_FreeRTOS_FindGateWay_IPv4_MultipleEndpoints( void )
{
    NetworkEndPoint_t xEndPointV4;
    NetworkEndPoint_t xEndPointV6;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize IPv6 network endpoint and add it to the list. */
    memset( &xEndPointV6, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPointV6.ipv6_settings.xGatewayAddress.ucBytes, &xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPointV6.bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints = &xEndPointV6;

    /* Initialize IPv4 network endpoint and add it to the list. */
    memset( &xEndPointV4, 0, sizeof( NetworkEndPoint_t ) );
    xEndPointV4.ipv4_settings.ulGatewayAddress = IPV4_DEFAULT_GATEWAY;
    pxNetworkEndPoints->pxNext = &xEndPointV4;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv4 );
    TEST_ASSERT_EQUAL( &xEndPointV4, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindGateWay should be able to find the endpoint with valid IPv6 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv6 endpoint and add it to the list.
 *     - Set the gateway address to 2001::fffe (xDefaultGatewayAddress_IPv6).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv6.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindGateWay_IPv6_HappyPath( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPoint.ipv6_settings.xGatewayAddress.ucBytes, &xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv6 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindGateWay should be able to return NULL if no valid IPv6 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv4 endpoint and add it to the list.
 *     - Set the gateway address to 192.168.123.254 (IPV4_DEFAULT_GATEWAY).
 *  - Create 1 IPv6 endpoint and add it to the list.
 *     - Set the gateway address to :: (invalid address).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv6.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindGateWay_IPv6_NotFound( void )
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 0 ].ipv4_settings.ulGatewayAddress = IPV4_DEFAULT_GATEWAY;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 0 ].bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv6 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindGateWay should be able to return the endpoint with valid IPv6 gateway address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv4 endpoint and add it to the list.
 *     - Set the gateway address to 192.168.123.254 (IPV4_DEFAULT_GATEWAY).
 *  - Create 1 IPv6 endpoint and add it to the list.
 *     - Set the gateway address to 2001::fffe (xDefaultGatewayAddress_IPv6).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv4.
 *  - Check if returned endpoint is same as second endpoint.
 */
void test_FreeRTOS_FindGateWay_IPv6_MultipleEndpoints( void )
{
    NetworkEndPoint_t xEndPointV4;
    NetworkEndPoint_t xEndPointV6;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize IPv4 network endpoint and add it to the list. */
    memset( &xEndPointV4, 0, sizeof( NetworkEndPoint_t ) );
    xEndPointV4.ipv4_settings.ulGatewayAddress = IPV4_DEFAULT_GATEWAY;
    pxNetworkEndPoints = &xEndPointV4;

    /* Initialize IPv6 network endpoint and add it to the list. */
    memset( &xEndPointV6, 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xEndPointV6.ipv6_settings.xGatewayAddress.ucBytes, &xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPointV6.bits.bIPv6 = pdTRUE;
    pxNetworkEndPoints->pxNext = &xEndPointV6;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv6 );
    TEST_ASSERT_EQUAL( &xEndPointV6, pxEndPoint );
}

/**
 * @brief pxGetSocketEndpoint should be able to return the endpoint attached in socket handler.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Create 1 socket handler.
 *     - Attach previous endpoint to socket handler.
 *  - Call pxGetSocketEndpoint with socket handler.
 *  - Check if returned endpoint is same.
 */
void test_pxGetSocketEndpoint_HappyPath()
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    FreeRTOS_Socket_t xSocket;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize socket handler. */
    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );
    xSocket.pxEndPoint = &xEndPoint;

    pxEndPoint = pxGetSocketEndpoint( &xSocket );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief pxGetSocketEndpoint should be able to return NULL if socket handler is also NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call pxGetSocketEndpoint with NULL.
 *  - Check if returned endpoint is NULL.
 */
void test_pxGetSocketEndpoint_Null()
{
    NetworkEndPoint_t * pxEndPoint = NULL;

    pxEndPoint = pxGetSocketEndpoint( NULL );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief vSetSocketEndpoint can set endpoint to socket handler successfully.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Create 1 socket handler.
 *  - Call vSetSocketEndpoint to attach previous endpoint to this socket handler.
 *  - Check if the endpoint in socket handler is same.
 */
void test_vSetSocketEndpoint_HappyPath()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize socket handler. */
    memset( &xSocket, 0, sizeof( FreeRTOS_Socket_t ) );

    vSetSocketEndpoint( &xSocket, &xEndPoint );

    TEST_ASSERT_EQUAL( &xEndPoint, xSocket.pxEndPoint );
}

/**
 * @brief vSetSocketEndpoint can return normally when socket handler is NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call vSetSocketEndpoint with NULL socket handler.
 */
void test_vSetSocketEndpoint_NullSocket()
{
    vSetSocketEndpoint( NULL, NULL );
}

/**
 * @brief pcEndpointName can get IPv4 address in string from endpoint.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint.
 *     - Set the IP address to 192.168.123.223 (IPV4_DEFAULT_ADDRESS).
 *  - Call pcEndpointName with enough buffer size.
 *  - Check if return buffer string is "192.168.123.223".
 */
void test_pcEndpointName_IPv4_HappyPath()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;
    static const char cIPString[] = "192.168.123.223";
    uint32_t lNameSize = sizeof( cIPString );
    char cName[ lNameSize ];
    const char * pcName = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;

    memset( cName, 0, sizeof( cName ) );

    xStubFreeRTOS_inet_ntop_TargetFamily = FREERTOS_AF_INET4;
    pvStubFreeRTOS_inet_ntop_TargetSource = &( xEndPoint.ipv4_settings.ulIPAddress );
    pcStubFreeRTOS_inet_ntop_TargetDestination = cName;
    ulStubFreeRTOS_inet_ntop_TargetSize = lNameSize;
    pcStubFreeRTOS_inet_ntop_TargetCopySource = cIPString;
    ulStubFreeRTOS_inet_ntop_CopySize = lNameSize;
    FreeRTOS_inet_ntop_Stub( pcStubFreeRTOS_inet_ntop );

    pcName = pcEndpointName( &xEndPoint, cName, lNameSize );
    TEST_ASSERT_EQUAL_MEMORY( pcName, cIPString, lNameSize );
}

/**
 * @brief pcEndpointName can return normally without accessing null pointer.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call pcEndpointName with null buffer pointer.
 */
void test_pcEndpointName_IPv4_NullBufferPointer()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;
    char cIPString[] = "192.168.123.223";
    int lNameSize = sizeof( cIPString ) + 1;
    const char * pcName = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;

    xStubFreeRTOS_inet_ntop_TargetFamily = FREERTOS_AF_INET4;
    pvStubFreeRTOS_inet_ntop_TargetSource = &( xEndPoint.ipv4_settings.ulIPAddress );
    pcStubFreeRTOS_inet_ntop_TargetDestination = NULL;
    ulStubFreeRTOS_inet_ntop_TargetSize = lNameSize;
    pcStubFreeRTOS_inet_ntop_TargetCopySource = NULL;
    ulStubFreeRTOS_inet_ntop_CopySize = 0;
    FreeRTOS_inet_ntop_Stub( pcStubFreeRTOS_inet_ntop );

    pcName = pcEndpointName( &xEndPoint, NULL, lNameSize );
    TEST_ASSERT_EQUAL( NULL, pcName );
}

/**
 * @brief pcEndpointName can get partial IPv4 address in string from endpoint when the buffer size is less than necessary size.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint.
 *     - Set the IP address to 192.168.123.223 (IPV4_DEFAULT_ADDRESS).
 *  - Call pcEndpointName with ( enough buffer size - 3 ).
 *  - Check if return buffer string is "192.168.123.".
 */
void test_pcEndpointName_IPv4_TruncateBuffer()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;
    const char cIPString[] = "192.168.123.223";
    int lNameSize = sizeof( cIPString ) - 3;
    char cName[ lNameSize ];
    const char * pcName = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;

    memset( &cName, 0, sizeof( cName ) );

    xStubFreeRTOS_inet_ntop_TargetFamily = FREERTOS_AF_INET4;
    pvStubFreeRTOS_inet_ntop_TargetSource = &( xEndPoint.ipv4_settings.ulIPAddress );
    pcStubFreeRTOS_inet_ntop_TargetDestination = cName;
    ulStubFreeRTOS_inet_ntop_TargetSize = lNameSize;
    pcStubFreeRTOS_inet_ntop_TargetCopySource = cIPString;
    ulStubFreeRTOS_inet_ntop_CopySize = lNameSize;
    FreeRTOS_inet_ntop_Stub( pcStubFreeRTOS_inet_ntop );

    pcName = pcEndpointName( &xEndPoint, cName, lNameSize );
    TEST_ASSERT_EQUAL_MEMORY( pcName, cIPString, lNameSize );
}

/**
 * @brief pcEndpointName can get string "NULL" when the endpoint is NULL pointer.
 *
 * Test step:
 *  - Call pcEndpointName with NULL endpoint.
 *  - Check if return buffer string is "NULL".
 */
void test_pcEndpointName_NullEndpoint()
{
    int lNameSize = 5;
    char cName[ lNameSize ];
    const char * pcName = NULL;

    pcName = pcEndpointName( NULL, cName, lNameSize );
    TEST_ASSERT_EQUAL_MEMORY( pcName, "NULL", lNameSize );
}

/**
 * @brief pcEndpointName can get IPv6 address in string from endpoint.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint.
 *     - Set the IP address to 2001::1 (xDefaultIPAddress_IPv6).
 *  - Call pcEndpointName with enough buffer size.
 *  - Check if return buffer string is "2001::1".
 */
void test_pcEndpointName_IPv6_HappyPath()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;
    static const char cIPString[] = "2001::1";
    uint32_t lNameSize = sizeof( cIPString );
    char cName[ lNameSize ];
    const char * pcName;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );

    memset( cName, 0, sizeof( cName ) );

    xStubFreeRTOS_inet_ntop_TargetFamily = FREERTOS_AF_INET6;
    pvStubFreeRTOS_inet_ntop_TargetSource = xEndPoint.ipv6_settings.xIPAddress.ucBytes;
    pcStubFreeRTOS_inet_ntop_TargetDestination = cName;
    ulStubFreeRTOS_inet_ntop_TargetSize = lNameSize;
    pcStubFreeRTOS_inet_ntop_TargetCopySource = cIPString;
    ulStubFreeRTOS_inet_ntop_CopySize = lNameSize;
    FreeRTOS_inet_ntop_Stub( pcStubFreeRTOS_inet_ntop );

    pcName = pcEndpointName( &xEndPoint, cName, lNameSize );
    TEST_ASSERT_EQUAL_MEMORY( pcName, cIPString, lNameSize );
}

/**
 * @brief pcEndpointName can get partial IPv6 address in string from endpoint when the buffer size is less than necessary size.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint.
 *     - Set the IP address to 2001::1 (xDefaultIPAddress_IPv6).
 *  - Call pcEndpointName with ( enough buffer size - 3 ).
 *  - Check if return buffer string is "2001".
 */
void test_pcEndpointName_IPv6_TruncateBuffer()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;
    const char cIPString[] = "2001::1";
    int lNameSize = sizeof( cIPString ) - 3;
    char cName[ lNameSize ];
    const char * pcName;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );

    memset( &cName, 0, sizeof( cName ) );

    xStubFreeRTOS_inet_ntop_TargetFamily = FREERTOS_AF_INET6;
    pvStubFreeRTOS_inet_ntop_TargetSource = xEndPoint.ipv6_settings.xIPAddress.ucBytes;
    pcStubFreeRTOS_inet_ntop_TargetDestination = cName;
    ulStubFreeRTOS_inet_ntop_TargetSize = lNameSize;
    pcStubFreeRTOS_inet_ntop_TargetCopySource = cIPString;
    ulStubFreeRTOS_inet_ntop_CopySize = lNameSize;
    FreeRTOS_inet_ntop_Stub( pcStubFreeRTOS_inet_ntop );

    pcName = pcEndpointName( &xEndPoint, cName, lNameSize );
    TEST_ASSERT_EQUAL_MEMORY( pcName, cIPString, lNameSize );
}

/**
 * @brief xIPv6_GetIPType returns eIPv6_Global if input address matches 2000::/3.
 *
 * Test step:
 *  - Create 1 IPv6 address.
 *     - Set the IP address to 2001::1 (xDefaultIPAddress_IPv6).
 *  - Call xIPv6_GetIPType to check IP type.
 *  - Check if it returns eIPv6_Global.
 */
void test_xIPv6_GetIPType_Global()
{
    IPv6_Type_t xReturn;

    xReturn = xIPv6_GetIPType( &xDefaultIPAddress_IPv6 );
    TEST_ASSERT_EQUAL( eIPv6_Global, xReturn );
}

/**
 * @brief xIPv6_GetIPType returns eIPv6_LinkLocal if input address matches FE80::/10.
 *
 * Test step:
 *  - Create 1 IPv6 address.
 *     - Set the IP address to FE8F::1:2.
 *  - Call xIPv6_GetIPType to check IP type.
 *  - Check if it returns eIPv6_LinkLocal.
 */
void test_xIPv6_GetIPType_LinkLocal()
{
    const IPv6_Address_t xIPv6Address = { 0xFE, 0x8F, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x01, 0x02 };
    IPv6_Type_t xReturn;

    xReturn = xIPv6_GetIPType( &xIPv6Address );
    TEST_ASSERT_EQUAL( eIPv6_LinkLocal, xReturn );
}

/**
 * @brief xIPv6_GetIPType returns eIPv6_Loopback if input address matches ::1/128.
 *
 * Test step:
 *  - Create 1 IPv6 address.
 *     - Set the IP address to ::1.
 *  - Call xIPv6_GetIPType to check IP type.
 *  - Check if it returns eIPv6_Loopback.
 */
void test_xIPv6_GetIPType_Loopback()
{
    const IPv6_Address_t xIPv6Address = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x01 };
    IPv6_Type_t xReturn;

    xIsIPv6Loopback_ExpectAndReturn( &xIPv6Address, pdTRUE );

    xReturn = xIPv6_GetIPType( &xIPv6Address );
    TEST_ASSERT_EQUAL( eIPv6_Loopback, xReturn );
}

/**
 * @brief xIPv6_GetIPType returns eIPv6_SiteLocal if input address matches FEC0::/10.
 *
 * Test step:
 *  - Create 1 IPv6 address.
 *     - Set the IP address to FECF::1:2.
 *  - Call xIPv6_GetIPType to check IP type.
 *  - Check if it returns eIPv6_SiteLocal.
 */
void test_xIPv6_GetIPType_SiteLocal()
{
    const IPv6_Address_t xIPv6Address = { 0xFE, 0xCF, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x01, 0x02 };
    IPv6_Type_t xReturn;

    xReturn = xIPv6_GetIPType( &xIPv6Address );
    TEST_ASSERT_EQUAL( eIPv6_SiteLocal, xReturn );
}

/**
 * @brief xIPv6_GetIPType returns eIPv6_Multicast if input address matches FF00::/8.
 *
 * Test step:
 *  - Create 1 IPv6 address.
 *     - Set the IP address to FFFF::1:2.
 *  - Call xIPv6_GetIPType to check IP type.
 *  - Check if it returns eIPv6_Multicast.
 */
void test_xIPv6_GetIPType_Multicast()
{
    const IPv6_Address_t xIPv6Address = { 0xFF, 0xFF, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x01, 0x02 };
    IPv6_Type_t xReturn;

    xReturn = xIPv6_GetIPType( &xIPv6Address );
    TEST_ASSERT_EQUAL( eIPv6_Multicast, xReturn );
}

/**
 * @brief xIPv6_GetIPType returns eIPv6_Unknown if input address doesn't match any rule.
 *
 * Test step:
 *  - Create 1 IPv6 address.
 *     - Set the IP address to 1234::1:2.
 *  - Call xIPv6_GetIPType to check IP type.
 *  - Check if it returns eIPv6_Unknown.
 */
void test_xIPv6_GetIPType_Unknown()
{
    const IPv6_Address_t xIPv6Address = { 0x12, 0x34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x01, 0x02 };
    IPv6_Type_t xReturn;

    xIsIPv6Loopback_ExpectAndReturn( &xIPv6Address, pdFALSE );

    xReturn = xIPv6_GetIPType( &xIPv6Address );
    TEST_ASSERT_EQUAL( eIPv6_Unknown, xReturn );
}

/**
 * @brief xIPv6_GetIPType returns eIPv6_Unknown if input address is NULL.
 *
 * Test step:
 *  - Call xIPv6_GetIPType with NULL input.
 *  - Check if it returns eIPv6_Unknown.
 */
void test_xIPv6_GetIPType_Null()
{
    IPv6_Type_t xReturn;

    xReturn = xIPv6_GetIPType( NULL );
    TEST_ASSERT_EQUAL( eIPv6_Unknown, xReturn );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with same IPv4 address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to the endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to the endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set IPv4 packet with destination address (IPV4_DEFAULT_ADDRESS),
 *    but different MAC address.
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same.
 */
void test_FreeRTOS_MatchingEndpoint_MatchIPv4Address()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( ProtocolPacket_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    const uint8_t ucLocalMACAddress_IPv4[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    pxProtocolPacket->xTCPPacket.xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xTCPPacket.xIPHeader.ulSourceIPAddress = IPV4_DEFAULT_ADDRESS;
    pxProtocolPacket->xTCPPacket.xIPHeader.ulDestinationIPAddress = IPV4_DEFAULT_ADDRESS;

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with same MAC address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to the endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to the endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set IPv4 packet with destination MAC address (ucDefaultMACAddress_IPv4),
 *    but different IP address.
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same.
 */
void test_FreeRTOS_MatchingEndpoint_MatchMACAddress()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( ProtocolPacket_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    pxProtocolPacket->xTCPPacket.xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xTCPPacket.xIPHeader.ulSourceIPAddress = IPV4_DEFAULT_GATEWAY;
    pxProtocolPacket->xTCPPacket.xIPHeader.ulDestinationIPAddress = IPV4_DEFAULT_GATEWAY;

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with same IPv4 address in ARP request packet.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to the endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to the endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set ARP request packet with destination IP address (IPV4_DEFAULT_ADDRESS),
 *    but different MAC address.
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same.
 */
void test_FreeRTOS_MatchingEndpoint_ARPReqMatchIPv4Address()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( ProtocolPacket_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    uint32_t ulIPAddress = IPV4_DEFAULT_GATEWAY;
    const uint8_t ucLocalMACAddress_IPv4[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xARPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xARPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    pxProtocolPacket->xARPPacket.xEthernetHeader.usFrameType = ipARP_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xARPPacket.xARPHeader.usOperation = ipARP_REQUEST;
    memcpy( pxProtocolPacket->xARPPacket.xARPHeader.ucSenderProtocolAddress, &ulIPAddress, sizeof( pxProtocolPacket->xARPPacket.xARPHeader.ucSenderProtocolAddress ) );
    pxProtocolPacket->xARPPacket.xARPHeader.ulTargetProtocolAddress = IPV4_DEFAULT_ADDRESS;

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with same MAC address in ARP request packet.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to the endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to the endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set ARP request packet with destination MAC address (ucDefaultMACAddress_IPv4),
 *    but different IP address.
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same.
 */
void test_FreeRTOS_MatchingEndpoint_ARPReqMatchMACAddress()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( ProtocolPacket_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    uint32_t ulIPAddress = IPV4_DEFAULT_ADDRESS;

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xARPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xARPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    pxProtocolPacket->xARPPacket.xEthernetHeader.usFrameType = ipARP_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xARPPacket.xARPHeader.usOperation = ipARP_REQUEST;
    memcpy( pxProtocolPacket->xARPPacket.xARPHeader.ucSenderProtocolAddress, &ulIPAddress, sizeof( pxProtocolPacket->xARPPacket.xARPHeader.ucSenderProtocolAddress ) );
    pxProtocolPacket->xARPPacket.xARPHeader.ulTargetProtocolAddress = IPV4_DEFAULT_GATEWAY;

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with same IPv4 address in ARP reply packet.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to the endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to the endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set ARP reply packet with destination IP address (IPV4_DEFAULT_ADDRESS),
 *    but different MAC address.
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same.
 */
void test_FreeRTOS_MatchingEndpoint_ARPReplyMatchIPv4Address()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( ProtocolPacket_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    uint32_t ulIPAddress = IPV4_DEFAULT_ADDRESS;
    const uint8_t ucLocalMACAddress_IPv4[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xARPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xARPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    pxProtocolPacket->xARPPacket.xEthernetHeader.usFrameType = ipARP_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xARPPacket.xARPHeader.usOperation = ipARP_REPLY;
    memcpy( pxProtocolPacket->xARPPacket.xARPHeader.ucSenderProtocolAddress, &ulIPAddress, sizeof( pxProtocolPacket->xARPPacket.xARPHeader.ucSenderProtocolAddress ) );
    pxProtocolPacket->xARPPacket.xARPHeader.ulTargetProtocolAddress = IPV4_DEFAULT_GATEWAY;

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with same MAC address in ARP reply packet.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to the endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to the endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set ARP reply packet with destination MAC address (ucDefaultMACAddress_IPv4),
 *    but different IP address.
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same.
 */
void test_FreeRTOS_MatchingEndpoint_ARPReplyMatchMACAddress()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( ProtocolPacket_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    uint32_t ulIPAddress = IPV4_DEFAULT_GATEWAY;

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xARPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xARPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    pxProtocolPacket->xARPPacket.xEthernetHeader.usFrameType = ipARP_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xARPPacket.xARPHeader.usOperation = ipARP_REPLY;
    memcpy( pxProtocolPacket->xARPPacket.xARPHeader.ucSenderProtocolAddress, &ulIPAddress, sizeof( pxProtocolPacket->xARPPacket.xARPHeader.ucSenderProtocolAddress ) );
    pxProtocolPacket->xARPPacket.xARPHeader.ulTargetProtocolAddress = IPV4_DEFAULT_ADDRESS;

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the IPv4 endpoint while receiving in ARP packet with invalid option code.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to the endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to the endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set ARP packet with invalid option code and
 *    destination IP address (IPV4_DEFAULT_ADDRESS), but different MAC address.
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same.
 */
void test_FreeRTOS_MatchingEndpoint_ARPWrongOption()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( ProtocolPacket_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    uint32_t ulIPAddress = IPV4_DEFAULT_ADDRESS;
    const uint8_t ucLocalMACAddress_IPv4[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xARPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xARPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    pxProtocolPacket->xARPPacket.xEthernetHeader.usFrameType = ipARP_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xARPPacket.xARPHeader.usOperation = ipARP_PROTOCOL_TYPE;
    memcpy( pxProtocolPacket->xARPPacket.xARPHeader.ucSenderProtocolAddress, &ulIPAddress, sizeof( pxProtocolPacket->xARPPacket.xARPHeader.ucSenderProtocolAddress ) );
    pxProtocolPacket->xARPPacket.xARPHeader.ulTargetProtocolAddress = IPV4_DEFAULT_GATEWAY;

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with same IPv4 address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 2 endpoints (e0, e1).
 *  - Put interface & endpoint into the list.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to e0 endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to e0 endpoint.
 *     - Assign 192.168.123.254 (IPV4_DEFAULT_GATEWAY) to e1 endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to e1 endpoint.
 *     - Attach e0 and e1 to interface.
 *  - Create a network buffer and IPv4 packet with destination IPv4 address (IPV4_DEFAULT_ADDRESS).
 *  - Call FreeRTOS_MatchingEndpoint with check if returned endpoint is e0.
 *  - Create a network buffer and IPv4 packet with destination IPv4 address (IPV4_DEFAULT_GATEWAY).
 *  - Call FreeRTOS_MatchingEndpoint with check if returned endpoint is e1.
 */
void test_FreeRTOS_MatchingEndpoint_OneMACOneIPv4()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( ProtocolPacket_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint e0. */
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 0 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint[ 0 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint[ 0 ].pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    /* Initialize endpoint e1. */
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 1 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_GATEWAY;
    memcpy( xEndPoint[ 1 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint[ 1 ].pxNetworkInterface = &xNetworkInterface;
    /* Attach endpoint to the end of list. */
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    /* Initialize e0 network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    pxProtocolPacket->xTCPPacket.xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xTCPPacket.xIPHeader.ulSourceIPAddress = IPV4_DEFAULT_GATEWAY;
    pxProtocolPacket->xTCPPacket.xIPHeader.ulDestinationIPAddress = IPV4_DEFAULT_ADDRESS;

    /* Query for e0. */
    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint[ 0 ], pxEndPoint );

    /* Initialize e1 network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    pxProtocolPacket->xTCPPacket.xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xTCPPacket.xIPHeader.ulSourceIPAddress = IPV4_DEFAULT_ADDRESS;
    pxProtocolPacket->xTCPPacket.xIPHeader.ulDestinationIPAddress = IPV4_DEFAULT_GATEWAY;

    /* Query for e1. */
    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint[ 1 ], pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns NULL when input interface is NULL.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to the endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to the endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set IPv4 packet with destination IP address (IPV4_DEFAULT_ADDRESS).
 *  - Call FreeRTOS_MatchingEndpoint with check if returned endpoint is same.
 */
void test_FreeRTOS_MatchingEndpoint_NullInterface()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( ProtocolPacket_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    const uint8_t ucLocalMACAddress_IPv4[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    pxProtocolPacket->xTCPPacket.xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xTCPPacket.xIPHeader.ulSourceIPAddress = IPV4_DEFAULT_ADDRESS;
    pxProtocolPacket->xTCPPacket.xIPHeader.ulDestinationIPAddress = IPV4_DEFAULT_ADDRESS;

    pxEndPoint = FreeRTOS_MatchingEndpoint( NULL, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns NULL when there is no matching IPv4 endpoint.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 2001::1 (xDefaultIPAddress_IPv6) to the endpoint.
 *     - Assign 11:22:33:ab:cd:ef (ucDefaultMACAddress_IPv6) to the endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set IPv4 packet with different destination IPv4/MAC address.
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is NULL.
 */
void test_FreeRTOS_MatchingEndpoint_IPv4NotFound()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( ProtocolPacket_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    const uint8_t ucLocalMACAddress_IPv4[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, sizeof( ucDefaultMACAddress_IPv6 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress_IPv4, sizeof( ucLocalMACAddress_IPv4 ) );
    pxProtocolPacket->xTCPPacket.xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xTCPPacket.xIPHeader.ulSourceIPAddress = IPV4_DEFAULT_ADDRESS;
    pxProtocolPacket->xTCPPacket.xIPHeader.ulDestinationIPAddress = IPV4_DEFAULT_ADDRESS;

    /* FreeRTOS_inet_ntop is used to print for debugging. Ignore it here. */
    FreeRTOS_inet_ntop_IgnoreAndReturn( NULL );
    FreeRTOS_inet_ntop_IgnoreAndReturn( NULL );

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with same IPv6 address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 2001::1 (xDefaultIPAddress_IPv6) to the endpoint.
 *     - Assign 11:22:33:ab:cd:ef (ucDefaultMACAddress_IPv6) to the endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set IPv6 packet with destination address (xDefaultIPAddress_IPv6),
 *    but different MAC address.
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same.
 */
void test_FreeRTOS_MatchingEndpoint_MatchIPv6Address()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    const uint8_t ucLocalMACAddress_IPv6[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, sizeof( ucDefaultMACAddress_IPv6 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress_IPv6, sizeof( ucLocalMACAddress_IPv6 ) );
    memcpy( pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress_IPv6, sizeof( ucLocalMACAddress_IPv6 ) );
    pxTCPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxTCPPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns NULL when there is no matching IPv6 endpoint.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to the endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to the endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and IPv6 packet with destination IPv6/MAC address (xDefaultIPAddress_IPv6).
 *  - Call FreeRTOS_MatchingEndpoint with check if returned endpoint is NULL.
 */
void test_FreeRTOS_MatchingEndpoint_IPv6NotFound()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    const uint8_t ucLocalMACAddress_IPv6[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucDefaultMACAddress_IPv6, sizeof( ucDefaultMACAddress_IPv6 ) );
    memcpy( pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes, ucDefaultMACAddress_IPv6, sizeof( ucDefaultMACAddress_IPv6 ) );
    pxTCPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );

    /* FreeRTOS_inet_ntop is used to print for debugging. Ignore it here. */
    FreeRTOS_inet_ntop_IgnoreAndReturn( "2001::1" );
    FreeRTOS_inet_ntop_IgnoreAndReturn( "2001::1" );

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxTCPPacket ) );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with same IPv6 address.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 2 endpoints (e0, e1).
 *  - Put interface & endpoint into the list.
 *     - Assign 2001::1 (xDefaultIPAddress_IPv6) to e0 endpoint.
 *     - Assign 11:22:33:ab:cd:ef (ucDefaultMACAddress_IPv6) to e0 endpoint.
 *     - Assign 2001::fffe (xDefaultGatewayAddress_IPv6) to e1 endpoint.
 *     - Assign 11:11:11:11:11:11 to e1 endpoint.
 *     - Attach e0 and e1 to interface.
 *  - Create a network buffer and IPv4 packet with destination IPv4 address (xDefaultIPAddress_IPv6).
 *  - Call FreeRTOS_MatchingEndpoint with check if returned endpoint is e0.
 *  - Create a network buffer and IPv4 packet with destination IPv4 address (xDefaultGatewayAddress_IPv6).
 *  - Call FreeRTOS_MatchingEndpoint with check if returned endpoint is e1.
 */
void test_FreeRTOS_MatchingEndpoint_OneMACOneIPv6()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    const uint8_t ucLocalMACAddress_IPv6[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint e0. */
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 0 ].bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint[ 0 ].ipv6_settings.xIPAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint[ 0 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, sizeof( ucDefaultMACAddress_IPv6 ) );
    xEndPoint[ 0 ].pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    /* Initialize endpoint e1. */
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 1 ].bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint[ 1 ].ipv6_settings.xIPAddress.ucBytes, xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint[ 1 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, sizeof( ucDefaultMACAddress_IPv6 ) );
    xEndPoint[ 1 ].pxNetworkInterface = &xNetworkInterface;
    /* Attach endpoint to the end of list. */
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    /* Initialize e0 network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress_IPv6, sizeof( ucLocalMACAddress_IPv6 ) );
    memcpy( pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress_IPv6, sizeof( ucLocalMACAddress_IPv6 ) );
    pxTCPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );

    /* Query for e0. */
    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxTCPPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint[ 0 ], pxEndPoint );

    /* Initialize e1 network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress_IPv6, sizeof( ucLocalMACAddress_IPv6 ) );
    memcpy( pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress_IPv6, sizeof( ucLocalMACAddress_IPv6 ) );
    pxTCPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xDefaultGatewayAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );

    /* Query for e1. */
    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxTCPPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint[ 1 ], pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with type.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 2 endpoints (e0, e1).
 *  - Put interface & endpoint into the list.
 *     - Assign 2001::1 (xDefaultIPAddress_IPv6) to e0 endpoint.
 *     - Assign 11:22:33:ab:cd:ef (ucDefaultMACAddress_IPv6) to e0 endpoint.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to e1 endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to e1 endpoint.
 *     - Attach e0 and e1 to interface.
 *  - Create a network buffer and IPv4 packet with different destination IPv6 address (xDefaultGatewayAddress_IPv6).
 *  - Call FreeRTOS_MatchingEndpoint with check if returned endpoint is e1. (Match by IP type.)
 *  - Create a network buffer and IPv4 packet with different destination IPv4 address (ucDefaultGatewayAddress_IPv4).
 *  - Call FreeRTOS_MatchingEndpoint with check if returned endpoint is e0. (Match by IP type.)
 */
void test_FreeRTOS_MatchingEndpoint_Type()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint[ 2 ];
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    const uint8_t ucLocalMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };
    /* Declare a non-global IPv6 address to test. */
    const IPv6_Address_t xNonGlobalIPAddress_IPv6 = { 0x12, 0x34, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint e0. */
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 0 ].bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint[ 0 ].ipv6_settings.xIPAddress.ucBytes, xNonGlobalIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint[ 0 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, sizeof( ucDefaultMACAddress_IPv6 ) );
    xEndPoint[ 0 ].pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint[ 0 ];

    /* Initialize endpoint e1. */
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint[ 1 ].ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint[ 1 ].xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint[ 1 ].pxNetworkInterface = &xNetworkInterface;
    /* Attach endpoint to the end of list. */
    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    /* Initialize e0 network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress, sizeof( ucLocalMACAddress ) );
    memcpy( pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress, sizeof( ucLocalMACAddress ) );
    pxTCPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );

    xIsIPv6Loopback_ExpectAndReturn( &( xNonGlobalIPAddress_IPv6 ), pdFALSE );

    /* Query for e0. */
    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxTCPPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint[ 0 ], pxEndPoint );

    /* Initialize e1 network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress, sizeof( ucLocalMACAddress ) );
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress, sizeof( ucLocalMACAddress ) );
    pxProtocolPacket->xTCPPacket.xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;
    /* IP part. */
    pxProtocolPacket->xTCPPacket.xIPHeader.ulSourceIPAddress = IPV4_DEFAULT_GATEWAY;
    pxProtocolPacket->xTCPPacket.xIPHeader.ulDestinationIPAddress = IPV4_DEFAULT_GATEWAY;

    /* Query for e1. */
    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxTCPPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint[ 1 ], pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with default gateway address (FE80::1).
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign FE70::1 to endpoint.
 *     - Assign 11:22:33:ab:cd:ef (ucDefaultMACAddress_IPv6) to endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set IPv6 packet with destination address FE80::1 (default gateway address).
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same (matched by IP type).
 */
void test_FreeRTOS_MatchingEndpoint_IPv6DefaultGatewayNotFound()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    const uint8_t ucLocalMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };
    /* Declare a default gateway IPv6 address to test. */
    const IPv6_Address_t xDefaultGatewayIPAddress_IPv6 = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint e0. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, sizeof( ucDefaultMACAddress_IPv6 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress, sizeof( ucLocalMACAddress ) );
    memcpy( pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress, sizeof( ucLocalMACAddress ) );
    pxTCPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xDefaultGatewayIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxTCPPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint with non-global address (FE80::123).
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign FE80::123 to endpoint.
 *     - Assign 11:22:33:ab:cd:ef (ucDefaultMACAddress_IPv6) to endpoint.
 *     - Attach endpoint to interface.
 *  - Create a network buffer and set IPv6 packet with destination address FE80::1 (default gateway address).
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same (matched by IP type).
 */
void test_FreeRTOS_MatchingEndpoint_IPv6NonGlobal()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );
    const uint8_t ucLocalMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };
    /* Declare a non-global IPv6 address to test. */
    const IPv6_Address_t xLocalIPAddress_IPv6 = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x23 };

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint e0. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xLocalIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv6, sizeof( ucDefaultMACAddress_IPv6 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucLocalMACAddress, sizeof( ucLocalMACAddress ) );
    memcpy( pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes, ucLocalMACAddress, sizeof( ucLocalMACAddress ) );
    pxTCPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xLocalIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxTCPPacket ) );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint triggers assertion if buffer pointer is NULL.
 *
 * Test step:
 *  - Call FreeRTOS_MatchingEndpoint with NULL buffer pointer.
 */
void test_FreeRTOS_MatchingEndpoint_NullBuffer()
{
    catch_assert( FreeRTOS_MatchingEndpoint( NULL, NULL ) );
}

/**
 * @brief FreeRTOS_MatchingEndpoint triggers assertion if buffer pointer is NULL.
 *
 * Test step:
 *  - Call FreeRTOS_MatchingEndpoint with buffer pointer with not aligned address.
 */
void test_FreeRTOS_MatchingEndpoint_BufferAddressNotAligned()
{
    uint8_t * pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) ] __attribute__( ( aligned( 32 ) ) );

    catch_assert( FreeRTOS_MatchingEndpoint( NULL, ( const uint8_t * ) pcNetworkBuffer ) );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns NULL when receiving custom frame type
 * but ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES is off.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *     - Assign 192.168.123.223 (IPV4_DEFAULT_ADDRESS) to the endpoint.
 *     - Assign ab:cd:ef:11:22:33 (ucDefaultMACAddress_IPv4) to the endpoint.
 *     - Assign 0xFF as frame type to the endpoint.
 *     - Attach endpoint to interface.
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is NULL.
 */
void test_FreeRTOS_MatchingEndpoint_MatchCustomFrameType()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    ProtocolPacket_t * pxProtocolPacket = ( ProtocolPacket_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* Initialize network buffer. */
    memset( pcNetworkBuffer, 0, sizeof( pcNetworkBuffer ) );
    /* Ethernet part. */
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    pxProtocolPacket->xTCPPacket.xEthernetHeader.usFrameType = 0xFF;
    /* IP part. */
    pxProtocolPacket->xTCPPacket.xIPHeader.ulSourceIPAddress = IPV4_DEFAULT_ADDRESS;
    pxProtocolPacket->xTCPPacket.xIPHeader.ulDestinationIPAddress = IPV4_DEFAULT_ADDRESS;

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) ( pxProtocolPacket ) );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief Test to check if FreeRTOS_InterfaceEPInSameSubnet_IPv6 returns a matching endpoint
 * on the interface given to FreeRTOS_InterfaceEPInSameSubnet_IPv6 thats on the same subnet as of
 * the given IPv6 address.
 */
void test_FreeRTOS_InterfaceEPInSameSubnet_IPv6_HappyPath( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    NetworkInterface_t xNetworkInterface;

    /* Initialize network interface and add it to the list. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint.ipv6_settings.xIPAddress ), &xDefaultIPAddress_IPv6, xEndPoint.ipv6_settings.uxPrefixLength, 0 );

    pxEndPoint = FreeRTOS_InterfaceEPInSameSubnet_IPv6( &xNetworkInterface, &xDefaultIPAddress_IPv6 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief Test to check if FreeRTOS_InterfaceEPInSameSubnet_IPv6 returns a NULL endpoint
 * if the interface given to FreeRTOS_InterfaceEPInSameSubnet_IPv6 is different from the
 * endpoint found.
 */
void test_FreeRTOS_InterfaceEPInSameSubnet_IPv6_DifferentInterface( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    NetworkInterface_t xNetworkInterface[ 2 ];

    /* Initialize network interface and add it to the list. */
    memset( &xNetworkInterface[ 0 ], 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface[ 0 ];

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xEndPoint.pxNetworkInterface = &xNetworkInterface[ 0 ];
    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    pxEndPoint = FreeRTOS_InterfaceEPInSameSubnet_IPv6( &xNetworkInterface[ 1 ], &xDefaultIPAddress_IPv6 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}
