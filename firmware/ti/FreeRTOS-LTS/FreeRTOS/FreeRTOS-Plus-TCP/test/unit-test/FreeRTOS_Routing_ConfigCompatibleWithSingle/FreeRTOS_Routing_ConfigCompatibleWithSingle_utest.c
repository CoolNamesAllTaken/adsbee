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

#include "FreeRTOSIPConfig.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_queue.h"
#include "mock_event_groups.h"
#include "mock_FreeRTOS_IPv6.h"

#include "FreeRTOS_Routing.h"

#include "catch_assert.h"

/* Default IPv4 address is 192.168.123.223, which is 0xDF7BA8C0. */
#define IPV4_DEFAULT_ADDRESS       ( 0xDF7BA8C0 )
/* Default IPv4 netmask is 255.255.255.0, which is 0x00FFFFFF. */
#define IPV4_DEFAULT_NETMASK       ( 0x00FFFFFF )
/* Default IPv4 netmask is 192.168.123.254, which is 0xFE7BA8C0. */
#define IPV4_DEFAULT_GATEWAY       ( 0xFE7BA8C0 )
/* Default IPv4 netmask is 192.168.123.1, which is 0x017BA8C0. */
#define IPV4_DEFAULT_DNS_SERVER    ( 0x017BA8C0 )

/* ===========================  EXTERN VARIABLES  =========================== */

const uint8_t ucDefaultIPAddress_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 192, 168, 123, 223 };
const uint8_t ucDefaultNetMask_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 255, 255, 255, 0 };
const uint8_t ucDefaultGatewayAddress_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 192, 168, 123, 254 };
const uint8_t ucDefaultDNSServerAddress_IPv4[ ipIP_ADDRESS_LENGTH_BYTES ] = { 192, 168, 123, 1 };
const uint8_t ucDefaultMACAddress_IPv4[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };

/* Default IPv6 address 1 is set to 2001::1 */
const IPv6_Address_t xDefaultIPAddress_IPv6_1 = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

/* Default IPv6 address 2 is set to 2003::1 */
const IPv6_Address_t xDefaultIPAddress_IPv6_2 = { 0x20, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
    pxNetworkEndPoints = NULL;
    pxNetworkInterfaces = NULL;
}

/* =============================== Test Cases =============================== */

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
    NetworkEndPoint_t xEndPoint[ 2 ];

    memset( &xInterfaces, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );

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

    /* Assertion triggered due to trying to add second endpoint with backward compatible enabled. */
    catch_assert( FreeRTOS_FillEndPoint( &xInterfaces,
                                         &xEndPoint[ 1 ],
                                         ucDefaultGatewayAddress_IPv4,
                                         ucDefaultNetMask_IPv4,
                                         ucDefaultGatewayAddress_IPv4,
                                         ucDefaultDNSServerAddress_IPv4,
                                         ucDefaultMACAddress_IPv4 ) );
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

    /* Assertion triggered due to trying to add second endpoint with backward compatible enabled. */
    catch_assert( FreeRTOS_FillEndPoint( &xInterfaces,
                                         &xEndPoint,
                                         ucDefaultIPAddress_IPv4,
                                         ucDefaultNetMask_IPv4,
                                         ucDefaultGatewayAddress_IPv4,
                                         ucDefaultDNSServerAddress_IPv4,
                                         ucDefaultMACAddress_IPv4 ) );
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
 * @brief The purpose of this test is to verify FreeRTOS_AddNetworkInterface two times with
 * different valid input parameters.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 *
 * Test step:
 *  - Call FreeRTOS_AddNetworkInterface two times with three different network interfaces.
 *  - Check if assertion triggered at the second time.
 */
void test_FreeRTOS_AddNetworkInterface_TwoInARow( void )
{
    NetworkInterface_t xNetworkInterface[ 2 ];
    NetworkInterface_t * pxNetworkInterface = NULL;
    int i = 0;

    for( i = 0; i < 2; i++ )
    {
        memset( &( xNetworkInterface[ i ] ), 0, sizeof( NetworkInterface_t ) );
    }

    ( void ) FreeRTOS_AddNetworkInterface( &( xNetworkInterface[ 0 ] ) );
    TEST_ASSERT_EQUAL( &( xNetworkInterface[ 0 ] ), pxNetworkInterfaces );

    /* In backward compatible, we only support 1 interface */
    catch_assert( FreeRTOS_AddNetworkInterface( &( xNetworkInterface[ 1 ] ) ) );
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
 *  - Create 1 network interface and attach them into pxNetworkInterfaces.
 *  - Check if pxNetworkInterfaces is same as first input.
 *  - Check if we can query next network interface and get NULL correctly by calling FreeRTOS_NextNetworkInterface.
 */
void test_FreeRTOS_NextNetworkInterface_HappyPath( void )
{
    NetworkInterface_t xNetworkInterface;
    NetworkInterface_t * pxNetworkInterface = NULL;

    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    pxNetworkInterface = FreeRTOS_NextNetworkInterface( &xNetworkInterface );

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
 *  - Loop to call FreeRTOS_FirstEndPoint to get first endpoint with each network interface.
 *  - Check if returned endpoint is same as first endpoint.
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
        /* In backward compatible, stack only supports one endpoint. */
        TEST_ASSERT_EQUAL( &( xEndPoint[ 0 ] ), pxEndPoint );
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
 *  - Loop to call FreeRTOS_FirstEndPoint to get e0 with each network interface.
 *  - Check if returned endpoint is same as e0.
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
        TEST_ASSERT_EQUAL( &( xEndPoint[ 0 ] ), pxEndPoint );
    }
}

/**
 * @brief FreeRTOS_NextEndPoint always returns NULL when backward compatible enabled.
 *
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoints and stored then into pxNetworkEndPoints.
 *  - Loop to call FreeRTOS_NextEndPoint to get endpoints.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_NextEndPoint_HappyPath( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxNetworkEndPoints = &xEndPoint;
    pxEndPoint = pxNetworkEndPoints;

    pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
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
 *  - Create 1 endpoint and add it to the list.
 *     - Set e0 IP address to 192.168.123.223 (IPV4_DEFAULT_ADDRESS).
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query different IP address.
 *  - Check if returned endpoint is NULL.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv4_NotFound( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize e0. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( IPV4_DEFAULT_GATEWAY, 0 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindEndPointOnIP_IPv4 should return first endpoint in the list when query IP address is 0.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint and add it to the list.
 *  - Call FreeRTOS_FindEndPointOnIP_IPv4 to query with 0 address.
 *  - Check if returned endpoint is the first endpoint.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv4_AnyEndpoint( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( 0, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
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

    /* Initialize network interface and add it to the list. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    xEndPoint.ipv4_settings.ulNetMask = IPV4_DEFAULT_NETMASK;
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* IPV4_DEFAULT_ADDRESS is 192.168.123.1 within the network region. */
    pxEndPoint = FreeRTOS_InterfaceEndPointOnNetMask( &xNetworkInterface, IPV4_DEFAULT_DNS_SERVER, 0 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_InterfaceEndPointOnNetMask returns NULL when there is no endpoint matches.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 IPv4 endpoint and add it to the list.
 *     - Set the IP address to 192.168.123.223 (IPV4_DEFAULT_ADDRESS).
 *     - Set the netmask to 255.255.255.0.
 *  - Call FreeRTOS_InterfaceEndPointOnNetMask to query for IP address 192.168.122.1.
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
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    xEndPoint.ipv4_settings.ulNetMask = IPV4_DEFAULT_NETMASK;
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    /* 192.168.122.1 is not in the network region. */
    pxEndPoint = FreeRTOS_InterfaceEndPointOnNetMask( &xNetworkInterface, 0x017AA8C0, 0 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
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
void test_FreeRTOS_FindGateWay_IPv4HappyPath( void )
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
 *  - Create 1 IPv4 endpoint and add it to the list.
 *     - Set the gateway address to 0 (invalid address).
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv4.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindGateWay_IPv4NotFound( void )
{
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv4 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief FreeRTOS_FindGateWay should be able to return NULL if no endpoint stored in the list.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Call FreeRTOS_FindGateWay with ipTYPE_IPv4.
 *  - Check if returned endpoint is same.
 */
void test_FreeRTOS_FindGateWay_IPv4EmptyList( void )
{
    NetworkEndPoint_t * pxEndPoint = NULL;

    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv4 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief When backward compatible enabled, FreeRTOS_MatchingEndpoint always return the only endpoint stored in the list.
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
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same.
 */
void test_FreeRTOS_MatchingEndpoint_MatchIPv4Address()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_MatchingEndpoint( NULL, NULL );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief When backward compatible enabled, FreeRTOS_FindEndPointOnIP_IPv6 always return the only endpoint stored in the list.
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
 *  - Call FreeRTOS_FindEndPointOnIP_IPv6 and check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnIP_IPv6_HappyPath()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( NULL );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief When backward compatible enabled, FreeRTOS_FindEndPointOnNetMask_IPv6 always return the only endpoint stored in the list.
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
 *  - Call FreeRTOS_FindEndPointOnNetMask_IPv6 and check if returned endpoint is same.
 */
void test_FreeRTOS_FindEndPointOnNetMask_IPv6_HappyPath()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.ipv4_settings.ulIPAddress = IPV4_DEFAULT_ADDRESS;
    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress_IPv4, sizeof( ucDefaultMACAddress_IPv4 ) );
    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    pxEndPoint = FreeRTOS_FindEndPointOnNetMask_IPv6( NULL );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief When compatible with single is enabled, FreeRTOS_InterfaceEPInSameSubnet_IPv6 compares the IPv6 address with the endpoint's IP.
 */
void test_FreeRTOS_InterfaceEPInSameSubnet_IPv6_HappyPath()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6_1.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint.ipv6_settings.xIPAddress ), &xDefaultIPAddress_IPv6_1, xEndPoint.ipv6_settings.uxPrefixLength, 0 );

    pxEndPoint = FreeRTOS_InterfaceEPInSameSubnet_IPv6( &xNetworkInterface, &xDefaultIPAddress_IPv6_1 );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief When compatible with single is enabled, FreeRTOS_InterfaceEPInSameSubnet_IPv6 compares the IPv6 address with the endpoint's IP.
 * In this case the IPv6 address is not on the same subnet.
 */
void test_FreeRTOS_InterfaceEPInSameSubnet_IPv6_UnHappyPath()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;

    /* Initialize network interface. */
    memset( &xNetworkInterface, 0, sizeof( NetworkInterface_t ) );
    pxNetworkInterfaces = &xNetworkInterface;

    /* Initialize endpoint. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, &xDefaultIPAddress_IPv6_2.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    xEndPoint.pxNetworkInterface = &xNetworkInterface;
    pxNetworkEndPoints = &xEndPoint;

    xCompareIPv6_Address_ExpectAndReturn( &( xEndPoint.ipv6_settings.xIPAddress ), &xDefaultIPAddress_IPv6_1, xEndPoint.ipv6_settings.uxPrefixLength, 1 );

    pxEndPoint = FreeRTOS_InterfaceEPInSameSubnet_IPv6( &xNetworkInterface, &xDefaultIPAddress_IPv6_1 );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}
