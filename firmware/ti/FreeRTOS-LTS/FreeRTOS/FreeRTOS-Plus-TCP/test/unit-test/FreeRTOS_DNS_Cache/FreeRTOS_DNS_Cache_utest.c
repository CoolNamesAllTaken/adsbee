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
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_task.h"
#include "mock_list.h"
#include "mock_queue.h"

#include "mock_FreeRTOS_DNS_Callback.h"
#include "mock_FreeRTOS_DNS_Parser.h"
#include "mock_FreeRTOS_DNS_Networking.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_DNS.h"

#include "FreeRTOS_DNS_Cache.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#define LLMNR_ADDRESS     "freertos"
#define GOOD_ADDRESS      "www.freertos.org"
#define BAD_ADDRESS       "this is a bad address"
#define DOTTED_ADDRESS    "192.268.0.1"

typedef void (* FOnDNSEvent ) ( const char * /* pcName */,
                                void * /* pvSearchID */,
                                struct freertos_addrinfo * /* pxAddressInfo */ );

/* ===========================   GLOBAL VARIABLES =========================== */
static int callback_called = 0;


/* ===========================  STATIC FUNCTIONS  =========================== */
static void dns_callback( const char * pcName,
                          void * pvSearchID,
                          uint32_t ulIPAddress )
{
    callback_called = 1;
}

/* ===========================  EXTERN VARIABLES  =========================== */
struct freertos_addrinfo pucAddrBuffer[ 2 ];
struct freertos_sockaddr pucSockAddrBuffer[ 1 ];

/* ============================  UNITY FIXTURES  ============================= */

/**
 * @brief calls at the beginning of each test case
 */
void setUp( void )
{
    FreeRTOS_dnsclear();
    callback_called = 0;
}

/**
 * @brief calls at the end of each test case
 */
void tearDown( void )
{
}

/*!
 * @brief DNS cache structure instantiation
 */
static DNSCacheRow_t xDNSCache[ ipconfigDNS_CACHE_ENTRIES ];


/* =============================  TEST CASES  =============================== */

/**
 * @brief catch assertion on name being non-NULL.
 */
void test_processDNS_CACHE_CatchAssert( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;

    xTaskGetTickCount_ExpectAndReturn( 5000 ); /* 5 seconds */

    catch_assert( FreeRTOS_dnslookup( NULL ) );
}

/**
 * @brief Ensures that the same entry is inserted into the cache and retrieved.
 */
void test_processDNS_CACHE_Success( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;
    IPv46_Address_t pxIP;

    pxIP.xIPAddress.ulIP_IPv4 = pulIP;
    pxIP.xIs_IPv6 = pdFALSE;

    xTaskGetTickCount_ExpectAndReturn( 3000 ); /* 3 seconds */
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "hello",
                         &pxIP,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL ); /* lives 3 seconds */

    xTaskGetTickCount_ExpectAndReturn( 5000 );                 /* 5 seconds */
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    x = FreeRTOS_dnslookup( "hello" );

    TEST_ASSERT_EQUAL( pulIP, x );
}

/**
 * @brief Ensures that the same entry is inserted into the cache and retrieved for IPv6
 */
void test_processDNS_CACHE_Success2( void )
{
    uint32_t ulReturn = 0U;
    uint32_t pulIP = 1234;
    IPv46_Address_t pxIP;

    pxIP.xIPAddress.ulIP_IPv4 = pulIP;
    pxIP.xIs_IPv6 = pdTRUE;

    xTaskGetTickCount_ExpectAndReturn( 3000 ); /* 3 seconds */
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "hello",
                         &pxIP,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL ); /* lives 3 seconds */

    xTaskGetTickCount_ExpectAndReturn( 5000 );                 /* 5 seconds */
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    ulReturn = FreeRTOS_dnslookup6( "hello", &( pxIP.xIPAddress.xIP_IPv6 ) );

    TEST_ASSERT_EQUAL( ulReturn, 1 );
}

/**
 * @brief Ensures that failure occurs when different entry is inserted into the cache and retrieved for IPv6
 */
void test_processDNS_CACHE_Fail_IPv6( void )
{
    uint32_t ulReturn = 0U;
    uint32_t pulIP = 1234;
    IPv46_Address_t pxIP;

    pxIP.xIPAddress.ulIP_IPv4 = pulIP;
    pxIP.xIs_IPv6 = pdFALSE;

    xTaskGetTickCount_ExpectAndReturn( 3000 ); /* 3 seconds */
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "hello",
                         &pxIP,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL ); /* lives 3 seconds */

    xTaskGetTickCount_ExpectAndReturn( 10000 );                /* 10 seconds */

    ulReturn = FreeRTOS_dnslookup6( "helloworld", &( pxIP.xIPAddress.xIP_IPv6 ) );

    TEST_ASSERT_EQUAL( ulReturn, 0 );
}

/**
 * @brief Cannot Confirm that the record in the DNS Cache is still fresh.
 */
void test_processDNS_CACHE_Entry_NotFresh( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;
    IPv46_Address_t pxIP;

    pxIP.xIPAddress.ulIP_IPv4 = pulIP;
    pxIP.xIs_IPv6 = 0;

    xTaskGetTickCount_ExpectAndReturn( 3000 ); /* 3 seconds */
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "hello",
                         &pxIP,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL ); /* lives 3 seconds */


    xTaskGetTickCount_ExpectAndReturn( 8000 ); /* 8 seconds */

    x = FreeRTOS_dnslookup( "hello" );

    TEST_ASSERT_EQUAL( 0, x );
}


/**
 * @brief Ensures empty cache returns zero
 */
void test_processDNS_CACHE_empty_cache( void )
{
    BaseType_t x;

    xTaskGetTickCount_ExpectAndReturn( 3000 );

    x = FreeRTOS_dnslookup( "hello" );

    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief Ensures entry not found returns zero
 */
void test_processDNS_CACHE_entry_not_found( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;
    IPv46_Address_t pxIP;

    pxIP.xIPAddress.ulIP_IPv4 = pulIP;

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "world",
                         &pxIP,
                         400, pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 3000 );

    x = FreeRTOS_dnslookup( "hello" );

    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief Ensures entry not found returns zero
 */
void test_processDNS_CACHE_update_entry( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;
    IPv46_Address_t pxIP;

    pxIP.xIPAddress.ulIP_IPv4 = pulIP;

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "world",
                         &pxIP,
                         400, pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_dns_update( "world",
                         &pxIP,
                         500, pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 3000 );

    x = FreeRTOS_dnslookup( "hello" );

    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief Ensures that if an entry is expired it is zeroed
 */
void test_processDNS_CACHE_expired_entry( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;
    IPv46_Address_t pxIP;

    pxIP.xIPAddress.ulIP_IPv4 = pulIP;

    xTaskGetTickCount_ExpectAndReturn( 3000 ); /* 3 seconds */
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "world",
                         &pxIP,
                         FreeRTOS_htonl( 20 ), pdFALSE, NULL ); /* lives 20 seconds */

    xTaskGetTickCount_ExpectAndReturn( 50000 );                 /* 50 Seconds */
    x = FreeRTOS_dnslookup( "world" );

    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief Exceeding ip limit for an entry
 */
void test_processDNS_CACHE_exceed_IP_entry_limit( void )
{
    BaseType_t x;
    uint32_t pulIP = 789;
    uint32_t pulIP_arr[ ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY ] = { 123 };
    IPv46_Address_t pxIP[ ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY ], pxIP_2;
    int i;

    pxIP_2.xIs_IPv6 = 0;
    pxIP_2.xIPAddress.ulIP_IPv4 = pulIP;

    memset( pulIP_arr, 123, ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY );

    for( i = 0; i < ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY; i++ )
    {
        pxIP[ i ].xIPAddress.ulIP_IPv4 = pulIP_arr[ i ];
        pxIP[ i ].xIs_IPv6 = 0;
        xTaskGetTickCount_ExpectAndReturn( 3000 );
        FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

        FreeRTOS_dns_update( "world",
                             &pxIP[ i ],
                             400, pdFALSE, NULL );
    }

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "world",
                         &pxIP_2,
                         FreeRTOS_htonl( 400 ), pdFALSE, NULL ); /* lives 400 seconds */

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );
    x = FreeRTOS_dnslookup( "world" );

    TEST_ASSERT_EQUAL( 789, x );
}

/**
 * @brief Exceeding host limit for an entry, circles back to zero
 */
void test_processDNS_CACHE_exceed_host_entry_limit( void )
{
    BaseType_t x;
    uint32_t pulIP_arr[ ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1 ] = { 123 };
    uint32_t pulIP = 456;
    char hosts[ ipconfigDNS_CACHE_NAME_LENGTH ] = { "hello" };
    char template[] = "helloXXXXXX";
    IPv46_Address_t pxIP[ ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY + 1 ], pxIP_2;
    int i;

    pxIP_2.xIs_IPv6 = 0;
    pxIP_2.xIPAddress.ulIP_IPv4 = pulIP;

    for( i = 0; i < ipconfigDNS_CACHE_ENTRIES; i++ )
    {
        pxIP[ i ].xIPAddress.ulIP_IPv4 = pulIP_arr[ i ];
        pxIP[ i ].xIs_IPv6 = 0;
        memcpy( template, "helloXXXXXX", strlen( template ) );

        if( mkstemp( template ) != -1 )
        {
            memcpy( hosts, template, ipconfigDNS_CACHE_ENTRIES );
        }

        xTaskGetTickCount_ExpectAndReturn( 3000 );
        FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

        FreeRTOS_dns_update( hosts,
                             &pxIP[ i ],
                             FreeRTOS_htonl( 400 ), pdFALSE, NULL ); /* lives 400 seconds */
    }

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "world",
                         &pxIP_2,
                         400, pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );
    x = FreeRTOS_dnslookup( "world" );

    TEST_ASSERT_EQUAL( 456, x );
}

/**
 * @brief Exceeding dns name limit
 */
void test_processDNS_CACHE_exceed_dns_name_limit( void )
{
    BaseType_t x;
    uint32_t pulIP = 1234;
    char long_dns_name[ ipconfigDNS_CACHE_NAME_LENGTH + 3 ];
    IPv46_Address_t pxIP;

    pxIP.xIPAddress.ulIP_IPv4 = pulIP;

    memset( long_dns_name, 'a', ipconfigDNS_CACHE_NAME_LENGTH + 3 );
    long_dns_name[ ipconfigDNS_CACHE_NAME_LENGTH + 2 ] = '\0';

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( long_dns_name,
                         &pxIP,
                         400, pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 50000 );
    x = FreeRTOS_dnslookup( long_dns_name );

    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief DNS Lookup success
 */

void test_prepare_DNSLookup( void )
{
    BaseType_t x = 0U;
    BaseType_t xFamily;
    struct freertos_addrinfo * pxAddressInfo = &pucAddrBuffer[ 0 ];
    struct freertos_addrinfo ** ppxAddressInfo = ( struct freertos_addrinfo ** ) &pucAddrBuffer;
    IPv46_Address_t xAddress;
    uint32_t ulIP = 1234U;

    struct freertos_sockaddr * sockaddr = &pucSockAddrBuffer[ 0 ];

    sockaddr->sin_address.ulIP_IPv4 = ulIP;

    pxAddressInfo->ai_addr = sockaddr;
    *ppxAddressInfo = pxAddressInfo;

    xFamily = FREERTOS_AF_INET;
    xAddress.xIs_IPv6 = pdFALSE;
    xAddress.xIPAddress.ulIP_IPv4 = ulIP;

    struct freertos_addrinfo * pxAddrInfo = &pucAddrBuffer[ 1 ];

    ( void ) memset( pxAddrInfo, 0, sizeof( *pxAddrInfo ) );
    pxAddrInfo->ai_canonname = pxAddrInfo->xPrivateStorage.ucName;
    ( void ) strncpy( pxAddrInfo->xPrivateStorage.ucName, "hello", sizeof( pxAddrInfo->xPrivateStorage.ucName ) );

    pxAddrInfo->ai_addr = ( ( struct freertos_sockaddr * ) &( pxAddrInfo->xPrivateStorage.sockaddr ) );

    pxAddrInfo->ai_addr = sockaddr;
    pxAddrInfo->ai_family = FREERTOS_AF_INET4;
    pxAddrInfo->ai_addrlen = ipSIZE_OF_IPv4_ADDRESS;

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "hello",
                         &xAddress,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 5000 );
    pxNew_AddrInfo_ExpectAnyArgsAndReturn( pxAddrInfo );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );
    xDNSCache[ 0 ].xAddresses[ 0 ] = xAddress;

    x = Prepare_CacheLookup( "hello", xFamily, ppxAddressInfo );
    TEST_ASSERT_EQUAL( ulIP, x );
}


/**
 * @brief DNS Lookup fail : pxAddressInfo = NULL
 */

void test_prepare_DNSLookup2( void )
{
    BaseType_t x;
    struct freertos_addrinfo * pxAddressInfo = NULL;
    IPv46_Address_t xAddress;

    xAddress.xIs_IPv6 = pdFALSE;
    xAddress.xIPAddress.ulIP_IPv4 = ~0U;

    xTaskGetTickCount_ExpectAndReturn( 3000 ); /* 3 seconds */
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "helloman",
                         &xAddress,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL ); /* lives 3 seconds */

    xTaskGetTickCount_ExpectAndReturn( 5000 );                 /* 5 seconds */
    pxNew_AddrInfo_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    x = Prepare_CacheLookup( "helloman", FREERTOS_AF_INET, &pxAddressInfo );
    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief DNS Lookup fail : (*ppxAddressInfo) == NULL, ( *pxAddressInfo = NULL )
 */
void test_prepare_DNSLookup3( void )
{
    BaseType_t x;
    IPv46_Address_t xAddress;

    xAddress.xIs_IPv6 = pdFALSE;
    xAddress.xIPAddress.ulIP_IPv4 = ~0U;

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "helloman",
                         &xAddress,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 5000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    x = Prepare_CacheLookup( "helloman", FREERTOS_AF_INET, NULL );
    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief DNS Lookup fail : (*ppxAddressInfo) == NULL
 */
void test_prepare_DNSLookup4( void )
{
    BaseType_t x;
    IPv46_Address_t xAddress;

    xAddress.xIs_IPv6 = pdFALSE;
    xAddress.xIPAddress.ulIP_IPv4 = ~0U;

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "hello",
                         &xAddress,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 5000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    x = Prepare_CacheLookup( "hello", FREERTOS_AF_INET, NULL );
    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief DNS Lookup fail : Different entry lookup
 */
void test_prepare_DNSLookup5( void )
{
    BaseType_t x = 0U;
    BaseType_t xFamily;
    struct freertos_addrinfo ** ppxAddressInfo = ( struct freertos_addrinfo ** ) &pucAddrBuffer;
    IPv46_Address_t xAddress;

    xFamily = FREERTOS_AF_INET;
    xAddress.xIs_IPv6 = pdFALSE;

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "hello",
                         &xAddress,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 5000 );

    x = Prepare_CacheLookup( "aws", xFamily, ppxAddressInfo );
    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief DNS Lookup fail : xFamily invalid
 */
void test_prepare_DNSLookup6( void )
{
    BaseType_t x = 0U;
    BaseType_t xFamily;
    struct freertos_addrinfo ** ppxAddressInfo = NULL;
    IPv46_Address_t xAddress;

    xFamily = FREERTOS_AF_INET ^ FREERTOS_AF_INET6;
    xAddress.xIs_IPv6 = pdFALSE;

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "hello",
                         &xAddress,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL );

    x = Prepare_CacheLookup( "hello", xFamily, ppxAddressInfo );
    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief DNS Lookup success : IPv6
 */
void test_prepare_DNSLookup_IPv6( void )
{
    BaseType_t x;
    BaseType_t xFamily = FREERTOS_AF_INET6;
    struct freertos_addrinfo * pxAddressInfo = &pucAddrBuffer[ 0 ];
    struct freertos_addrinfo ** ppxAddressInfo = ( struct freertos_addrinfo ** ) &pxAddressInfo;
    IPv46_Address_t xAddress;

    xAddress.xIs_IPv6 = pdTRUE;
    memcpy( xAddress.xIPAddress.xIP_IPv6.ucBytes, "great ip address", 16 );

    *ppxAddressInfo = pxAddressInfo;

    struct freertos_addrinfo * pxAddrInfo = &pucAddrBuffer[ 1 ];

    ( void ) memset( pxAddrInfo, 0, sizeof( *pxAddrInfo ) );
    pxAddrInfo->ai_canonname = pxAddrInfo->xPrivateStorage.ucName;
    ( void ) strncpy( pxAddrInfo->xPrivateStorage.ucName, "hello", sizeof( pxAddrInfo->xPrivateStorage.ucName ) );

    pxAddrInfo->ai_addr = ( ( struct freertos_sockaddr * ) &( pxAddrInfo->xPrivateStorage.sockaddr ) );

    pxAddrInfo->ai_family = FREERTOS_AF_INET6;
    pxAddrInfo->ai_addrlen = ipSIZE_OF_IPv6_ADDRESS;

    xTaskGetTickCount_ExpectAndReturn( 3000 ); /* 3 seconds */
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "hello",
                         &xAddress,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL ); /* lives 3 seconds */

    xTaskGetTickCount_ExpectAndReturn( 5000 );                 /* 5 seconds */
    pxNew_AddrInfo_ExpectAnyArgsAndReturn( pxAddrInfo );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    x = Prepare_CacheLookup( "hello", xFamily, ppxAddressInfo );
    TEST_ASSERT_EQUAL( 1, x );
}

/**
 * @brief DNS IPv6 Lookup fail : pxAddressInfo = NULL
 */

void test_prepare_DNSLookup2_IPv6( void )
{
    BaseType_t x = 0U;
    BaseType_t xFamily;
    struct freertos_addrinfo * pxAddressInfo = NULL;
    struct freertos_addrinfo ** ppxAddressInfo;
    IPv46_Address_t xAddress;

    xFamily = FREERTOS_AF_INET6;
    xAddress.xIs_IPv6 = pdTRUE;
    memcpy( xAddress.xIPAddress.xIP_IPv6.ucBytes, "great ip address", 16 );
    ppxAddressInfo = &pxAddressInfo;

    xTaskGetTickCount_ExpectAndReturn( 3000 ); /* 3 seconds */
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "helloman",
                         &xAddress,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL ); /* lives 3 seconds */

    xTaskGetTickCount_ExpectAndReturn( 5000 );                 /* 5 seconds */
    pxNew_AddrInfo_ExpectAnyArgsAndReturn( NULL );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    x = Prepare_CacheLookup( "helloman", xFamily, ppxAddressInfo );
    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief DNS IPv6 Lookup fail : (*ppxAddressInfo) == NULL, ( *pxAddressInfo = NULL )
 */
void test_prepare_DNSLookup3_IPv6( void )
{
    BaseType_t x = 0U;
    BaseType_t xFamily;
    struct freertos_addrinfo ** ppxAddressInfo = NULL;
    IPv46_Address_t xAddress;

    xFamily = FREERTOS_AF_INET6;
    xAddress.xIs_IPv6 = pdTRUE;
    memcpy( xAddress.xIPAddress.xIP_IPv6.ucBytes, "great ip address", 16 );

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "helloman",
                         &xAddress,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 5000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    x = Prepare_CacheLookup( "helloman", xFamily, ppxAddressInfo );
    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief DNS IPv6 Lookup fail : (*ppxAddressInfo) == NULL
 */
void test_prepare_DNSLookup4_IPv6( void )
{
    BaseType_t x = 0U;
    BaseType_t xFamily;
    struct freertos_addrinfo ** ppxAddressInfo = NULL;
    IPv46_Address_t xAddress;


    xFamily = FREERTOS_AF_INET6;
    xAddress.xIs_IPv6 = pdTRUE;
    memcpy( xAddress.xIPAddress.xIP_IPv6.ucBytes, "great ip address", 16 );

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "hello",
                         &xAddress,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 5000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );


    x = Prepare_CacheLookup( "hello", xFamily, ppxAddressInfo );
    TEST_ASSERT_EQUAL( 0, x );
}

/**
 * @brief DNS IPv6 Lookup fail : Different entry lookup
 */
void test_prepare_DNSLookup5_IPv6( void )
{
    BaseType_t x = 0U;
    BaseType_t xFamily;
    struct freertos_addrinfo ** ppxAddressInfo = ( struct freertos_addrinfo ** ) &pucAddrBuffer;
    IPv46_Address_t xAddress;

    xFamily = FREERTOS_AF_INET6;
    xAddress.xIs_IPv6 = pdTRUE;

    xTaskGetTickCount_ExpectAndReturn( 3000 );
    FreeRTOS_inet_ntop_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_dns_update( "hello",
                         &xAddress,
                         FreeRTOS_htonl( 3 ), pdFALSE, NULL );

    xTaskGetTickCount_ExpectAndReturn( 5000 );

    x = Prepare_CacheLookup( "aws", xFamily, ppxAddressInfo );
    TEST_ASSERT_EQUAL( 0, x );
}
