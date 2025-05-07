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

#include "mock_task.h"
#include "mock_list.h"

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_queue.h"
#include "mock_event_groups.h"

#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IPv6.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_IP_Utils.h"
#include "mock_FreeRTOS_IPv6_Utils.h"
#include "mock_FreeRTOS_Routing.h"
#include "mock_NetworkBufferManagement.h"

#include "catch_assert.h"
#include "FreeRTOS_ND_stubs.c"
#include "FreeRTOS_ND.h"

/* ===========================  EXTERN VARIABLES  =========================== */

extern const char * pcMessageType( BaseType_t xType );

/*  The ND cache. */
extern NDCacheRow_t xNDCache[ ipconfigND_CACHE_ENTRIES ];

/* Setting IPv6 address as "fe80::7009" */
static const IPv6_Address_t xDefaultIPAddress =
{
    0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x09
};

/* IPv6 multi-cast address is ff02::. */
static const IPv6_Address_t xMultiCastIPAddress =
{
    0xff, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
};

/* Setting eIPv6_SiteLocal IPv6 address as "feC0::7009" */
static const IPv6_Address_t xSiteLocalIPAddress =
{
    0xfe, 0xC0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x09
};

/* Setting IPv6 Gateway address as "fe80::1" */
static const IPv6_Address_t xGatewayIPAddress =
{
    0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01
};

/* IPv6 default MAC address. */
static const MACAddress_t xDefaultMACAddress = { 0x22, 0x22, 0x22, 0x22, 0x22, 0x22 };

#define xHeaderSize                                   ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t ) )

/** @brief When ucAge becomes 3 or less, it is time for a new
 * neighbour solicitation.
 */
#define ndMAX_CACHE_AGE_BEFORE_NEW_ND_SOLICITATION    ( 3U )

/* =============================== Test Cases =============================== */

/**
 * @brief This function find the MAC-address of a multicast IPv6 address
 *        with a valid endpoint.
 */
void test_eNDGetCacheEntry_MulticastEndPoint( void )
{
    eARPLookupResult_t eResult;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;

    ( void ) memcpy( xIPAddress.ucBytes, xMultiCastIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdTRUE );
    vSetMultiCastIPv6MacAddress_ExpectAnyArgs();

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( NULL );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
}

/**
 * @brief This function find the MAC-address of a multicast IPv6 address
 *        with a valid endpoint.
 */
void test_eNDGetCacheEntry_Multicast_ValidEndPoint( void )
{
    NetworkEndPoint_t xEndPoint1, xEndPoint2, xEndPoint3, * pxEndPoint = &xEndPoint1;
    eARPLookupResult_t eResult;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xEndPoint1.bits.bIPv6 = 0;
    xEndPoint2.bits.bIPv6 = 1;
    xEndPoint3.bits.bIPv6 = 1;
    ( void ) memcpy( xIPAddress.ucBytes, xMultiCastIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdTRUE );
    vSetMultiCastIPv6MacAddress_ExpectAnyArgs();

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint1 );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( &xEndPoint2 );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Unknown );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( &xEndPoint3 );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
}

/**
 * @brief This function find the MAC-address of a multicast IPv6 address
 *        with a NULL endpoint.
 */
void test_eNDGetCacheEntry_Multicast_InvalidEndPoint( void )
{
    NetworkEndPoint_t ** ppxEndPoint = NULL;
    eARPLookupResult_t eResult;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    ( void ) memcpy( xIPAddress.ucBytes, xMultiCastIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdTRUE );
    vSetMultiCastIPv6MacAddress_ExpectAnyArgs();

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, ppxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address, but the entry is present on the ND Cache,
 *        with an invalid EndPoint.
 */
void test_eNDGetCacheEntry_NDCacheLookupHit_InvalidEndPoint( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t ** ppxEndPoint = NULL;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucValid = 1;

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, ppxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xNDCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( MACAddress_t ) );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address, but the entry is present on the ND Cache,
 *        with an valid EndPoint. The endpoint gets updated based on the
 *        endpoint in ND Cache.
 */
void test_eNDGetCacheEntry_NDCacheLookupHit_ValidEndPoint( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t * pxEndPoint, xEndPoint1, xEndPoint2;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memset( &xEndPoint2, 0, sizeof( NetworkEndPoint_t ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucValid = 1;
    xNDCache[ xUseEntry ].pxEndPoint = &xEndPoint2;
    pxEndPoint = &xEndPoint1;

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xNDCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL_MEMORY( pxEndPoint, &xEndPoint2, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address, ND cache lookup fails with invalid Endpoint.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_InvalidEntry( void )
{
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucValid = 0; /*Invalid Cache entry needs to be skipped */
    pxEndPoint = &xEndPoint;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address, ND cache lookup fails with invalid entry.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_InvalidEntry2( void )
{
    NetworkEndPoint_t ** ppxEndPoint = NULL, xEndPoint;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucValid = 0; /*Invalid Cache entry needs to be skipped */

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( &xEndPoint );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, ppxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address & ND cache lookup fails as Entry is valid
 *        but the MAC-address doesn't match.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_NoEntry( void )
{
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucValid = 1; /*Valid Cache entry needs to be skipped */
    pxEndPoint = &xEndPoint;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address & ND cache lookup fails to find a valid
 *        Endpoint as well as no Endpoint of type eIPv6_LinkLocal.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_NoLinkLocal( void )
{
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucValid = 1; /*Valid Cache entry needs to be skipped */
    pxEndPoint = &xEndPoint;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address which is
 *        not multi cast address & ND cache lookup fails to find a valid
 *        Endpoint but was able to find of type eIPv6_LinkLocal.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_LinkLocal( void )
{
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    pxEndPoint = &xEndPoint;

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_LinkLocal );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
}

/**
 * @brief This function find the MAC-address of an IPv6 address when
 *        there is a Cache miss but gateway has an entry in the cache.
 */
void test_eNDGetCacheEntry_NDCacheLookupHit_Gateway( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t * pxEndPoint, xEndPoint1, xEndPoint2;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    pxEndPoint = &xEndPoint2;
    ( void ) memcpy( xEndPoint1.ipv6_settings.xGatewayAddress.ucBytes, xGatewayIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xGatewayIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucValid = 1; /*Valid Cache entry needs to be skipped */
    ( void ) memcpy( xIPAddress.ucBytes, xSiteLocalIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( &xEndPoint1 );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheHit, eResult );
    TEST_ASSERT_EQUAL_MEMORY( xMACAddress.ucBytes, xNDCache[ xUseEntry ].xMACAddress.ucBytes, sizeof( MACAddress_t ) );
}

/**
 * @brief This function can't find the MAC-address of an IPv6 address when
 *        there is a Cache miss and gateway has no entry in the cache.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_Gateway( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t * pxEndPoint, xEndPoint1, xEndPoint2;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    pxEndPoint = &xEndPoint2;
    ( void ) memset( &xEndPoint1, 0, sizeof( NetworkEndPoint_t ) );
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xGatewayIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    xNDCache[ xUseEntry ].ucValid = 1; /*Valid Cache entry needs to be skipped */
    ( void ) memcpy( xIPAddress.ucBytes, xSiteLocalIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( &xEndPoint1 );

    eResult = eNDGetCacheEntry( &xIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
}

/**
 * @brief This function can't find the MAC-address of an IPv6 address when
 *        there is a Cache miss and gateway has no entry in the cache.
 */
void test_eNDGetCacheEntry_NDCacheLookupMiss_NoEP( void )
{
    MACAddress_t xMACAddress;
    NetworkEndPoint_t * pxEndPoint, xEndPoint;
    eARPLookupResult_t eResult;
    BaseType_t xUseEntry = 0;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucValid = 1; /*Valid Cache entry needs to be skipped */
    pxEndPoint = &xEndPoint;

    xIsIPv6AllowedMulticast_ExpectAnyArgsAndReturn( pdFALSE );

    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_SiteLocal );
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_FindGateWay_ExpectAnyArgsAndReturn( NULL );

    /* TODO: This function should take a const pointer; remove const cast when it does. */
    eResult = eNDGetCacheEntry( ( IPv6_Address_t * ) &xSiteLocalIPAddress, &xMACAddress, &pxEndPoint );

    TEST_ASSERT_EQUAL( eARPCacheMiss, eResult );
}

/**
 * @brief This function verified that the ip address was not found on ND cache
 *        and there was no free space to store the New Entry, hence the
 *        IP-address, MAC-address and an end-point combination was not stored.
 */
void test_vNDRefreshCacheEntry_NoMatchingEntryCacheFull( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    int i;

    ( void ) memset( xIPAddress.ucBytes, 0, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /* Filling the ND cache with non matching IP/MAC combination */
    for( i = 0; i < ipconfigND_CACHE_ENTRIES; i++ )
    {
        ( void ) memcpy( xNDCache[ i ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
        xNDCache[ i ].ucAge = 255;
        xNDCache[ i ].ucValid = pdTRUE;
    }

    /* Pass a NULL IP address which will not match.*/
    vNDRefreshCacheEntry( &xMACAddress, &xIPAddress, &xEndPoint );
}

/**
 * @brief This function verified that the ip address was not found on ND cache
 *        and there was space to store the New Entry, hence the IP-address,
 *        MAC-address and an end-point combination was stored in that location.
 */
void test_vNDRefreshCacheEntry_NoMatchingEntryAdd( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 0;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Since no matching entry will be found, 0th entry will be updated to have the below details. */
    vNDRefreshCacheEntry( &xMACAddress, &xIPAddress, &xEndPoint );

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, ( uint8_t ) ipconfigMAX_ARP_AGE );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucValid, pdTRUE );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].pxEndPoint, &xEndPoint, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function verified that the ip address was found on ND cache
 *        and the entry was refreshed at the same location.
 */
void test_vNDRefreshCacheEntry_MatchingEntryRefresh( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );
    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xNDCache[ xUseEntry ].ucValid = pdTRUE;

    /* Since a matching entry is found at xUseEntry = 1st location, the entry will be refreshed.*/
    vNDRefreshCacheEntry( &xMACAddress, &xIPAddress, &xEndPoint );

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, ( uint8_t ) ipconfigMAX_ARP_AGE );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].pxEndPoint, &xEndPoint, sizeof( NetworkEndPoint_t ) );
}

/**
 * @brief This function verifies all invalid cache entry condition.
 */
void test_vNDAgeCache_InvalidCache( void )
{
    int i;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /* Invalidate all cache entry. */
    for( i = 0; i < ipconfigND_CACHE_ENTRIES; i++ )
    {
        xNDCache[ i ].ucAge = 0;
    }

    vNDAgeCache();
}

/**
 * @brief This function wipes out the entries from ND cache
 *        when the age reaches 0.
 */
void test_vNDAgeCache_AgeZero( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1, i;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /* Invalidate all cache entry. */
    for( i = 0; i < ipconfigND_CACHE_ENTRIES; i++ )
    {
        xNDCache[ i ].ucAge = 0;
    }

    xNDCache[ xUseEntry ].ucAge = 1;
    xNDCache[ xUseEntry ].ucValid = 1;
    ( void ) memset( &xMACAddress, 0, sizeof( MACAddress_t ) );
    ( void ) memset( &xIPAddress, 0, ipSIZE_OF_IPv6_ADDRESS );

    ( void ) memcpy( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );

    vNDAgeCache();

    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    TEST_ASSERT_EQUAL_MEMORY( xNDCache[ xUseEntry ].xMACAddress.ucBytes, xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, 0 );
    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucValid, 0 );
}

/**
 * @brief This function checks the case when the entry is not yet valid,
 *        then it is waiting an ND advertisement.
 */
void test_vNDAgeCache_InvalidEntry( void )
{
    BaseType_t xUseEntry = 1;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /*Update Entry one as invalid ucValid = 0 */
    xNDCache[ xUseEntry ].ucAge = 10;
    xNDCache[ xUseEntry ].ucValid = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    vNDAgeCache();
}

/**
 * @brief This function checks the case when the entry age is
 *        less than ndMAX_CACHE_AGE_BEFORE_NEW_ND_SOLICITATION.
 *        This entry will get removed soon.
 */
void test_vNDAgeCache_ValidEntry( void )
{
    BaseType_t xUseEntry = 1;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /*Update Entry one as invalid ucValid = 0 */
    xNDCache[ xUseEntry ].ucAge = ndMAX_CACHE_AGE_BEFORE_NEW_ND_SOLICITATION;
    xNDCache[ xUseEntry ].ucValid = 1;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    vNDAgeCache();
}

/**
 * @brief This function checks the case when The age has just ticked down,
 *        with nothing to do.
 */
void test_vNDAgeCache_ValidEntryDecrement( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint1, xEndPoint2;
    BaseType_t xUseEntry = 1, xAgeDefault = 10;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /*Update Entry one as Valid entry */
    xNDCache[ xUseEntry ].ucAge = xAgeDefault;
    xNDCache[ xUseEntry ].ucValid = 1;

    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, xAgeDefault - 1 );
}

/**
 * @brief This function handles Sending out an NEIGHBOR SOLICITATION request
 *        for the IPv6 address, and fails as Endpoint is NULL.
 */

void test_vNDAgeCache_NSNullEP( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = NULL;
    BaseType_t xUseEntry = 1, xAgeDefault = 10;
    NetworkBufferDescriptor_t xNetworkBuffer;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /*Update Entry one as Valid entry */
    xNDCache[ xUseEntry ].ucAge = xAgeDefault;
    xNDCache[ xUseEntry ].ucValid = 0;
    xNDCache[ xUseEntry ].pxEndPoint = NULL;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, xAgeDefault - 1 );
}

/**
 * @brief This function handles Sending out an NEIGHBOR SOLICITATION request
 *        for the IPv6 address, and fails as pxDescriptor is NULL.
 */

void test_vNDAgeCache_NSIncorrectDataLen( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1, xAgeDefault = 10;
    NetworkBufferDescriptor_t xNetworkBuffer;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    xNetworkBuffer.xDataLength = xHeaderSize - 1;
    /*Update Entry one as Valid entry */
    xNDCache[ xUseEntry ].ucAge = xAgeDefault;
    xNDCache[ xUseEntry ].ucValid = 0;
    xNDCache[ xUseEntry ].pxEndPoint = &xEndPoint;
    xEndPoint.bits.bIPv6 = 1;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );

    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, xAgeDefault - 1 );
}

/**
 * @brief This function handles Reducing the age counter in each entry within the ND cache.
 *        Just before getting to zero, 3 times a neighbour solicitation will be sent. It also takes
 *        care of Sending out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 *        add an entry into the ND table that indicates that an ND reply is
 *        outstanding so re-transmissions can be generated.
 */

void test_vNDAgeCache_NSHappyPath( void )
{
    MACAddress_t xMACAddress;
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    BaseType_t xUseEntry = 1, xAgeDefault = 10;
    NetworkBufferDescriptor_t xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket, * pxICMPPacket = &xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = &( pxICMPPacket->xICMPHeaderIPv6 );
    uint32_t ulPayloadLength = 32U;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );

    /*Update Entry one as Valid entry */
    xNDCache[ xUseEntry ].ucAge = xAgeDefault;
    xNDCache[ xUseEntry ].ucValid = 0;
    xNDCache[ xUseEntry ].pxEndPoint = &xEndPoint;
    xEndPoint.bits.bIPv6 = 1;
    xNetworkBuffer.xDataLength = xHeaderSize;
    xNetworkBuffer.pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    vNDAgeCache();

    TEST_ASSERT_EQUAL( xNDCache[ xUseEntry ].ucAge, xAgeDefault - 1 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucVersionTrafficClass, 0x60 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.usPayloadLength, FreeRTOS_htons( ulPayloadLength ) );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucNextHeader, ipPROTOCOL_ICMP_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucHopLimit, 255 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfMessage, ipICMP_NEIGHBOR_SOLICITATION_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionType, ndICMP_SOURCE_LINK_LAYER_ADDRESS );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionLength, 1U ); /* times 8 bytes. */
}

/**
 * @brief Clear the Neighbour Discovery cache.
 */
void test_FreeRTOS_ClearND( void )
{
    NDCacheRow_t xTempNDCache[ ipconfigND_CACHE_ENTRIES ];

    /* Set xNDCache to non zero entries*/
    ( void ) memset( xNDCache, 1, sizeof( xNDCache ) );
    ( void ) memset( xTempNDCache, 0, sizeof( xTempNDCache ) );
    FreeRTOS_ClearND();

    TEST_ASSERT_EQUAL_MEMORY( xNDCache, xTempNDCache, sizeof( xNDCache ) );
}

/**
 * @brief Toggle happy path.
 */
void test_FreeRTOS_PrintNDCache( void )
{
    BaseType_t xUseEntry = 0;

    ( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
    /* First Entry added as a valid Cache Entry to be printed */
    xNDCache[ xUseEntry ].ucValid = 1;

    FreeRTOS_PrintNDCache();
}

/**
 * @brief This function handles the case when vNDSendNeighbourSolicitation
 *        fails as endpoint is NULL.
 */
void test_vNDSendNeighbourSolicitation_NULL_EP( void )
{
    IPv6_Address_t xIPAddress;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xNetworkBuffer.pxEndPoint = NULL;

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    vNDSendNeighbourSolicitation( &xNetworkBuffer, &xIPAddress );
}

/**
 * @brief This function handles the case when vNDSendNeighbourSolicitation
 *        fails as bIPv6 is not set.
 */
void test_vNDSendNeighbourSolicitation_bIPv6_NotSet( void )
{
    IPv6_Address_t xIPAddress;
    NetworkEndPoint_t xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer;

    xEndPoint.bits.bIPv6 = pdFALSE;
    xNetworkBuffer.pxEndPoint = &xEndPoint;

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    vNDSendNeighbourSolicitation( &xNetworkBuffer, &xIPAddress );
}

/**
 * @brief This function Send out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 *        add an entry into the ND table that indicates that an ND reply is
 *        outstanding so re-transmissions can be generated.
 */
void test_vNDSendNeighbourSolicitation_HappyPath( void )
{
    IPv6_Address_t xIPAddress;
    NetworkBufferDescriptor_t xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket, * pxICMPPacket = &xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = &( pxICMPPacket->xICMPHeaderIPv6 );
    NetworkEndPoint_t xEndPoint;
    uint32_t ulPayloadLength = 32U;

    xEndPoint.bits.bIPv6 = 1;
    xNetworkBuffer.pxEndPoint = &xEndPoint;
    xNetworkBuffer.xDataLength = xHeaderSize;
    xNetworkBuffer.pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    vNDSendNeighbourSolicitation( &xNetworkBuffer, &xIPAddress );

    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucVersionTrafficClass, 0x60 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.usPayloadLength, FreeRTOS_htons( ulPayloadLength ) );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucNextHeader, ipPROTOCOL_ICMP_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucHopLimit, 255 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfMessage, ipICMP_NEIGHBOR_SOLICITATION_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionType, ndICMP_SOURCE_LINK_LAYER_ADDRESS );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionLength, 1U ); /* times 8 bytes. */
}

/**
 * @brief This function handles NULL Endpoint case
 *        while sending a PING request which means
 *        No endpoint found for the target IP-address.
 */
void test_SendPingRequestIPv6_NULL_EP( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 0;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Unknown );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );


    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles case when find endpoint for
 *        pxIPAddress fails and while getting the endpoint for the
 *        same IP type bIPv6 is not set.
 */
void test_SendPingRequestIPv6_bIPv6_NotSet( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = ipconfigNETWORK_MTU;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 0;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles case when find endpoint for
 *        pxIPAddress fails and found the endpoint for the
 *        same IP type but there are no bytes to be send.
 *        uxNumberOfBytesToSend is set to 0.
 */
void test_SendPingRequestIPv6_bIPv6_NoBytesToSend( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 0;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles case when uxNumberOfBytesToSend
 *        is set to proper but there is not enough space.
 */
void test_SendPingRequestIPv6_bIPv6_NotEnoughSpace( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = ipconfigNETWORK_MTU;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );
    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles case when we do not
 *        have enough space for the Number of bytes to be send.
 */
void test_SendPingRequestIPv6_IncorrectBytesSend( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = ipconfigNETWORK_MTU;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( pxEndPoint );

    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 0U );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles failure case when network
 *        buffer returned is NULL.
 */
void test_SendPingRequestIPv6_NULL_Buffer( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 100;
    BaseType_t xReturn;

    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );


    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );


    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief This function handles sending and IPv6 ping request
 *        assert as pxEndPoint->bits.bIPv6 is not set.
 */
void test_SendPingRequestIPv6_Assert( void )
{
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer = { 0 };
    uint8_t ucEthernetBuffer[ 1500 ] = { 0 };
    IPv6_Address_t xIPAddress = { 0 };
    size_t uxNumberOfBytesToSend = 100;
    BaseType_t xReturn;
    uint16_t usSequenceNumber = 1;

    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( ucEthernetBuffer );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );


    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    xSendEventStructToIPTask_IgnoreAndReturn( pdPASS );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    /*Returns ping sequence number */
    TEST_ASSERT_EQUAL( xReturn, usSequenceNumber );
}

/**
 * @brief This function handles sending and IPv6 ping request
 *        and returning the sequence number in case of success.
 */
void test_SendPingRequestIPv6_SendToIP_Pass( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer = { 0 }, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ 1500 ] = { 0 };
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 100;
    BaseType_t xReturn;
    uint16_t usSequenceNumber = 1;

    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    xNetworkBuffer.xDataLength = sizeof( ucEthernetBuffer );
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );


    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );
    xSendEventStructToIPTask_IgnoreAndReturn( pdPASS );

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    /*Returns ping sequence number */
    TEST_ASSERT_EQUAL( xReturn, usSequenceNumber );
}

/**
 * @brief This function handles failure case while sending
 *        IPv6 ping request when sending an event to IP task fails.
 */
void test_SendPingRequestIPv6_SendToIP_Fail( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    uint8_t ucEthernetBuffer[ 1500 ] = { 0 };
    IPv6_Address_t xIPAddress;
    size_t uxNumberOfBytesToSend = 100;
    BaseType_t xReturn;
    uint16_t usSequenceNumber = 1;

    xNetworkBuffer.pucEthernetBuffer = ucEthernetBuffer;
    ( void ) memcpy( xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    pxEndPoint->bits.bIPv6 = 1;
    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAnyArgsAndReturn( NULL );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    xIPv6_GetIPType_ExpectAnyArgsAndReturn( eIPv6_Global );


    uxGetNumberOfFreeNetworkBuffers_ExpectAndReturn( 4U );
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );
    xSendEventStructToIPTask_IgnoreAndReturn( pdFAIL );
    vReleaseNetworkBufferAndDescriptor_Ignore();

    xReturn = FreeRTOS_SendPingRequestIPv6( &xIPAddress, uxNumberOfBytesToSend, 0 );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}


/**
 * @brief This function process ICMP message when endpoint is valid
 *        but the bIPv6 bit is false indicating IPv4 message.
 */
void test_prvProcessICMPMessage_IPv6_EP( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    eFrameProcessingResult_t eReturn;
    NetworkEndPoint_t xEndPoint;

    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_DEST_UNREACHABLE_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_DEST_UNREACHABLE_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_DEST_UNREACHABLE_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PACKET_TOO_BIG_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PACKET_TOO_BIG_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PACKET_TOO_BIG_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_TIME_EXCEEDED_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_TIME_EXCEEDED_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_TIME_EXCEEDED_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PARAMETER_PROBLEM_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PARAMETER_PROBLEM_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PARAMETER_PROBLEM_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_ROUTER_SOLICITATION_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_ROUTER_SOLICITATION_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_ROUTER_ADVERTISEMENT_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_ROUTER_ADVERTISEMENT_IPv6( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_ROUTER_ADVERTISEMENT_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REQUEST_IPv6 but the data size is incorrect.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REQUEST_IPv6_IncorrectSize( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    size_t uxICMPSize, uxNeededSize;
    uint16_t usICMPSize;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xICMPPacket.xIPHeader.usPayloadLength = 100;
    usICMPSize = FreeRTOS_ntohs( xICMPPacket.xIPHeader.usPayloadLength );
    uxICMPSize = ( size_t ) usICMPSize;
    uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
    /* Assign less size than expected */
    pxNetworkBuffer->xDataLength = uxICMPSize;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REQUEST_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REQUEST_IPv6_CorrectSizeAssert1( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    size_t uxICMPSize, uxNeededSize;
    uint16_t usICMPSize;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xICMPPacket.xIPHeader.usPayloadLength = 100;
    usICMPSize = FreeRTOS_ntohs( xICMPPacket.xIPHeader.usPayloadLength );
    uxICMPSize = ( size_t ) usICMPSize;
    uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
    /* Assign less size than expected */
    pxNetworkBuffer->xDataLength = uxNeededSize + 1;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REQUEST_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REQUEST_IPv6_CorrectSize( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    size_t uxICMPSize, uxNeededSize;
    uint16_t usICMPSize;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
    xICMPPacket.xIPHeader.usPayloadLength = 100;
    usICMPSize = FreeRTOS_ntohs( xICMPPacket.xIPHeader.usPayloadLength );
    uxICMPSize = ( size_t ) usICMPSize;
    uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
    /* Assign less size than expected */
    pxNetworkBuffer->xDataLength = uxNeededSize + 1;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REPLY_IPv6.
 *        It handles case where A reply was received to an outgoing
 *        ping but the payload of the reply was not correct.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REPLY_IPv6_eInvalidData( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    ICMPEcho_IPv6_t * pxICMPEchoHeader = ( ( ICMPEcho_IPv6_t * ) pxICMPHeader_IPv6 );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    size_t uxICMPSize, uxNeededSize;
    uint16_t usICMPSize;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    xICMPPacket.xIPHeader.usPayloadLength = 100;
    usICMPSize = FreeRTOS_ntohs( xICMPPacket.xIPHeader.usPayloadLength );
    uxICMPSize = ( size_t ) usICMPSize;
    uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
    /* Assign less size than expected */
    pxNetworkBuffer->xDataLength = uxICMPSize;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    vApplicationPingReplyHook_Expect( eInvalidData, pxICMPEchoHeader->usIdentifier );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_PING_REPLY_IPv6.
 *        It handles case where A reply was received to an outgoing
 *        ping but the payload of the reply was not correct.
 */
void test_prvProcessICMPMessage_IPv6_ipICMP_PING_REPLY_IPv6_eSuccess( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t * pxICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6;
    ICMPEcho_IPv6_t * pxICMPEchoHeader;
    uint8_t ucBuffer[ sizeof( ICMPPacket_IPv6_t ) + ipBUFFER_PADDING ], * pucByte;
    NetworkEndPoint_t xEndPoint;
    size_t uxDataLength;
    eFrameProcessingResult_t eReturn;

    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &ucBuffer;
    pxICMPPacket = ( ( ICMPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );
    pxICMPPacket->xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
    pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_ntohs( ipBUFFER_PADDING );
    pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( pxICMPPacket->xICMPHeaderIPv6 ) );
    pxICMPEchoHeader = ( ( ICMPEcho_IPv6_t * ) pxICMPHeader_IPv6 );
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;

    uxDataLength = ipNUMERIC_CAST( size_t, FreeRTOS_ntohs( pxICMPPacket->xIPHeader.usPayloadLength ) );
    uxDataLength = uxDataLength - sizeof( ICMPEcho_IPv6_t );

    pucByte = ( ucBuffer + sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) + sizeof( ICMPEcho_IPv6_t ) );

    ( void ) memset( pucByte, ipECHO_DATA_FILL_BYTE, uxDataLength );

    vApplicationPingReplyHook_Expect( eSuccess, pxICMPEchoHeader->usIdentifier );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_SOLICITATION_IPv6.
 *        It handles case where endpoint was not found on the network.
 */
void test_prvProcessICMPMessage_IPv6_NeighborSolicitationNullEP( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer = { 0 }, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket = { 0 };
    NetworkEndPoint_t xEndPoint = { 0 };
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    ( void ) memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = sizeof( xICMPPacket );

    FreeRTOS_InterfaceEPInSameSubnet_IPv6_ExpectAnyArgsAndReturn( NULL );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_SOLICITATION_IPv6.
 *        It handles case where when data length is less than
 *        expected.
 */
void test_prvProcessICMPMessage_IPv6_NeighborSolicitationIncorrectLen( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = 0;

    FreeRTOS_InterfaceEPInSameSubnet_IPv6_ExpectAnyArgsAndReturn( &xEndPoint );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_SOLICITATION_IPv6.
 */
void test_prvProcessICMPMessage_IPv6_NeighborSolicitation( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxICMPHeader_IPv6->ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = xHeaderSize + ipBUFFER_PADDING;
    ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( xEndPoint.xMACAddress.ucBytes, xDefaultMACAddress.ucBytes, sizeof( MACAddress_t ) );

    FreeRTOS_InterfaceEPInSameSubnet_IPv6_ExpectAnyArgsAndReturn( &xEndPoint );
    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfMessage, ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfService, 0U );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionType, ndICMP_TARGET_LINK_LAYER_ADDRESS );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionLength, 1U );
    TEST_ASSERT_EQUAL_MEMORY( pxICMPHeader_IPv6->ucOptionBytes, xEndPoint.xMACAddress.ucBytes, sizeof( MACAddress_t ) );
    TEST_ASSERT_EQUAL( xICMPPacket.xIPHeader.ucHopLimit, 255U );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6.
 *        It handles case when pxARPWaitingNetworkBuffer is NULL.
 */
void test_prvProcessICMPMessage_IPv6_NeighborAdvertisement1( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
    pxARPWaitingNetworkBuffer = NULL;


    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6.
 *        It handles case header is of ipSIZE_OF_IPv4_HEADER type.
 */
void test_prvProcessICMPMessage_IPv6_NeighborAdvertisement2( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    NetworkBufferDescriptor_t xARPWaitingNetworkBuffer;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;

    pxARPWaitingNetworkBuffer = &xARPWaitingNetworkBuffer;
    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv4_HEADER );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6.
 *        This verifies a case 'pxARPWaitingNetworkBuffer' was
 *        not waiting for this new address look-up.
 */
void test_prvProcessICMPMessage_IPv6_NeighborAdvertisement3( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    NetworkBufferDescriptor_t xARPWaitingNetworkBuffer;
    IPPacket_IPv6_t xIPPacket;
    IPHeader_IPv6_t * pxIPHeader = &( xIPPacket.xIPHeader );

    pxARPWaitingNetworkBuffer = &xARPWaitingNetworkBuffer;
    pxARPWaitingNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xIPPacket;
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;

    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv6_HEADER );

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6.
 *        This verifies a case where a packet is handled as a new
 *        incoming IP packet when a neighbour advertisement has been received,
 *        and 'pxARPWaitingNetworkBuffer' was waiting for this new address look-up.
 */
void test_prvProcessICMPMessage_IPv6_NeighborAdvertisement4( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    NetworkBufferDescriptor_t xARPWaitingNetworkBuffer;
    IPPacket_IPv6_t xIPPacket;
    IPHeader_IPv6_t * pxIPHeader = &( xIPPacket.xIPHeader );

    pxARPWaitingNetworkBuffer = &xARPWaitingNetworkBuffer;
    pxARPWaitingNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xIPPacket;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
    ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( pxIPHeader->xSourceAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );


    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv6_HEADER );
    xSendEventStructToIPTask_IgnoreAndReturn( pdFAIL );
    vReleaseNetworkBufferAndDescriptor_Ignore();
    vIPSetARPResolutionTimerEnableState_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    TEST_ASSERT_EQUAL( pxARPWaitingNetworkBuffer, NULL );
}

/**
 * @brief This function process ICMP message when message type is
 *        ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6.
 *        This verifies a case where a packet is handled as a new
 *        incoming IP packet when a neighbour advertisement has been received,
 *        and 'pxARPWaitingNetworkBuffer' was waiting for this new address look-up.
 */
void test_prvProcessICMPMessage_IPv6_NeighborAdvertisement5( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;
    NetworkBufferDescriptor_t xARPWaitingNetworkBuffer;
    IPPacket_IPv6_t xIPPacket;
    IPHeader_IPv6_t * pxIPHeader = &( xIPPacket.xIPHeader );

    pxARPWaitingNetworkBuffer = &xARPWaitingNetworkBuffer;
    pxARPWaitingNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xIPPacket;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
    ( void ) memcpy( pxICMPHeader_IPv6->xIPv6Address.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    ( void ) memcpy( pxIPHeader->xSourceAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );


    uxIPHeaderSizePacket_IgnoreAndReturn( ipSIZE_OF_IPv6_HEADER );
    xSendEventStructToIPTask_IgnoreAndReturn( pdPASS );
    vIPSetARPResolutionTimerEnableState_ExpectAnyArgs();

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
    TEST_ASSERT_EQUAL( pxARPWaitingNetworkBuffer, NULL );
}

/**
 * @brief This function process ICMP message when message type is incorrect.
 */
void test_prvProcessICMPMessage_IPv6_Default( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkEndPoint_t xEndPoint;
    eFrameProcessingResult_t eReturn;

    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    xICMPPacket.xICMPHeaderIPv6.ucTypeOfMessage = 0;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( eReturn, eReleaseBuffer );
}

/**
 * @brief This case validates failure in sending
 *        Neighbour Advertisement message because of
 *        failure in getting network buffer.
 */
void test_FreeRTOS_OutputAdvertiseIPv6_Default( void )
{
    NetworkEndPoint_t xEndPoint;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    FreeRTOS_OutputAdvertiseIPv6( &xEndPoint );
}

/**
 * @brief This case validates failure in sending
 *        Neighbour Advertisement message because of
 *        interface being NULL.
 */
void test_FreeRTOS_OutputAdvertiseIPv6_Assert( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;

    xEndPoint.pxNetworkInterface = NULL;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );

    catch_assert( FreeRTOS_OutputAdvertiseIPv6( &xEndPoint ) );
}

/**
 * @brief This case validates sending out
 *        Neighbour Advertisement message.
 */
void test_FreeRTOS_OutputAdvertiseIPv6_HappyPath( void )
{
    NetworkBufferDescriptor_t xNetworkBuffer, * pxNetworkBuffer = &xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket, * pxICMPPacket = &xICMPPacket;
    ICMPHeader_IPv6_t * pxICMPHeader_IPv6 = ( ( ICMPHeader_IPv6_t * ) &( pxICMPPacket->xICMPHeaderIPv6 ) );
    NetworkEndPoint_t xEndPoint;
    NetworkInterface_t xInterface;

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    xEndPoint.pxNetworkInterface = &xInterface;
    ( void ) memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    xEndPoint.pxNetworkInterface->pfOutput = &NetworkInterfaceOutputFunction_Stub;

    pxICMPHeader_IPv6->usChecksum = 0U;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( pxNetworkBuffer );
    usGenerateProtocolChecksum_IgnoreAndReturn( ipCORRECT_CRC );

    FreeRTOS_OutputAdvertiseIPv6( &xEndPoint );

    TEST_ASSERT_EQUAL( pxICMPPacket->xEthernetHeader.usFrameType, ipIPv6_FRAME_TYPE );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.ucVersionTrafficClass, 0x60 );
    TEST_ASSERT_EQUAL( pxICMPPacket->xIPHeader.usPayloadLength, FreeRTOS_htons( sizeof( ICMPHeader_IPv6_t ) ) );
    TEST_ASSERT_EQUAL_MEMORY( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucTypeOfMessage, ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6 );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionType, ndICMP_TARGET_LINK_LAYER_ADDRESS );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->ucOptionLength, 1 );
    TEST_ASSERT_EQUAL_MEMORY( pxICMPHeader_IPv6->xIPv6Address.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, sizeof( pxICMPHeader_IPv6->xIPv6Address.ucBytes ) );
    TEST_ASSERT_EQUAL( pxICMPHeader_IPv6->usChecksum, 0 );
}

/**
 * @brief Create an IPv6 address, based on a prefix.
 *        with the bits after the prefix having random value.
 *        But fails to get the random number.
 */
void test_FreeRTOS_CreateIPv6Address_RandomFail( void )
{
    IPv6_Address_t * pxIPAddress, * pxPrefix;
    size_t uxPrefixLength;
    BaseType_t xDoRandom = pdTRUE, xReturn;

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );

    xReturn = FreeRTOS_CreateIPv6Address( pxIPAddress, pxPrefix, uxPrefixLength, xDoRandom );

    TEST_ASSERT_EQUAL( xReturn, pdFAIL );
}

/**
 * @brief Create an IPv6 address, based on a prefix.
 *        with the bits after the prefix having random value
 *        but incorrect prefix length.
 */
void test_FreeRTOS_CreateIPv6Address_Assert1( void )
{
    IPv6_Address_t * pxIPAddress, * pxPrefix;
    size_t uxPrefixLength = 0;
    BaseType_t xDoRandom = pdTRUE, xReturn, xIndex;

    for( xIndex = 0; xIndex < 4; xIndex++ )
    {
        xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    }

    catch_assert( FreeRTOS_CreateIPv6Address( pxIPAddress, pxPrefix, uxPrefixLength, xDoRandom ) );
}

/**
 * @brief Create an IPv6 address, based on a prefix.
 *        with the bits after the prefix having random value
 *        but incorrect prefix length and xDoRandom is 0.
 */
void test_FreeRTOS_CreateIPv6Address_Assert2( void )
{
    IPv6_Address_t xIPAddress, xPrefix;
    /* The maximum allowed prefix length was increased to 128 because of the loopback address. */
    size_t uxPrefixLength = 8U * ipSIZE_OF_IPv6_ADDRESS + 1;
    BaseType_t xDoRandom = pdFALSE, xReturn, xIndex;

    catch_assert( FreeRTOS_CreateIPv6Address( &xIPAddress, &xPrefix, uxPrefixLength, xDoRandom ) );
}

/**
 * @brief Create an IPv6 address, based on a prefix.
 *        with the bits after the prefix having random value.
 */
void test_FreeRTOS_CreateIPv6Address_Pass1( void )
{
    IPv6_Address_t xIPAddress, xPrefix;
    size_t uxPrefixLength = 8U;
    BaseType_t xDoRandom = pdTRUE, xReturn, xIndex;

    for( xIndex = 0; xIndex < 4; xIndex++ )
    {
        xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    }

    xReturn = FreeRTOS_CreateIPv6Address( &xIPAddress, &xPrefix, uxPrefixLength, xDoRandom );

    TEST_ASSERT_EQUAL( xReturn, pdPASS );
}

/**
 * @brief Create an IPv6 address, based on a prefix.
 *        with the bits after the prefix having random value
 *        and uxPrefixLength is not a multiple of 8.
 */
void test_FreeRTOS_CreateIPv6Address_Pass2( void )
{
    IPv6_Address_t xIPAddress, xPrefix;
    size_t uxPrefixLength = 7;
    BaseType_t xDoRandom = pdTRUE, xReturn, xIndex;

    for( xIndex = 0; xIndex < 4; xIndex++ )
    {
        xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    }

    xReturn = FreeRTOS_CreateIPv6Address( &xIPAddress, &xPrefix, uxPrefixLength, xDoRandom );

    TEST_ASSERT_EQUAL( xReturn, pdPASS );
}

void test_FreeRTOS_CreateIPv6Address_Pass3( void ) /*CHECK if needed */
{
    IPv6_Address_t xIPAddress, xPrefix;
    size_t uxPrefixLength = 127;
    BaseType_t xDoRandom = pdTRUE, xReturn, xIndex;

    for( xIndex = 0; xIndex < 4; xIndex++ )
    {
        xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    }

    xReturn = FreeRTOS_CreateIPv6Address( &xIPAddress, &xPrefix, uxPrefixLength, xDoRandom );

    TEST_ASSERT_EQUAL( xReturn, pdPASS );
}

/**
 * @brief Cover all the pcMessageType print
 *        scenario.
 */
void test_pcMessageType_All( void )
{
    BaseType_t xType;

    xType = ipICMP_DEST_UNREACHABLE_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_PACKET_TOO_BIG_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_TIME_EXCEEDED_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_PARAMETER_PROBLEM_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_PING_REQUEST_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_PING_REPLY_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_ROUTER_SOLICITATION_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_ROUTER_ADVERTISEMENT_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
    ( void ) pcMessageType( xType );

    xType = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6 + 1;
    ( void ) pcMessageType( xType );
}
