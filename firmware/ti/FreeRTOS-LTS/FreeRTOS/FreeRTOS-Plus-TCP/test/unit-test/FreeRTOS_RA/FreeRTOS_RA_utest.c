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

#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_NetworkBufferManagement.h"

#include "catch_assert.h"
#include "FreeRTOS_ND.h"
#include "FreeRTOS_RA_stubs.c"

/* ================================  TYPES  ================================= */

#include "pack_struct_start.h"
struct xEthernetPacketICMPv6RouterAdvertisementPrefixOption
{
    EthernetHeader_t xEthernetHeader;              /*  0 + 14 = 14 */
    IPHeader_IPv6_t xIPHeader;                     /* 14 + 40 = 54 */
    ICMPRouterAdvertisement_IPv6_t xAdvertisement; /* 54 + 16 = 70 */
    ICMPPrefixOption_IPv6_t xPrefixOption;         /* 70 + 32 = 102 */
}
#include "pack_struct_end.h"
typedef struct xEthernetPacketICMPv6RouterAdvertisementPrefixOption EthernetPacketICMPv6RouterAdvertisementPrefixOption_t;

/* ===========================  EXTERN VARIABLES  =========================== */

/** The default value for the IPv6-field 'ucVersionTrafficClass'. */
#define raDEFAULT_VERSION_TRAFFIC_CLASS     0x60U
/** The default value for the IPv6-field 'ucHopLimit'. */
#define raDEFAULT_HOP_LIMIT                 255U

#define raHeaderBytesRS                     ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) )
#define raHeaderBytesRA                     ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterAdvertisement_IPv6_t ) )

/* Define an option length to be used in all test cases */
#define raPrefixOptionlen                   8

/** @brief Options that can be sent in a ROuter Advertisement packet. */
#define ndICMP_SOURCE_LINK_LAYER_ADDRESS    1
#define ndICMP_TARGET_LINK_LAYER_ADDRESS    2
#define ndICMP_PREFIX_INFORMATION           3
#define ndICMP_REDIRECTED_HEADER            4
#define ndICMP_MTU_OPTION                   5

#define eRAStateUnkown                      7

/* Setting IPv6 address as "fe80::7009" */
const IPv6_Address_t xDefaultIPAddress =
{
    0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x70, 0x09
};

/* =============================== Test Cases =============================== */

/**
 * @brief This function verify sending an Router Solicitation ICMPv6
 *        message With a NULL Endpoint.
 */
void test_vNDSendRouterSolicitation_NullEndpoint( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    IPv6_Address_t * pxIPAddress;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = NULL;

    catch_assert( vNDSendRouterSolicitation( pxNetworkBuffer, pxIPAddress ) );
}

/**
 * @brief This function verify sending an Router Solicitation ICMPv6 message
 *        With a bIPv6 not set in Endpoint.
 */
void test_vNDSendRouterSolicitation_FalsebIPv6( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPv6_Address_t * pxIPAddress, xIPAddress;

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    xEndPoint.bits.bIPv6 = pdFALSE_UNSIGNED;

    catch_assert( vNDSendRouterSolicitation( pxNetworkBuffer, pxIPAddress ) );
}

/**
 * @brief This function verify sending an Router Solicitation ICMPv6 message
 *        And RA was not able to find a Link-local address.
 */
void test_vNDSendRouterSolicitation_xHasLocal0( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPv6_Address_t xIPAddress;
    ICMPPacket_IPv6_t * pxICMPPacket, xICMPPacket;
    IPHeader_IPv6_t xIPHeader;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xIPHeader, 0, sizeof( IPHeader_IPv6_t ) );
    pxNetworkBuffer = &xNetworkBuffer;
    pxICMPPacket = &xICMPPacket;
    pxNetworkBuffer->xDataLength = raHeaderBytesRS - 1;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) ( uint8_t * ) &xICMPPacket;
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxICMPPacket->xIPHeader = xIPHeader;

    memset( &xEndPoint.ipv6_settings, 0, sizeof( IPV6Parameters_t ) );
    memset( &pxICMPPacket->xIPHeader, 0, sizeof( IPHeader_IPv6_t ) );

    /* Link-Local unicast address prefixed FE80::/10 */
    xEndPoint.ipv6_settings.xIPAddress.ucBytes[ 0 ] = 0xfeU;

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vNDSendRouterSolicitation( pxNetworkBuffer, &xIPAddress );
}

/**
 * @brief This function verify sending an Router Solicitation ICMPv6 message
 *        And RA was able to find a Link-local address.
 */
void test_vNDSendRouterSolicitation_xHasLocal1( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPv6_Address_t xIPAddress;
    ICMPPacket_IPv6_t * pxICMPPacket, xICMPPacket;
    IPHeader_IPv6_t xIPHeader;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xIPHeader, 0, sizeof( IPHeader_IPv6_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxICMPPacket = &xICMPPacket;
    pxNetworkBuffer->xDataLength = raHeaderBytesRS - 1;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) ( uint8_t * ) &xICMPPacket;
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxICMPPacket->xIPHeader = xIPHeader;

    memset( &xEndPoint.ipv6_settings, 0, sizeof( IPV6Parameters_t ) );
    memset( &pxICMPPacket->xIPHeader, 0, sizeof( IPHeader_IPv6_t ) );

    /* Link-Local unicast address prefixed FE80::/10 */
    xEndPoint.ipv6_settings.xIPAddress.ucBytes[ 0 ] = 0xfeU;
    xEndPoint.ipv6_settings.xIPAddress.ucBytes[ 1 ] = 0x80U;

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vNDSendRouterSolicitation( pxNetworkBuffer, &xIPAddress );
}

/**
 * @brief This function verify sending an Router Solicitation ICMPv6 message
 *        With a pxDescriptor being NULL.
 */
void test_vNDSendRouterSolicitation_NullDesc( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPv6_Address_t xIPAddress;
    ICMPPacket_IPv6_t * pxICMPPacket, xICMPPacket;
    IPHeader_IPv6_t xIPHeader;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xIPHeader, 0, sizeof( IPHeader_IPv6_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxICMPPacket = &xICMPPacket;
    pxNetworkBuffer->xDataLength = raHeaderBytesRS - 1;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) ( uint8_t * ) &xICMPPacket;
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxICMPPacket->xIPHeader = xIPHeader;

    memset( &xEndPoint.ipv6_settings, 0, sizeof( IPV6Parameters_t ) );
    memset( &pxICMPPacket->xIPHeader, 0, sizeof( IPHeader_IPv6_t ) );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );

    vReleaseNetworkBufferAndDescriptor_Expect( pxNetworkBuffer );

    vNDSendRouterSolicitation( pxNetworkBuffer, &xIPAddress );
}

/**
 * @brief This function verify successfully sending an
 *        ICMPv6 message of the type: Router Solicitation
 */
void test_vNDSendRouterSolicitation_HappyPath( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    IPv6_Address_t xIPAddress;
    ICMPPacket_IPv6_t * pxICMPPacket, xICMPPacket;
    IPHeader_IPv6_t xIPHeader;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xIPHeader, 0, sizeof( IPHeader_IPv6_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxICMPPacket = &xICMPPacket;
    pxNetworkBuffer->xDataLength = raHeaderBytesRS + 1;
    pxNetworkBuffer->pxEndPoint = &xEndPoint;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) ( uint8_t * ) &xICMPPacket;
    xEndPoint.bits.bIPv6 = pdTRUE_UNSIGNED;
    pxICMPPacket->xIPHeader = xIPHeader;

    memset( &xEndPoint.ipv6_settings, 0, sizeof( IPV6Parameters_t ) );
    memset( &pxICMPPacket->xIPHeader, 0, sizeof( IPHeader_IPv6_t ) );

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC );
    vReturnEthernetFrame_ExpectAnyArgs();

    vNDSendRouterSolicitation( pxNetworkBuffer, &xIPAddress );

    TEST_ASSERT_EQUAL( raDEFAULT_VERSION_TRAFFIC_CLASS, pxICMPPacket->xIPHeader.ucVersionTrafficClass );
    TEST_ASSERT_EQUAL( FreeRTOS_htons( sizeof( ICMPRouterSolicitation_IPv6_t ) ), pxICMPPacket->xIPHeader.usPayloadLength );
    TEST_ASSERT_EQUAL( ipPROTOCOL_ICMP_IPv6, pxICMPPacket->xIPHeader.ucNextHeader );
    TEST_ASSERT_EQUAL( raDEFAULT_HOP_LIMIT, pxICMPPacket->xIPHeader.ucHopLimit );
}

/**
 * @brief This function verify received Neighbour Advertisement message
 *        without EndPoint.
 */
void test_vReceiveNA_NoEndPoint( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    ICMPPacket_IPv6_t xICMPPacket;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );

    pxNetworkBuffer = &xNetworkBuffer;

    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) ( uint8_t * ) &xICMPPacket;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( NULL );

    vReceiveNA( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0, xEndPoint.xRAData.bits.bIPAddressInUse );
}

/**
 * @brief This function verify received Neighbour Advertisement message
 *        to see that the chosen IP-address is not in use.
 */
void test_vReceiveNA_bIPAddressNotInUse1( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    ICMPPacket_IPv6_t xICMPPacket;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) ( uint8_t * ) &xICMPPacket;
    xEndPoint.bits.bWantRA = pdFALSE_UNSIGNED;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );

    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );

    vReceiveNA( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0, xEndPoint.xRAData.bits.bIPAddressInUse );
}

/**
 * @brief This function verify received Neighbour Advertisement message
 *        to see that the chosen IP-address is not in use.
 */
void test_vReceiveNA_bIPAddressNotInUse2( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    ICMPPacket_IPv6_t xICMPPacket;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) ( uint8_t * ) &xICMPPacket;
    xEndPoint.bits.bWantRA = pdTRUE_UNSIGNED;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );

    vReceiveNA( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0, xEndPoint.xRAData.bits.bIPAddressInUse );
}

/**
 * @brief This function verify received Neighbour Advertisement message
 *        to see that the chosen IP-address is not in use.
 */
void test_vReceiveNA_bIPAddressNotInUse3( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    ICMPPacket_IPv6_t xICMPPacket;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) ( uint8_t * ) &xICMPPacket;
    xEndPoint.bits.bWantRA = pdTRUE_UNSIGNED;
    xEndPoint.xRAData.eRAState = eRAStateIPWait;

    memset( xEndPoint.ipv6_settings.xIPAddress.ucBytes, 0, ipSIZE_OF_IPv6_ADDRESS );
    memset( xICMPPacket.xICMPHeaderIPv6.xIPv6Address.ucBytes, 1, ipSIZE_OF_IPv6_ADDRESS );
    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );

    vReceiveNA( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0, xEndPoint.xRAData.bits.bIPAddressInUse );
}

/**
 * @brief This function verify received Neighbour Advertisement message
 *        to see that the chosen IP-address is not in use.
 */
void test_vReceiveNA_bIPAddressNotInUse4( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    ICMPPacket_IPv6_t xICMPPacket;
    IPv6_Address_t xIPAddress;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) ( uint8_t * ) &xICMPPacket;
    xEndPoint.xRAData.eRAState = eRAStateWait;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );

    vReceiveNA( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( 0, xEndPoint.xRAData.bits.bIPAddressInUse );
}

/**
 * @brief This function verify received Neighbour Advertisement message
 *        to see that the chosen IP-address is already in use.
 */
void test_vReceiveNA_bIPAddressInUse( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint;
    ICMPPacket_IPv6_t xICMPPacket;
    IPv6_Address_t xIPAddress;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) ( uint8_t * ) &xICMPPacket;
    xEndPoint.bits.bWantRA = pdTRUE_UNSIGNED;
    xEndPoint.xRAData.eRAState = eRAStateIPWait;

    /* Setting IPv6 address as "fe80::7009" */
    memcpy( &xIPAddress, &xDefaultIPAddress, sizeof( IPv6_Address_t ) );

    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( xICMPPacket.xICMPHeaderIPv6.xIPv6Address.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( &xEndPoint );

    vDHCP_RATimerReload_ExpectAnyArgs();

    FreeRTOS_NextEndPoint_ExpectAnyArgsAndReturn( NULL );

    vReceiveNA( pxNetworkBuffer );

    TEST_ASSERT_EQUAL( 1, xEndPoint.xRAData.bits.bIPAddressInUse );
}

/**
 * @brief This function verify the handling
 *        of incorrect data length.
 */
void test_vReceiveRA_IncorrectDataLength( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    /* Setting incorrect data length */
    pxNetworkBuffer->xDataLength = raHeaderBytesRA - 1;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify the handling
 *        of Advertisement Lifetime as zero.
 */
void test_vReceiveRA_ZeroAdvertisementLifetime( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;
    ICMPPacket_IPv6_t xICMPPacket;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + 1;

    pxAdvertisement = ( ( ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = 0;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify the handling
 *        of NULL pxInterface.
 */
void test_vReceiveRA_NullpxInterface( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;
    ICMPPacket_IPv6_t xICMPPacket;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + 1;
    pxNetworkBuffer->pxInterface = NULL;

    pxAdvertisement = ( ( ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = 1;

    catch_assert( vReceiveRA( pxNetworkBuffer ) );
}

/**
 * @brief This function verify NULL ICMP prefix
 *        option pointer as no options field.
 */
void test_vReceiveRA_NullICMPPrefix( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;
    NetworkInterface_t xInterface;
    ICMPPacket_IPv6_t xICMPPacket;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA;
    pxNetworkBuffer->pxInterface = &xInterface;

    pxAdvertisement = ( ( ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = 1;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present with data length as zero.
 */
void test_vReceiveRA_NullICMPPrefix_ZeroOptionLength( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    /* Data Length to be less than expected */
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + 10;
    uxNeededSize = raHeaderBytesRA;

    pxAdvertisement = ( ( ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = 1;

    pxPrefixOption = ( ICMPPrefixOption_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_PREFIX_INFORMATION;
    /* Number of Options present - 8-byte blocks. */
    uxOptionsLength = 2;
    pxPrefixOption->ucLength = 0;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present but data length less than the
 *        required data length by option field.
 */
void test_vReceiveRA_NullICMPPrefix_NotEnoughBytes( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    /* Data Length to be less than expected */
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + 10;
    uxNeededSize = raHeaderBytesRA;

    pxAdvertisement = ( ( ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = 1;

    pxPrefixOption = ( ICMPPrefixOption_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_PREFIX_INFORMATION;
    /* Number of Options present - 8-byte blocks. */
    uxOptionsLength = 2;
    pxPrefixOption->ucLength = uxOptionsLength;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_SOURCE_LINK_LAYER_ADDRESS.
 */
void test_vReceiveRA_ValidICMPPrefix_Option1( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xInterface, 0, sizeof( NetworkInterface_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + raPrefixOptionlen;
    uxNeededSize = raHeaderBytesRA;

    pxAdvertisement = ( ( ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = 1;

    pxPrefixOption = ( ICMPPrefixOption_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_SOURCE_LINK_LAYER_ADDRESS;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_TARGET_LINK_LAYER_ADDRESS.
 */
void test_vReceiveRA_ValidICMPPrefix_Option2( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    NetworkEndPoint_t xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xInterface, 0, sizeof( NetworkInterface_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + raPrefixOptionlen;
    uxNeededSize = raHeaderBytesRA;

    pxAdvertisement = ( ( ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = 1;

    pxPrefixOption = ( ICMPPrefixOption_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_TARGET_LINK_LAYER_ADDRESS;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_PREFIX_INFORMATION.
 */
void test_vReceiveRA_ValidICMPPrefix_Option3( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    NetworkEndPoint_t xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xInterface, 0, sizeof( NetworkInterface_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + raPrefixOptionlen;
    uxNeededSize = raHeaderBytesRA;

    pxAdvertisement = ( ( ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = 1;

    pxPrefixOption = ( ICMPPrefixOption_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_PREFIX_INFORMATION;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;


    xEndPoint.bits.bWantRA = pdFALSE_UNSIGNED;

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    vReceiveRA( pxNetworkBuffer );
}


/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_TARGET_LINK_LAYER_ADDRESS.
 */
void test_vReceiveRA_ValidICMPPrefix_Option4( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xInterface, 0, sizeof( NetworkInterface_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + raPrefixOptionlen;
    uxNeededSize = raHeaderBytesRA;

    pxAdvertisement = ( ( ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = 1;

    pxPrefixOption = ( ICMPPrefixOption_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_REDIRECTED_HEADER;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_TARGET_LINK_LAYER_ADDRESS.
 */
void test_vReceiveRA_ValidICMPPrefix_Option5( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xInterface, 0, sizeof( NetworkInterface_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + raPrefixOptionlen;
    uxNeededSize = raHeaderBytesRA;
    pxAdvertisement = ( ( ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = pdTRUE_UNSIGNED;

    pxPrefixOption = ( ICMPPrefixOption_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = ndICMP_MTU_OPTION;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    ulChar2u32_ExpectAnyArgsAndReturn( 0x12345678 );

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present as default case.
 */
void test_vReceiveRA_ValidICMPPrefix_Option6( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xInterface, 0, sizeof( NetworkInterface_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + raPrefixOptionlen;
    uxNeededSize = raHeaderBytesRA;
    pxAdvertisement = ( ( ICMPRouterAdvertisement_IPv6_t * ) &( xICMPPacket.xICMPHeaderIPv6 ) );
    pxAdvertisement->usLifetime = pdTRUE_UNSIGNED;

    pxPrefixOption = ( ICMPPrefixOption_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = eRAStateUnkown;

    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify ICMP prefix option with
 *        options present as ndICMP_TARGET_LINK_LAYER_ADDRESS.
 */
void test_vReceiveRA_ValidICMPPrefix_IncorrectOption( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    ICMPPacket_IPv6_t xICMPPacket;
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint;
    size_t uxIndex = 0U, uxNeededSize, uxOptionsLength;
    uint8_t * pucBytes;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xInterface, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkInterface_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + raPrefixOptionlen;
    uxNeededSize = raHeaderBytesRA;

    pxPrefixOption = ( ICMPPrefixOption_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
    pxPrefixOption->ucType = 0;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify vReceiveRA success case.
 */
void test_vReceiveRA_vRAProccess( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    EthernetPacketICMPv6RouterAdvertisementPrefixOption_t xICMPPacket;
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( xICMPPacket ) );
    memset( &xInterface, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + raPrefixOptionlen;
    pxAdvertisement = &xICMPPacket.xAdvertisement;
    pxAdvertisement->usLifetime = pdTRUE_UNSIGNED;

    pxPrefixOption = &xICMPPacket.xPrefixOption;
    pxPrefixOption->ucType = ndICMP_PREFIX_INFORMATION;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;

    pxEndPoint->bits.bWantRA = pdTRUE_UNSIGNED;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    vReceiveRA( pxNetworkBuffer );
}

/**
 * @brief This function verify vReceiveRA success case.
 */
void test_vReceiveRA_vRAProcess( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    EthernetPacketICMPv6RouterAdvertisementPrefixOption_t xICMPPacket;
    NetworkInterface_t xInterface;
    NetworkEndPoint_t xEndPoint, * pxEndPoint = &xEndPoint;
    ICMPPrefixOption_IPv6_t * pxPrefixOption;
    ICMPRouterAdvertisement_IPv6_t * pxAdvertisement;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( xICMPPacket ) );
    memset( &xInterface, 0, sizeof( NetworkInterface_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;
    pxNetworkBuffer->pxInterface = &xInterface;
    pxNetworkBuffer->xDataLength = raHeaderBytesRA + raPrefixOptionlen;
    pxAdvertisement = &xICMPPacket.xAdvertisement;
    pxAdvertisement->usLifetime = pdTRUE_UNSIGNED;

    pxPrefixOption = &xICMPPacket.xPrefixOption;
    pxPrefixOption->ucType = ndICMP_PREFIX_INFORMATION;
    /* Only 1 option */
    pxPrefixOption->ucLength = 1;


    pxEndPoint->bits.bWantRA = pdTRUE_UNSIGNED;
    pxEndPoint->xRAData.eRAState = eRAStateWait;

    FreeRTOS_FirstEndPoint_ExpectAnyArgsAndReturn( pxEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_ExpectAnyArgs();

    vReceiveRA( pxNetworkBuffer );


    TEST_ASSERT_EQUAL( pxEndPoint->ipv6_settings.uxPrefixLength, pxPrefixOption->ucPrefixLength );
    TEST_ASSERT_EQUAL( pdTRUE_UNSIGNED, pxEndPoint->xRAData.bits.bRouterReplied );
    TEST_ASSERT_EQUAL( 0, pxEndPoint->xRAData.uxRetryCount );
    TEST_ASSERT_EQUAL( FreeRTOS_ntohl( pxPrefixOption->ulPreferredLifeTime ), pxEndPoint->xRAData.ulPreferredLifeTime );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxEndPoint->xRAData.bits.bIPAddressInUse );
    TEST_ASSERT_EQUAL( eRAStateIPWait, pxEndPoint->xRAData.eRAState );
}

/**
 *  @brief This function verify RA state machine
 *         with RA NULL endpoint.
 */
void test_vRAProcess_NullEndPoint( void )
{
    NetworkEndPoint_t * pxEndPoint = NULL;
    IPv6_Address_t xIPAddress;

    catch_assert( vRAProcess( pdTRUE, pxEndPoint ) );
}

/**
 *  @brief This function verify RA state machine with RA wait state
 *         as eRAStateApply {Set during RA_Init}
 *         And failed to get network buffer.
 */
void test_vRAProcess_eRAStateApply1( void )
{
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );

    pxEndPoint = &xEndPoint;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_ExpectAnyArgs();

    /* pdTRUE for vRAProcessInit */
    vRAProcess( pdTRUE, &xEndPoint );

    TEST_ASSERT_EQUAL( eRAStateWait, xEndPoint.xRAData.eRAState );
}

/**
 *  @brief This function verify RA state machine with RA wait state as
 *         eRAStateApply {Set during RA_Init}
 *         And Send an ICMPv6 message of the type: Router Solicitation.
 */
void test_vRAProcess_eRAStateApply2( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;
    ICMPPacket_IPv6_t * pxICMPPacket, xICMPPacket;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint = &xEndPoint;
    pxNetworkBuffer = &xNetworkBuffer;

    pxICMPPacket = &xICMPPacket;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxEndPoint->bits.bIPv6 = pdTRUE_UNSIGNED;

    pxGetNetworkBufferWithDescriptor_ExpectAndReturn( raHeaderBytesRS, 0, &xNetworkBuffer );
    FreeRTOS_FirstEndPoint_IgnoreAndReturn( &xEndPoint );
    FreeRTOS_NextEndPoint_IgnoreAndReturn( NULL );
    pxDuplicateNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    /*usGenerateProtocolChecksum_ExpectAnyArgsAndReturn( ipCORRECT_CRC ); */
    /*vReturnEthernetFrame_ExpectAnyArgs(); */

    vReleaseNetworkBufferAndDescriptor_Expect( &xNetworkBuffer );

    vDHCP_RATimerReload_ExpectAnyArgs();

    /* pdFALSE for vRAProcessInit */
    vRAProcess( pdTRUE, &xEndPoint );

    TEST_ASSERT_EQUAL( eRAStateWait, xEndPoint.xRAData.eRAState );
}

/**
 *  @brief This function verify RA state machine with RA wait state as
 *         eRAStateLease.
 */
void test_vRAProcess_eRAStateLease( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;
    ICMPPacket_IPv6_t * pxICMPPacket, xICMPPacket;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint = &xEndPoint;
    pxNetworkBuffer = &xNetworkBuffer;

    pxICMPPacket = &xICMPPacket;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    pxEndPoint->bits.bIPv6 = pdTRUE_UNSIGNED;
    pxEndPoint->xRAData.eRAState = eRAStateLease;

    vDHCP_RATimerReload_ExpectAnyArgs();

    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eRAStateApply, xEndPoint.xRAData.eRAState );
    TEST_ASSERT_EQUAL( 0, pxEndPoint->xRAData.uxRetryCount );
}

/**
 *  @brief This function verify RA state machine with RA wait state as
 *         unexpected.
 */
void test_vRAProcess_UndefinedState( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;
    ICMPPacket_IPv6_t * pxICMPPacket, xICMPPacket;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xICMPPacket, 0, sizeof( ICMPPacket_IPv6_t ) );
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint = &xEndPoint;
    pxNetworkBuffer = &xNetworkBuffer;

    pxICMPPacket = &xICMPPacket;
    pxNetworkBuffer->pucEthernetBuffer = ( uint8_t * ) &xICMPPacket;

    pxEndPoint->bits.bIPv6 = pdTRUE_UNSIGNED;
    /* Unexpected state */
    pxEndPoint->xRAData.eRAState = eRAStateUnkown;

    vDHCP_RATimerReload_ExpectAnyArgs();

    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eRAStateUnkown, xEndPoint.xRAData.eRAState );
}

/**
 *  @brief This function verify RA state machine with RA wait state as eRAStateWait.
 */
void test_vRAProcess_eRAStateWait( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;

    pxEndPoint->xRAData.eRAState = eRAStateWait;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_ExpectAnyArgs();

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eRAStateWait, xEndPoint.xRAData.eRAState );
}

/**
 *  @brief This function verify RA state machine with RA wait state as eRAStateWait.
 *         Router Solicitation has been sent, waited for a reply, but no came and
 *         the retry count becomes more that ipconfigRA_SEARCH_COUNT.
 */
void test_vRAProcess_eRAStateWait_RetryExceed( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;
    UBaseType_t retry = ( UBaseType_t ) ipconfigRA_SEARCH_COUNT;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint->xRAData.eRAState = eRAStateWait;
    pxEndPoint->xRAData.uxRetryCount = ( UBaseType_t ) ipconfigRA_SEARCH_COUNT;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( &xNetworkBuffer );
    vDHCP_RATimerReload_ExpectAnyArgs();

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxEndPoint->xRAData.bits.bRouterReplied );
    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxEndPoint->xRAData.uxRetryCount );
    TEST_ASSERT_EQUAL( eRAStateIPWait, xEndPoint.xRAData.eRAState );
}

/**
 *  @brief This function verify RA state machine with RA wait state as eRAStateIPWait.
 *         With bIPAddressInUse True which implies Another device has
 *         responded with the same IPv4 address.
 */
void test_vRAProcess_eRAStateIPWait_AddressInUse( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint->xRAData.eRAState = eRAStateIPWait;
    pxEndPoint->xRAData.bits.bIPAddressInUse = pdTRUE_UNSIGNED;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_ExpectAnyArgs();

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( pdFALSE_UNSIGNED, pxEndPoint->xRAData.uxRetryCount );
    TEST_ASSERT_EQUAL( eRAStateIPWait, xEndPoint.xRAData.eRAState );
}

/**
 *  @brief This function verify RA state machine with RA wait state as eRAStateIPWait,
 *         With retry.
 */
void test_vRAProcess_eRAStateIPWait_Retry( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint->xRAData.eRAState = eRAStateIPWait;
    pxEndPoint->xRAData.uxRetryCount = 0;

    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    vDHCP_RATimerReload_ExpectAnyArgs();

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( 1U, pxEndPoint->xRAData.uxRetryCount );
    TEST_ASSERT_EQUAL( eRAStateIPWait, xEndPoint.xRAData.eRAState );
}

/**
 *  @brief This function verify RA state machine with RA wait state as eRAStateIPWait.
 *         And Obtained configuration from a router.
 */
void test_vRAProcess_eRAStateIPWait_RASuccess( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint->xRAData.eRAState = eRAStateIPWait;
    pxEndPoint->xRAData.uxRetryCount = ipconfigRA_IP_TEST_COUNT;
    /* Obtained configuration from a router. */
    pxEndPoint->xRAData.bits.bRouterReplied = pdTRUE_UNSIGNED;

    vIPNetworkUpCalls_Expect( &xEndPoint );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eRAStateLease, xEndPoint.xRAData.eRAState );
}

/**
 *  @brief This function verify RA state machine with RA wait state
 *         as eRAStateIPWait.
 *         Using the default network parameters.
 */
void test_vRAProcess_eRAStateIPWait_UsingDefaultAddress( void )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer, xNetworkBuffer;
    NetworkEndPoint_t xEndPoint, * pxEndPoint;
    IPv6_Address_t xIPAddress;

    memset( &xNetworkBuffer, 0, sizeof( NetworkBufferDescriptor_t ) );
    memset( &xIPAddress, 0, sizeof( IPv6_Address_t ) );
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxNetworkBuffer = &xNetworkBuffer;
    pxEndPoint = &xEndPoint;
    memset( pxEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    pxEndPoint->xRAData.eRAState = eRAStateIPWait;
    pxEndPoint->xRAData.uxRetryCount = ipconfigRA_IP_TEST_COUNT;
    /* Using the default network parameters. */
    pxEndPoint->xRAData.bits.bRouterReplied = pdFALSE_UNSIGNED;

    vIPNetworkUpCalls_Expect( &xEndPoint );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );

    /* pdFALSE Indicating vRAProcessInit is already done */
    vRAProcess( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eRAStateFailed, xEndPoint.xRAData.eRAState );
}
