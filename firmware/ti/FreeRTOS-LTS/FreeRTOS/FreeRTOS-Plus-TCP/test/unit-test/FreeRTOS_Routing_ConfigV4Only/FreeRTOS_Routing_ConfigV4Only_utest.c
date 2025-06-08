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

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_Routing.h"

#include "catch_assert.h"

/* ===========================  EXTERN VARIABLES  =========================== */

/* Default IPv4 address is 192.168.123.223, which is 0xDF7BA8C0. */
#define IPV4_DEFAULT_ADDRESS       ( 0xDF7BA8C0 )
/* Default IPv4 netmask is 255.255.255.0, which is 0x00FFFFFF. */
#define IPV4_DEFAULT_NETMASK       ( 0x00FFFFFF )
/* Default IPv4 netmask is 192.168.123.254, which is 0xFE7BA8C0. */
#define IPV4_DEFAULT_GATEWAY       ( 0xFE7BA8C0 )
/* Default IPv4 netmask is 192.168.123.1, which is 0x017BA8C0. */
#define IPV4_DEFAULT_DNS_SERVER    ( 0x017BA8C0 )

const uint8_t ucDefaultMACAddress_IPv4[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };

/* Default IPv6 address is set to 2001::1 */
const IPv6_Address_t xDefaultIPAddress_IPv6 = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
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
 * @brief FreeRTOS_MatchingEndpoint returns the endpoint matched for custom frame type.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 interface and 1 endpoint.
 *  - Put interface & endpoint into the list.
 *  - Prepare an custom packet with:
 *     - IP address 192.168.123.223.
 *     - MAC address ab:cd:ef:11:22:33.
 *     - Frame type in ethernet header 0xFF.
 *  - Call FreeRTOS_MatchingEndpoint and check if returned endpoint is same.
 */
void test_FreeRTOS_MatchingEndpoint_MatchCustomFrameType()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( TCPPacket_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
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
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xDestinationAddress.ucBytes, ucDefaultMACAddress_IPv4, ipMAC_ADDRESS_LENGTH_BYTES );
    memcpy( pxProtocolPacket->xTCPPacket.xEthernetHeader.xSourceAddress.ucBytes, ucDefaultMACAddress_IPv4, ipMAC_ADDRESS_LENGTH_BYTES );
    pxProtocolPacket->xTCPPacket.xEthernetHeader.usFrameType = 0xFF;
    /* IP part. */
    pxProtocolPacket->xTCPPacket.xIPHeader.ulSourceIPAddress = IPV4_DEFAULT_ADDRESS;
    pxProtocolPacket->xTCPPacket.xIPHeader.ulDestinationIPAddress = IPV4_DEFAULT_ADDRESS;

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) pxProtocolPacket );
    TEST_ASSERT_EQUAL( &xEndPoint, pxEndPoint );
}

/**
 * @brief FreeRTOS_MatchingEndpoint returns NULL when receiving IPv6 packet but no IPv6 endpoint in the list.
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
void test_FreeRTOS_MatchingEndpoint_IPv6Disabled()
{
    NetworkInterface_t xNetworkInterface;
    NetworkEndPoint_t xEndPoint;
    NetworkEndPoint_t * pxEndPoint = NULL;
    uint8_t * pcNetworkBuffer[ sizeof( TCPPacket_IPv6_t ) + 4 ] __attribute__( ( aligned( 32 ) ) );
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) ( ( uintptr_t ) ( pcNetworkBuffer ) + 2U );

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
    memcpy( pxTCPPacket->xEthernetHeader.xDestinationAddress.ucBytes, ucDefaultMACAddress_IPv6, ipMAC_ADDRESS_LENGTH_BYTES );
    memcpy( pxTCPPacket->xEthernetHeader.xSourceAddress.ucBytes, ucDefaultMACAddress_IPv6, ipMAC_ADDRESS_LENGTH_BYTES );
    pxTCPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
    /* IP part. */
    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, ipSIZE_OF_IPv4_ADDRESS );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xDefaultIPAddress_IPv6.ucBytes, ipSIZE_OF_IPv4_ADDRESS );

    pxEndPoint = FreeRTOS_MatchingEndpoint( &xNetworkInterface, ( const uint8_t * ) pxTCPPacket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint );
}

/**
 * @brief pcEndpointName can't get IPv6 address in string from endpoint due to IPv6 is disabled.
 *
 * pxNetworkInterfaces is a global variable using in FreeRTOS_Routing as link list head of all interfaces.
 * pxNetworkEndPoints is a global variable using in FreeRTOS_Routing as link list head of all endpoints.
 *
 * Test step:
 *  - Create 1 endpoint.
 *     - Set the IP address to 2001::1 (xDefaultIPAddress_IPv6).
 *  - Call pcEndpointName with enough buffer size.
 *  - Check if return buffer string is NULL.
 */
void test_pcEndpointName_IPv6HappyPath()
{
    NetworkEndPoint_t xEndPoint;
    FreeRTOS_Socket_t xSocket;
    const char cIPString[] = "2001::1";
    int lNameSize = sizeof( cIPString ) + 1;
    char cName[ lNameSize ];
    const char * pcName;

    /* Initialize network endpoint and add it to the list. */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xEndPoint.bits.bIPv6 = pdTRUE;

    memset( &cName, 0, sizeof( cName ) );

    pcName = pcEndpointName( &xEndPoint, cName, lNameSize );
    TEST_ASSERT_EQUAL_STRING( "NULL", pcName );
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
 *  - Check if returned endpoint is NULL.
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
