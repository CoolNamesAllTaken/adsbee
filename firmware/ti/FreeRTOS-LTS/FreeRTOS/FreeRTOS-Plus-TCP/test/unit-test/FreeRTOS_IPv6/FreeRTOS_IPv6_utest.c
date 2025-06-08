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

/* This must come after list.h is included (in this case, indirectly
 * by mock_list.h). */
#include "mock_FreeRTOS_Routing.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IPv6_Utils.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IPv6.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

#include "FreeRTOS_IPv6_stubs.c"

/* ===========================  EXTERN VARIABLES  =========================== */

extern const struct xIPv6_Address FreeRTOS_in6addr_any;
extern const struct xIPv6_Address FreeRTOS_in6addr_loopback;

/* =============================== Test Cases =============================== */

/**
 * @brief Prepare a packet with unspecified address in source address.
 *        Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_SourceUnspecifiedAddress()
{
    IPHeader_IPv6_t xIPv6Address;
    eFrameProcessingResult_t eResult;

    memset( &xIPv6Address, 0, sizeof( xIPv6Address ) );
    memcpy( xIPv6Address.xDestinationAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( xIPv6Address.xSourceAddress.ucBytes, FreeRTOS_in6addr_any.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    eResult = prvAllowIPPacketIPv6( &xIPv6Address, NULL, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief Prepare a packet with unspecified address in destination address.
 *        Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_DestinationUnspecifiedAddress()
{
    IPHeader_IPv6_t xIPv6Address;
    eFrameProcessingResult_t eResult;

    memset( &xIPv6Address, 0, sizeof( xIPv6Address ) );
    memcpy( xIPv6Address.xDestinationAddress.ucBytes, FreeRTOS_in6addr_any.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( xIPv6Address.xSourceAddress.ucBytes, xIPAddressFive.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    eResult = prvAllowIPPacketIPv6( &xIPv6Address, NULL, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::5. And it's not a loopback packet.
 *        Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_HappyPath()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief Prepare a packet from 2001:1234:5678::5 -> FF02::1. Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_MulticastAddress()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    /* Multicast IPv6 address is FF02::1 */
    IPv6_Address_t xMCIPAddress = { 0xFF, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, xMCIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &( pxTCPPacket->xIPHeader.xSourceAddress ), pxNetworkBuffer->pxEndPoint );
    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief Prepare a packet from 2001:1234:5678::5 -> ::1.
 *        Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_LoopbackAddress()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    NetworkEndPoint_t xEndPoint;

    memcpy( pxTCPPacket->xIPHeader.xSourceAddress.ucBytes, FreeRTOS_in6addr_loopback.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, FreeRTOS_in6addr_loopback.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, &xEndPoint );

    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 0 );

    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::11.
 *        Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_LoopbackNotMatchDest()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes[ 15 ] = 0x11;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, pxNetworkBuffer->pxEndPoint );
    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 0 );
    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief Prepare a packet from 2001:1234:5678::10 -> ::1.
 *         Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_LoopbackNotMatchSrc()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    NetworkEndPoint_t xEndPoint;

    memcpy( pxTCPPacket->xIPHeader.xDestinationAddress.ucBytes, FreeRTOS_in6addr_loopback.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, &xEndPoint );
    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 0 );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::FFFF when network is down.
 *        Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_NetworkDown()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxNetworkBuffer->pxEndPoint = NULL;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, NULL );
    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 0 );
    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipCORRECT_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::5. And the source MAC address in packet is same as endpoint.
 *        Check if prvAllowIPPacketIPv6 determines to process it.
 */
void test_prvAllowIPPacketIPv6_SelfSend()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, pxNetworkBuffer->pxEndPoint );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
}

/**
 * @brief Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::5. But the checksum is wrong.
 *        Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_ChecksumError()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    FreeRTOS_FindEndPointOnMAC_ExpectAndReturn( &pxTCPPacket->xEthernetHeader.xSourceAddress, NULL, NULL );
    usGenerateProtocolChecksum_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE, ipWRONG_CRC );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::5. But there is no rule to process this packet.
 *        Check if prvAllowIPPacketIPv6 determines to release it.
 */
void test_prvAllowIPPacketIPv6_InvalidPacket()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;

    pxNetworkBuffer->pxEndPoint = NULL;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &pxTCPPacket->xIPHeader.xSourceAddress, NULL );
    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 1 );

    eResult = prvAllowIPPacketIPv6( &pxTCPPacket->xIPHeader, pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief Prepare a packet from 2001:1234:5678::10 -> 2001:1234:5678::5. But the address in endpoint in network descriptor is different from packet.
 *        Check if prvAllowIPPacketIPv6 determines to lease it.
 */
void test_prvAllowIPPacketIPv6_EndpointDifferentAddress()
{
    eFrameProcessingResult_t eResult;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();
    TCPPacket_IPv6_t * pxTCPPacket = ( TCPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer;
    NetworkEndPoint_t xEndpoint;
    /* Different IPv6 address is 2001:1234:5678::FFFF */
    IPv6_Address_t xDiffIPAddress = { 0x20, 0x01, 0x12, 0x34, 0x56, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF };

    memset( &xEndpoint, 0, sizeof( xEndpoint ) );
    xEndpoint.bits.bIPv6 = 1U;
    memcpy( xEndpoint.ipv6_settings.xIPAddress.ucBytes, xDiffIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    pxNetworkBuffer->pxEndPoint = &xEndpoint;

    FreeRTOS_FindEndPointOnIP_IPv6_ExpectAndReturn( &( pxTCPPacket->xIPHeader.xSourceAddress ), NULL );
    FreeRTOS_IsNetworkUp_IgnoreAndReturn( 1 );

    eResult = prvAllowIPPacketIPv6( &( pxTCPPacket->xIPHeader ), pxNetworkBuffer, 0U );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief Prepare a packet have extension with following order. Check if eHandleIPv6ExtensionHeaders determines to process it.
 *         - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *         - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *         - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *         - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *         - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *         - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *         - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *         - ipPROTOCOL_TCP
 *            - 1 byte payload
 */
void test_eHandleIPv6ExtensionHeaders_TCPHappyPath()
{
    eFrameProcessingResult_t eResult;
    uint8_t ucExtHeaderNum = 7U;
    uint8_t ucProtocol = ipPROTOCOL_TCP;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ucProtocol );
    uint8_t * pxPayload = &( pxNetworkBuffer->pucEthernetBuffer[
                                 ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH + sizeof( TCPHeader_t )
                             ] );

    *pxPayload = 'a';

    usGetExtensionHeaderLength_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, NULL, ucExtHeaderNum * 8U );
    usGetExtensionHeaderLength_IgnoreArg_pucProtocol();
    usGetExtensionHeaderLength_ReturnThruPtr_pucProtocol( &ucProtocol );

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
    TEST_ASSERT_EQUAL( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( TCPHeader_t ) + 1U, pxNetworkBuffer->xDataLength );
}

/**
 * @brief Prepare a packet have extension with following order. Check if eHandleIPv6ExtensionHeaders determines to process it.
 *         - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *         - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *         - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *         - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *         - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *         - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *         - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *         - ipPROTOCOL_UDP
 *            - 1 byte payload
 */
void test_eHandleIPv6ExtensionHeaders_UDPHappyPath()
{
    eFrameProcessingResult_t eResult;
    uint8_t ucExtHeaderNum = 7U;
    uint8_t ucProtocol = ipPROTOCOL_UDP;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ucProtocol );
    UDPHeader_t * pxProtocolHeader = ( UDPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH ] );
    uint8_t * pxPayload;

    pxPayload = ( uint8_t * ) ( pxProtocolHeader + 1 );
    *pxPayload = 'a';

    usGetExtensionHeaderLength_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, NULL, ucExtHeaderNum * 8U );
    usGetExtensionHeaderLength_IgnoreArg_pucProtocol();
    usGetExtensionHeaderLength_ReturnThruPtr_pucProtocol( &ucProtocol );

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
    TEST_ASSERT_EQUAL( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( UDPHeader_t ) + 1U, pxNetworkBuffer->xDataLength );
}

/**
 * @brief Prepare a packet have extension with following order. Check if eHandleIPv6ExtensionHeaders determines to process it.
 *         - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *         - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *         - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *         - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *         - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *         - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *         - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *         - ipPROTOCOL_ICMP_IPv6
 *            - 1 byte payload
 */
void test_eHandleIPv6ExtensionHeaders_ICMPv6HappyPath()
{
    eFrameProcessingResult_t eResult;
    uint8_t ucExtHeaderNum = 7U;
    uint8_t ucProtocol = ipPROTOCOL_ICMP_IPv6;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ucProtocol );
    ICMPHeader_IPv6_t * pxProtocolHeader = ( ICMPHeader_IPv6_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH ] );
    uint8_t * pxPayload;

    pxPayload = ( uint8_t * ) ( pxProtocolHeader + 1 );
    *pxPayload = 'a';

    usGetExtensionHeaderLength_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, NULL, ucExtHeaderNum * 8U );
    usGetExtensionHeaderLength_IgnoreArg_pucProtocol();
    usGetExtensionHeaderLength_ReturnThruPtr_pucProtocol( &ucProtocol );

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eProcessBuffer, eResult );
    TEST_ASSERT_EQUAL( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t ) + 1U, pxNetworkBuffer->xDataLength );
}

/**
 * @brief Prepare a packet have extension with following order. Check if eHandleIPv6ExtensionHeaders determines to release it due to not support.
 *        And the extension headers still exist.
 *         - ipIPv6_EXT_HEADER_HOP_BY_HOP
 *         - ipIPv6_EXT_HEADER_ROUTING_HEADER
 *         - ipIPv6_EXT_HEADER_FRAGMENT_HEADER
 *         - ipIPv6_EXT_HEADER_SECURE_PAYLOAD
 *         - ipIPv6_EXT_HEADER_AUTHEN_HEADER
 *         - ipIPv6_EXT_HEADER_DESTINATION_OPTIONS
 *         - ipIPv6_EXT_HEADER_MOBILITY_HEADER
 *         - ipPROTOCOL_TCP
 *            - 1 byte payload
 */
void test_eHandleIPv6ExtensionHeaders_TCPHappyPathNotRemove()
{
    eFrameProcessingResult_t eResult;
    uint8_t ucExtHeaderNum = 7U;
    uint8_t ucProtocol = ipPROTOCOL_TCP;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ucProtocol );
    TCPHeader_t * pxProtocolHeader = ( TCPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH ] );
    uint8_t * pxPayload;

    pxPayload = ( uint8_t * ) ( pxProtocolHeader + 1 );
    *pxPayload = 'a';

    usGetExtensionHeaderLength_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, NULL, ucExtHeaderNum * 8U );
    usGetExtensionHeaderLength_IgnoreArg_pucProtocol();
    usGetExtensionHeaderLength_ReturnThruPtr_pucProtocol( &ucProtocol );

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdFALSE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
    TEST_ASSERT_EQUAL( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + TEST_IPv6_DEFAULT_EXTENSION_HEADERS_LENGTH + sizeof( TCPHeader_t ) + 1U, pxNetworkBuffer->xDataLength );
}

/**
 * @brief Prepare a packet with 0 buffer length. Check if eHandleIPv6ExtensionHeaders determines to release it.
 */
void test_eHandleIPv6ExtensionHeaders_ShortBufferLength()
{
    eFrameProcessingResult_t eResult;
    uint8_t ucExtHeaderNum = 7U;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptor();

    pxNetworkBuffer->xDataLength = 0;

    usGetExtensionHeaderLength_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, NULL, ucExtHeaderNum * 8U );
    usGetExtensionHeaderLength_IgnoreArg_pucProtocol();

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief Prepare a packet with small IP payload length. Check if eHandleIPv6ExtensionHeaders determines to release it.
 */
void test_eHandleIPv6ExtensionHeaders_SmallIPPayloadLength()
{
    eFrameProcessingResult_t eResult;
    uint8_t ucExtHeaderNum = 7U;
    uint8_t ucProtocol = ipPROTOCOL_TCP;
    NetworkBufferDescriptor_t * pxNetworkBuffer = prvInitializeNetworkDescriptorWithExtensionHeader( ucProtocol );
    IPPacket_IPv6_t * pxIPPacket_IPv6 = ( ( IPPacket_IPv6_t * ) pxNetworkBuffer->pucEthernetBuffer );

    pxIPPacket_IPv6->xIPHeader.usPayloadLength = FreeRTOS_htons( 20 ); /* Need to remove 56 bytes extension header but only 20 bytes length set in IP header. */

    usGetExtensionHeaderLength_ExpectAndReturn( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, NULL, ucExtHeaderNum * 8U );
    usGetExtensionHeaderLength_IgnoreArg_pucProtocol();

    eResult = eHandleIPv6ExtensionHeaders( pxNetworkBuffer, pdTRUE );
    TEST_ASSERT_EQUAL( eReleaseBuffer, eResult );
}

/**
 * @brief Prepare a IPv6 addresses FF00:: ~ FFF0::. Check if xIsIPv6AllowedMulticast returns pdFALSE.
 */
void test_xIsIPv6AllowedMulticast_ZeroScope()
{
    IPv6_Address_t xMulticastZeroGroupID = { 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
    BaseType_t xReturn;
    uint16_t ucScope;

    for( ucScope = 0x0; ucScope <= 0xF0; ucScope += 0x10 )
    {
        xMulticastZeroGroupID.ucBytes[ 1 ] = ( uint8_t ) ucScope;
        xReturn = xIsIPv6AllowedMulticast( &xMulticastZeroGroupID );
        TEST_ASSERT_EQUAL( pdFALSE, xReturn );
    }
}

/**
 * @brief Prepare IPv6 addresses FF00:: ~ FF0F::. Check if xIsIPv6AllowedMulticast returns pdTRUE.
 */
void test_xIsIPv6AllowedMulticast_ReservedAddress()
{
    IPv6_Address_t xMulticastZeroFlag = { 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
    BaseType_t xReturn;
    uint8_t ucFlag;

    for( ucFlag = 0x0; ucFlag <= 0xF; ucFlag++ )
    {
        xMulticastZeroFlag.ucBytes[ 1 ] = ucFlag;
        xReturn = xIsIPv6AllowedMulticast( &xMulticastZeroFlag );
        TEST_ASSERT_EQUAL( pdFALSE, xReturn );
    }
}

/**
 * @brief Prepare IPv6 address FF11::1. Check if xIsIPv6AllowedMulticast returns pdTRUE.
 */
void test_xIsIPv6AllowedMulticast_ValidAddress()
{
    IPv6_Address_t xMulticastZeroFlag = { 0xFF, 0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    BaseType_t xReturn;

    xReturn = xIsIPv6AllowedMulticast( &xMulticastZeroFlag );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
}

/**
 * @brief Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 */
void test_xCompareIPv6_Address_LLMNR()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xab, 0xcd, 0xef };
    IPv6_Address_t xRightAddress = { 0xFF, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xab, 0xcd, 0xef };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 16 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 */
void test_xCompareIPv6_Address_AllNodes()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0x20, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xab, 0xcd, 0xef };
    IPv6_Address_t xRightAddress = { 0xFF, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 16 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 */
void test_xCompareIPv6_Address_BothLocalAddresses()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    IPv6_Address_t xRightAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 16 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 */
void test_xCompareIPv6_Address_CoverageLocalAddressLeftFF80()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0xFF, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    IPv6_Address_t xRightAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 128 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 */
void test_xCompareIPv6_Address_CoverageLocalAddressLeftFE81()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0xFE, 0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    IPv6_Address_t xRightAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 128 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 */
void test_xCompareIPv6_Address_CoverageLocalAddressRightFF80()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    IPv6_Address_t xRightAddress = { 0xFF, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 128 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. Check if xIsIPv6AllowedMulticast returns 0.
 */
void test_xCompareIPv6_Address_CoverageLocalAddressRightFE81()
{
    BaseType_t xReturn;
    IPv6_Address_t xLeftAddress = { 0xFE, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    IPv6_Address_t xRightAddress = { 0xFE, 0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02 };

    xReturn = xCompareIPv6_Address( &xLeftAddress, &xRightAddress, 128 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. With prefix length 0, xCompareIPv6_Address should take all IP address as same region.
 */
void test_xCompareIPv6_Address_ZeroPrefixLength()
{
    BaseType_t xReturn;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xIPAddressTen, 0 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. With prefix length 128, xCompareIPv6_Address should compare whole IP address.
 */
void test_xCompareIPv6_Address_SameAddressPrefix128()
{
    BaseType_t xReturn;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xIPAddressFive, 128 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. With prefix length 64, xCompareIPv6_Address should compare first 64 bit of IP address.
 */
void test_xCompareIPv6_Address_SameRegionPrefix64()
{
    BaseType_t xReturn;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xIPAddressTen, 64 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. With prefix length 64, xCompareIPv6_Address should compare first 64 bit of IP address.
 */
void test_xCompareIPv6_Address_DifferentRegionPrefix64()
{
    BaseType_t xReturn;
    IPv6_Address_t xRightAddress = { 0xFF, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10 };

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xRightAddress, 64 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. With prefix length 4, xCompareIPv6_Address should compare first 4 bit of IP address.
 */
void test_xCompareIPv6_Address_DifferentRegionPrefix4()
{
    BaseType_t xReturn;
    IPv6_Address_t xRightAddress;

    memcpy( xRightAddress.ucBytes, &xIPAddressFive, ipSIZE_OF_IPv6_ADDRESS );
    xRightAddress.ucBytes[ 0 ] = 0x40;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xRightAddress, 4 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. With prefix length 44, xCompareIPv6_Address should compare first 44 bit of IP address.
 */
void test_xCompareIPv6_Address_DifferentRegionPrefix44()
{
    BaseType_t xReturn;
    IPv6_Address_t xRightAddress;

    memcpy( xRightAddress.ucBytes, &xIPAddressFive, ipSIZE_OF_IPv6_ADDRESS );
    xRightAddress.ucBytes[ 5 ] = 0x88;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xRightAddress, 44 );
    TEST_ASSERT_NOT_EQUAL( 0, xReturn );
}

/**
 * @brief Prepare IPv6 address below. With prefix length 44, xCompareIPv6_Address should compare first 44 bit of IP address.
 */
void test_xCompareIPv6_Address_SameRegionPrefix44()
{
    BaseType_t xReturn;

    xReturn = xCompareIPv6_Address( &xIPAddressFive, &xIPAddressTen, 44 );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/**
 * @brief Test xGetExtensionOrder.
 */
void test_xGetExtensionOrder()
{
    BaseType_t xReturn;

    xReturn = xGetExtensionOrder( ipIPv6_EXT_HEADER_HOP_BY_HOP, 0U );
    TEST_ASSERT_EQUAL( 1, xReturn );

    xReturn = xGetExtensionOrder( ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, 0U );
    TEST_ASSERT_EQUAL( 7, xReturn );

    xReturn = xGetExtensionOrder( ipIPv6_EXT_HEADER_DESTINATION_OPTIONS, ipIPv6_EXT_HEADER_ROUTING_HEADER );
    TEST_ASSERT_EQUAL( 2, xReturn );

    xReturn = xGetExtensionOrder( ipIPv6_EXT_HEADER_ROUTING_HEADER, 0U );
    TEST_ASSERT_EQUAL( 3, xReturn );

    xReturn = xGetExtensionOrder( ipIPv6_EXT_HEADER_FRAGMENT_HEADER, 0U );
    TEST_ASSERT_EQUAL( 4, xReturn );

    xReturn = xGetExtensionOrder( ipIPv6_EXT_HEADER_AUTHEN_HEADER, 0U );
    TEST_ASSERT_EQUAL( 5, xReturn );

    xReturn = xGetExtensionOrder( ipIPv6_EXT_HEADER_SECURE_PAYLOAD, 0U );
    TEST_ASSERT_EQUAL( 6, xReturn );

    xReturn = xGetExtensionOrder( ipIPv6_EXT_HEADER_MOBILITY_HEADER, 0U );
    TEST_ASSERT_EQUAL( 8, xReturn );

    xReturn = xGetExtensionOrder( ipPROTOCOL_TCP, 0U );
    TEST_ASSERT_EQUAL( -1, xReturn );
}
