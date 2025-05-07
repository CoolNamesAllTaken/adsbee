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
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_FreeRTOS_BitConfig.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_DHCP.h"

/*#include "FreeRTOS_IP_stubs.c" */
#include "catch_assert.h"

#include "FreeRTOS_DHCPv6.h"
#include "FreeRTOS_DHCPv6_stubs.c"

/* ===========================  EXTERN VARIABLES  =========================== */

#define TEST_DHCPV6_IAID                     ( 0x27fe8f95 )

#define TEST_DHCPv6_DEFAULT_DUID_TYPE        ( 1U )
#define TEST_DHCPv6_DIFFERENT_DUID_TYPE      ( 2U )
#define TEST_DHCPv6_DEFAULT_DUID_LENGTH      ( 14U )
#define TEST_DHCPv6_DIFFERENT_DUID_LENGTH    ( 12U )

extern BaseType_t xDHCPv6SocketUserCount;

extern void prvSendDHCPMessage( NetworkEndPoint_t * pxEndPoint );
extern void prvCloseDHCPv6Socket( NetworkEndPoint_t * pxEndPoint );
extern const char * prvStateName( eDHCPState_t eState );
extern BaseType_t prvDHCPv6_subOption( uint16_t usOption,
                                       const DHCPOptionSet_t * pxSet,
                                       DHCPMessage_IPv6_t * pxDHCPMessage,
                                       BitConfig_t * pxMessage );

/* ============================  Unity Fixtures  ============================ */

/*! called before each test case */
void setUp( void )
{
    InitializeUnitTest();
    memset( xTestDHCPv6BitOperation, 0, sizeof( xTestDHCPv6BitOperation ) );
    ulTestDHCPv6BitOperationWriteIndex = 0;
    ulTestDHCPv6BitOperationReadIndex = 0;
}

/*! called after each test case */
void tearDown( void )
{
}

/* ==============================  Test Cases  ============================== */

static void vAddBitOperation( eTestDHCPv6BitOperationType_t eType,
                              const void * pvVal,
                              uint32_t ulSize,
                              uint8_t * pucDebugMsg )
{
    const uint8_t * pucVal;
    const uint16_t * pusVal;
    const uint32_t * pulVal;

    TEST_ASSERT_TRUE( ulTestDHCPv6BitOperationWriteIndex < TEST_DHCPv6_BIT_OPERATION_MAX_NUM );

    xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].eOperationType = eType;
    xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].ulCustomLength = ulSize;

    switch( eType )
    {
        case eTestDHCPv6BitOperationWrite8:
        case eTestDHCPv6BitOperationRead8:
            pucVal = ( uint8_t * ) pvVal;
            xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].val.ucVal = *pucVal;
            break;

        case eTestDHCPv6BitOperationWrite16:
        case eTestDHCPv6BitOperationRead16:
            pusVal = ( uint16_t * ) pvVal;
            xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].val.usVal = *pusVal;
            break;

        case eTestDHCPv6BitOperationWrite32:
        case eTestDHCPv6BitOperationRead32:
            pulVal = ( uint32_t * ) pvVal;
            xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].val.ulVal = *pulVal;
            break;

        case eTestDHCPv6BitOperationWriteCustom:
        case eTestDHCPv6BitOperationReadCustom:
        case eTestDHCPv6BitOperationReadPeek:
            TEST_ASSERT_LESS_THAN( TEST_DHCPv6_BIT_OPERATION_MAX_SIZE, ulSize );
            memcpy( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].val.ucValCustom, pvVal, ulSize );
            break;
    }

    TEST_ASSERT_LESS_THAN_size_t( TEST_DHCPv6_BIT_OPERATION_DEBUG_MSG_MAX_SIZE, strlen( pucDebugMsg ) );
    strcpy( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationWriteIndex ].ucDebugMsg, pucDebugMsg );

    ulTestDHCPv6BitOperationWriteIndex++;
}

static void prvSetBitOperationStub()
{
    xBitConfig_init_Stub( xStubxBitConfig_init );
    vBitConfig_write_8_Stub( xStubvBitConfig_write_8 );
    vBitConfig_write_16_Stub( xStubvBitConfig_write_16 );
    vBitConfig_write_32_Stub( xStubvBitConfig_write_32 );
    vBitConfig_write_uc_Stub( xStubvBitConfig_write_uc );
    pucBitConfig_peek_last_index_uc_Stub( xStubpucBitConfig_peek_last_index_uc );
    vBitConfig_release_Ignore();

    ucBitConfig_read_8_Stub( xStubucBitConfig_read_8 );
    usBitConfig_read_16_Stub( xStubusBitConfig_read_16 );
    ulBitConfig_read_32_Stub( xStubulBitConfig_read_32 );
    xBitConfig_read_uc_Stub( xStubxBitConfig_read_uc );
}

static void prvAddMsgHeader( BaseType_t xIsWrite,
                             uint8_t ucMessageType )
{
    uint8_t ucVal;

    if( xIsWrite == pdTRUE )
    {
        /* Provide the message type and transaction ID for DHCPv6. */
        ucVal = ucMessageType;
        vAddBitOperation( eTestDHCPv6BitOperationWrite8, &ucVal, 1, "Type" );
        vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );
    }
    else
    {
        /* Provide the message type and transaction ID for DHCPv6. */
        ucVal = ucMessageType;
        vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "Type" );
        vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );
    }
}

static void prvAddOptionClient( BaseType_t xIsWrite )
{
    uint16_t usVal;
    uint32_t ulVal;

    if( xIsWrite == pdTRUE )
    {
        /* Option Client ID */
        usVal = DHCPv6_Option_Client_Identifier;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientID" );
        usVal = 14U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientIDLength" );
        /* Client ID - DUID & hardware Type */
        usVal = 1U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientIDDUIDType" );
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionClientIDHWType" );
        /* Client ID - Time Stamp */
        ulVal = ulApplicationTimeHook() - SECS_FROM_1970_TILL_2000;
        vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionClientIDTimeStamp" );
        /* Client ID - MAC Address */
        vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, ucDefaultMACAddress, ipMAC_ADDRESS_LENGTH_BYTES, "OptionClientIDMAC" );
    }
    else
    {
        usVal = DHCPv6_Option_Client_Identifier;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientID" );
        usVal = 14U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDLength" );
        /* Client ID - DUID & hardware Type */
        usVal = 1U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDDUIDType" );
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDHWType" );
        /* Client ID - remain ID */
        vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &ucTestDHCPv6OptionClientID[ 4 ], sizeof( ucTestDHCPv6OptionClientID ) - 4, "OptionClientIDRemain" );
    }

    /* Call peek function to compare client ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadPeek, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ), "OptionClientIDPeek" );
}

static void prvAddOptionServer( BaseType_t xIsWrite,
                                BaseType_t xIsDifferentType,
                                BaseType_t xIsDifferentLength,
                                BaseType_t xIsDifferentID )
{
    uint16_t usVal;
    uint32_t ulVal;
    uint8_t ucDifferentServerID[] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };

    if( xIsWrite == pdTRUE )
    {
        /* Option Server ID */
        usVal = DHCPv6_Option_Server_Identifier;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionServerID" );
        usVal = xIsDifferentLength == pdTRUE ? TEST_DHCPv6_DIFFERENT_DUID_LENGTH : TEST_DHCPv6_DEFAULT_DUID_LENGTH;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionServerIDLength" );
        /* Server ID - DUID & hardware Type */
        usVal = xIsDifferentType == pdTRUE ? TEST_DHCPv6_DIFFERENT_DUID_TYPE : TEST_DHCPv6_DEFAULT_DUID_TYPE;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionServerIDDUIDType" );
        usVal = 1U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionServerIDHWType" );

        /* Server ID - remain ID */
        if( xIsDifferentID == pdFALSE )
        {
            vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ), "OptionServerIDRemain" );
        }
        else
        {
            vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, ucDifferentServerID, sizeof( ucDifferentServerID ), "OptionServerIDRemain" );
        }
    }
    else
    {
        /* Option Server ID */
        usVal = DHCPv6_Option_Server_Identifier;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerID" );
        usVal = xIsDifferentLength == pdTRUE ? TEST_DHCPv6_DIFFERENT_DUID_LENGTH : TEST_DHCPv6_DEFAULT_DUID_LENGTH;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDLength" );
        /* Server ID - DUID & hardware Type */
        usVal = xIsDifferentType == pdTRUE ? TEST_DHCPv6_DIFFERENT_DUID_TYPE : TEST_DHCPv6_DEFAULT_DUID_TYPE;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDDUIDType" );
        usVal = 1U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDHWType" );

        /* Server ID - remain ID */
        if( xIsDifferentID == pdFALSE )
        {
            vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ), "OptionServerIDRemain" );
        }
        else
        {
            vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucDifferentServerID, sizeof( ucDifferentServerID ), "OptionServerIDRemain" );
        }
    }
}

static void prvAddOptionElapsedTime( BaseType_t xIsWrite )
{
    uint16_t usVal;

    if( xIsWrite == pdTRUE )
    {
        /* Option Elapsed Time */
        usVal = DHCPv6_Option_Elapsed_Time;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionElapsed" );
        usVal = 2U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionElapsedLength" );
        usVal = 0U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionElapsedValue" );
    }
    else
    {
        /* Option Elapsed Time */
        usVal = DHCPv6_Option_Elapsed_Time;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionElapsed" );
        usVal = 2U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionElapsedLength" );
        usVal = 0U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionElapsedValue" );
    }
}

static void prvAddOptionIA_Prefix( BaseType_t xIsWrite )
{
    uint8_t ucVal;
    uint16_t usVal;
    uint32_t ulVal;

    if( xIsWrite == pdTRUE )
    {
        /* Option IA_Prefix */
        usVal = DHCPv6_Option_IA_Prefix;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_Prefix" );
        usVal = 25U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_PrefixLength" );
        /* Preferred Life Time */
        ulVal = 4500U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PrefixPreferLifeTime" );
        /* Valid Life Time */
        ulVal = 7200U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PrefixValidLifeTime" );
        /* Prefix length */
        ucVal = 64U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite8, &ucVal, 1, "OptionIA_PrefixPrefixLength" );
        /* Prefix */
        vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, xDefaultNetPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS, "OptionIA_PrefixAddress" );
    }
    else
    {
        /* Option IA_Prefix */
        usVal = DHCPv6_Option_IA_Prefix;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_Prefix" );
        usVal = 25U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_PrefixLength" );
        /* Preferred Life Time */
        ulVal = 4500U;
        vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_PrefixPreferLifeTime" );
        /* Valid Life Time */
        ulVal = 7200U;
        vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_PrefixValidLifeTime" );
        /* Prefix length */
        ucVal = 64U;
        vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "OptionIA_PrefixPrefixLength" );
        /* Prefix */
        vAddBitOperation( eTestDHCPv6BitOperationReadCustom, xDefaultNetPrefix.ucBytes, ipSIZE_OF_IPv6_ADDRESS, "OptionIA_PrefixAddress" );
    }
}

static void prvAddOptionIA_PD( BaseType_t xIsWrite )
{
    uint16_t usVal;
    uint32_t ulVal;

    if( xIsWrite == pdTRUE )
    {
        /* Option IA_PD */
        usVal = DHCPv6_Option_IA_for_Prefix_Delegation;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_PD" );
        usVal = 41U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_PDLength" );
        ulVal = TEST_DHCPV6_IAID;
        vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PDIAID" );
        ulVal = 3600U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PDT1" );
        ulVal = 5400U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_PDT2" );
    }
    else
    {
        /* Option IA_PD */
        usVal = DHCPv6_Option_IA_for_Prefix_Delegation;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_PD" );
        usVal = 41U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_PDLength" );
        ulVal = TEST_DHCPV6_IAID;
        vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_PDIAID" );
        ulVal = 3600U;
        vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_PDT1" );
        ulVal = 5400U;
        vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_PDT2" );
    }

    /* Add sub-option IA-Prefix */
    prvAddOptionIA_Prefix( xIsWrite );
}

static void prvAddOptionIA_NA( BaseType_t xIsWrite,
                               uint16_t usLength )
{
    uint16_t usVal;
    uint32_t ulVal;

    if( xIsWrite == pdTRUE )
    {
        /* Option IA_NA */
        usVal = DHCPv6_Option_NonTemporaryAddress;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_NA" );
        usVal = usLength;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_NALength" );
        ulVal = TEST_DHCPV6_IAID;
        vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_NAIAID" );
        /* T1 */
        ulVal = 4500U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_NAT1" );
        /* T2 */
        ulVal = 7200U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_NAT2" );
    }
    else
    {
        /* Option IA_NA */
        usVal = DHCPv6_Option_NonTemporaryAddress;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NA" );
        usVal = usLength;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NALength" );
        ulVal = TEST_DHCPV6_IAID;
        vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAIAID" );
        /* T1 */
        ulVal = 4500U;
        vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAT1" );
        /* T2 */
        ulVal = 7200U;
        vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NAT2" );
    }
}

static void prvAddOptionIA_TA( BaseType_t xIsWrite )
{
    uint16_t usVal;
    uint32_t ulVal;

    if( xIsWrite == pdTRUE )
    {
        /* IA_TA */
        usVal = DHCPv6_Option_TemporaryAddress;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_TA" );
        usVal = 4U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_TALength" );
        /* Code will use xBitConfig_read_uc to drop all messages in option IA_TA */
        ulVal = TEST_DHCPV6_IAID;
        vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, &ulVal, 4, "OptionIA_TAIAID" );
    }
    else
    {
        /* IA_TA */
        usVal = DHCPv6_Option_TemporaryAddress;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_TA" );
        usVal = 4U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_TALength" );
        /* Code will use xBitConfig_read_uc to drop all messages in option IA_TA */
        ulVal = TEST_DHCPV6_IAID;
        vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &ulVal, 4, "OptionIA_TAIAID" );
    }
}

static void prvAddOptionIAAddress( BaseType_t xIsWrite )
{
    uint16_t usVal;
    uint32_t ulVal;

    if( xIsWrite == pdTRUE )
    {
        /* IA_NA sub-option IA Address */
        usVal = DHCPv6_Option_IA_Address;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_NASubIAAddress" );
        usVal = 24U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionIA_NASubIAAddressLength" );
        vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS, "OptionIA_NASubIAAddressIP" );
        /* Preferred Life Time */
        ulVal = 900U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_NASubIAAddressPreferLifeTime" );
        /* Valid Life Time */
        ulVal = 900U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite32, &ulVal, 4, "OptionIA_NASubIAAddressValidLifeTime" );
    }
    else
    {
        /* IA_NA sub-option IA Address */
        usVal = DHCPv6_Option_IA_Address;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAAddress" );
        usVal = 24U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAAddressLength" );
        vAddBitOperation( eTestDHCPv6BitOperationReadCustom, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS, "OptionIA_NASubIAAddressIP" );
        /* Preferred Life Time */
        ulVal = 900U;
        vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAAddressPreferLifeTime" );
        /* Valid Life Time */
        ulVal = 900U;
        vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_NASubIAAddressValidLifeTime" );
    }
}

static void prvAddOptionStatusCode( BaseType_t xIsWrite )
{
    const uint8_t ucStatusCodeSuccess[] = "success";
    uint16_t usVal;
    uint32_t ulVal;

    if( xIsWrite == pdTRUE )
    {
        /* Status Code */
        usVal = DHCPv6_Option_Status_Code;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionSubStatus" );
        usVal = 9U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionSubStatusLength" );
        usVal = 0U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionStatusValue" );
        /* Status message */
        vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, ucStatusCodeSuccess, sizeof( ucStatusCodeSuccess ), "OptionStatusMessage" );
    }
    else
    {
        /* Status Code */
        usVal = DHCPv6_Option_Status_Code;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatus" );
        usVal = 9U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusLength" );
        usVal = 0U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusValue" );
        /* Status message */
        vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucStatusCodeSuccess, sizeof( ucStatusCodeSuccess ), "OptionStatusMessage" );
    }
}

static void prvAddOptionPreference( BaseType_t xIsWrite )
{
    uint8_t ucVal;
    uint16_t usVal;

    if( xIsWrite == pdTRUE )
    {
        /* Option Preference */
        usVal = DHCPv6_Option_Preference;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionPreference" );
        usVal = 1U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionPreferenceLength" );
        /* Put 0 as preference value */
        ucVal = 0U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite8, &ucVal, 1, "OptionPreferenceValue" );
    }
    else
    {
        /* Option Preference */
        usVal = DHCPv6_Option_Preference;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionPreference" );
        usVal = 1U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionPreferenceLength" );
        /* Put 0 as preference value */
        ucVal = 0U;
        vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "OptionPreferenceValue" );
    }
}

static void prvAddOptionList( BaseType_t xIsWrite )
{
    uint16_t usVal;

    if( xIsWrite == pdTRUE )
    {
        /* Option List */
        usVal = DHCPv6_Option_Option_List;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionList" );
        usVal = 4U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionListLength" );
        usVal = DHCP6_OPTION_REQUEST_DNS;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionListDNS" );
        usVal = DHCP6_OPTION_REQUEST_DOMAIN_SEARCH_LIST;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionListDomainSearchList" );
    }
    else
    {
        /* Option List */
        usVal = DHCPv6_Option_Option_List;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionList" );
        usVal = 4U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionListLength" );
        usVal = DHCP6_OPTION_REQUEST_DNS;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionListDNS" );
        usVal = DHCP6_OPTION_REQUEST_DOMAIN_SEARCH_LIST;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionListDomainSearchList" );
    }
}

static void prvAddOptionDNSServer( BaseType_t xIsWrite,
                                   uint8_t ucDNSNum )
{
    uint16_t usVal;
    int i;

    TEST_ASSERT_LESS_OR_EQUAL( 3, ucDNSNum );

    if( xIsWrite == pdTRUE )
    {
        /* Option DNS recursive name server */
        usVal = DHCPv6_Option_DNS_recursive_name_server;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionDNSRecursiveNameServer" );
        usVal = 16U * ucDNSNum;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionDNSRecursiveNameServerLength" );

        for( i = 0; i < ucDNSNum; i++ )
        {
            vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, &xDNSAddress[ i ], sizeof( IPv6_Address_t ), "OptionDNSInfo" );
        }
    }
    else
    {
        /* Option DNS recursive name server */
        usVal = DHCPv6_Option_DNS_recursive_name_server;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionDNSRecursiveNameServer" );
        usVal = 16U * ucDNSNum;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionDNSRecursiveNameServerLength" );

        for( i = 0; i < ucDNSNum; i++ )
        {
            vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &xDNSAddress[ i ], sizeof( IPv6_Address_t ), "OptionDNSInfo" );
        }
    }
}

static void prvAddOptionDomainSearchList( BaseType_t xIsWrite )
{
    uint16_t usVal;
    uint8_t ucValCustom[ 2 ];

    if( xIsWrite == pdTRUE )
    {
        /* Option DNS recursive name server */
        usVal = DHCPv6_Option_Domain_Search_List;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionDomainSearchList" );
        usVal = 2U;
        vAddBitOperation( eTestDHCPv6BitOperationWrite16, &usVal, 2, "OptionDomainSearchListLength" );
        vAddBitOperation( eTestDHCPv6BitOperationWriteCustom, &ucValCustom, 2, "OptionDomainSearchListValue" );
    }
    else
    {
        /* Option DNS recursive name server */
        usVal = DHCPv6_Option_Domain_Search_List;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionDomainSearchList" );
        usVal = 2U;
        vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionDomainSearchListLength" );
        vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &ucValCustom, 2, "OptionDomainSearchListValue" );
    }
}

/**
 * @brief Prepare function calls for sending DHCPv6 solicitation message.
 */
static void prvPrepareSolicitation()
{
    prvSetBitOperationStub();
    prvAddMsgHeader( pdTRUE, DHCPv6_message_Type_Solicit );
    prvAddOptionClient( pdTRUE );
    prvAddOptionElapsedTime( pdTRUE );
    prvAddOptionIA_PD( pdTRUE );
    prvAddOptionIA_NA( pdTRUE, 12U );
}

/**
 * @brief Prepare buffer content as DHCPv6 advertise.
 */
static void prvPrepareAdvertise()
{
    /* We hard code the option sequence in advertise message.
     * 1. Client ID
     * 2. Server ID
     * 3. IA_NA
     *     - Sub-option IA Address
     *     - Sub-option IA Prefix
     *     - Sub-option Status Code
     * 4. Status Code
     * 5. Preference
     */
    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Advertise );
    prvAddOptionClient( pdFALSE );
    prvAddOptionServer( pdFALSE, pdFALSE, pdFALSE, pdFALSE );
    prvAddOptionIA_NA( pdFALSE, 82U );
    /* Add IA_Address as sub-option in IA_NA */
    prvAddOptionIAAddress( pdFALSE );
    /* Add IA_Prefix as sub-option in IA_NA */
    prvAddOptionIA_Prefix( pdFALSE );
    /* Add Status code as sub-option in IA_NA */
    prvAddOptionStatusCode( pdFALSE );
    /* Add Status code as option */
    prvAddOptionStatusCode( pdFALSE );
    prvAddOptionPreference( pdFALSE );
}

/**
 * @brief Prepare buffer content as DHCPv6 advertise with IA_TA option.
 */
static void prvPrepareAdvertiseIATA()
{
    /* We hard code the option sequence in advertise message.
     * 1. Client ID
     * 2. Server ID
     * 3. IA_TA - not implemented, ignored
     * 4. IA_PD
     */
    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Advertise );
    prvAddOptionClient( pdFALSE );
    prvAddOptionServer( pdFALSE, pdFALSE, pdFALSE, pdFALSE );
    prvAddOptionIA_TA( pdFALSE );
    prvAddOptionIA_PD( pdFALSE );
}

/**
 * @brief Prepare buffer content as DHCPv6 advertise without server ID.
 */
static void prvPrepareAdvertiseNoServerID()
{
    /* We hard code the option sequence in advertise message.
     * 1. Client ID
     * 2. IA_NA
     *     - Sub-option IA Address
     *     - Sub-option IA Prefix
     *     - Sub-option Status Code
     * 3. Status Code
     * 5. Preference
     */
    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Advertise );
    prvAddOptionClient( pdFALSE );
    prvAddOptionIA_NA( pdFALSE, 82U );
    /* Add IA_Address as sub-option in IA_NA */
    prvAddOptionIAAddress( pdFALSE );
    /* Add IA_Prefix as sub-option in IA_NA */
    prvAddOptionIA_Prefix( pdFALSE );
    /* Add Status code as sub-option in IA_NA */
    prvAddOptionStatusCode( pdFALSE );
    /* Add Status code as option */
    prvAddOptionStatusCode( pdFALSE );
    prvAddOptionPreference( pdFALSE );
}

/**
 * @brief Prepare buffer content as DHCPv6 advertise.
 */
static void prvPrepareAdvertiseSubStatusCodeFail()
{
    /* We hard code the option sequence in advertise message.
     * 1. Client ID
     * 2. Server ID
     * 3. IA_NA
     *     - Sub-option IA Address
     *     - Sub-option IA Prefix
     *     - Sub-option Status Code
     * 4. Status Code
     * 5. Preference
     */
    uint16_t usVal;
    uint8_t usStatusFail[] = "Fail";

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Advertise );
    prvAddOptionClient( pdFALSE );
    prvAddOptionServer( pdFALSE, pdFALSE, pdFALSE, pdFALSE );
    prvAddOptionIA_NA( pdFALSE, 79U );
    /* Add IA_Address as sub-option in IA_NA */
    prvAddOptionIAAddress( pdFALSE );
    /* Add IA_Prefix as sub-option in IA_NA */
    prvAddOptionIA_Prefix( pdFALSE );
    /* Add Status code as sub-option in IA_NA */
    usVal = DHCPv6_Option_Status_Code;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubStatus" );
    usVal = 6U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubStatusLength" );
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubStatusValue" );
    /* Status message */
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, usStatusFail, sizeof( usStatusFail ), "OptionIA_NASubStatusMessage" );
}

/**
 * @brief Prepare function calls for sending DHCPv6 request message.
 */
static void prvPrepareRequest()
{
    /* We hard code the option sequence in request message.
     * 1. Client ID
     * 2. Server ID
     * 3. Option List
     * 4. Elapsed Time
     * 5. IA_PD
     * 6. IA_NA
     * 7. DNS Server List
     */
    prvSetBitOperationStub();
    prvAddMsgHeader( pdTRUE, DHCPv6_message_Type_Request );
    prvAddOptionClient( pdTRUE );
    prvAddOptionServer( pdTRUE, pdFALSE, pdFALSE, pdFALSE );
    prvAddOptionList( pdTRUE );
    prvAddOptionElapsedTime( pdTRUE );
    prvAddOptionIA_PD( pdTRUE );
    prvAddOptionIA_NA( pdTRUE, 12U );
    prvAddOptionDNSServer( pdTRUE, 0 );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReply()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID
     * 2. Server ID
     * 3. IA_NA
     *     - Sub-option IA Address
     * 4. Status Code
     * 5. Preference
     */
    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );
    prvAddOptionClient( pdFALSE );
    prvAddOptionServer( pdFALSE, pdFALSE, pdFALSE, pdFALSE );
    prvAddOptionIA_NA( pdFALSE, 40U );
    /* IA_NA sub-option IA Address */
    prvAddOptionIAAddress( pdFALSE );
    prvAddOptionStatusCode( pdFALSE );
    prvAddOptionPreference( pdFALSE );
}

/**
 * @brief Append 1 DNS server info to reply message.
 */
static void prvPrepareReplyWithDomainSearchList()
{
    prvPrepareReply();
    prvAddOptionDomainSearchList( pdFALSE );
}

/**
 * @brief Append 1 DNS server info to reply message.
 */
static void prvPrepareReplyWithDNS()
{
    prvPrepareReply();
    prvAddOptionDNSServer( pdFALSE, 1 );
}

/**
 * @brief Append 3 DNS servers info ( more than ipconfigENDPOINT_DNS_ADDRESS_COUNT ) to reply message.
 */
static void prvPrepareReplyWithMultipleDNS()
{
    prvPrepareReply();
    prvAddOptionDNSServer( pdFALSE, 3 );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply with different server DUID type.
 */
static void prvPrepareReplyDifferentServerDUIDType()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID
     * 2. Server ID with different DUID type
     * 3. IA_NA
     *     - Sub-option IA Address
     * 4. Status Code
     * 5. Preference
     */
    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );
    prvAddOptionClient( pdFALSE );
    prvAddOptionServer( pdFALSE, pdTRUE, pdFALSE, pdFALSE );
    prvAddOptionIA_NA( pdFALSE, 40U );
    /* IA_NA sub-option IA Address */
    prvAddOptionIAAddress( pdFALSE );
    prvAddOptionStatusCode( pdFALSE );
    prvAddOptionPreference( pdFALSE );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply with different server DUID type.
 */
static void prvPrepareReplyDifferentServerLength()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID
     * 2. Server ID with different DUID length
     * 3. IA_NA
     *     - Sub-option IA Address
     * 4. Status Code
     * 5. Preference
     */
    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );
    prvAddOptionClient( pdFALSE );
    prvAddOptionServer( pdFALSE, pdFALSE, pdTRUE, pdFALSE );
    prvAddOptionIA_NA( pdFALSE, 40U );
    /* IA_NA sub-option IA Address */
    prvAddOptionIAAddress( pdFALSE );
    prvAddOptionStatusCode( pdFALSE );
    prvAddOptionPreference( pdFALSE );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply with different server DUID.
 */
static void prvPrepareReplyDifferentServerDUID()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID
     * 2. Server ID with different DUID
     * 3. IA_NA
     *     - Sub-option IA Address
     * 4. Status Code
     * 5. Preference
     */
    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );
    prvAddOptionClient( pdFALSE );
    prvAddOptionServer( pdFALSE, pdFALSE, pdFALSE, pdTRUE );
    prvAddOptionIA_NA( pdFALSE, 40U );
    /* IA_NA sub-option IA Address */
    prvAddOptionIAAddress( pdFALSE );
    prvAddOptionStatusCode( pdFALSE );
    prvAddOptionPreference( pdFALSE );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyInvalidIA_NA()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID
     * 2. Server ID
     * 3. IA_NA - with invalid sub-option length
     */
    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );
    prvAddOptionClient( pdFALSE );
    prvAddOptionServer( pdFALSE, pdFALSE, pdFALSE, pdFALSE );
    /* IA_NA with invalid sub-option length */
    prvAddOptionIA_NA( pdFALSE, 14U );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyInvalidIA_NASubOption()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID
     * 2. Server ID
     * 3. IA_NA - with invalid sub-option
     */
    uint16_t usVal;
    uint8_t ucValCustom[ 2 ];

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );
    prvAddOptionClient( pdFALSE );
    prvAddOptionServer( pdFALSE, pdFALSE, pdFALSE, pdFALSE );
    /* IA_NA with invalid sub-option */
    prvAddOptionIA_NA( pdFALSE, 42U );
    /* IA_NA sub-option unknown */
    usVal = 0xFF;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubInvalid" );
    usVal = 2U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubInvalidLength" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &ucValCustom, 2, "OptionIA_NASubInvalidValue" );
    /* IA_NA sub-option IA address with invalid length */
    usVal = DHCPv6_Option_IA_Address;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAAddress" );
    usVal = 20U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_NASubIAAddressLength" );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyInvalidIA_PD()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID
     * 2. Server ID
     * 3. IA_PD - with invalid sub-option length
     */
    uint16_t usVal;
    uint32_t ulVal;

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );
    prvAddOptionClient( pdFALSE );
    prvAddOptionServer( pdFALSE, pdFALSE, pdFALSE, pdFALSE );
    /* Option IA_PD with invalid sub-option length */
    usVal = DHCPv6_Option_IA_for_Prefix_Delegation;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_PD" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionIA_PDLength" );
    ulVal = TEST_DHCPV6_IAID;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_PDIAID" );
    ulVal = 3600U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_PDT1" );
    ulVal = 5400U;
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "OptionIA_PDT2" );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyClientIDTooSmall()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID with length too small
     */
    uint16_t usVal;
    uint32_t ulVal;

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );

    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientID" );
    usVal = 2U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDLengthSmall" );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyClientIDTooBig()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID with length too small
     */
    uint16_t usVal;
    uint32_t ulVal;

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );

    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientID" );
    usVal = 256U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDLengthBig" );
    /* Client ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDHWType" );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyClientIDLengthWrong()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID with length too small
     */
    uint16_t usVal;
    uint32_t ulVal;
    uint8_t ucValCustom[ 12 ];

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );

    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientID" );
    usVal = 16U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDLength" );
    /* Client ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDHWType" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &ucValCustom, 12, "OptionClientIDRemainBig" );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyClientIDPeekFalse()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID with length too small
     */
    uint16_t usVal;
    uint32_t ulVal;

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );

    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDLength" );
    /* Client ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDHWType" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &ucTestDHCPv6OptionClientID[ 4 ], sizeof( ucTestDHCPv6OptionClientID ) - 4, "OptionClientIDRemain" );
    /* Call peek function to compare client ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadPeek, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ), "OptionClientIDPeekFalse" );
    vAddBitOperation( eTestDHCPv6BitOperationReturnFalse, NULL, 0, "" );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyClientIDContentWrong()
{
    /* We hard code the option sequence in reply message.
     * 1. Client ID with length too small
     */
    uint16_t usVal;
    uint32_t ulVal;
    uint8_t ucWrongClientID[] = { 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11 };

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );

    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDLength" );
    /* Client ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDHWType" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &ucWrongClientID[ 4 ], sizeof( ucWrongClientID ) - 4, "OptionClientIDRemain" );
    /* Call peek function to compare client ID */
    vAddBitOperation( eTestDHCPv6BitOperationReadPeek, ucWrongClientID, sizeof( ucWrongClientID ), "OptionClientIDPeek" );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyServerIDTooSmall()
{
    /* We hard code the option sequence in reply message.
     * 1. Server ID with length too small
     */
    uint16_t usVal;
    uint32_t ulVal;

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );

    usVal = DHCPv6_Option_Server_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerID" );
    usVal = 2U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDLengthSmall" );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyServerIDTooBig()
{
    /* We hard code the option sequence in reply message.
     * 1. Server ID with length too small
     */
    uint16_t usVal;
    uint32_t ulVal;

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );

    usVal = DHCPv6_Option_Server_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerID" );
    usVal = 256U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDLengthBig" );
    /* Client ID - DUID & hardware Type */
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDDUIDType" );
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionServerIDHWType" );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyDNSLengthZero()
{
    /* We hard code the option sequence in reply message.
     * 1. DNS info with 0 length
     */
    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );
    prvAddOptionDNSServer( pdFALSE, 0 );
}

/**
 * @brief Prepare buffer content as DHCPv6 reply.
 */
static void prvPrepareReplyDNSLengthNotAllow()
{
    /* We hard code the option sequence in reply message.
     * 1. DNS info with 1 length (length must be a multiple of 16)
     */
    uint16_t usVal;

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Reply );
    /* Option DNS recursive name server */
    usVal = DHCPv6_Option_DNS_recursive_name_server;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionDNSRecursiveNameServer" );
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionDNSRecursiveNameServerValue" );
}

/**
 * @brief Prepare buffer content with known message type.
 */
static void prvPrepareUnknownMsgType()
{
    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, 0xEE );
}

/**
 * @brief Prepare buffer content with different transaction ID.
 */
static void prvPrepareWrongTransactionID()
{
    uint8_t ucVal;
    uint8_t ucTestInvalidDHCPv6TransactionID[] = { 0x65, 0x43, 0x21 };

    prvSetBitOperationStub();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Advertise;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "TypeAdvertise" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestInvalidDHCPv6TransactionID, 3, "InvalidTransactionID" );
}

/**
 * @brief Prepare buffer content with transaction ID then set the error bit.
 */
static void prvPrepareErrorTransactionID()
{
    uint8_t ucVal;

    prvSetBitOperationStub();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Advertise;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "TypeAdvertise" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );
    vAddBitOperation( eTestDHCPv6BitOperationSetError, 0, 0, "SetError" );
}

/**
 * @brief Prepare operations for reading error on option.
 */
static void prvPrepareErrorOption()
{
    uint8_t ucVal;
    uint16_t usVal;

    prvSetBitOperationStub();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Advertise;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "TypeAdvertise" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );
    /* Option Client ID */
    usVal = DHCPv6_Option_Client_Identifier;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientID" );
    usVal = 14U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionClientIDLength" );
    vAddBitOperation( eTestDHCPv6BitOperationSetError, 0, 0, "SetError" );
}

/**
 * @brief Prepare content with status code but the option length is less than minimal requirement.
 */
static void prvPrepareAdvertiseStatusCodeLengthTooSmall()
{
    uint8_t ucVal;
    uint16_t usVal;
    uint32_t ulVal;

    xBitConfig_init_Stub( xStubxBitConfig_init );
    pucBitConfig_peek_last_index_uc_Stub( xStubpucBitConfig_peek_last_index_uc );
    ucBitConfig_read_8_Stub( xStubucBitConfig_read_8 );
    xBitConfig_read_uc_Stub( xStubxBitConfig_read_uc );
    usBitConfig_read_16_Stub( xStubusBitConfig_read_16 );
    ulBitConfig_read_32_Stub( xStubulBitConfig_read_32 );
    vBitConfig_release_Ignore();

    /* Provide the message type and transaction ID for DHCPv6. */
    ucVal = DHCPv6_message_Type_Advertise;
    vAddBitOperation( eTestDHCPv6BitOperationRead8, &ucVal, 1, "TypeAdvertise" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucTestDHCPv6TransactionID, 3, "TransactionID" );

    /* Option Status Code */
    usVal = DHCPv6_Option_Status_Code;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatus" );
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusLength" );
}

/**
 * @brief Prepare content with status code but the option length is larger than packet size.
 */
static void prvPrepareAdvertiseStatusCodeLengthTooBig()
{
    uint16_t usVal;

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Advertise );

    /* Option Status Code */
    usVal = DHCPv6_Option_Status_Code;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatus" );
    usVal = 0xFFFF;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusLength" );
}

/**
 * @brief Prepare status code with long message.
 */
static void prvPrepareAdvertiseStatusCodeLongMessage()
{
    uint16_t usVal;
    /* For now, local buffer size is 50. Declare a message with larger size. */
    const uint8_t ucStatusCodeLongMessage[] = "012345678901234567890123456789012345678901234567890123456789";

    prvSetBitOperationStub();
    prvAddMsgHeader( pdFALSE, DHCPv6_message_Type_Advertise );

    /* Option Status Code */
    usVal = DHCPv6_Option_Status_Code;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatus" );
    usVal = sizeof( ucStatusCodeLongMessage ) + 2;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusLength" );
    usVal = 1U;
    vAddBitOperation( eTestDHCPv6BitOperationRead16, &usVal, 2, "OptionStatusValue" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, ucStatusCodeLongMessage, 49, "OptionStatusMessage" );
    vAddBitOperation( eTestDHCPv6BitOperationReadCustom, &( ucStatusCodeLongMessage[ 49 ] ), sizeof( ucStatusCodeLongMessage ) - 49, "OptionStatusMessage2" );
}

/**
 * @brief Check if eGetDHCPv6State can return DHCP state correctly.
 */
void test_eGetDHCPv6State_HappyPath()
{
    NetworkEndPoint_t xEndPoint;
    eDHCPState_t eState = eInitialWait, eStateMax = eNotUsingLeasedAddress;
    eDHCPState_t eReturnState;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );

    for( eState = eInitialWait; eState <= eNotUsingLeasedAddress; eState++ )
    {
        xEndPoint.xDHCPData.eDHCPState = eState;
        eReturnState = eGetDHCPv6State( &xEndPoint );
        TEST_ASSERT_EQUAL( eState, eReturnState );
    }
}

/**
 * @brief Check if eGetDHCPv6State trigger assertion when input is NULL.
 */
void test_eGetDHCPv6State_NullInput()
{
    catch_assert( eGetDHCPv6State( NULL ) );
}

/**
 * @brief Check if vDHCPv6Process trigger assertion when input is NULL.
 */
void test_vDHCPv6Process_NullInput()
{
    catch_assert( vDHCPv6Process( pdTRUE, NULL ) );
    catch_assert( vDHCPv6Process( pdFALSE, NULL ) );
}

/**
 * @brief Check if vDHCPv6Process can reset successfully from eInitialWait.
 */
void test_vDHCPv6Process_ResetFromInit()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    xEndPoint.xDHCPData.eDHCPState = eInitialWait;
    xEndPoint.xDHCPData.eExpectedState = eInitialWait;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xLocalDHCPv6Socket );
    xSocketValid_ExpectAndReturn( &xLocalDHCPv6Socket, pdTRUE );
    prvSetCheckerAndReturn_FreeRTOS_setsockopt( &xLocalDHCPv6Socket, sizeof( TickType_t ) );
    FreeRTOS_setsockopt_Stub( xStubFreeRTOS_setsockopt );
    prvSetCheckerAndReturn_vSocketBind( &xLocalDHCPv6Socket );
    vSocketBind_Stub( xStubvSocketBind );
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdTRUE, &xEndPoint );
    vPortFree( xEndPoint.pxDHCPMessage ); /* Make LeakSanitizer happy. */

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingSendFirstDiscover. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint.xDHCPData.eDHCPState );
    /* We should set 2 socket options (FREERTOS_SO_RCVTIMEO and FREERTOS_SO_SNDTIMEO). */
    TEST_ASSERT_EQUAL( ( 1 << FREERTOS_SO_RCVTIMEO | 1 << FREERTOS_SO_SNDTIMEO ), xStubFreeRTOS_setsockopt_lOptionName_BitMap );
}

/**
 * @brief Check if vDHCPv6Process can reset successfully from eLeasedAddress.
 */
void test_vDHCPv6Process_ResetFromLease()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xLocalDHCPv6Socket;
    const IPv6_Address_t xIPAddress = { 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    DHCPMessage_IPv6_t xDHCPMessage;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    xEndPoint.xDHCPData.eDHCPState = eLeasedAddress;
    xEndPoint.xDHCPData.eExpectedState = eLeasedAddress;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xLocalDHCPv6Socket );
    xSocketValid_ExpectAndReturn( &xLocalDHCPv6Socket, pdTRUE );
    prvSetCheckerAndReturn_FreeRTOS_setsockopt( &xLocalDHCPv6Socket, sizeof( TickType_t ) );
    FreeRTOS_setsockopt_Stub( xStubFreeRTOS_setsockopt );
    prvSetCheckerAndReturn_vSocketBind( &xLocalDHCPv6Socket );
    vSocketBind_Stub( xStubvSocketBind );
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdTRUE, &xEndPoint );

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingSendFirstDiscover. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint.xDHCPData.eDHCPState );
    /* We should set 2 socket options (FREERTOS_SO_RCVTIMEO and FREERTOS_SO_SNDTIMEO). */
    TEST_ASSERT_EQUAL( ( 1 << FREERTOS_SO_RCVTIMEO | 1 << FREERTOS_SO_SNDTIMEO ), xStubFreeRTOS_setsockopt_lOptionName_BitMap );
}

/**
 * @brief Check if vDHCPv6Process can reset successfully when state is different from expect state.
 */
void test_vDHCPv6Process_ResetDifferentState()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xLocalDHCPv6Socket;
    const IPv6_Address_t xIPAddress = { 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
    DHCPMessage_IPv6_t xDHCPMessage;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    xEndPoint.xDHCPData.eDHCPState = eInitialWait;
    xEndPoint.xDHCPData.eExpectedState = eLeasedAddress;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xLocalDHCPv6Socket );
    xSocketValid_ExpectAndReturn( &xLocalDHCPv6Socket, pdTRUE );
    prvSetCheckerAndReturn_FreeRTOS_setsockopt( &xLocalDHCPv6Socket, sizeof( TickType_t ) );
    FreeRTOS_setsockopt_Stub( xStubFreeRTOS_setsockopt );
    prvSetCheckerAndReturn_vSocketBind( &xLocalDHCPv6Socket );
    vSocketBind_Stub( xStubvSocketBind );
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdTRUE, &xEndPoint );

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingSendFirstDiscover. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint.xDHCPData.eDHCPState );
    /* We should set 2 socket options (FREERTOS_SO_RCVTIMEO and FREERTOS_SO_SNDTIMEO). */
    TEST_ASSERT_EQUAL( ( 1 << FREERTOS_SO_RCVTIMEO | 1 << FREERTOS_SO_SNDTIMEO ), xStubFreeRTOS_setsockopt_lOptionName_BitMap );
}

/**
 * @brief Check if vDHCPv6Process can continue from eWaitingSendFirstDiscover successfully.
 */
void test_vDHCPv6Process_SolicitationHappyPath()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    xEndPoint.xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );

    /* Prepare bit message for solicitation. */
    prvPrepareSolicitation();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* The endpoint sends the DHCPv6 Solicitation message to find the DHCPv6 server.
     * Then change the state to eWaitingOffer. */
    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL( 0, xDHCPMessage.ulTimeStamp );
    TEST_ASSERT_EQUAL( TEST_DHCPV6_TRANSACTION_ID, xEndPoint.xDHCPData.ulTransactionId );
}

/**
 * @brief Check if vDHCPv6Process can stop when state is different from expect state.
 */
void test_vDHCPv6Process_SolicitationDifferentState()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    xEndPoint.xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.eExpectedState = eLeasedAddress;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can continue from eWaitingOffer successfully.
 */
void test_vDHCPv6Process_AdvertiseHappyPath()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareAdvertise();

    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );

    prvPrepareRequest();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* The endpoint receives the DHCPv6 Advertise message from DHCPv6 server.
     * Then change the state to eWaitingAcknowledge. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can ignore IA_TA option which is not supported.
 */
void test_vDHCPv6Process_AdvertiseIATA()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 93 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareAdvertiseIATA();

    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );

    prvPrepareRequest();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* The endpoint receives the DHCPv6 Advertise message from DHCPv6 server.
     * Then change the state to eWaitingAcknowledge. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can continue from eWaitingAcknowledge successfully.
 */
void test_vDHCPv6Process_ReplyHappyPath()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 102 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReply();

    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpv6DEFAULT_LEASE_TIME );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* Check if the IP address provided in reply is set to endpoint properly. */
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPAddress.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief The address of endpoint is timeout. Endpoint sends the DHCPv6 request to ask for renew.
 */
void test_vDHCPv6Process_DHCPLeaseTimeout()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eLeasedAddress;
    xEndPoint.xDHCPData.eExpectedState = eLeasedAddress;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    xDHCPv6Socket = &xLocalDHCPv6Socket;
    /* Assume that DHCPv6 had got the advertise and sent request once. */
    xEndPoint.xDHCPData.xDHCPTxTime = pdMS_TO_TICKS( 0 );
    xEndPoint.xDHCPData.xDHCPTxPeriod = pdMS_TO_TICKS( 5000 );
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    /* Because we assume DHCPv6 got advertise, so we should set the server information in DHCP message. */
    xEndPoint.pxDHCPMessage = &xDHCPMessage;
    xDHCPMessage.xServerID.uxLength = 10U; /* 14 - 4 */
    xDHCPMessage.xServerID.usDUIDType = 1U;
    xDHCPMessage.xServerID.usHardwareType = 1U;
    memcpy( xDHCPMessage.xServerID.pucID, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ) );

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );

    prvPrepareRequest();
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* The address of endpoint is leased. Endpoint sends the DHCPv6 request to ask for renew.
     * Then change the state to eWaitingAcknowledge. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief When the socket is failed on creation, we should use default setting as IP address.
 */
void test_vDHCPv6Process_GiveupWhenSocketNull()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_defaults.xIPAddress.ucBytes, &xDefaultIPAddress.ucBytes, sizeof( IPv6_Address_t ) );
    memcpy( xEndPoint.ipv6_defaults.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_defaults.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = NULL;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* When giving up, the state is set to eNotUsingLeasedAddress. Then using default setting as IPv6 address. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xEndPoint.xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPAddress.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief Check if vDHCPv6Process send another DHCPv6 reply when timeout triggered on waiting reply.
 * Then reset the state to initial when timeout period is out of bound.
 */
void test_vDHCPv6Process_WaitReplyTimeout()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    /* Assume that DHCPv6 had got the advertise and sent request once. */
    xEndPoint.xDHCPData.xDHCPTxTime = pdMS_TO_TICKS( 0 );
    xEndPoint.xDHCPData.xDHCPTxPeriod = pdMS_TO_TICKS( 5000 );
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    /* Because we assume DHCPv6 got advertise, so we should set the server information in DHCP message. */
    xEndPoint.pxDHCPMessage = &xDHCPMessage;
    xDHCPMessage.xServerID.uxLength = 10U; /* 14 - 4 */
    xDHCPMessage.xServerID.usDUIDType = 1U;
    xDHCPMessage.xServerID.usHardwareType = 1U;
    memcpy( xDHCPMessage.xServerID.pucID, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ) );

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    /* 1st timeout at 5001ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) );
    /* Update tx time to 5001ms. And the tx period is updated to 10000ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) );
    /* 2nd timeout at 5001 + 10001 ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) + pdMS_TO_TICKS( 10001 ) );
    /* Update tx time to 5001ms + 10001 ms. And the tx period is updated to 20000ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) + pdMS_TO_TICKS( 10001 ) );
    /* 3rd timeout at 5001 + 10001 + 20001 ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) + pdMS_TO_TICKS( 10001 ) + pdMS_TO_TICKS( 20001 ) );
    /* Timeout triggered. Reset the DHCPv6 to initial state */

    /* 1st timeout makes 1st request message resend. */
    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );
    prvPrepareRequest();

    /* 2nd timeout makes 2nd request message resend. */
    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );
    prvPrepareRequest();

    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    /* 1st process to trigger 1st timeout. */
    vDHCPv6Process( pdFALSE, &xEndPoint );
    /* 2nd process to trigger 2nd timeout. */
    vDHCPv6Process( pdFALSE, &xEndPoint );
    /* 3rd process to trigger final timeout. */
    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eInitialWait, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packets with unknown message type.
 */
void test_vDHCPv6Process_prvDHCPv6Analyse_UnknownMsgType()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareUnknownMsgType();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packets with wrong transaction ID.
 */
void test_vDHCPv6Process_prvDHCPv6Analyse_WrongTransactionID()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareWrongTransactionID();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packets while error occurred on bit configuration.
 */
void test_vDHCPv6Process_prvDHCPv6Analyse_ReadTransactionIDError()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareErrorTransactionID();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packets while error occurred on reading option.
 */
void test_vDHCPv6Process_prvDHCPv6Analyse_ReadOptionError()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareErrorOption();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packets while advertise message without server ID.
 */
void test_vDHCPv6Process_prvDHCPv6Analyse_LackServerID()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 126 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareAdvertiseNoServerID();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packets while failing on initialization of bit configuration.
 */
void test_vDHCPv6Process_prvDHCPv6Analyse_BitConfigInitError()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 126 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    xBitConfig_init_IgnoreAndReturn( pdFAIL );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packets when any option's length is less than minimal requirement.
 */
void test_vDHCPv6Process_prvIsOptionLengthValid_OptionLessThanMinLength()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 500 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareAdvertiseStatusCodeLengthTooSmall();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packets when any option's length is larger than packet size.
 */
void test_vDHCPv6Process_prvIsOptionLengthValid_OptionLargerThanMaxLength()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 500 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareAdvertiseStatusCodeLengthTooBig();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can truncate the message in the local buffer.
 */
void test_vDHCPv6Process_prvDHCPv6_handleStatusCode_MessageTooLong()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 71 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareAdvertiseStatusCodeLongMessage();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Receive the message when global endpoint list is empty.
 */
void test_vDHCPv6Process_xDHCPv6Process_PassReplyToEndPoint_EmptyEndpointList()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareAdvertise();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if DHCPv6 can search endpoint correctly.
 */
void test_vDHCPv6Process_xDHCPv6Process_PassReplyToEndPoint_MultipleEndpoints()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    /* 3 endpoints:
     *  - IPv4 endpoint with DHCP disabled
     *  - IPv4 endpoint with DHCP enabled
     *  - IPv6 endpoint with DHCP disabled
     *  - IPv6 endpoint with DHCP enabled with different transaction ID
     *  - IPv6 endpoint with DHCP enabled with state eLeasedAddress */
    NetworkEndPoint_t xMultipleEndPoint[ 5 ];
    const uint32_t ulDifferentTransactionID = 0x111111;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    memset( &xMultipleEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xMultipleEndPoint[ 0 ].xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    xMultipleEndPoint[ 0 ].bits.bIPv6 = pdFALSE;
    xMultipleEndPoint[ 0 ].bits.bWantDHCP = pdFALSE;

    memset( &xMultipleEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xMultipleEndPoint[ 1 ].xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    xMultipleEndPoint[ 1 ].bits.bIPv6 = pdFALSE;
    xMultipleEndPoint[ 1 ].bits.bWantDHCP = pdTRUE;

    memset( &xMultipleEndPoint[ 2 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xMultipleEndPoint[ 2 ].xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    xMultipleEndPoint[ 2 ].bits.bIPv6 = pdTRUE;
    xMultipleEndPoint[ 2 ].bits.bWantDHCP = pdFALSE;

    memset( &xMultipleEndPoint[ 3 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xMultipleEndPoint[ 3 ].xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    xMultipleEndPoint[ 3 ].bits.bIPv6 = pdTRUE;
    xMultipleEndPoint[ 3 ].bits.bWantDHCP = pdTRUE;
    xMultipleEndPoint[ 3 ].xDHCPData.eDHCPState = eWaitingOffer;
    xMultipleEndPoint[ 3 ].xDHCPData.eExpectedState = eWaitingOffer;
    xMultipleEndPoint[ 3 ].xDHCPData.ulTransactionId = ulDifferentTransactionID;

    memset( &xMultipleEndPoint[ 4 ], 0, sizeof( NetworkEndPoint_t ) );
    memcpy( xMultipleEndPoint[ 4 ].xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    xMultipleEndPoint[ 4 ].bits.bIPv6 = pdTRUE;
    xMultipleEndPoint[ 4 ].bits.bWantDHCP = pdTRUE;
    xMultipleEndPoint[ 4 ].xDHCPData.eDHCPState = eLeasedAddress;
    xMultipleEndPoint[ 4 ].xDHCPData.eExpectedState = eLeasedAddress;
    xMultipleEndPoint[ 4 ].xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;

    pxNetworkEndPoints = &xMultipleEndPoint[ 0 ];
    xMultipleEndPoint[ 0 ].pxNext = &xMultipleEndPoint[ 1 ];
    xMultipleEndPoint[ 1 ].pxNext = &xMultipleEndPoint[ 2 ];
    xMultipleEndPoint[ 2 ].pxNext = &xMultipleEndPoint[ 3 ];
    xMultipleEndPoint[ 3 ].pxNext = &xMultipleEndPoint[ 4 ];
    xMultipleEndPoint[ 4 ].pxNext = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;
    xDHCPMessage.xServerID.usDUIDType = 1U;
    xDHCPMessage.xServerID.uxLength = 10U;
    memcpy( xDHCPMessage.xServerID.pucID, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ) );

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareAdvertise();

    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );

    prvPrepareRequest();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief The server DUID type in reply message is different from advertise.
 */
void test_vDHCPv6Process_xDHCPv6Process_PassReplyToEndPoint_DifferentServerDUIDType()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;
    xDHCPMessage.xServerID.usDUIDType = 1U;
    xDHCPMessage.xServerID.uxLength = 14U;
    memcpy( xDHCPMessage.xServerID.pucID, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ) );

    FreeRTOS_recvfrom_IgnoreAndReturn( 102 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyDifferentServerDUIDType();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief The server ID length in reply message is different from advertise.
 */
void test_vDHCPv6Process_xDHCPv6Process_PassReplyToEndPoint_DifferentServerLength()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;
    xDHCPMessage.xServerID.usDUIDType = 1U;
    xDHCPMessage.xServerID.uxLength = 10U;
    memcpy( xDHCPMessage.xServerID.pucID, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ) );

    FreeRTOS_recvfrom_IgnoreAndReturn( 100 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyDifferentServerLength();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief The server ID length in reply message is invalid.
 */
void test_vDHCPv6Process_xDHCPv6Process_PassReplyToEndPoint_DifferentServerLength_HigherThanThreshold()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;
    xDHCPMessage.xServerID.usDUIDType = 1U;
    xDHCPMessage.xServerID.uxLength = 150U;
    memcpy( xDHCPMessage.xServerID.pucID, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ) );

    FreeRTOS_recvfrom_IgnoreAndReturn( 100 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyDifferentServerLength();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}


/**
 * @brief The server DUID in reply message is different from advertise.
 */
void test_vDHCPv6Process_xDHCPv6Process_PassReplyToEndPoint_DifferentServerDUID()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;
    xDHCPMessage.xServerID.usDUIDType = 1U;
    xDHCPMessage.xServerID.uxLength = 10U;
    memcpy( xDHCPMessage.xServerID.pucID, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ) );

    FreeRTOS_recvfrom_IgnoreAndReturn( 102 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyDifferentServerDUID();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief DHCPv6 agent receives the message for different endpoint.
 */
void test_vDHCPv6Process_xDHCPv6Process_PassReplyToEndPoint_DifferentEndpoint()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;
    NetworkEndPoint_t xDifferentEndPoint;
    DHCPMessage_IPv6_t xDifferentDHCPMessage;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );
    memset( &xDifferentDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memset( &xDifferentEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    xDifferentEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xDifferentEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xDifferentEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xDifferentEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xDifferentEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );
    xDifferentEndPoint.pxDHCPMessage = &xDifferentDHCPMessage;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;
    xDHCPMessage.xServerID.usDUIDType = 1U;
    xDHCPMessage.xServerID.uxLength = 10U;
    memcpy( xDHCPMessage.xServerID.pucID, ucTestDHCPv6OptionServerID, sizeof( ucTestDHCPv6OptionServerID ) );

    FreeRTOS_recvfrom_IgnoreAndReturn( 102 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReply();

    /* These are happened on different endpoint */
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpv6DEFAULT_LEASE_TIME );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xDifferentEndPoint );

    /* The reply is for endpoint. The state is changed to eLeasedAddress. */
    TEST_ASSERT_EQUAL( eLeasedAddress, xEndPoint.xDHCPData.eDHCPState );
    /* No message for different endpoint. Keep in same state. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xDifferentEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief DHCPv6 reset but get failure when allocating memory by pvPortMalloc.
 */
void test_vDHCPv6Process_ResetAllocateFail()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xLocalDHCPv6Socket;
    const IPv6_Address_t xIPAddress = { 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    xEndPoint.xDHCPData.eDHCPState = eLeasedAddress;
    memcpy( xEndPoint.ipv6_settings.xIPAddress.ucBytes, xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xEndPoint.pxDHCPMessage = NULL;

    vAddStubsOperation( eTestStubsAllocateFail );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );

    vDHCPv6Process( pdTRUE, &xEndPoint );

    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xEndPoint.xDHCPData.eDHCPState );
    /* We should set 2 socket options (FREERTOS_SO_RCVTIMEO and FREERTOS_SO_SNDTIMEO). */
    TEST_ASSERT_EQUAL( ( 1 << FREERTOS_SO_RCVTIMEO | 1 << FREERTOS_SO_SNDTIMEO ), xStubFreeRTOS_setsockopt_lOptionName_BitMap );
}

/**
 * @brief FreeRTOS_recvfrom returns failure.
 */
void test_vDHCPv6Process_RecvFailure()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( -pdFREERTOS_ERRNO_ENOTCONN );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* Check if the IP address provided in reply is set to endpoint properly. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief FreeRTOS_recvfrom returns pdFREERTOS_ERRNO_EAGAIN.
 */
void test_vDHCPv6Process_RecvEagain()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( -pdFREERTOS_ERRNO_EAGAIN );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* Check if the IP address provided in reply is set to endpoint properly. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Got 1 DNS server info from reply message.
 */
void test_vDHCPv6Process_vDHCPv6ProcessEndPoint_HandleReply_WithDNS()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 122 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyWithDNS();

    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpv6DEFAULT_LEASE_TIME );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* Check if the IP address provided in reply is set to endpoint properly. */
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPAddress.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief Got multiple DNS server info from reply message.
 */
void test_vDHCPv6Process_vDHCPv6ProcessEndPoint_HandleReply_ManyDNS()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 154 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyWithMultipleDNS();

    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpv6DEFAULT_LEASE_TIME );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* Check if the IP address provided in reply is set to endpoint properly. */
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPAddress.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief Got reply message with short lease time. Should update lease time to minimum value.
 */
void test_vDHCPv6Process_vDHCPv6ProcessEndPoint_HandleReply_ShortLeaseTime()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );
    xEndPoint.xDHCPData.ulLeaseTime = dhcpv6MINIMUM_LEASE_TIME - 1;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 102 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReply();

    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpv6MINIMUM_LEASE_TIME );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* Check if the IP address provided in reply is set to endpoint properly. */
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPAddress.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief Got reply message with valid lease time.
 */
void test_vDHCPv6Process_vDHCPv6ProcessEndPoint_HandleReply_CustomLeaseTime()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );
    xEndPoint.xDHCPData.ulLeaseTime = dhcpv6MINIMUM_LEASE_TIME + 1;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 102 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReply();

    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpv6MINIMUM_LEASE_TIME + 1 );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* Check if the IP address provided in reply is set to endpoint properly. */
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPAddress.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief xApplicationDHCPHook_Multi returns fail while receiving advertise.
 */
void test_vDHCPv6Process_xDHCPv6ProcessEndPoint_HandleAdvertise_HookFailure()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    vAddStubsOperation( eTestStubsHookFail );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    prvPrepareAdvertise();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief xApplicationDHCPHook_Multi returns eDHCPUseDefaults while receiving advertise.
 */
void test_vDHCPv6Process_xDHCPv6ProcessEndPoint_HandleAdvertise_HookDefault()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_defaults.xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xEndPoint.ipv6_defaults.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 144 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    vAddStubsOperation( eTestStubsHookUseDefault );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    prvPrepareAdvertise();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xEndPoint.xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPAddress.ucBytes, xEndPoint.ipv6_defaults.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief Check if xDHCPv6ProcessEndPoint_HandleState triggers assertion when receiving NULL message pointer.
 */
void test_vDHCPv6Process_xDHCPv6ProcessEndPoint_HandleState_NullMessage()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_defaults.xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xEndPoint.ipv6_defaults.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = NULL;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );

    catch_assert( vDHCPv6Process( pdFALSE, &xEndPoint ) );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief DHCPv6 should skip sending solicitation when hook return fail.
 */
void test_vDHCPv6Process_xDHCPv6ProcessEndPoint_HandleState_HookFailure()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xLocalDHCPv6Socket;
    DHCPMessage_IPv6_t xDHCPMessage;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_defaults.xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xEndPoint.ipv6_defaults.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.eExpectedState = eWaitingSendFirstDiscover;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    vAddStubsOperation( eTestStubsHookFail );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief DHCPv6 should skip sending solicitation when hook return eDHCPUseDefaults.
 */
void test_vDHCPv6Process_xDHCPv6ProcessEndPoint_HandleState_HookDefault()
{
    NetworkEndPoint_t xEndPoint;
    struct xSOCKET xLocalDHCPv6Socket;
    DHCPMessage_IPv6_t xDHCPMessage;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_defaults.xIPAddress.ucBytes, xDefaultIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
    xEndPoint.ipv6_defaults.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.eExpectedState = eWaitingSendFirstDiscover;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    vAddStubsOperation( eTestStubsHookUseDefault );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process send another DHCPv6 solicitation when timeout triggered on waiting advertise.
 * Then reset the state to initial when timeout period is out of bound.
 */
void test_vDHCPv6Process_WaitAdvertiseTimeout()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    /* Assume that DHCPv6 has sent solicitation once. */
    xEndPoint.xDHCPData.xDHCPTxTime = pdMS_TO_TICKS( 0 );
    xEndPoint.xDHCPData.xDHCPTxPeriod = pdMS_TO_TICKS( 5000 );
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    /* Because we assume DHCPv6 got advertise, so we should set the server information in DHCP message. */
    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    /* 1st timeout at 5001ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) );
    /* Update tx time to 5001ms. And the tx period is updated to 10000ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) );
    /* 2nd timeout at 5001 + 10001 ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) + pdMS_TO_TICKS( 10001 ) );
    /* Update tx time to 5001ms + 10001 ms. And the tx period is updated to 20000ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) + pdMS_TO_TICKS( 10001 ) );
    /* 3rd timeout at 5001 + 10001 + 20001 ms. */
    xTaskGetTickCount_IgnoreAndReturn( pdMS_TO_TICKS( 5001 ) + pdMS_TO_TICKS( 10001 ) + pdMS_TO_TICKS( 20001 ) );
    /* Timeout triggered. Reset the DHCPv6 to initial state */

    /* 1st timeout makes 1st solicitation message resend. */
    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );
    prvPrepareSolicitation();

    /* 2nd timeout makes 2nd solicitation message resend. */
    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );
    prvPrepareSolicitation();

    /* Final timeout, giving up. */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* 1st process to trigger 1st timeout. */
    vDHCPv6Process( pdFALSE, &xEndPoint );
    /* 2nd process to trigger 2nd timeout. */
    vDHCPv6Process( pdFALSE, &xEndPoint );
    /* 3rd process to trigger final timeout. */
    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process disables the timer when the state is eNotUsingLeasedAddress.
 */
void test_vDHCPv6Process_xDHCPv6ProcessEndPoint_HandleState_NotUsingLeasedAddress()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eNotUsingLeasedAddress;
    xEndPoint.xDHCPData.eExpectedState = eNotUsingLeasedAddress;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;

    /* Because we assume DHCPv6 got advertise, so we should set the server information in DHCP message. */
    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process ignore everything in unknown state.
 */
void test_vDHCPv6Process_xDHCPv6ProcessEndPoint_HandleState_UnknownState()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = 0xFE;
    xEndPoint.xDHCPData.eExpectedState = 0xFE;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;

    /* Because we assume DHCPv6 got advertise, so we should set the server information in DHCP message. */
    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( 0xFE, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Endpoints should close the socket when last endpoint request to close the socket.
 */
void test_vDHCPv6Process_prvCloseDHCPv6Socket_MultipleEndpointsCloseSockets()
{
    NetworkEndPoint_t xEndPoint[ 2 ];
    DHCPMessage_IPv6_t xDHCPMessage[ 2 ];
    struct xSOCKET xLocalDHCPv6Socket[ 2 ];

    /* Initialize first endpoint */
    memset( &xEndPoint[ 0 ], 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPMessage[ 0 ], 0, sizeof( DHCPMessage_IPv6_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    memcpy( xEndPoint[ 0 ].xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint[ 0 ].ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint[ 0 ].ipv6_settings.uxPrefixLength = 64;
    xEndPoint[ 0 ].bits.bIPv6 = pdTRUE;
    xEndPoint[ 0 ].bits.bWantDHCP = pdTRUE;
    xEndPoint[ 0 ].xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint[ 0 ].xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint[ 0 ].xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint[ 0 ].xDHCPData.xDHCPSocket = NULL;
    memcpy( xEndPoint[ 0 ].xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );
    xEndPoint[ 0 ].pxDHCPMessage = &xDHCPMessage[ 0 ];

    pxNetworkEndPoints = &xEndPoint[ 0 ];

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xLocalDHCPv6Socket[ 0 ] );
    xSocketValid_ExpectAndReturn( &xLocalDHCPv6Socket[ 0 ], pdTRUE );
    prvSetCheckerAndReturn_FreeRTOS_setsockopt( &xLocalDHCPv6Socket[ 0 ], sizeof( TickType_t ) );
    FreeRTOS_setsockopt_Stub( xStubFreeRTOS_setsockopt );
    prvSetCheckerAndReturn_vSocketBind( &xLocalDHCPv6Socket[ 0 ] );
    vSocketBind_Stub( xStubvSocketBind );
    vDHCP_RATimerReload_Expect( &xEndPoint[ 0 ], dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdTRUE, &xEndPoint[ 0 ] );
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint[ 0 ].xDHCPData.eDHCPState );

    /* Initialize second endpoint */
    memset( &xEndPoint[ 1 ], 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPMessage[ 1 ], 0, sizeof( DHCPMessage_IPv6_t ) );

    memcpy( xEndPoint[ 1 ].xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint[ 1 ].ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint[ 1 ].ipv6_settings.uxPrefixLength = 64;
    xEndPoint[ 1 ].bits.bIPv6 = pdTRUE;
    xEndPoint[ 1 ].bits.bWantDHCP = pdTRUE;
    xEndPoint[ 1 ].xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint[ 1 ].xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint[ 1 ].xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    memcpy( xEndPoint[ 1 ].xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );
    xEndPoint[ 1 ].pxDHCPMessage = &xDHCPMessage[ 1 ];
    xEndPoint[ 1 ].xDHCPData.xDHCPSocket = NULL;

    pxNetworkEndPoints->pxNext = &xEndPoint[ 1 ];

    vDHCP_RATimerReload_Expect( &xEndPoint[ 1 ], dhcpINITIAL_TIMER_PERIOD );

    vDHCPv6Process( pdTRUE, &xEndPoint[ 1 ] );
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, xEndPoint[ 1 ].xDHCPData.eDHCPState );

    /* Process 1st endpoint again but got failure at DHCP hook callback. */
    xEndPoint[ 0 ].xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    vAddStubsOperation( eTestStubsHookFail );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint[ 0 ], pdFALSE );
    vIPNetworkUpCalls_Expect( &xEndPoint[ 0 ] );
    vDHCPv6Process( pdFALSE, &xEndPoint[ 0 ] );
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xEndPoint[ 0 ].xDHCPData.eDHCPState );

    /* Process 2nd endpoint again but got failure at DHCP hook callback. Trigger socket close flow */
    xEndPoint[ 1 ].xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    vAddStubsOperation( eTestStubsHookFail );
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint[ 1 ], pdFALSE );
    vSocketClose_ExpectAndReturn( &xLocalDHCPv6Socket[ 0 ], NULL );
    vIPNetworkUpCalls_Expect( &xEndPoint[ 1 ] );
    vDHCPv6Process( pdFALSE, &xEndPoint[ 1 ] );
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, xEndPoint[ 1 ].xDHCPData.eDHCPState );
}

/**
 * @brief When endpoint should do nothing when trying to close socket but no one created it.
 */
void test_prvCloseDHCPv6Socket_CloseSocketWithoutCreate()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    /* Initialize first endpoint */
    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;
    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );
    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    xDHCPv6Socket = &xLocalDHCPv6Socket;
    pxNetworkEndPoints = &xEndPoint;

    prvCloseDHCPv6Socket( &xEndPoint );
}

/**
 * @brief Endpoints should trigger assertion when FreeRTOS_socket return invalid socket handler.
 */
void test_vDHCPv6Process_prvCreateDHCPv6Socket_CreateSocketFail()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;
    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = NULL;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );
    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    pxNetworkEndPoints = &xEndPoint;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xLocalDHCPv6Socket );
    xSocketValid_ExpectAndReturn( &xLocalDHCPv6Socket, pdFALSE );

    catch_assert( vDHCPv6Process( pdTRUE, &xEndPoint ) );
}

/**
 * @brief Endpoints should trigger assertion when vSocketBind return fail.
 */
void test_vDHCPv6Process_prvCreateDHCPv6Socket_BindSocketFail()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;
    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = NULL;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );
    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    pxNetworkEndPoints = &xEndPoint;

    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET6, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xLocalDHCPv6Socket );
    xSocketValid_ExpectAndReturn( &xLocalDHCPv6Socket, pdTRUE );
    prvSetCheckerAndReturn_FreeRTOS_setsockopt( &xLocalDHCPv6Socket, sizeof( TickType_t ) );
    FreeRTOS_setsockopt_Stub( xStubFreeRTOS_setsockopt );
    vSocketBind_IgnoreAndReturn( 1 );

    catch_assert( vDHCPv6Process( pdTRUE, &xEndPoint ) );
}

/**
 * @brief NULL endpoint pointer.
 */
void test_prvSendDHCPMessage_NullEndpoint()
{
    catch_assert( prvSendDHCPMessage( NULL ) );
}

/**
 * @brief Check if DHCPv6 skip sending solicitation when it fail to get random number.
 */
void test_vDHCPv6Process_prvSendDHCPMessage_RandomFail()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    xEndPoint.xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    xApplicationGetRandomNumber_IgnoreAndReturn( pdFAIL );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if DHCPv6 skip sending solicitation when its socket is NULL.
 */
void test_vDHCPv6Process_prvSendDHCPMessage_NullSocket()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.xDHCPSocket = NULL;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 1 );
    xTaskGetTickCount_IgnoreAndReturn( 1 );
    xApplicationGetRandomNumber_IgnoreAndReturn( pdPASS );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if DHCPv6 skip sending solicitation when it fail to init bit configuration.
 */
void test_vDHCPv6Process_prvSendDHCPMessage_BitConfigInitFail()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 1 );
    xTaskGetTickCount_IgnoreAndReturn( 1 );
    xApplicationGetRandomNumber_IgnoreAndReturn( pdPASS );
    xBitConfig_init_IgnoreAndReturn( pdFALSE );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if prvSendDHCPMessage stop sending when the state is unexpected.
 */
void test_prvSendDHCPMessage_UnexpectedState()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;

    xEndPoint.xDHCPData.eDHCPState = 0xFF;
    xEndPoint.xDHCPData.eExpectedState = 0xFF;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    xApplicationGetRandomNumber_IgnoreAndReturn( pdPASS );
    xBitConfig_init_IgnoreAndReturn( pdTRUE );
    vBitConfig_release_Ignore();

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    prvSendDHCPMessage( &xEndPoint );
}

/**
 * @brief Check if vDHCPv6Process can drop packet with invalid length IA_NA.
 */
void test_vDHCPv6Process_ReplyInvalidLengthIANA()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 102 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyInvalidIA_NA();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packet with invalid length IA_PD.
 */
void test_vDHCPv6Process_ReplyInvalidLengthIAPD()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 102 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyInvalidIA_PD();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packet when sub-option is invalid in IA_NA.
 */
void test_vDHCPv6Process_ReplyInvalidSubOptionIANA()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 256 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyInvalidIA_NASubOption();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packet when option length of client ID is too small.
 */
void test_vDHCPv6Process_prvDHCPv6_handleOption_ClientLengthTooSmall()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 256 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyClientIDTooSmall();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packet when option length of client ID is too big.
 */
void test_vDHCPv6Process_prvDHCPv6_handleOption_ClientLengthTooBig()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 512 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyClientIDTooBig();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packet when option length of client ID is wrong.
 */
void test_vDHCPv6Process_prvDHCPv6_handleOption_WrongClientID()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 512 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    prvPrepareReplyClientIDLengthWrong();
    vDHCPv6Process( pdFALSE, &xEndPoint );

    FreeRTOS_recvfrom_IgnoreAndReturn( 512 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    prvPrepareReplyClientIDPeekFalse();
    vDHCPv6Process( pdFALSE, &xEndPoint );

    FreeRTOS_recvfrom_IgnoreAndReturn( 512 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );
    prvPrepareReplyClientIDContentWrong();
    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packet when option length of server ID is too small.
 */
void test_vDHCPv6Process_prvDHCPv6_handleOption_ServerLengthTooSmall()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 256 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyServerIDTooSmall();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packet when option length of server ID is too big.
 */
void test_vDHCPv6Process_prvDHCPv6_handleOption_ServerLengthTooBig()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 512 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyServerIDTooBig();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packet when option length of DNS is invalid.
 */
void test_vDHCPv6Process_prvDHCPv6_handleOption_InvalidDNSLength()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 512 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyDNSLengthZero();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    FreeRTOS_recvfrom_IgnoreAndReturn( 512 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyDNSLengthNotAllow();

    vDHCPv6Process( pdFALSE, &xEndPoint );

    TEST_ASSERT_EQUAL( eWaitingAcknowledge, xEndPoint.xDHCPData.eDHCPState );
}

/**
 * @brief Check if vDHCPv6Process can drop packet when option length of DNS is invalid.
 */
void test_vDHCPv6Process_prvDHCPv6_handleOption_DomainSearchList()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.eExpectedState = eWaitingAcknowledge;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 108 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareReplyWithDomainSearchList();

    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpv6DEFAULT_LEASE_TIME );
    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* Check if the IP address provided in reply is set to endpoint properly. */
    TEST_ASSERT_EQUAL_MEMORY( xDefaultIPAddress.ucBytes, xEndPoint.ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
}

/**
 * @brief To cover rare scenario in prvStateName
 */
void test_prvStateName_Coverage()
{
    ( void ) prvStateName( eNotUsingLeasedAddress );
    ( void ) prvStateName( eSendDHCPRequest );
}

/**
 * @brief Check if prvDHCPv6_subOption detects the invalid length.
 */
void test_prvDHCPv6_subOption_UsedLengthLarger()
{
    DHCPOptionSet_t xSet;
    BitConfig_t xMessage;
    uint32_t ulVal;

    memset( &xSet, 0, sizeof( DHCPOptionSet_t ) );
    memset( &xMessage, 0, sizeof( BitConfig_t ) );
    xSet.uxOptionLength = 10U;
    xSet.uxStart = 0U;
    xMessage.uxIndex = 0U;

    prvSetBitOperationStub();
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "Dummy1" );
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "Dummy2" );
    vAddBitOperation( eTestDHCPv6BitOperationRead32, &ulVal, 4, "Dummy3" );
    prvDHCPv6_subOption( DHCPv6_Option_NonTemporaryAddress, &xSet, NULL, &xMessage );
}

/**
 * @brief Check if vDHCPv6Process can ignore the advertise when sub-option status code returns fail.
 */
void test_vDHCPv6Process_AdvertiseStatusFail()
{
    NetworkEndPoint_t xEndPoint;
    DHCPMessage_IPv6_t xDHCPMessage;
    struct xSOCKET xLocalDHCPv6Socket;

    memset( &xEndPoint, 0, sizeof( NetworkEndPoint_t ) );
    memset( &xLocalDHCPv6Socket, 0, sizeof( struct xSOCKET ) );
    memset( &xDHCPMessage, 0, sizeof( DHCPMessage_IPv6_t ) );

    pxNetworkEndPoints = &xEndPoint;

    memcpy( xEndPoint.xMACAddress.ucBytes, ucDefaultMACAddress, sizeof( ucDefaultMACAddress ) );
    memcpy( xEndPoint.ipv6_settings.xPrefix.ucBytes, &xDefaultNetPrefix.ucBytes, sizeof( IPv6_Address_t ) );
    xEndPoint.ipv6_settings.uxPrefixLength = 64;
    xEndPoint.bits.bIPv6 = pdTRUE;
    xEndPoint.bits.bWantDHCP = pdTRUE;

    xEndPoint.xDHCPData.eDHCPState = eWaitingOffer;
    xEndPoint.xDHCPData.eExpectedState = eWaitingOffer;
    xEndPoint.xDHCPData.ulTransactionId = TEST_DHCPV6_TRANSACTION_ID;
    xEndPoint.xDHCPData.xDHCPSocket = &xLocalDHCPv6Socket;
    memcpy( xEndPoint.xDHCPData.ucClientDUID, ucTestDHCPv6OptionClientID, sizeof( ucTestDHCPv6OptionClientID ) );

    xEndPoint.pxDHCPMessage = &xDHCPMessage;

    FreeRTOS_recvfrom_IgnoreAndReturn( 123 );
    FreeRTOS_recvfrom_IgnoreAndReturn( 0 );
    xTaskGetTickCount_IgnoreAndReturn( 0 );

    prvPrepareAdvertiseSubStatusCodeFail();

    xApplicationGetRandomNumber_Stub( xStubxApplicationGetRandomNumber );
    FreeRTOS_inet_pton6_IgnoreAndReturn( pdTRUE );
    FreeRTOS_sendto_IgnoreAndReturn( 0 );

    vDHCPv6Process( pdFALSE, &xEndPoint );

    /* The endpoint receives the DHCPv6 Advertise message from DHCPv6 server.
     * Then change the state to eWaitingAcknowledge. */
    TEST_ASSERT_EQUAL( eWaitingOffer, xEndPoint.xDHCPData.eDHCPState );
}

void test_vDHCPv6Stop( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint_1 = { 0 }, * pxEndPoint_1 = &xEndPoint_1;
    NetworkEndPoint_t xEndPoint_2 = { 0 }, * pxEndPoint_2 = &xEndPoint_2;
    NetworkEndPoint_t xEndPoint_3 = { 0 }, * pxEndPoint_3 = &xEndPoint_3;

    /* Socket is already created. */
    xDHCPv6Socket = &xTestSocket;

    /* 2 end-points opened the socket */
    xDHCPv6SocketUserCount = 2;
    pxEndPoint_1->xDHCPData.xDHCPSocket = FREERTOS_INVALID_SOCKET;
    pxEndPoint_2->xDHCPData.xDHCPSocket = &xTestSocket;
    pxEndPoint_3->xDHCPData.xDHCPSocket = &xTestSocket;

    /* Stop DHCP for end-point 1 */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint_1, pdFALSE );

    vDHCPv6Stop( pxEndPoint_1 );

    TEST_ASSERT_EQUAL( 2, xDHCPv6SocketUserCount );
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv6Socket );
    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, pxEndPoint_1->xDHCPData.xDHCPSocket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint_2->xDHCPData.xDHCPSocket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint_3->xDHCPData.xDHCPSocket );

    /* Stop DHCP for end-point 2 */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint_2, pdFALSE );

    vDHCPv6Stop( pxEndPoint_2 );

    TEST_ASSERT_EQUAL( 1, xDHCPv6SocketUserCount );
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv6Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint_2->xDHCPData.xDHCPSocket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint_3->xDHCPData.xDHCPSocket );

    /* Stop DHCP for end-point 3 */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint_3, pdFALSE );

    /* Expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    vDHCPv6Stop( pxEndPoint_3 );

    TEST_ASSERT_EQUAL( 0, xDHCPv6SocketUserCount );
    TEST_ASSERT_EQUAL( NULL, xDHCPv6Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint_3->xDHCPData.xDHCPSocket );
}
