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
#include <unity.h>

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Routing.h"
#include "FreeRTOS_BitConfig.h"

/* ===========================  EXTERN VARIABLES  =========================== */

#define TEST_DHCPV6_DEBUG                               ( 0 )

/* The maximum size in single read/write operation. */
#define TEST_DHCPv6_BIT_OPERATION_MAX_SIZE              ( 64 )
/* The maximum number of bit operations in a test case. */
#define TEST_DHCPv6_BIT_OPERATION_MAX_NUM               ( 128 )
/* The maximum size of debug message of bit operations. */
#define TEST_DHCPv6_BIT_OPERATION_DEBUG_MSG_MAX_SIZE    ( 64 )

#define TEST_DHCPV6_TRANSACTION_ID                      ( 0x123456 )
#define TEST_DHCPV6_OPTION_CLIENT_ID                    ( 0x00010001C792BC80121122334422 )
#define TEST_DHCPV6_OPTION_SERVER_ID                    ( 0x28BADC54000ACD295EB6 )

typedef enum eTestStubsOperation
{
    eTestStubsOperationNone = 0,
    eTestStubsAllocateFail,
    eTestStubsHookFail,
    eTestStubsHookUseDefault
} eTestStubsOperation_t;

/** @brief A list of all network end-points.  Each element has a next pointer. */
struct xNetworkEndPoint * pxNetworkEndPoints = NULL;

extern Socket_t xDHCPv6Socket;

eTestStubsOperation_t eTestStubsOperation = eTestStubsOperationNone;

static uint8_t ucTestDHCPv6TransactionID[] = { 0x12, 0x34, 0x56 };

static uint8_t ucTestDHCPv6OptionClientID[] = { 0x00, 0x01, 0x00, 0x01, 0xC7, 0x92, 0xBC, 0x80, 0x12, 0x11, 0x22, 0x33, 0x44, 0x22 };

static uint8_t ucTestDHCPv6OptionServerID[] = { 0x28, 0xBA, 0xDC, 0x54, 0x00, 0x0A, 0xCD, 0x29, 0x5E, 0xB6 };

const uint8_t ucDefaultMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0xab, 0xcd, 0xef, 0x11, 0x22, 0x33 };
const IPv6_Address_t xDefaultNetPrefix = { 0x20, 0x01, 0x04, 0x70, 0xEC, 0x54, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };

/* Default IPv6 address is set to 2001:0470:EC54::5 */
const IPv6_Address_t xDefaultIPAddress = { 0x20, 0x01, 0x04, 0x70, 0xEC, 0x54, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05 };
const IPv6_Address_t xDNSAddress[ 3 ] =
{
    /* 2001:0470:EC54::FF */
    { 0x20, 0x01, 0x04, 0x70, 0xEC, 0x54, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF },
    /* 2001:0470:EC54::FE */
    { 0x20, 0x01, 0x04, 0x70, 0xEC, 0x54, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFE },
    /* 2001:0470:EC54::FD */
    { 0x20, 0x01, 0x04, 0x70, 0xEC, 0x54, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFE }
};

typedef enum eTestDHCPv6BitOperationType
{
    eTestDHCPv6BitOperationNone = 0,
    eTestDHCPv6BitOperationWrite8,
    eTestDHCPv6BitOperationWrite16,
    eTestDHCPv6BitOperationWrite32,
    eTestDHCPv6BitOperationWriteCustom,
    eTestDHCPv6BitOperationRead8,
    eTestDHCPv6BitOperationRead16,
    eTestDHCPv6BitOperationRead32,
    eTestDHCPv6BitOperationReadCustom,
    eTestDHCPv6BitOperationReadPeek,
    eTestDHCPv6BitOperationSetError,
    eTestDHCPv6BitOperationReturnFalse
} eTestDHCPv6BitOperationType_t;

typedef struct xTestDHCPv6BitOperation
{
    eTestDHCPv6BitOperationType_t eOperationType;
    uint32_t ulCustomLength;
    union operationValue
    {
        uint8_t ucVal;
        uint16_t usVal;
        uint32_t ulVal;
        uint8_t ucValCustom[ TEST_DHCPv6_BIT_OPERATION_MAX_SIZE ];
    } val;
    uint8_t ucDebugMsg[ TEST_DHCPv6_BIT_OPERATION_DEBUG_MSG_MAX_SIZE ];
} xTestDHCPv6BitOperation_t;

xTestDHCPv6BitOperation_t xTestDHCPv6BitOperation[ TEST_DHCPv6_BIT_OPERATION_MAX_NUM ];
uint32_t ulTestDHCPv6BitOperationWriteIndex;
uint32_t ulTestDHCPv6BitOperationReadIndex;

Socket_t xStubFreeRTOS_setsockopt_xSocket;
size_t xStubFreeRTOS_setsockopt_uxOptionLength;
int32_t xStubFreeRTOS_setsockopt_lOptionName_BitMap;
FreeRTOS_Socket_t * xStubvSocketBind_pxSocket;

/* ======================== Stub Callback Functions ========================= */

void prvSetCheckerAndReturn_FreeRTOS_setsockopt( Socket_t xSocket,
                                                 size_t uxOptionLength )
{
    xStubFreeRTOS_setsockopt_xSocket = xSocket;
    xStubFreeRTOS_setsockopt_uxOptionLength = uxOptionLength;
    xStubFreeRTOS_setsockopt_lOptionName_BitMap = 0;
}

BaseType_t xStubFreeRTOS_setsockopt( Socket_t xSocket,
                                     int32_t lLevel,
                                     int32_t lOptionName,
                                     const void * pvOptionValue,
                                     size_t uxOptionLength,
                                     int NumCalls )
{
    TEST_ASSERT_EQUAL( xStubFreeRTOS_setsockopt_xSocket, xSocket );
    TEST_ASSERT_EQUAL( xStubFreeRTOS_setsockopt_uxOptionLength, uxOptionLength );

    xStubFreeRTOS_setsockopt_lOptionName_BitMap |= ( 1 << lOptionName );

    return pdTRUE;
}

void prvSetCheckerAndReturn_vSocketBind( FreeRTOS_Socket_t * pxSocket )
{
    xStubvSocketBind_pxSocket = pxSocket;
}

BaseType_t xStubvSocketBind( FreeRTOS_Socket_t * pxSocket,
                             struct freertos_sockaddr * pxBindAddress,
                             size_t uxAddressLength,
                             BaseType_t xInternal,
                             int NumCalls )
{
    TEST_ASSERT_EQUAL( xStubvSocketBind_pxSocket, pxSocket );
    TEST_ASSERT_EQUAL( FREERTOS_AF_INET6, pxBindAddress->sin_family );
    TEST_ASSERT_EQUAL( sizeof( struct freertos_sockaddr ), pxBindAddress->sin_len );
    TEST_ASSERT_EQUAL( ipDHCPv6_CLIENT_PORT, FreeRTOS_ntohs( pxBindAddress->sin_port ) );
    TEST_ASSERT_EQUAL( pdFALSE, xInternal );

    return 0;
}

BaseType_t xStubxApplicationGetRandomNumber( uint32_t * pulNumber,
                                             int NumCalls )
{
    if( pulNumber != NULL )
    {
        *pulNumber = 0xFF000000 | TEST_DHCPV6_TRANSACTION_ID;
    }

    return pdPASS;
}

void xStubvBitConfig_write_8( BitConfig_t * pxConfig,
                              uint8_t ucValue,
                              int NumCalls )
{
    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationWrite8, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    TEST_ASSERT_EQUAL( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ucVal, ucValue );
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }
}

void xStubvBitConfig_write_16( BitConfig_t * pxConfig,
                               uint16_t usValue,
                               int NumCalls )
{
    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationWrite16, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    TEST_ASSERT_EQUAL( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.usVal, usValue );
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }
}

void xStubvBitConfig_write_32( BitConfig_t * pxConfig,
                               uint32_t ulValue,
                               int NumCalls )
{
    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationWrite32, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    TEST_ASSERT_EQUAL( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ulVal, ulValue );
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }
}

void xStubvBitConfig_write_uc( BitConfig_t * pxConfig,
                               const uint8_t * pucData,
                               size_t uxSize,
                               int NumCalls )
{
    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationWriteCustom, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    TEST_ASSERT_EQUAL_MEMORY( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ucValCustom, pucData, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ulCustomLength );
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }
}

BaseType_t xStubxBitConfig_init( BitConfig_t * pxConfig,
                                 const uint8_t * pucData,
                                 size_t uxSize,
                                 int NumCalls )
{
    BaseType_t xReturn = pdPASS;

    memset( pxConfig, 0, sizeof( BitConfig_t ) );

    pxConfig->uxSize = uxSize;
    pxConfig->uxIndex = 0;
    pxConfig->xHasError = pdFALSE;

    return xReturn;
}

uint8_t xStubucBitConfig_read_8( BitConfig_t * pxConfig,
                                 int NumCalls )
{
    uint8_t ucReturn = 0;

    pxConfig->uxIndex++;

    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationRead8, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    ucReturn = xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ucVal;
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }

    return ucReturn;
}

BaseType_t xStubxBitConfig_read_uc( BitConfig_t * pxConfig,
                                    uint8_t * pucData,
                                    size_t uxSize,
                                    int NumCalls )
{
    BaseType_t xReturn = pdTRUE;

    pxConfig->uxIndex += uxSize;

    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationReadCustom, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );

    if( pucData != NULL )
    {
        memcpy( pucData, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ucValCustom, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ulCustomLength );
    }

    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }

    return xReturn;
}

uint16_t xStubusBitConfig_read_16( BitConfig_t * pxConfig,
                                   int NumCalls )
{
    uint16_t usReturn = 0;

    pxConfig->uxIndex += 2;

    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationRead16, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    usReturn = xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.usVal;
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }

    return usReturn;
}

uint32_t xStubulBitConfig_read_32( BitConfig_t * pxConfig,
                                   int NumCalls )
{
    uint32_t ulReturn = 0;

    pxConfig->uxIndex += 4;

    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationRead32, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    ulReturn = xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ulVal;
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }

    return ulReturn;
}

BaseType_t xStubpucBitConfig_peek_last_index_uc( BitConfig_t * pxConfig,
                                                 uint8_t * pucData,
                                                 size_t uxSize,
                                                 int NumCalls )
{
    BaseType_t xReturn = pdTRUE;

    #if TEST_DHCPV6_DEBUG
        FreeRTOS_debug_printf( ( "Checking %s\n", xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ucDebugMsg ) );
    #endif

    TEST_ASSERT_EQUAL( eTestDHCPv6BitOperationReadPeek, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType );
    memcpy( pucData, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].val.ucValCustom, xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].ulCustomLength );
    ulTestDHCPv6BitOperationReadIndex++;

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationSetError )
    {
        #if TEST_DHCPV6_DEBUG
            FreeRTOS_debug_printf( ( "Setting Error\n" ) );
        #endif
        pxConfig->xHasError = pdTRUE;
        ulTestDHCPv6BitOperationReadIndex++;
    }

    if( xTestDHCPv6BitOperation[ ulTestDHCPv6BitOperationReadIndex ].eOperationType == eTestDHCPv6BitOperationReturnFalse )
    {
        xReturn = pdFALSE;
        ulTestDHCPv6BitOperationReadIndex++;
    }

    return xReturn;
}

void InitializeUnitTest()
{
    pxNetworkEndPoints = NULL;
    xDHCPv6Socket = NULL;
    eTestStubsOperation = eTestStubsOperationNone;
}

uint32_t ulApplicationTimeHook( void )
{
    /** @brief The function time() counts since 1-1-1970.  The DHCPv6 time-stamp however
     * uses a time stamp that had zero on 1-1-2000. */
    return 946684800U;
}

void vAddStubsOperation( eTestStubsOperation_t eOperation )
{
    eTestStubsOperation = eOperation;
}

eDHCPCallbackAnswer_t xApplicationDHCPHook_Multi( eDHCPCallbackPhase_t eDHCPPhase,
                                                  struct xNetworkEndPoint * pxEndPoint,
                                                  IP_Address_t * pxIPAddress )
{
    eDHCPCallbackAnswer_t eReturn = eDHCPContinue;

    if( eTestStubsOperation == eTestStubsHookFail )
    {
        eReturn = eDHCPStopNoChanges;
    }
    else if( eTestStubsOperation == eTestStubsHookUseDefault )
    {
        eReturn = eDHCPUseDefaults;
    }

    return eReturn;
}

void * pvPortMalloc( size_t xWantedSize )
{
    void * pvReturn = NULL;

    if( eTestStubsOperation != eTestStubsAllocateFail )
    {
        pvReturn = malloc( xWantedSize );
    }

    return pvReturn;
}

void vPortFree( void * pv )
{
    free( pv );
}

void vPortEnterCritical( void )
{
}

void vPortExitCritical( void )
{
}
