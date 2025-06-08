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
#include "mock_task.h"
#include "mock_queue.h"
#include "mock_portable.h"

#include "FreeRTOS_BitConfig.h"

#include "mock_list.h"

#include "FreeRTOSIPConfig.h"

/* ===========================  EXTERN VARIABLES  =========================== */

/* The length of the binary data stream used for validating test cases. */
#define SIZE_OF_BINARY_STREAM    10

/* ==============================  Test Cases  ============================== */

/**
 * @brief This functions verifies failure in initialising
 *        a bit-config struct when Memory Allocation fails.
 */
void test_xBitConfig_init_Fail( void )
{
    BitConfig_t xConfig, * pxConfig = &xConfig;
    uint8_t * pucData = NULL;
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    BaseType_t xResult = pdFALSE;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );

    pvPortMalloc_ExpectAnyArgsAndReturn( NULL );

    xResult = xBitConfig_init( pxConfig, pucData, uxSize );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
    TEST_ASSERT_EQUAL( pdTRUE, pxConfig->xHasError );
}

/**
 * @brief This functions verifies bit-config struct
 *        Memory Allocation when pucData is NULL
 *        which means bit-stream not to be analysed.
 */
void test_xBitConfig_init_pucDataNull( void )
{
    BitConfig_t xConfig, * pxConfig = &xConfig;
    uint8_t * pucData = NULL;
    /* The length of the binary data stream. */
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    uint8_t ucContent[ uxSize ], ucContentReturn[ uxSize ];
    BaseType_t xResult = pdFALSE;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    memset( ucContent, 1, uxSize );
    memset( ucContentReturn, 0, uxSize );
    pxConfig->ucContents = ucContent;

    pvPortMalloc_ExpectAnyArgsAndReturn( ucContent );

    xResult = xBitConfig_init( pxConfig, pucData, uxSize );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    TEST_ASSERT_EQUAL( uxSize, pxConfig->uxSize );
    TEST_ASSERT_EQUAL_MEMORY( pxConfig->ucContents, ucContentReturn, uxSize );
}


/**
 * @brief This functions verifies bit-config struct
 *        Memory Allocation when pucData is Not NULL
 *        which means bit-stream must be analysed.
 */
void test_xBitConfig_init_HappyPath( void )
{
    BitConfig_t xConfig;
    /* The length of the binary data stream. */
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    uint8_t ucContent[ uxSize ];
    uint8_t ucData[ uxSize ];
    BaseType_t xResult = pdFALSE;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    memset( &ucData, 1, uxSize );
    memset( &ucContent, 0, uxSize );
    xConfig.ucContents = ucContent;

    pvPortMalloc_ExpectAnyArgsAndReturn( ucContent );

    xResult = xBitConfig_init( &xConfig, ucData, uxSize );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    TEST_ASSERT_EQUAL( uxSize, xConfig.uxSize );
    TEST_ASSERT_EQUAL_MEMORY( ucContent, ucData, uxSize );
}

/**
 * @brief This functions verifies failure of
 *        reading from a bit-config struct as
 *        xHasError bit is set.
 */
void test_xBitConfig_read_uc_xHasError( void )
{
    BitConfig_t xConfig;
    uint8_t * pucData = NULL;
    BaseType_t xResult = pdFALSE;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    xConfig.xHasError = pdTRUE;

    xResult = xBitConfig_read_uc( &xConfig, pucData, SIZE_OF_BINARY_STREAM );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/**
 * @brief This functions verifies failure of
 *        reading from a bit-config struct as
 *        an out of bound read.
 */

void test_xBitConfig_read_uc_OutOfBoundRead( void )
{
    BitConfig_t xConfig, * pxConfig = &xConfig;
    uint8_t * pucData;
    BaseType_t xResult = pdFALSE;

    memset( pxConfig, 0, sizeof( BitConfig_t ) );
    pxConfig->xHasError = pdFALSE;
    pxConfig->uxIndex = 1;
    pxConfig->uxSize = SIZE_OF_BINARY_STREAM;

    xResult = xBitConfig_read_uc( pxConfig, pucData, SIZE_OF_BINARY_STREAM );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
    TEST_ASSERT_EQUAL( pdTRUE, pxConfig->xHasError );
}

/**
 * @brief This functions verifies failure of
 *        reading from a bit-config struct with
 *        pucData as NULL.
 */

void test_xBitConfig_read_uc_NullData( void )
{
    BitConfig_t xConfig, * pxConfig = &xConfig;
    BaseType_t xResult = pdFALSE;

    memset( pxConfig, 0, sizeof( BitConfig_t ) );
    pxConfig->xHasError = pdFALSE;
    pxConfig->uxIndex = 0;
    pxConfig->uxSize = SIZE_OF_BINARY_STREAM;

    xResult = xBitConfig_read_uc( pxConfig, NULL, SIZE_OF_BINARY_STREAM );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    TEST_ASSERT_EQUAL( SIZE_OF_BINARY_STREAM, pxConfig->uxIndex );
}

/**
 * @brief This functions verifies successful
 *        reading from a bit-config struct.
 */

void test_xBitConfig_read_uc_HappyPath( void )
{
    BitConfig_t xConfig, * pxConfig = &xConfig;
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    uint8_t ucContents[ uxSize ], ucData[ uxSize ];
    BaseType_t xResult = pdFALSE;

    memset( pxConfig, 0, sizeof( BitConfig_t ) );
    memset( ucContents, 1, uxSize );
    memset( ucData, 0, uxSize );
    memset( ucContents, 1, uxSize );
    pxConfig->xHasError = pdFALSE;
    pxConfig->uxIndex = 0;
    pxConfig->uxSize = uxSize;
    pxConfig->ucContents = ucContents;

    xResult = xBitConfig_read_uc( pxConfig, ucData, uxSize );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    TEST_ASSERT_EQUAL( uxSize, pxConfig->uxIndex );
    TEST_ASSERT_EQUAL_MEMORY( pxConfig->ucContents, ucData, uxSize );
}

/**
 * @brief This functions verifies failure to
 *        Peek the last byte from a bit-config
 *        struct as xHasError bit is set.
 */

void test_pucBitConfig_peek_last_index_uc_xHasError( void )
{
    BitConfig_t xConfig;
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    BaseType_t xResult = pdFALSE;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    xConfig.xHasError = pdTRUE;

    xResult = pucBitConfig_peek_last_index_uc( &xConfig, NULL, uxSize );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/**
 * @brief This functions verifies failure to
 *        Peek the last byte from a bit-config
 *        struct as pucData is NULL.
 */

void test_pucBitConfig_peek_last_index_uc_NullpucData( void )
{
    BitConfig_t xConfig;
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    BaseType_t xResult = pdFALSE;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    xConfig.xHasError = pdFALSE;
    xConfig.uxIndex = uxSize;

    xResult = pucBitConfig_peek_last_index_uc( &xConfig, NULL, uxSize );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
    TEST_ASSERT_EQUAL( pdTRUE, xConfig.xHasError );
}


/**
 * @brief This functions verifies failure to
 *        Peek the last byte from a bit-config
 *        struct as an out of bound peak.
 */

void test_pucBitConfig_peek_OutOfBound( void )
{
    BitConfig_t xConfig;
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    uint8_t ucData;
    BaseType_t xResult = pdFALSE;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    xConfig.xHasError = pdFALSE;
    xConfig.uxIndex = 0;

    xResult = pucBitConfig_peek_last_index_uc( &xConfig, &ucData, uxSize );

    TEST_ASSERT_EQUAL( pdFALSE, xResult );
    TEST_ASSERT_EQUAL( pdTRUE, xConfig.xHasError );
}

/**
 * @brief This functions verifies success while
 *        Peeking the last 5 byte from a bit-config
 *        struct.
 */

void test_pucBitConfig_peek_last_index_uc_HappyPath( void )
{
    BitConfig_t xConfig;
    size_t uxSize = 5; /* Read last 5 bytes */
    uint8_t ucData[ uxSize ], ucContents[ SIZE_OF_BINARY_STREAM ];
    BaseType_t xResult = pdFALSE;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    memset( ucData, 0, uxSize );
    memset( ucContents, 1, SIZE_OF_BINARY_STREAM );
    xConfig.xHasError = pdFALSE;
    xConfig.uxIndex = SIZE_OF_BINARY_STREAM;
    xConfig.ucContents = ucContents;

    xResult = pucBitConfig_peek_last_index_uc( &xConfig, ucData, uxSize );

    TEST_ASSERT_EQUAL( pdTRUE, xResult );
    TEST_ASSERT_EQUAL_MEMORY( xConfig.ucContents, ucData, uxSize );
}

/**
 * @brief This functions verifies failure to
 *        returning a byte from the bit stream
 *         as xHasError is set.
 */

void test_ucBitConfig_read_8_fail( void )
{
    BitConfig_t xConfig, * pxConfig = &xConfig;
    uint8_t ucResult;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    pxConfig->xHasError = pdTRUE;

    ucResult = ucBitConfig_read_8( pxConfig );

    TEST_ASSERT_EQUAL( 0xffU, ucResult );
}

/**
 * @brief This functions verifies successfully reading
 *        a byte from the bit stream.
 */

void test_xBitConfig_read_8_HappyPath( void )
{
    BitConfig_t xConfig, * pxConfig = &xConfig;
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    uint8_t ucContents[ uxSize ];
    uint8_t ucResult;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    memset( &ucContents, 0, uxSize );
    memset( ucContents, 1, uxSize );
    pxConfig->xHasError = pdFALSE;
    pxConfig->uxIndex = 0;
    pxConfig->uxSize = uxSize;
    pxConfig->ucContents = ucContents;

    ucResult = ucBitConfig_read_8( pxConfig );

    TEST_ASSERT_EQUAL( ucContents[ 0 ], ucResult );
    TEST_ASSERT_EQUAL( 1, pxConfig->uxIndex );
}

/**
 * @brief This functions verifies failure to
 *        returning 2 byte from the bit stream
 *        as xHasError is set.
 */

void test_usBitConfig_read_16_fail( void )
{
    BitConfig_t xConfig, * pxConfig = &xConfig;
    uint16_t ucResult;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    pxConfig->xHasError = pdTRUE;

    ucResult = usBitConfig_read_16( pxConfig );

    TEST_ASSERT_EQUAL( 0xffffU, ucResult );
    TEST_ASSERT_EQUAL( pdTRUE, xConfig.xHasError );
}

/**
 * @brief This functions verifies reading and
 *        returning 2 byte from the bit stream.
 */

void test_usBitConfig_read_16_HappyPath( void )
{
    BitConfig_t xConfig, * pxConfig = &xConfig;
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    uint8_t ucContents[ uxSize ];
    uint16_t ucResult, ucResultExpected;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    memset( ucContents, 1, uxSize );
    pxConfig->xHasError = pdFALSE;
    pxConfig->uxIndex = 0;
    pxConfig->uxSize = uxSize;
    pxConfig->ucContents = ucContents;

    ucResultExpected = ( ( ( uint16_t ) ucContents[ 0 ] ) << 8 ) |
                       ( ( ( uint16_t ) ucContents[ 1 ] ) );

    ucResult = usBitConfig_read_16( pxConfig );

    TEST_ASSERT_EQUAL( ucResultExpected, ucResult );
}

/**
 * @brief This functions verifies failure to
 *        returning 4 byte from the bit stream
 *        as xHasError is set.
 */

void test_ulBitConfig_read_32_fail( void )
{
    BitConfig_t xConfig, * pxConfig = &xConfig;
    uint32_t ulResult;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    pxConfig->xHasError = pdTRUE;

    ulResult = ulBitConfig_read_32( pxConfig );

    TEST_ASSERT_EQUAL( 0xffffffffU, ulResult );
    TEST_ASSERT_EQUAL( pdTRUE, xConfig.xHasError );
}

/**
 * @brief This functions verifies reading and
 *        returning 4 byte from the bit stream.
 */

void test_ulBitConfig_read_32_HappyPath( void )
{
    BitConfig_t xConfig, * pxConfig = &xConfig;
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    uint8_t ucContents[ uxSize ];
    uint32_t ulResult, ulResultExpected;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    memset( ucContents, 1, uxSize );
    pxConfig->xHasError = pdFALSE;
    pxConfig->uxIndex = 0;
    pxConfig->uxSize = uxSize;
    pxConfig->ucContents = ucContents;

    ulResultExpected = ( ( ( uint32_t ) ucContents[ 0 ] ) << 24 ) |
                       ( ( ( uint32_t ) ucContents[ 1 ] ) << 16 ) |
                       ( ( ( uint32_t ) ucContents[ 2 ] ) << 8 ) |
                       ( ( ( uint32_t ) ucContents[ 3 ] ) );

    ulResult = ulBitConfig_read_32( pxConfig );

    TEST_ASSERT_EQUAL( ulResultExpected, ulResult );
    TEST_ASSERT_EQUAL( sizeof( uint32_t ), pxConfig->uxIndex );
}

/**
 * @brief This functions verifies failure to
 *        writing any number of bytes from the bit stream.
 */

void test_vBitConfig_write_uc_xHasError( void )
{
    BitConfig_t xConfig;
    uint8_t * pucData;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    xConfig.xHasError = pdTRUE;

    vBitConfig_write_uc( &xConfig, pucData, SIZE_OF_BINARY_STREAM );
}

/**
 * @brief This functions verifies failure to
 *        writing bytes to bit stream because
 *        of out of bound write.
 */

void test_vBitConfig_write_uc_OutOfBoundWrite( void )
{
    BitConfig_t xConfig;
    uint8_t * pucData;

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    xConfig.xHasError = pdFALSE;
    xConfig.uxIndex = SIZE_OF_BINARY_STREAM;
    xConfig.uxSize = SIZE_OF_BINARY_STREAM;

    vBitConfig_write_uc( &xConfig, pucData, SIZE_OF_BINARY_STREAM );

    TEST_ASSERT_EQUAL( pdTRUE, xConfig.xHasError );
}

/**
 * @brief This functions verifies writing SIZE_OF_BINARY_STREAM
 *        bytes in the bit stream.
 */

void test_vBitConfig_write_uc_HappyPath( void )
{
    BitConfig_t xConfig;
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    uint8_t ucContents[ uxSize ];
    uint8_t ucData[ uxSize ];

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    memset( ucContents, 0, uxSize );
    memset( ucContents, 1, uxSize );
    xConfig.xHasError = pdFALSE;
    xConfig.uxIndex = 0;
    xConfig.uxSize = uxSize;
    xConfig.ucContents = ucContents;

    vBitConfig_write_uc( &xConfig, ucData, uxSize );

    TEST_ASSERT_EQUAL( SIZE_OF_BINARY_STREAM, xConfig.uxIndex );
    TEST_ASSERT_EQUAL_MEMORY( xConfig.ucContents, ucData, uxSize );
}

/**
 * @brief This functions verifies writing a
 *        byte to the bit stream.
 */
void test_vBitConfig_write_8( void )
{
    BitConfig_t xConfig;
    size_t uxSize = SIZE_OF_BINARY_STREAM, uxIndex = 0;
    uint8_t ucValue = 1;
    uint8_t ucContents[ uxSize ];

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    memset( ucContents, 0, uxSize );
    xConfig.xHasError = pdFALSE;
    xConfig.uxIndex = uxIndex;
    xConfig.uxSize = uxSize;
    xConfig.ucContents = ucContents;

    vBitConfig_write_8( &xConfig, ucValue );

    TEST_ASSERT_EQUAL( sizeof( uint8_t ), xConfig.uxIndex );
    TEST_ASSERT_EQUAL( xConfig.ucContents[ uxIndex ], ucValue );
}

/**
 * @brief This functions verifies writing a
 *        2 byte to the bit stream.
 */
void test_vBitConfig_write_16( void )
{
    BitConfig_t xConfig;
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    uint16_t ucValue = 0;
    uint8_t ucContents[ uxSize ];
    uint8_t pucData[ sizeof ucValue ];

    pucData[ 0 ] = ( uint8_t ) ( ( ucValue >> 8 ) & 0xFFU );
    pucData[ 1 ] = ( uint8_t ) ( ucValue & 0xFFU );

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    memset( ucContents, 0, uxSize );
    xConfig.xHasError = pdFALSE;
    xConfig.uxIndex = 0;
    xConfig.uxSize = uxSize;
    xConfig.ucContents = ucContents;

    vBitConfig_write_16( &xConfig, ucValue );

    TEST_ASSERT_EQUAL( sizeof( uint16_t ), xConfig.uxIndex );
    TEST_ASSERT_EQUAL_MEMORY( xConfig.ucContents, pucData, sizeof( ucValue ) );
}

/**
 * @brief This functions verifies writing a
 *        4 byte to the bit stream.
 */
void test_vBitConfig_write_32( void )
{
    BitConfig_t xConfig;
    size_t uxSize = SIZE_OF_BINARY_STREAM;
    uint32_t ucValue = 0;
    uint8_t ucContents[ uxSize ];
    uint8_t pucData[ sizeof( ucValue ) ];

    memset( &xConfig, 0, sizeof( BitConfig_t ) );
    xConfig.xHasError = pdFALSE;
    xConfig.uxIndex = 0;
    xConfig.uxSize = uxSize;
    xConfig.ucContents = ucContents;

    pucData[ 0 ] = ( uint8_t ) ( ( ucValue >> 24 ) & 0xFFU );
    pucData[ 1 ] = ( uint8_t ) ( ( ucValue >> 16 ) & 0xFFU );
    pucData[ 2 ] = ( uint8_t ) ( ( ucValue >> 8 ) & 0xFFU );
    pucData[ 3 ] = ( uint8_t ) ( ucValue & 0xFFU );

    vBitConfig_write_32( &xConfig, ucValue );

    TEST_ASSERT_EQUAL( sizeof( uint32_t ), xConfig.uxIndex );
    TEST_ASSERT_EQUAL_MEMORY( xConfig.ucContents, pucData, sizeof( ucValue ) );
}

/**
 * @brief This functions verifies failure in
 *        releasing the buffer as it is NULL.
 */
void test_vBitConfig_NoReleaseNULL( void )
{
    BitConfig_t * pxConfig = NULL;

    vBitConfig_release( pxConfig );
}

/**
 * @brief This functions verifies failure in
 *        release the buffer as it is NULL.
 */
void test_vBitConfig_ReleaseNULL( void )
{
    BitConfig_t xConfig, xConfigExpected;

    memset( &xConfig, 1, sizeof( BitConfig_t ) );
    memset( &xConfigExpected, 0, sizeof( BitConfig_t ) );
    xConfig.ucContents = NULL;

    vBitConfig_release( &xConfig );

    TEST_ASSERT_EQUAL_MEMORY( &xConfigExpected, &xConfig, sizeof( BitConfig_t ) );
}

/**
 * @brief This functions verifies releasing
 *        the buffer and clear the bit stream structure.
 */
void test_vBitConfig_Release( void )
{
    BitConfig_t xConfig, xConfigExpected;
    uint8_t ucContent[ SIZE_OF_BINARY_STREAM ];

    memset( &xConfig, 1, sizeof( BitConfig_t ) );
    memset( ucContent, 1, SIZE_OF_BINARY_STREAM );
    memset( &xConfigExpected, 0, sizeof( BitConfig_t ) );
    xConfig.ucContents = ucContent;

    vPortFree_ExpectAnyArgs();

    vBitConfig_release( &xConfig );

    TEST_ASSERT_EQUAL_MEMORY( &xConfigExpected, &xConfig, sizeof( BitConfig_t ) );
}
