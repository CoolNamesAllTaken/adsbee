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

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_UDP_IP.h"

#include "FreeRTOS_Stream_Buffer.h"

#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"


/*
 * @brief Function to calculate smaller of the two numbers given.
 */
static size_t FreeRTOS_min_stub( size_t a,
                                 size_t b,
                                 int callback_count )
{
    /* Avoid compiler warnings about unused variable. */
    ( void ) callback_count;

    if( a < b )
    {
        return a;
    }
    else
    {
        return b;
    }
}

/*
 * @brief Test when upper and lower values are same.
 */
void test_uxStreamBufferSpace_SameLocation( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    size_t xReturn;
    size_t uxUpper = 0;
    size_t uxLower = 0;

    xReturn = uxStreamBufferSpace( &xLocalBuffer, uxUpper, uxLower );
    TEST_ASSERT_EQUAL( xLocalBuffer.LENGTH + uxUpper - uxLower - 1, xReturn );
}

/*
 * @brief Test when upper is greater than lower value.
 */
void test_uxStreamBufferSpace_UpperGTLower( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    size_t xReturn;
    size_t uxUpper = 5;
    size_t uxLower = 0;

    xReturn = uxStreamBufferSpace( &xLocalBuffer, uxUpper, uxLower );
    TEST_ASSERT_EQUAL( uxUpper - uxLower - 1, xReturn );
}

/*
 * @brief Test when upper is smaller than lower value.
 */
void test_uxStreamBufferSpace_UpperLTLower( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    size_t xReturn;
    size_t uxUpper = 0;
    size_t uxLower = 5;

    xReturn = uxStreamBufferSpace( &xLocalBuffer, uxUpper, uxLower );
    TEST_ASSERT_EQUAL( xLocalBuffer.LENGTH + uxUpper - uxLower - 1, xReturn );
}

/*
 * @brief Test when upper and lower are same value.
 */
void test_uxStreamBufferDistance_SameLocation( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    size_t xReturn;
    size_t uxUpper = 0;
    size_t uxLower = 0;

    xReturn = uxStreamBufferDistance( &xLocalBuffer, uxUpper, uxLower );
    TEST_ASSERT_EQUAL( uxUpper - uxLower, xReturn );
}

/*
 * @brief Test when upper is greater than lower value.
 */
void test_uxStreamBufferDistance_UpperGTLower( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    size_t xReturn;
    size_t uxUpper = 5;
    size_t uxLower = 0;

    xReturn = uxStreamBufferDistance( &xLocalBuffer, uxUpper, uxLower );
    TEST_ASSERT_EQUAL( uxUpper - uxLower, xReturn );
}

/*
 * @brief Test when upper is smaller than lower value.
 */
void test_uxStreamBufferDistance_UpperLTLower( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    size_t xReturn;
    size_t uxUpper = 0;
    size_t uxLower = 5;

    xReturn = uxStreamBufferDistance( &xLocalBuffer, uxUpper, uxLower );
    TEST_ASSERT_EQUAL( xLocalBuffer.LENGTH + uxUpper - uxLower, xReturn );
}

/*
 * @brief Test the wrapper and assert on the output.
 */
void test_uxStreamBufferGetSpace( void )
{
    size_t uxHead = 10;
    size_t uxTail = 5;
    size_t uxReturn;

    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxHead = uxHead;
    xLocalBuffer.uxTail = uxTail;

    uxReturn = uxStreamBufferGetSpace( &xLocalBuffer );

    TEST_ASSERT_EQUAL( uxHead - uxTail - 1, uxReturn );
}

/*
 * @brief Test the wrapper and assert on the output.
 */
void test_uxStreamBufferFrontSpace( void )
{
    size_t uxFront = 10;
    size_t uxTail = 5;
    size_t uxReturn;

    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxFront = uxFront;
    xLocalBuffer.uxTail = uxTail;

    uxReturn = uxStreamBufferFrontSpace( &xLocalBuffer );

    TEST_ASSERT_EQUAL( uxFront - uxTail - 1, uxReturn );
}

/*
 * @brief Test the wrapper and assert on the output.
 */
void test_uxStreamBufferGetSize( void )
{
    size_t uxHead = 10;
    size_t uxTail = 5;
    size_t uxReturn;

    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxHead = uxHead;
    xLocalBuffer.uxTail = uxTail;

    uxReturn = uxStreamBufferGetSize( &xLocalBuffer );

    TEST_ASSERT_EQUAL( uxHead - uxTail, uxReturn );
}

/*
 * @brief Test the wrapper and assert on the output.
 */
void test_uxStreamBufferMidSpace( void )
{
    size_t uxHead = 10;
    size_t uxMid = 5;
    size_t uxReturn;

    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxHead = uxHead;
    xLocalBuffer.uxMid = uxMid;

    uxReturn = uxStreamBufferMidSpace( &xLocalBuffer );

    TEST_ASSERT_EQUAL( uxHead - uxMid, uxReturn );
}

/*
 * @brief Clear the stream buffer and test the values.
 */
void test_vStreamBufferClear( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxHead = 10;
    xLocalBuffer.uxTail = 10;
    xLocalBuffer.uxFront = 10;
    xLocalBuffer.uxMid = 10;

    vStreamBufferClear( &xLocalBuffer );

    /* Make sure that all values except the length are reset to 0. */
    TEST_ASSERT_EQUAL( 10, xLocalBuffer.LENGTH );
    TEST_ASSERT_EQUAL( 0, xLocalBuffer.uxHead );
    TEST_ASSERT_EQUAL( 0, xLocalBuffer.uxTail );
    TEST_ASSERT_EQUAL( 0, xLocalBuffer.uxFront );
    TEST_ASSERT_EQUAL( 0, xLocalBuffer.uxMid );
}

/*
 * @brief Test moving the mid of the stream buffer when the
 *        count is less than the distance.
 */
void test_vStreamBufferMoveMid_CountLTDistance( void )
{
    size_t Mid = 5;
    size_t uxCount = 2;

    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxHead = 9;
    xLocalBuffer.uxMid = Mid;

    vStreamBufferMoveMid( &xLocalBuffer, uxCount );

    TEST_ASSERT_EQUAL( Mid + uxCount, xLocalBuffer.uxMid );
}

/*
 * @brief Test moving the mid of the stream buffer when the
 *        count is greater than the distance.
 */
void test_vStreamBufferMoveMid_CountGTDistance( void )
{
    size_t Mid = 5;
    size_t uxCount = 5;

    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxHead = 9;
    xLocalBuffer.uxMid = Mid;

    vStreamBufferMoveMid( &xLocalBuffer, uxCount );

    /* Since we wanted to move mid further than the head, now mid will
     * point to head as well. */
    TEST_ASSERT_EQUAL( xLocalBuffer.uxHead, xLocalBuffer.uxMid );
}

/*
 * @brief Test moving the mid of the stream buffer when the
 *        count is equal to the distance and there is a rollover.
 */
void test_vStreamBufferMoveMid_CountEQDistance_RollOver( void )
{
    size_t Mid = 5;
    size_t uxCount = 8;

    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxHead = 3;
    xLocalBuffer.uxMid = Mid;

    vStreamBufferMoveMid( &xLocalBuffer, uxCount );

    /* Since we wanted to move mid equal to the distance, and the head has rolled over,
     * mid will also roll over. */
    TEST_ASSERT_EQUAL( xLocalBuffer.uxHead, xLocalBuffer.uxMid );
}

/*
 * @brief Test when left and right are zero.
 */
void test_xStreamBufferLessThenEqual_LeftRightZero( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxTail = 10;
    BaseType_t xResult;

    xResult = xStreamBufferLessThenEqual( &xLocalBuffer, 0, 0 );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

/*
 * @brief Test when left and right are non zero but equal and are less
 *        than tail pointer.
 */
void test_xStreamBufferLessThenEqual_LeftRightNonZeroButEqual( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxTail = 10;
    BaseType_t xResult;
    size_t uxValue = 2;

    xResult = xStreamBufferLessThenEqual( &xLocalBuffer, uxValue, uxValue );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

/*
 * @brief Test when left and right are equal but are greater than tail.
 */
void test_xStreamBufferLessThenEqual_LeftRightEqualButGreaterThanTail( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxTail = 5;
    BaseType_t xResult;
    size_t uxValue = 6;

    xResult = xStreamBufferLessThenEqual( &xLocalBuffer, uxValue, uxValue );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

/*
 * @brief Test when Left is greater than right and both are greater than tail.
 */
void test_xStreamBufferLessThenEqual_LeftGTRightBothGreaterThanTail( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxTail = 5;
    BaseType_t xResult;
    size_t uxLeft = 7;
    size_t uxRight = 6;

    xResult = xStreamBufferLessThenEqual( &xLocalBuffer, uxLeft, uxRight );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/*
 * @brief Test when left is greater than right and tail. Right is smaller
 *        than the tail.
 */
void test_xStreamBufferLessThenEqual_LeftGTRightAndTail( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxTail = 5;
    BaseType_t xResult;
    size_t uxLeft = 7;
    size_t uxRight = 4;

    xResult = xStreamBufferLessThenEqual( &xLocalBuffer, uxLeft, uxRight );
    TEST_ASSERT_EQUAL( pdTRUE, xResult );
}

/*
 * @brief Test when left is less than both right and tail. Right is greater
 *        than the tail.
 */
void test_xStreamBufferLessThenEqual_LeftLTRightAndTail( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxTail = 5;
    BaseType_t xResult;
    size_t uxLeft = 4;
    size_t uxRight = 7;

    xResult = xStreamBufferLessThenEqual( &xLocalBuffer, uxLeft, uxRight );
    TEST_ASSERT_EQUAL( pdFALSE, xResult );
}

/*
 * @brief Test getting a pointer to the data.
 */
void test_uxStreamBufferGetPtr( void )
{
    StreamBuffer_t xLocalBuffer;

    xLocalBuffer.LENGTH = 10;
    xLocalBuffer.uxTail = 5;
    size_t uxResult;
    size_t uxLeft = 4;
    size_t uxRight = 7;
    uint8_t * pucData;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );
    uxResult = uxStreamBufferGetPtr( &xLocalBuffer, &pucData );
    TEST_ASSERT_EQUAL( 5, uxResult );
    TEST_ASSERT_EQUAL_PTR( xLocalBuffer.ucArray + xLocalBuffer.uxTail, pucData );
}

/*
 * @brief Test adding to the stream buffer when everything is zeroed out.
 */
void test_uxStreamBufferAdd_EverythingResetToZero( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxByteCount = 0;
    size_t uxReturn;

    /* Add in a known pattern. */
    memset( pucData, 0xAA, 512 );

    /* Clear the Buffer. */
    memset( pxLocalBuffer, 0, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    pxLocalBuffer->LENGTH = usBufferSize;
    pxLocalBuffer->uxHead = 0;
    pxLocalBuffer->uxTail = 0;
    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    uxReturn = uxStreamBufferAdd( pxLocalBuffer, uxOffset, pucData, uxByteCount );

    TEST_ASSERT_EQUAL( 0, uxReturn );
    /* Check that the data is still untouched i.e. 0. */
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, pxLocalBuffer->ucArray, usBufferSize );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test adding to the buffer when it is already full with
 *        zero offset.
 */
void test_uxStreamBufferAdd_BufferFullZeroOffset( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxByteCount = 0;
    size_t uxReturn;

    /* Add in a known pattern. */
    memset( pucData, 0xAA, 512 );

    /* Clear the Buffer. */
    memset( pxLocalBuffer, 0, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    pxLocalBuffer->LENGTH = usBufferSize;
    pxLocalBuffer->uxHead = 100;
    pxLocalBuffer->uxTail = pxLocalBuffer->uxHead + 1;
    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    uxReturn = uxStreamBufferAdd( pxLocalBuffer, uxOffset, pucData, uxByteCount );

    TEST_ASSERT_EQUAL( 0, uxReturn );
    /* Check that the data is still untouched i.e. 0. */
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, pxLocalBuffer->ucArray, usBufferSize );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test adding to the buffer when it is already full with
 *        positive offset.
 */
void test_uxStreamBufferAdd_BufferFullPositiveOffset( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 10;
    uint8_t pucData[ 512 ];
    size_t uxByteCount = 0;
    size_t uxReturn;

    /* Add in a known pattern. */
    memset( pucData, 0xAA, 512 );

    /* Clear the Buffer. */
    memset( pxLocalBuffer, 0, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    pxLocalBuffer->LENGTH = usBufferSize;
    pxLocalBuffer->uxHead = 100;
    pxLocalBuffer->uxTail = pxLocalBuffer->uxHead + 1;
    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    uxReturn = uxStreamBufferAdd( pxLocalBuffer, uxOffset, pucData, uxByteCount );

    TEST_ASSERT_EQUAL( 0, uxReturn );
    /* Check that the data is still untouched i.e. 0. */
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, pxLocalBuffer->ucArray, usBufferSize );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test adding to the buffer when it has more space than the data.
 *        And it has zero offset where data write causes head to rollover.
 */
void test_uxStreamBufferAdd_BufferHasMoreSpaceThanData_ZeroOffset_DataWriteCausesRollover_FrontAheadOfHead( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxByteCount = sizeof( pucData );
    size_t uxReturn;
    size_t uxBytesToBeWritten = 512;
    const size_t uxBytesWrittenInFirstGo = 24;

    /* Clear everything. */
    memset( pxLocalBuffer, 0, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Head at almost the end for rollover to happen. */
    pxLocalBuffer->uxHead = 1000;
    /* Only 600 bytes available. */
    pxLocalBuffer->uxTail = pxLocalBuffer->uxHead + 600 + 1;
    /* Rollover adjustment. */
    pxLocalBuffer->uxTail -= pxLocalBuffer->LENGTH;

    pxLocalBuffer->uxMid = 0;
    /* Front is already ahead of the Head. */
    pxLocalBuffer->uxFront = 500;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    uxReturn = uxStreamBufferAdd( pxLocalBuffer, uxOffset, pucData, uxByteCount );

    /* Only these many bytes should be written. */
    TEST_ASSERT_EQUAL( uxBytesToBeWritten, uxReturn );

    /* Assert that data was indeed written. Here in 2 steps. */
    TEST_ASSERT_EQUAL_MEMORY( pucData, pxLocalBuffer->ucArray + 1000, uxBytesWrittenInFirstGo );
    /* Rollover! */
    TEST_ASSERT_EQUAL_MEMORY( pucData, pxLocalBuffer->ucArray + 0, uxBytesToBeWritten - uxBytesWrittenInFirstGo );

    /* Make sure that the rest of buffer is untouched. i.e. zero.*/
    TEST_ASSERT_EACH_EQUAL_UINT8( 0,
                                  pxLocalBuffer->ucArray + uxBytesToBeWritten - uxBytesWrittenInFirstGo,
                                  usBufferSize - uxBytesToBeWritten );

    /* Make sure that the head is moved since data was written. */
    TEST_ASSERT_EQUAL( 488, pxLocalBuffer->uxHead );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test adding to the buffer when it has less space than data with
 *        zero offset.
 */
void test_uxStreamBufferAdd_BufferHasLessSpaceThanData_ZeroOffset( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxByteCount = sizeof( pucData );
    size_t uxReturn;

    /* Clear everything. */
    memset( pxLocalBuffer, 0, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Head at 0 for simplicity. */
    pxLocalBuffer->uxHead = 0;
    /* Only 500 bytes available. */
    pxLocalBuffer->uxTail = pxLocalBuffer->uxHead + 500 + 1;
    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    uxReturn = uxStreamBufferAdd( pxLocalBuffer, uxOffset, pucData, uxByteCount );

    /* Only 500 bytes should be written. */
    TEST_ASSERT_EQUAL( 500, uxReturn );

    /* Assert that data was indeed written. */
    TEST_ASSERT_EQUAL_MEMORY( pxLocalBuffer->ucArray + uxOffset, pucData, 500 - uxOffset );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test adding to the buffer when it has less space than the data.
 *        And it has non-zero offset.
 */
void test_uxStreamBufferAdd_BufferHasLessSpaceThanData_NonZeroOffset( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 10;
    uint8_t pucData[ 512 ];
    size_t uxByteCount = sizeof( pucData );
    size_t uxReturn;
    size_t uxBytesToBeWritten = 500;

    /* Clear everything. */
    memset( pxLocalBuffer, 0, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Head at 0 for simplicity. */
    pxLocalBuffer->uxHead = 0;
    /* Only 500 bytes available. */
    pxLocalBuffer->uxTail = pxLocalBuffer->uxHead + uxBytesToBeWritten + 1;
    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    uxReturn = uxStreamBufferAdd( pxLocalBuffer, uxOffset, pucData, uxByteCount );

    /* Only these many bytes should be written. */
    TEST_ASSERT_EQUAL( uxBytesToBeWritten - uxOffset, uxReturn );

    /* Assert that data was indeed written. */
    TEST_ASSERT_EQUAL_MEMORY( pucData, pxLocalBuffer->ucArray + uxOffset, uxBytesToBeWritten - uxOffset );

    /* Make sure that rest of the buffer is untouched. i.e. zero.*/
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, pxLocalBuffer->ucArray + uxBytesToBeWritten, usBufferSize - uxBytesToBeWritten );

    /* Make sure that the head is not moved since data was written at an offset. */
    TEST_ASSERT_EQUAL( 0, pxLocalBuffer->uxHead );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test adding to the buffer when it has less space than the data.
 *        And it has non-zero offset which causes rollover.
 */
void test_uxStreamBufferAdd_BufferHasLessSpaceThanData_NonZeroOffsetCausesRollover( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 100;
    uint8_t pucData[ 512 ];
    size_t uxByteCount = sizeof( pucData );
    size_t uxReturn;
    size_t uxBytesToBeWritten = 500;

    /* Clear everything. */
    memset( pxLocalBuffer, 0, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Head at almost the end for rollover to happen. */
    pxLocalBuffer->uxHead = 1000;
    /* Only 500 bytes available. */
    pxLocalBuffer->uxTail = pxLocalBuffer->uxHead + uxBytesToBeWritten + 1;
    /* Rollover adjustment. */
    pxLocalBuffer->uxTail -= pxLocalBuffer->LENGTH;

    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    uxReturn = uxStreamBufferAdd( pxLocalBuffer, uxOffset, pucData, uxByteCount );

    /* Only these many bytes should be written. */
    TEST_ASSERT_EQUAL( uxBytesToBeWritten - uxOffset, uxReturn );

    /* Assert that data was indeed written. */
    TEST_ASSERT_EQUAL_MEMORY( pucData, pxLocalBuffer->ucArray + 76, uxBytesToBeWritten - uxOffset );

    /* Make sure that the rest of buffer is untouched. i.e. zero.*/
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, pxLocalBuffer->ucArray + uxBytesToBeWritten, usBufferSize - uxBytesToBeWritten );

    /* Make sure that the head is not moved since data was written at an offset. */
    TEST_ASSERT_EQUAL( 1000, pxLocalBuffer->uxHead );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test adding to the buffer when it has less space than the data.
 *        And it has zero offset where data write causes head to rollover.
 */
void test_uxStreamBufferAdd_BufferHasLessSpaceThanData_ZeroOffset_DataWriteCausesRollover( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxByteCount = sizeof( pucData );
    size_t uxReturn;
    size_t uxBytesToBeWritten = 500;
    const size_t uxBytesWrittenInFirstGo = 24;

    /* Clear everything. */
    memset( pxLocalBuffer, 0, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Head at almost the end for rollover to happen. */
    pxLocalBuffer->uxHead = 1000;
    /* Only 500 bytes available. */
    pxLocalBuffer->uxTail = pxLocalBuffer->uxHead + uxBytesToBeWritten + 1;
    /* Rollover adjustment. */
    pxLocalBuffer->uxTail -= pxLocalBuffer->LENGTH;

    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    uxReturn = uxStreamBufferAdd( pxLocalBuffer, uxOffset, pucData, uxByteCount );

    /* Only these many bytes should be written. */
    TEST_ASSERT_EQUAL( uxBytesToBeWritten - uxOffset, uxReturn );

    /* Assert that data was indeed written. Here in 2 steps. */
    TEST_ASSERT_EQUAL_MEMORY( pucData, pxLocalBuffer->ucArray + 1000, uxBytesWrittenInFirstGo );
    /* Rollover! */
    TEST_ASSERT_EQUAL_MEMORY( pucData, pxLocalBuffer->ucArray + 0, uxBytesToBeWritten - uxBytesWrittenInFirstGo );

    /* Make sure that the rest of buffer is untouched. i.e. zero.*/
    TEST_ASSERT_EACH_EQUAL_UINT8( 0,
                                  pxLocalBuffer->ucArray + uxBytesToBeWritten - uxBytesWrittenInFirstGo,
                                  usBufferSize - uxBytesToBeWritten );

    /* Make sure that the head is moved since data was written. */
    TEST_ASSERT_EQUAL( pxLocalBuffer->uxTail - 1, pxLocalBuffer->uxHead );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test adding to the buffer when NULL pointer is passed with
 *        zero offset and data write causes a head pointer roll over.
 */
void test_uxStreamBufferAdd_NULLData_BufferHasLessSpaceThanData_ZeroOffset_DataWriteCausesRollover( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxByteCount = sizeof( pucData );
    size_t uxReturn;
    size_t uxBytesToBeWritten = 500;
    size_t uxNewHeadLocationAfterRollover = uxBytesToBeWritten - 24;

    /* Clear everything. */
    memset( pxLocalBuffer, 0, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Head at almost the end for rollover to happen. */
    pxLocalBuffer->uxHead = 1000;
    /* Only 500 bytes available. */
    pxLocalBuffer->uxTail = pxLocalBuffer->uxHead + uxBytesToBeWritten + 1;
    /* Rollover adjustment. */
    pxLocalBuffer->uxTail -= pxLocalBuffer->LENGTH;

    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    uxReturn = uxStreamBufferAdd( pxLocalBuffer, uxOffset, NULL, uxByteCount );

    /* Nothing should be written but tail will be updated. */
    TEST_ASSERT_EQUAL( uxBytesToBeWritten, uxReturn );

    /* Make sure that the rest of buffer is untouched. i.e. zero.*/
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, pxLocalBuffer->ucArray, usBufferSize );

    /* Make sure that the head is moved as well. */
    TEST_ASSERT_EQUAL( uxNewHeadLocationAfterRollover, pxLocalBuffer->uxHead );
    /* Make sure that the front pointer is moved as well. */
    TEST_ASSERT_EQUAL( uxNewHeadLocationAfterRollover, pxLocalBuffer->uxFront );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test adding to the buffer when NULL pointer is passed with
 *        zero offset and when the data write causes head roll over
 *        with front pointer greater than the head pointer.
 */
void test_uxStreamBufferAdd_NULLData_BufferHasLessSpaceThanData_ZeroOffset_DataWriteCausesRollover_Front( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxByteCount = sizeof( pucData );
    size_t uxReturn;
    size_t uxBytesToBeWritten = 500;
    size_t uxNewHeadLocationAfterRollover = uxBytesToBeWritten - 24;

    /* Clear everything. */
    memset( pxLocalBuffer, 0, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Head at almost the end for rollover to happen. */
    pxLocalBuffer->uxHead = 1000;
    /* Only 500 bytes available. */
    pxLocalBuffer->uxTail = pxLocalBuffer->uxHead + uxBytesToBeWritten + 1;
    /* Rollover adjustment. */
    pxLocalBuffer->uxTail -= pxLocalBuffer->LENGTH;

    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = pxLocalBuffer->uxHead - 2;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    vTaskSuspendAll_Expect();
    xTaskResumeAll_ExpectAndReturn( pdTRUE );

    uxReturn = uxStreamBufferAdd( pxLocalBuffer, uxOffset, NULL, uxByteCount );

    /* Nothing should be written but tail should be updated. */
    TEST_ASSERT_EQUAL( uxBytesToBeWritten, uxReturn );

    /* Make sure that the rest of buffer is untouched. i.e. zero.*/
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, pxLocalBuffer->ucArray, usBufferSize );

    /* Make sure that the head is moved as well. */
    TEST_ASSERT_EQUAL( uxNewHeadLocationAfterRollover, pxLocalBuffer->uxHead );

    TEST_ASSERT_EQUAL( pxLocalBuffer->uxHead, pxLocalBuffer->uxFront );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test reading from the stream buffer when all values are reset
 *        to 0.
 */
void test_uxStreamBufferGet_ResetEverything( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxMaxCount = 0;
    size_t uxReturn;
    BaseType_t xPeek = 0;

    /* Clear everything. */
    memset( pxLocalBuffer, 0, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    uxReturn = uxStreamBufferGet( pxLocalBuffer, uxOffset, pucData, uxMaxCount, xPeek );

    /* Nothing should be written. */
    TEST_ASSERT_EQUAL( 0, uxReturn );

    /* Make sure that the rest of buffer is untouched. i.e. zero.*/
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, pxLocalBuffer->ucArray, usBufferSize );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test reading from the stream buffer when there are just enough
 *        bytes and we are reading without offset.
 */
void test_uxStreamBufferGet_BytesRequiredEQBytesPresent_NoOffset( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxMaxCount = 500;
    size_t uxBufferSpace = 500;
    size_t uxReturn;
    BaseType_t xPeek = 0;

    /* Clear everything and fill it with 0x11. */
    memset( pxLocalBuffer, 0x11, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Tail to 0 for simplicity. */
    pxLocalBuffer->uxTail = 0;
    /* Only these many bytes available. */
    pxLocalBuffer->uxHead = pxLocalBuffer->uxTail + uxBufferSpace;

    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    uxReturn = uxStreamBufferGet( pxLocalBuffer, uxOffset, pucData, uxMaxCount, xPeek );

    /* 500 bytes should be written. */
    TEST_ASSERT_EQUAL( uxBufferSpace, uxReturn );
    TEST_ASSERT_EQUAL( uxBufferSpace, pxLocalBuffer->uxTail );
    TEST_ASSERT_EQUAL_MEMORY( pxLocalBuffer->ucArray, pucData, uxMaxCount );

    /* Make sure that the rest of buffer is untouched. i.e. zero.*/
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, pucData + uxMaxCount, sizeof( pucData ) - uxMaxCount );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test reading from the stream buffer when there are just enough
 *        bytes and we are reading with a positive offset.
 */
void test_uxStreamBufferGet_BytesRequiredEQBytesPresent_PositiveOffset( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 50;
    uint8_t pucData[ 512 ];
    size_t uxMaxCount = 500;
    size_t uxBufferSpace = 500;
    size_t uxReturn;
    BaseType_t xPeek = 0;

    /* Clear everything and fill it with 0x11. */
    memset( pxLocalBuffer, 0x11, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Tail to 0 for simplicity. */
    pxLocalBuffer->uxTail = 0;
    /* Only these many bytes available. */
    pxLocalBuffer->uxHead = pxLocalBuffer->uxTail + uxBufferSpace;

    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    uxReturn = uxStreamBufferGet( pxLocalBuffer, uxOffset, pucData, uxMaxCount, xPeek );

    /* 500 bytes should be written. */
    TEST_ASSERT_EQUAL( uxBufferSpace - uxOffset, uxReturn );
    /* Since we are reading at an offset, the tail should not be moved. */
    TEST_ASSERT_EQUAL( 0, pxLocalBuffer->uxTail );
    /* See if the data is copied. */
    TEST_ASSERT_EQUAL_MEMORY( pxLocalBuffer->ucArray, pucData, uxBufferSpace - uxOffset );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test reading from the stream buffer when there are just enough
 *        bytes and we are reading with positive offset and the tail is
 *        about to rollover the stream buffer.
 */
void test_uxStreamBufferGet_BytesRequiredEQBytesPresent_PositiveOffset_TailAboutToRollOver( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 50;
    uint8_t pucData[ 512 ];
    size_t uxMaxCount = 500;
    size_t uxBufferSpace = 500;
    size_t uxReturn;
    BaseType_t xPeek = 0;

    /* Clear everything and fill it with 0x11. */
    memset( pxLocalBuffer, 0x11, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Tail to 0 for simplicity. */
    pxLocalBuffer->uxTail = 1000;
    /* Only these many bytes available. */
    pxLocalBuffer->uxHead = pxLocalBuffer->uxTail + uxBufferSpace;
    /* Rollover adjustment. */
    pxLocalBuffer->uxHead -= pxLocalBuffer->LENGTH;

    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    uxReturn = uxStreamBufferGet( pxLocalBuffer, uxOffset, pucData, uxMaxCount, xPeek );

    /* 500 bytes should be written. */
    TEST_ASSERT_EQUAL( uxBufferSpace - uxOffset, uxReturn );
    /* Since we are reading at an offset, the tail should not be moved. */
    TEST_ASSERT_EQUAL( 1000, pxLocalBuffer->uxTail );
    /* See if the data is copied. */
    TEST_ASSERT_EQUAL_MEMORY( pxLocalBuffer->ucArray, pucData, uxBufferSpace - uxOffset );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test reading from the stream buffer when there are just enough
 *        bytes and we are reading without offset and the tail is about
 *        to rollover.
 */
void test_uxStreamBufferGet_BytesRequiredEQBytesPresent_ZeroOffset_TailAboutToRollOver( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxMaxCount = 500;
    size_t uxBufferSpace = 500;
    size_t uxReturn;
    BaseType_t xPeek = 0;

    /* Clear everything and fill it with 0x11. */
    memset( pxLocalBuffer, 0x11, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Tail to 0 for simplicity. */
    pxLocalBuffer->uxTail = 1000;
    /* Only these many bytes available. */
    pxLocalBuffer->uxHead = pxLocalBuffer->uxTail + uxBufferSpace;
    /* Rollover adjustment. */
    pxLocalBuffer->uxHead -= pxLocalBuffer->LENGTH;

    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    uxReturn = uxStreamBufferGet( pxLocalBuffer, uxOffset, pucData, uxMaxCount, xPeek );

    /* 500 bytes should be written. */
    TEST_ASSERT_EQUAL( uxBufferSpace - uxOffset, uxReturn );
    /* the tail should be moved. */
    TEST_ASSERT_EQUAL( uxMaxCount - 24, pxLocalBuffer->uxTail );
    /* See if the data is copied. */
    TEST_ASSERT_EQUAL_MEMORY( pxLocalBuffer->ucArray, pucData, uxBufferSpace - uxOffset );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test reading from the stream buffer when there are just enough
 *        bytes and we are reading without any offset and the tail is about
 *        to roll over. But, as a twist, we are just peeking into the buffer.
 */
void test_uxStreamBufferGet_BytesRequiredEQBytesPresent_ZeroOffset_TailAboutToRollOver_ButJustPeeking( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxMaxCount = 500;
    size_t uxBufferSpace = 500;
    size_t uxReturn;
    /* We are just peeking. */
    BaseType_t xPeek = 1;

    /* Clear everything and fill it with 0x11. */
    memset( pxLocalBuffer, 0x11, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Tail to 0 for simplicity. */
    pxLocalBuffer->uxTail = 1000;
    /* Only these many bytes available. */
    pxLocalBuffer->uxHead = pxLocalBuffer->uxTail + uxBufferSpace;
    /* Rollover adjustment. */
    pxLocalBuffer->uxHead -= pxLocalBuffer->LENGTH;

    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    uxReturn = uxStreamBufferGet( pxLocalBuffer, uxOffset, pucData, uxMaxCount, xPeek );

    /* 500 bytes should be written. */
    TEST_ASSERT_EQUAL( uxBufferSpace - uxOffset, uxReturn );
    /* the tail should not be moved. */
    TEST_ASSERT_EQUAL( 1000, pxLocalBuffer->uxTail );
    /* See if the data is copied. */
    TEST_ASSERT_EQUAL_MEMORY( pxLocalBuffer->ucArray, pucData, uxBufferSpace - uxOffset );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}

/*
 * @brief Test reading from the stream buffer when we provide a NULL buffer to
 *        copy data.
 */
void test_uxStreamBufferGet_NULLPointer( void )
{
    const uint16_t usBufferSize = 1024;
    /* Now we need to get a buffer which can store up to 1024 bytes. */
    StreamBuffer_t * pxLocalBuffer = malloc( sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );
    size_t uxOffset = 0;
    uint8_t pucData[ 512 ];
    size_t uxMaxCount = 500;
    size_t uxBufferSpace = 500;
    size_t uxReturn;
    BaseType_t xPeek = 0;

    /* Clear everything and fill it with 0x11. */
    memset( pxLocalBuffer, 0x11, sizeof( StreamBuffer_t ) - sizeof( pxLocalBuffer->ucArray ) + usBufferSize );

    /* Fill the Data (0xAB) */
    memset( pucData, 0xAB, sizeof( pucData ) );

    pxLocalBuffer->LENGTH = usBufferSize;
    /* Set Tail to 0 for simplicity. */
    pxLocalBuffer->uxTail = 1000;
    /* Only these many bytes available. */
    pxLocalBuffer->uxHead = pxLocalBuffer->uxTail + uxBufferSpace;
    /* Rollover adjustment. */
    pxLocalBuffer->uxHead -= pxLocalBuffer->LENGTH;

    pxLocalBuffer->uxMid = 0;
    pxLocalBuffer->uxFront = 0;

    FreeRTOS_min_size_t_Stub( FreeRTOS_min_stub );

    uxReturn = uxStreamBufferGet( pxLocalBuffer, uxOffset, NULL, uxMaxCount, xPeek );

    /* No bytes should be read. But still the tail moves forward. */
    TEST_ASSERT_EQUAL( 500, uxReturn );
    /* The tail should be moved. */
    TEST_ASSERT_EQUAL( 476, pxLocalBuffer->uxTail );
    /* Make sure that the rest of buffer is untouched. i.e. zero.*/
    TEST_ASSERT_EACH_EQUAL_UINT8( 0xAB, pucData, sizeof( pucData ) );

    /* Free the allocated data. */
    free( pxLocalBuffer );
}
