/*
 * AWS IoT Core MQTT File Streams Embedded C v1.1.0
 * Copyright (C) 2023 Amazon.com, Inc. and its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License. See the LICENSE accompanying this file
 * for the specific language governing permissions and limitations under
 * the License.
 */

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "unity.h"
#include "MQTTFileDownloader.h"
#include "MQTTFileDownloader_defaults.h"
#include "MQTTFileDownloader_base64.h"

#define GET_STREAM_REQUEST_BUFFER_SIZE    256U

/* ============================   TEST GLOBALS ============================= */
const size_t destLength = mqttFileDownloader_CONFIG_BLOCK_SIZE;
const uint8_t * encodedTest = ( const uint8_t * ) "dGVzdA=="; /* The string 'test' base64 encoded */
size_t encodedTestLen = 8U;
size_t decodedTestLen = 4U;

uint8_t destBuffer[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];

Base64Status_t decodeStatus;
size_t decodeLen;
/* ===========================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    decodeStatus = Base64Success;

    memset( destBuffer, 0U, mqttFileDownloader_CONFIG_BLOCK_SIZE );
}

/* Called after each test method. */
void tearDown()
{
}

/* Called at the beginning of the whole suite. */
void suiteSetUp()
{
}

/* Called at the end of the whole suite. */
int suiteTearDown( int numFailures )
{
    return numFailures;
}


/* ===============================   TESTS   =============================== */

void test_base64Decode_decodesDataSuccessfully( void )
{
    /* Setting to an error before the test to make sure it's the function which succeeds */
    decodeStatus = Base64NullPointerInput;

    decodeStatus = base64_Decode( destBuffer, destLength, &decodeLen, encodedTest, encodedTestLen );

    TEST_ASSERT_EQUAL( Base64Success, decodeStatus );
    TEST_ASSERT_EQUAL( decodedTestLen, decodeLen );
}

void test_base64Decode_decodesDataSuccessfully_2Chars( void )
{
    /* Setting to an error before the test to make sure it's the function which succeeds */
    decodeStatus = Base64NullPointerInput;

    decodeStatus = base64_Decode( destBuffer, destLength, &decodeLen, ( const uint8_t * ) "dHk=", 4U );

    TEST_ASSERT_EQUAL( Base64Success, decodeStatus );
    TEST_ASSERT_EQUAL( 2, decodeLen );
}

void test_base64Decode_decodesDataSuccessfully_3Chars( void )
{
    /* Setting to an error before the test to make sure it's the function which succeeds */
    decodeStatus = Base64NullPointerInput;

    decodeStatus = base64_Decode( destBuffer, destLength, &decodeLen, ( const uint8_t * ) "dHJ5", 3U );

    TEST_ASSERT_EQUAL( Base64NonZeroPadding, decodeStatus );
}

void test_base64Decode_returnsInvalidBufferSize_givenTooSmallOfBuffer( void )
{
    /* Setting to an error before the test to make sure it's the function which succeeds */
    decodeStatus = Base64NullPointerInput;
    decodeLen = 123456789U;

    decodeStatus = base64_Decode( destBuffer, 3U, &decodeLen, encodedTest, encodedTestLen );

    TEST_ASSERT_EQUAL( Base64InvalidBufferSize, decodeStatus );
    TEST_ASSERT_EQUAL( 123456789U, decodeLen );
}

void test_base64Decode_returnsBase64InvalidSymbol_givenOverPadding( void )
{
    decodeLen = 123456789U;

    uint8_t allPaddingSymbols[ 3U ] = { 0 };
    allPaddingSymbols[ 0 ] = 61U;
    allPaddingSymbols[ 1 ] = 61U;
    allPaddingSymbols[ 2 ] = 61U;

    decodeStatus = base64_Decode( destBuffer, destLength, &decodeLen, ( const uint8_t * ) &allPaddingSymbols, 3U );

    TEST_ASSERT_EQUAL( Base64InvalidPaddingSymbol, decodeStatus );
    TEST_ASSERT_EQUAL( 123456789U, decodeLen );
}

void test_base64Decode_returnsBase64InvalidSymbol_givenInvalidCharacter( void )
{
    decodeLen = 123456789U;

    uint8_t invalidSymbols[ 2U ] = { 0 };
    invalidSymbols[ 0 ] = 255U;
    invalidSymbols[ 1 ] = 255;

    decodeStatus = base64_Decode( destBuffer, destLength, &decodeLen, ( const uint8_t * ) &invalidSymbols, 2U );

    TEST_ASSERT_EQUAL( Base64InvalidSymbol, decodeStatus );
    TEST_ASSERT_EQUAL( 123456789U, decodeLen );
}

void test_base64Decode_returnsBase64InvalidSymbolOrdering_givenWhitespaceNewlinePaddingOrdering( void )
{
    decodeLen = 123456789U;

    uint8_t whitespaceNewlinePadding[ 3U ] = { 0 };
    whitespaceNewlinePadding[ 0 ] = 32U;
    whitespaceNewlinePadding[ 1 ] = 10U;
    whitespaceNewlinePadding[ 2 ] = 61U;

    decodeStatus = base64_Decode( destBuffer, destLength, &decodeLen, ( const uint8_t * ) &whitespaceNewlinePadding, 3U );

    TEST_ASSERT_EQUAL( Base64InvalidSymbolOrdering, decodeStatus );
    TEST_ASSERT_EQUAL( 123456789U, decodeLen );
}

void test_base64Decode_returnsBase64InvalidSymbolOrdering_givenWhitespaceBeforeCharacter( void )
{
    decodeLen = 123456789U;

    uint8_t whitespaceThenCharacter[ 2U ] = { 0 };
    whitespaceThenCharacter[ 0 ] = 32U;
    whitespaceThenCharacter[ 1 ] = 65U;

    decodeStatus = base64_Decode( destBuffer, destLength, &decodeLen, ( const uint8_t * ) &whitespaceThenCharacter, 2U );

    TEST_ASSERT_EQUAL( Base64InvalidSymbolOrdering, decodeStatus );
    TEST_ASSERT_EQUAL( 123456789U, decodeLen );
}

void test_base64Decode_returnsBase64InvalidSymbolOrdering_givenPaddingBeforeCharacter( void )
{
    decodeLen = 123456789U;

    uint8_t paddingBeforeChar[ 2U ] = { 0 };
    paddingBeforeChar[ 0 ] = 61U;
    paddingBeforeChar[ 1 ] = 65U;

    decodeStatus = base64_Decode( destBuffer, destLength, &decodeLen, ( const uint8_t * ) &paddingBeforeChar, 2U );

    TEST_ASSERT_EQUAL( Base64InvalidSymbolOrdering, decodeStatus );
    TEST_ASSERT_EQUAL( 123456789U, decodeLen );
}

void test_base64Decode_returnsNullPointerInput_givenNullEncodedData( void )
{
    decodeStatus = base64_Decode( destBuffer, destLength, &decodeLen, NULL, 3U );

    TEST_ASSERT_EQUAL( Base64NullPointerInput, decodeStatus );
}

void test_base64Decode_returnsNullPointerInput_givenNullDest( void )
{
    decodeStatus = base64_Decode( NULL, destLength, &decodeLen, ( const uint8_t * ) encodedTest, 3U );

    TEST_ASSERT_EQUAL( Base64NullPointerInput, decodeStatus );
}

void test_base64Decode_returnsNullPointerInput_givenNullResultLengthPtr( void )
{
    decodeStatus = base64_Decode( destBuffer, destLength, NULL, ( const uint8_t * ) encodedTest, 3U );

    TEST_ASSERT_EQUAL( Base64NullPointerInput, decodeStatus );
}

void test_base64Decode_returnsInvalidInputSize_givenSmallEncodeLength( void )
{
    decodeStatus = base64_Decode( destBuffer, destLength, &decodeLen, ( const uint8_t * ) encodedTest, 1U );

    TEST_ASSERT_EQUAL( Base64InvalidInputSize, decodeStatus );
}
