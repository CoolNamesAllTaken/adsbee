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

#include "mock_cbor.h"

#include "MQTTFileDownloader_cbor.h"

/**
 * @brief Number of keys in cbor get stream request message.
 */
#define CBOR_GETSTREAMREQUEST_ITEM_COUNT    6

/* ============================   TEST GLOBALS ============================= */
const uint8_t * decodeMessageBuffer = ( const uint8_t * ) "decodeMessageBuffer";
uint8_t * encodeMessageBuffer = ( uint8_t * ) "encodeMessageBuffer";
const uint8_t * blockBitmap = ( const uint8_t * ) "blockBitmap";
const char * clientToken = "clientToken";
int32_t blockId = 1;
int32_t blockSize = 2;
int32_t blockOffset = 1;
int32_t fileId = 999;
int32_t numOfBlocksRequested = 1;
size_t blockBitmapSize = 98765;
size_t encodedMessageSize = 1234;
size_t payloadSize = 123456789;
size_t payloadSizeReceived = 33333;
uint8_t payloadVal = 4;
uint8_t * PayloadPtr = &payloadVal;
uint8_t * const * payload = &PayloadPtr;

CborValue cborMap;
CborValue cborValue;
CborEncoder cborEncoder;
CborEncoder cborMapEncoder;

bool result;
/* ===========================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    result = false;
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

/* ==============================   HELPERS   ============================== */

void cborInitializesSuccessful( void )
{
    cbor_parser_init_ExpectAndReturn( decodeMessageBuffer, 1234U, 0, NULL, NULL, CborNoError );
    cbor_parser_init_IgnoreArg_parser();
    cbor_parser_init_IgnoreArg_it();
    cbor_parser_init_ReturnThruPtr_it( &cborMap );
}

void cborFindsFileIdKey( void )
{
    cbor_value_map_find_value_ExpectAndReturn( &cborMap, OTA_CBOR_FILEID_KEY, NULL, CborNoError );
    cbor_value_map_find_value_IgnoreArg_element();
    cbor_value_map_find_value_ReturnThruPtr_element( &cborValue );
}

void cborFileIdKeyCorrectType( void )
{
    cbor_value_get_type_ExpectAndReturn( &cborValue, CborIntegerType );
    cbor_value_get_int_ExpectAndReturn( &cborValue, &fileId, CborNoError );
}

void cborFindsBlockIdKey( void )
{
    cbor_value_map_find_value_ExpectAndReturn( &cborMap, OTA_CBOR_BLOCKID_KEY, &cborValue, CborNoError );
    cbor_value_map_find_value_IgnoreArg_element();
    cbor_value_map_find_value_ReturnThruPtr_element( &cborValue );
}

void cborBlockIdKeyCorrectType( void )
{
    cbor_value_get_type_ExpectAndReturn( &cborValue, ( CborType ) CborNoError );
    cbor_value_get_int_ExpectAndReturn( &cborValue, &blockId, CborNoError );
}

void cborFindsBlockSizeKey( void )
{
    cbor_value_map_find_value_ExpectAndReturn( &cborMap, OTA_CBOR_BLOCKSIZE_KEY, &cborValue, CborNoError );
    cbor_value_map_find_value_IgnoreArg_element();
    cbor_value_map_find_value_ReturnThruPtr_element( &cborValue );
}

void cborBlockSizeKeyCorrectType( void )
{
    cbor_value_get_type_ExpectAndReturn( &cborValue, ( CborType ) CborNoError );
    cbor_value_get_int_ExpectAndReturn( &cborValue, &blockSize, CborNoError );
}

void cborFindsPayloadKeyInMap( void )
{
    cbor_value_map_find_value_ExpectAndReturn( &cborMap, OTA_CBOR_BLOCKPAYLOAD_KEY, &cborValue, CborNoError );
    cbor_value_map_find_value_IgnoreArg_element();
    cbor_value_map_find_value_ReturnThruPtr_element( &cborValue );
}

void cborDeterminesPayloadSizeReceived( void )
{
    cbor_value_calculate_string_length_ExpectAndReturn( &cborValue, NULL, CborNoError );
    cbor_value_calculate_string_length_IgnoreArg_length();
    cbor_value_calculate_string_length_ReturnThruPtr_length( &payloadSizeReceived );
}

void cborCreatesEncoder( void )
{
    cbor_encoder_init_Expect( NULL, encodeMessageBuffer, 1234U, 0 );
    cbor_encoder_init_IgnoreArg_encoder();
    cbor_encoder_init_ReturnThruPtr_encoder( &cborEncoder );
}

void cborCreatesMapEncoder( void )
{
    cbor_encoder_create_map_ExpectAndReturn( &cborEncoder, NULL, CBOR_GETSTREAMREQUEST_ITEM_COUNT, CborNoError );
    cbor_encoder_create_map_IgnoreArg_mapEncoder();
    cbor_encoder_create_map_ReturnThruPtr_mapEncoder( &cborMapEncoder );
}

void cborEncodesClientToken( void )
{
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_CLIENTTOKEN_KEY, CborNoError );
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, clientToken, CborNoError );
}

void cborEncodesFileId( void )
{
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_FILEID_KEY, CborNoError );
    cbor_encode_int_ExpectAndReturn( &cborMapEncoder, fileId, CborNoError );
}

void cborEncodesBlockSize( void )
{
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_BLOCKSIZE_KEY, CborNoError );
    cbor_encode_int_ExpectAndReturn( &cborMapEncoder, blockSize, CborNoError );
}

void cborEncodesBlockOffset( void )
{
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_BLOCKOFFSET_KEY, CborNoError );
    cbor_encode_int_ExpectAndReturn( &cborMapEncoder, blockOffset, CborNoError );
}

void cborEncodesBitmap( void )
{
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_BLOCKBITMAP_KEY, CborNoError );
    cbor_encode_byte_string_ExpectAndReturn( &cborMapEncoder, blockBitmap, blockBitmapSize, CborNoError );
}

void cborEncodesNumberOfBlocks( void )
{
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_NUMBEROFBLOCKS_KEY, CborNoError );
    cbor_encode_int_ExpectAndReturn( &cborMapEncoder, numOfBlocksRequested, CborNoError );
}

/* ===============================   TESTS   =============================== */

void test_Decode_succeeds( void )
{
    uint8_t * payloadPtr;

    payloadSizeReceived = payloadSize - 1;

    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();
    cborFindsBlockIdKey();
    cborBlockIdKeyCorrectType();
    cborFindsBlockSizeKey();
    cborBlockSizeKeyCorrectType();
    cborFindsPayloadKeyInMap();
    cbor_value_get_type_ExpectAndReturn( &cborValue, CborByteStringType );
    cborDeterminesPayloadSizeReceived();
    cbor_value_copy_byte_string_ExpectAndReturn( &cborValue, payloadPtr, &payloadSize, NULL, CborNoError );
    cbor_value_copy_byte_string_IgnoreArg_next();

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, &payloadPtr, &payloadSize );
    TEST_ASSERT_TRUE( result );
}

void test_Decode_returnsFalse_givenNullFields( void )
{
    result = true;
    result = CBOR_Decode_GetStreamResponseMessage( NULL, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );

    result = true;
    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, NULL, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );

    result = true;
    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, NULL, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );

    result = true;
    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, NULL, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );

    result = true;
    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, NULL, &payloadSize );
    TEST_ASSERT_FALSE( result );

    result = true;
    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, NULL );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_cannotInitParser( void )
{
    cbor_parser_init_ExpectAndReturn( decodeMessageBuffer, 1234U, 0, NULL, NULL, CborUnknownError );
    cbor_parser_init_IgnoreArg_parser();
    cbor_parser_init_IgnoreArg_it();

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_valueIsNotMap( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, false );

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_cannotFindFileIdInMap( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );

    cbor_value_map_find_value_ExpectAndReturn( &cborMap, OTA_CBOR_FILEID_KEY, NULL, CborUnknownError );
    cbor_value_map_find_value_IgnoreArg_element();

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_fileIdTypeInMapWrong( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cbor_value_get_type_ExpectAndReturn( &cborValue, CborUndefinedType );

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_cannotGetFileIdValue( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cbor_value_get_type_ExpectAndReturn( &cborValue, CborIntegerType );
    cbor_value_get_int_ExpectAndReturn( &cborValue, &fileId, CborUnknownError );

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_cannotFindBlockIdInMap( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();

    cbor_value_map_find_value_ExpectAndReturn( &cborMap, OTA_CBOR_BLOCKID_KEY, &cborValue, CborUnknownError );

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_blockIdWrongTypeInMap( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();
    cborFindsBlockIdKey();
    cbor_value_get_type_ExpectAndReturn( &cborValue, CborUndefinedType );

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_cannotGetBlockIdValue( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();
    cborFindsBlockIdKey();
    cbor_value_get_type_ExpectAndReturn( &cborValue, ( CborType ) CborNoError );
    cbor_value_get_int_ExpectAndReturn( &cborValue, &blockId, CborUnknownError );

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_cannotFindBlockSizeInMap( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();
    cborFindsBlockIdKey();
    cborBlockIdKeyCorrectType();
    cbor_value_map_find_value_ExpectAndReturn( &cborMap, OTA_CBOR_BLOCKSIZE_KEY, &cborValue, CborUnknownError );

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_blockSizeWrongTypeInMap( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();
    cborFindsBlockIdKey();
    cborBlockIdKeyCorrectType();
    cborFindsBlockSizeKey();
    cbor_value_get_type_ExpectAndReturn( &cborValue, ( CborType ) CborUnknownError );

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_cannotGetBlockSizeValue( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();
    cborFindsBlockIdKey();
    cborBlockIdKeyCorrectType();
    cborFindsBlockSizeKey();
    cbor_value_get_type_ExpectAndReturn( &cborValue, ( CborType ) CborNoError );
    cbor_value_get_int_ExpectAndReturn( &cborValue, &blockSize, CborUnknownError );

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_cannotFindBlockPayloadInMap( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();
    cborFindsBlockIdKey();
    cborBlockIdKeyCorrectType();
    cborFindsBlockSizeKey();
    cborBlockSizeKeyCorrectType();
    cbor_value_map_find_value_ExpectAndReturn( &cborMap, OTA_CBOR_BLOCKPAYLOAD_KEY, &cborValue, CborUnknownError );

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_blockPayloadWrongTypeInMap( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();
    cborFindsBlockIdKey();
    cborBlockIdKeyCorrectType();
    cborFindsBlockSizeKey();
    cborBlockSizeKeyCorrectType();
    cborFindsPayloadKeyInMap();

    cbor_value_get_type_ExpectAndReturn( &cborValue, ( CborType ) CborUnknownError );

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_cannotCalculateBlockPayloadLengthString( void )
{
    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();
    cborFindsBlockIdKey();
    cborBlockIdKeyCorrectType();
    cborFindsBlockSizeKey();
    cborBlockSizeKeyCorrectType();
    cborFindsPayloadKeyInMap();
    cbor_value_get_type_ExpectAndReturn( &cborValue, CborByteStringType );
    cbor_value_calculate_string_length_ExpectAndReturn( &cborValue, NULL, CborUnknownError );
    cbor_value_calculate_string_length_IgnoreArg_length();

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_blockPayloadLargerThanBuffer( void )
{
    payloadSizeReceived = payloadSize + 1;

    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();
    cborFindsBlockIdKey();
    cborBlockIdKeyCorrectType();
    cborFindsBlockSizeKey();
    cborBlockSizeKeyCorrectType();
    cborFindsPayloadKeyInMap();
    cbor_value_get_type_ExpectAndReturn( &cborValue, CborByteStringType );
    cborDeterminesPayloadSizeReceived();

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, payload, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Decode_returnsFalse_failsCopyingPayloadByteString( void )
{
    uint8_t * payloadPtr;

    payloadSizeReceived = payloadSize - 1;

    cborInitializesSuccessful();
    cbor_value_is_map_ExpectAndReturn( &cborMap, true );
    cborFindsFileIdKey();
    cborFileIdKeyCorrectType();
    cborFindsBlockIdKey();
    cborBlockIdKeyCorrectType();
    cborFindsBlockSizeKey();
    cborBlockSizeKeyCorrectType();
    cborFindsPayloadKeyInMap();
    cbor_value_get_type_ExpectAndReturn( &cborValue, CborByteStringType );
    cborDeterminesPayloadSizeReceived();
    cbor_value_copy_byte_string_ExpectAndReturn( &cborValue, payloadPtr, &payloadSize, NULL, CborUnknownError );
    cbor_value_copy_byte_string_IgnoreArg_next();

    result = CBOR_Decode_GetStreamResponseMessage( decodeMessageBuffer, 1234U, &fileId, &blockId, &blockSize, &payloadPtr, &payloadSize );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_succeeds( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cborEncodesFileId();
    cborEncodesBlockSize();
    cborEncodesBlockOffset();
    cborEncodesBitmap();
    cborEncodesNumberOfBlocks();
    cbor_encoder_close_container_checked_ExpectAndReturn( &cborEncoder, &cborMapEncoder, CborNoError );
    cbor_encoder_get_buffer_size_ExpectAndReturn( &cborEncoder, encodeMessageBuffer, 99999 );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_TRUE( result );
    TEST_ASSERT_EQUAL( encodedMessageSize, 99999 );
}

void test_Encode_returnsFalse_givenNullFields( void )
{
    result = true;
    result = CBOR_Encode_GetStreamRequestMessage( NULL, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );

    result = true;
    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, NULL, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );

    result = true;
    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, NULL, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );

    result = true;
    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, NULL, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_failsToCreateMap( void )
{
    cborCreatesEncoder();
    cbor_encoder_create_map_ExpectAndReturn( &cborEncoder, NULL, CBOR_GETSTREAMREQUEST_ITEM_COUNT, CborUnknownError );
    cbor_encoder_create_map_IgnoreArg_mapEncoder();
    cbor_encoder_create_map_ReturnThruPtr_mapEncoder( &cborMapEncoder );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeClientTokenKey( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_CLIENTTOKEN_KEY, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeClientTokenValue( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_CLIENTTOKEN_KEY, CborNoError );
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, clientToken, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeFileIdKey( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_FILEID_KEY, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeFileIdValue( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_FILEID_KEY, CborNoError );
    cbor_encode_int_ExpectAndReturn( &cborMapEncoder, fileId, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeBlockSizeKey( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cborEncodesFileId();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_BLOCKSIZE_KEY, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeBlockSizeValue( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cborEncodesFileId();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_BLOCKSIZE_KEY, CborNoError );
    cbor_encode_int_ExpectAndReturn( &cborMapEncoder, blockSize, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeBlockOffsetKey( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cborEncodesFileId();
    cborEncodesBlockSize();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_BLOCKOFFSET_KEY, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeBlockOffsetValue( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cborEncodesFileId();
    cborEncodesBlockSize();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_BLOCKOFFSET_KEY, CborNoError );
    cbor_encode_int_ExpectAndReturn( &cborMapEncoder, blockOffset, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeBitmapKey( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cborEncodesFileId();
    cborEncodesBlockSize();
    cborEncodesBlockOffset();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_BLOCKBITMAP_KEY, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeBitmapValue( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cborEncodesFileId();
    cborEncodesBlockSize();
    cborEncodesBlockOffset();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_BLOCKBITMAP_KEY, CborNoError );
    cbor_encode_byte_string_ExpectAndReturn( &cborMapEncoder, blockBitmap, blockBitmapSize, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeNumberBlocksKey( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cborEncodesFileId();
    cborEncodesBlockSize();
    cborEncodesBlockOffset();
    cborEncodesBitmap();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_NUMBEROFBLOCKS_KEY, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_cannotEncodeNumberBlocksValue( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cborEncodesFileId();
    cborEncodesBlockSize();
    cborEncodesBlockOffset();
    cborEncodesBitmap();
    cbor_encode_text_stringz_ExpectAndReturn( &cborMapEncoder, OTA_CBOR_NUMBEROFBLOCKS_KEY, CborNoError );
    cbor_encode_int_ExpectAndReturn( &cborMapEncoder, numOfBlocksRequested, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}

void test_Encode_returnsFalse_failsToCloseMapEncoder( void )
{
    cborCreatesEncoder();
    cborCreatesMapEncoder();
    cborEncodesClientToken();
    cborEncodesFileId();
    cborEncodesBlockSize();
    cborEncodesBlockOffset();
    cborEncodesBitmap();
    cborEncodesNumberOfBlocks();
    cbor_encoder_close_container_checked_ExpectAndReturn( &cborEncoder, &cborMapEncoder, CborUnknownError );

    result = CBOR_Encode_GetStreamRequestMessage( encodeMessageBuffer, 1234U, &encodedMessageSize, clientToken, fileId, blockSize, blockOffset, blockBitmap, blockBitmapSize, numOfBlocksRequested );
    TEST_ASSERT_FALSE( result );
}
