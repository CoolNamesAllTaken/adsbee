/*
 * AWS IoT Core MQTT File Streams Embedded C v1.1.0
 * Copyright (C) 2023 Amazon.com, Inc. and its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License. See the LICENSE accompanying this file
 * for the specific language governing permissions and limitations under
 * the License.
 */

/**
 * @file MQTTFileDownloader_cbor.c
 * @brief CBOR encode/decode routines.
 */

#include "MQTTFileDownloader_cbor.h"
#include "cbor.h"
#include <stdlib.h>

/**
 * @brief Number of keys in cbor get stream request message.
 */
#define CBOR_GETSTREAMREQUEST_ITEM_COUNT    6

/* ========================================================================== */

/**
 * @brief Helper function to verify the data type of the value in map.
 *
 * @param[in] expectedType Data type expected.
 * @param[in] Value Value to check.
 * @return CborError
 */
static CborError checkDataType( CborType expectedType,
                                const CborValue * Value )
{
    CborError cborResult = CborNoError;
    CborType actualType = cbor_value_get_type( Value );

    if( actualType != expectedType )
    {
        cborResult = CborErrorIllegalType;
    }

    return cborResult;
}

/**
 * @brief Decode a Get Stream response message from AWS IoT OTA.
 *
 * @param[in] messageBuffer message to decode.
 * @param[in] messageSize size of the message to decode.
 * @param[out] fileId Decoded file id value.
 * @param[out] blockId Decoded block id value.
 * @param[out] blockSize Decoded block size value.
 * @param[out] payload Buffer for the decoded payload.
 * @param[in,out] payloadSize maximum size of the buffer as in and actual
 * payload size for the decoded payload as out.
 *
 * @return TRUE when success, otherwise FALSE.
 */
bool CBOR_Decode_GetStreamResponseMessage( const uint8_t * messageBuffer,
                                           size_t messageSize,
                                           int32_t * fileId,
                                           int32_t * blockId,
                                           int32_t * blockSize,
                                           uint8_t * const * payload,
                                           size_t * payloadSize )
{
    CborError cborResult = CborNoError;
    CborParser parser;
    CborValue value, cborMap;
    size_t payloadSizeReceived = 0;

    if( ( fileId == NULL ) || ( blockId == NULL ) || ( blockSize == NULL ) ||
        ( payload == NULL ) || ( payloadSize == NULL ) ||
        ( messageBuffer == NULL ) )
    {
        cborResult = CborUnknownError;
    }

    /* Initialize the parser. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_parser_init( messageBuffer,
                                       messageSize,
                                       0,
                                       &parser,
                                       &cborMap );
    }

    /* Get the outer element and confirm that it's a "map," i.e., a set of
     * CBOR key/value pairs. */
    if( CborNoError == cborResult )
    {
        if( false == cbor_value_is_map( &cborMap ) )
        {
            cborResult = CborErrorIllegalType;
        }
    }

    /* Find the file ID. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_FILEID_KEY,
                                                &value );
    }

    if( CborNoError == cborResult )
    {
        cborResult = checkDataType( CborIntegerType, &value );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_get_int( &value, ( int32_t * ) fileId );
    }

    /* Find the block ID. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_BLOCKID_KEY,
                                                &value );
    }

    if( CborNoError == cborResult )
    {
        cborResult = checkDataType( CborIntegerType, &value );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_get_int( &value, ( int32_t * ) blockId );
    }

    /* Find the block size. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_BLOCKSIZE_KEY,
                                                &value );
    }

    if( CborNoError == cborResult )
    {
        cborResult = checkDataType( CborIntegerType, &value );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_get_int( &value, ( int32_t * ) blockSize );
    }

    /* Find the payload bytes. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_BLOCKPAYLOAD_KEY,
                                                &value );
    }

    if( CborNoError == cborResult )
    {
        cborResult = checkDataType( CborByteStringType, &value );
    }

    /* Calculate the size we need to malloc for the payload. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_calculate_string_length( &value,
                                                         &payloadSizeReceived );
    }

    if( CborNoError == cborResult )
    {
        /* Check if the received payload size is less than or equal to buffer
         * size. */
        if( payloadSizeReceived <= ( *payloadSize ) )
        {
            *payloadSize = payloadSizeReceived;
        }
        else
        {
            cborResult = CborErrorOutOfMemory;
        }
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_copy_byte_string( &value,
                                                  *payload,
                                                  payloadSize,
                                                  NULL );
    }

    return CborNoError == cborResult;
}

/**
 * @brief Create an encoded Get Stream Request message for the AWS IoT OTA
 * service. The service allows block count or block bitmap to be requested,
 * but not both.
 *
 * @param[in,out] messageBuffer Buffer to store the encoded message.
 * @param[in] messageBufferSize Size of the buffer to store the encoded message.
 * @param[out] encodedMessageSize Size of the final encoded message.
 * @param[in] clientToken Client token in the encoded message.
 * @param[in] fileId Value of file id in the encoded message.
 * @param[in] blockSize Value of block size in the encoded message.
 * @param[in] blockOffset Value of block offset in the encoded message.
 * @param[in] blockBitmap bitmap in the encoded message.
 * @param[in] blockBitmapSize Size of the provided bitmap buffer.
 * @param[in] numOfBlocksRequested number of blocks to request in the encoded
 * message.
 *
 * @return TRUE when success, otherwise FALSE.
 */
bool CBOR_Encode_GetStreamRequestMessage( uint8_t * messageBuffer,
                                          size_t messageBufferSize,
                                          size_t * encodedMessageSize,
                                          const char * clientToken,
                                          uint32_t fileId,
                                          uint32_t blockSize,
                                          uint32_t blockOffset,
                                          const uint8_t * blockBitmap,
                                          size_t blockBitmapSize,
                                          uint32_t numOfBlocksRequested )
{
    CborError cborResult = CborNoError;
    CborEncoder encoder, cborMapEncoder;

    if( ( messageBuffer == NULL ) || ( encodedMessageSize == NULL ) ||
        ( clientToken == NULL ) || ( blockBitmap == NULL ) )
    {
        cborResult = CborUnknownError;
    }

    /* Initialize the CBOR encoder. */
    if( CborNoError == cborResult )
    {
        cbor_encoder_init( &encoder, messageBuffer, messageBufferSize, 0 );
        cborResult = cbor_encoder_create_map( &encoder,
                                              &cborMapEncoder,
                                              CBOR_GETSTREAMREQUEST_ITEM_COUNT );
    }

    /* Encode the client token key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_CLIENTTOKEN_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder, clientToken );
    }

    /* Encode the file ID key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_FILEID_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder, ( int64_t ) fileId );
    }

    /* Encode the block size key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_BLOCKSIZE_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder, ( int64_t ) blockSize );
    }

    /* Encode the block offset key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_BLOCKOFFSET_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder, ( int64_t ) blockOffset );
    }

    /* Encode the block bitmap key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_BLOCKBITMAP_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_byte_string( &cborMapEncoder,
                                              blockBitmap,
                                              blockBitmapSize );
    }

    /* Encode the number of blocks requested key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_NUMBEROFBLOCKS_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder, ( int64_t ) numOfBlocksRequested );
    }

    /* Close the encoder. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encoder_close_container_checked( &encoder,
                                                           &cborMapEncoder );
    }

    /* Get the encoded size. */
    if( CborNoError == cborResult )
    {
        *encodedMessageSize = cbor_encoder_get_buffer_size( &encoder,
                                                            messageBuffer );
    }

    return CborNoError == cborResult;
}
