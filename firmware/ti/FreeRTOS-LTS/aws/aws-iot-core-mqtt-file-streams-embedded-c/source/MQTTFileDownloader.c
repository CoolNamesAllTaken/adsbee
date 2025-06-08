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
 * @file MQTTFileDownloader.c
 * @brief MQTT file streaming APIs.
 */
/* Standard includes. */

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "MQTTFileDownloader.h"
#include "MQTTFileDownloader_defaults.h"
#include "MQTTFileDownloader_base64.h"
#include "MQTTFileDownloader_cbor.h"
#include "core_json.h"

/**
 * @brief Macro to check whether a character is an ASCII digit or not.
 */
#define IS_CHAR_DIGIT( x )    ( ( ( x ) >= '0' ) && ( ( x ) <= '9' ) )

/**
 * @brief Macro to convert an ASCII digit to integer.
 */
#define CHAR_TO_DIGIT( x )    ( ( x ) - '0' )

/**
 * @brief Build a string from a set of strings
 *
 * @param[in] buffer Buffer to place the output string in.
 * @param[in] bufferSizeBytes Size of the buffer pointed to by buffer.
 * @param[in] strings NULL-terminated array of string pointers.
 * @return size_t Length of the output string, not including the terminator.
 */
static size_t stringBuilder( char * buffer,
                             size_t bufferSizeBytes,
                             const char * const strings[] );

/**
 * @brief Create MQTT topics from common substrings and input variables.
 *
 * @param[out] topicBuffer Buffer to place the output topic in.
 * @param[in] topicBufferLen Length of topicBuffer.
 * @param[in] streamName Name of the MQTT stream.
 * @param[in] streamNameLength Length of the MQTT stream name.
 * @param[in] thingName Name of the thing.
 * @param[in] thingNameLength Length of the thing name of the Device.
 * @param[in] apiSuffix Last part of the MQTT topic.
 *
 * @return uint16_t Length of the MQTT topic, not including the terminator.
 */
static uint16_t createTopic( char * topicBuffer,
                             size_t topicBufferLen,
                             const char * streamName,
                             size_t streamNameLength,
                             const char * thingName,
                             size_t thingNameLength,
                             const char * apiSuffix );

/**
 * @brief Handles and decodes the received message in CBOR format.
 *
 * @param[in] message Incoming MQTT message received.
 * @param[in] messageLength Length of the MQTT message received.
 * @param[out] fileId ID of the file to which the data block belongs.
 * @param[out] blockId ID of the received block.
 * @param[out] blockSize Size of the receive block in bytes.
 * @param[out] decodedData Buffer to place the decoded data in.
 * @param[out] decodedDataLength Length of decoded data.
 *
 * @return uint8_t returns appropriate MQTT File Downloader Status.
 */
static MQTTFileDownloaderStatus_t handleCborMessage( const uint8_t * message,
                                                     size_t messageLength,
                                                     int32_t * fileId,
                                                     int32_t * blockId,
                                                     int32_t * blockSize,
                                                     uint8_t * decodedData,
                                                     size_t * decodedDataLength );

/**
 * @brief Handles and decodes the received message in JSON format.
 *
 * @param[in] message Incoming MQTT message received.
 * @param[in] messageLength Length of the MQTT message received.
 * @param[out] fileId ID of the file to which the data block belongs.
 * @param[out] blockId ID of the received block.
 * @param[out] blockSize Size of the receive block in bytes.
 * @param[out] decodedData Buffer to place the decoded data in.
 * @param[out] decodedDataLength Length of decoded data.
 *
 * @return uint8_t returns appropriate MQTT File Downloader Status.
 */
static MQTTFileDownloaderStatus_t handleJsonMessage( uint8_t * message,
                                                     size_t messageLength,
                                                     int32_t * fileId,
                                                     int32_t * blockId,
                                                     int32_t * blockSize,
                                                     uint8_t * decodedData,
                                                     size_t * decodedDataLength );

/**
 * @brief Parses C-string interpreting its contents as a POSITIVE
 *        int32_t number.
 *
 * @param[in] str String which has the ASCII representation of the
 *            number.
 * @param[in] len Length of the string.
 * @param[out] num Pointer to an int32_t variable which will be filled
 *            with the parsed value. If the return value of the function
 *            call is false, then the value present in num is invalid.
 *
 * @return bool if the string is malformed or the decoded number
 * cannot fit in an int32_t value then this function returns false. On
 * successful parsing, it returns true.
 */
static bool getNumberFromString( const char * str,
                                 size_t len,
                                 int32_t * num );

static size_t stringBuilder( char * buffer,
                             size_t bufferSizeBytes,
                             const char * const strings[] )
{
    size_t curLen = 0;
    size_t i;
    size_t thisLength = 0;

    buffer[ 0 ] = '\0';

    for( i = 0; strings[ i ] != NULL; i++ )
    {
        thisLength = strlen( strings[ i ] );

        if( ( thisLength + curLen + 1U ) > bufferSizeBytes )
        {
            curLen = 0;
            break;
        }

        ( void ) strncat( buffer, strings[ i ], bufferSizeBytes - curLen - 1U );
        curLen += thisLength;
    }

    buffer[ curLen ] = '\0';

    return curLen;
}

static uint16_t createTopic( char * topicBuffer,
                             size_t topicBufferLen,
                             const char * streamName,
                             size_t streamNameLength,
                             const char * thingName,
                             size_t thingNameLength,
                             const char * apiSuffix )
{
    uint16_t topicLen = 0;
    char streamNameBuff[ STREAM_NAME_MAX_LEN + 1 ];
    char thingNameBuff[ MAX_THINGNAME_LEN + 1 ];

    /* NULL-terminated list of topic string parts. */
    const char * topicParts[] =
    {
        MQTT_API_THINGS,
        NULL, /* Thing Name not available at compile
               * time, initialized below. */
        MQTT_API_STREAMS,
        NULL, /* Stream Name not available at compile
               * time, initialized below.*/
        NULL,
        NULL
    };

    ( void ) memset( streamNameBuff, ( int32_t ) '\0', STREAM_NAME_MAX_LEN + 1U );
    ( void ) memcpy( streamNameBuff, streamName, streamNameLength );

    ( void ) memset( thingNameBuff, ( int32_t ) '\0', MAX_THINGNAME_LEN + 1U );
    ( void ) memcpy( thingNameBuff, thingName, thingNameLength );

    topicParts[ 1 ] = ( const char * ) thingNameBuff;
    topicParts[ 3 ] = ( const char * ) streamNameBuff;
    topicParts[ 4 ] = ( const char * ) apiSuffix;

    topicLen = ( uint16_t ) stringBuilder( topicBuffer,
                                           topicBufferLen,
                                           topicParts );

    return topicLen;
}

MQTTFileDownloaderStatus_t mqttDownloader_init( MqttFileDownloaderContext_t * context,
                                                const char * streamName,
                                                size_t streamNameLength,
                                                const char * thingName,
                                                size_t thingNameLength,
                                                DataType_t dataType )
{
    const char * streamDataApiSuffix = NULL;
    const char * getStreamApiSuffix = NULL;
    MQTTFileDownloaderStatus_t initStatus = MQTTFileDownloaderSuccess;

    if( ( streamName == NULL ) || ( streamNameLength == 0U ) ||
        ( thingName == NULL ) || ( thingNameLength == 0U ) || ( context == NULL ) )
    {
        initStatus = MQTTFileDownloaderBadParameter;
    }

    if( initStatus == MQTTFileDownloaderSuccess )
    {
        /* Initializing MQTT File Downloader context */
        ( void ) memset( context->topicStreamData, ( int32_t ) '\0', TOPIC_STREAM_DATA_BUFFER_SIZE );
        ( void ) memset( context->topicGetStream, ( int32_t ) '\0', TOPIC_GET_STREAM_BUFFER_SIZE );
        context->topicStreamDataLength = 0U;
        context->topicGetStreamLength = 0U;
        context->dataType = ( uint8_t ) dataType;

        if( context->dataType == ( uint8_t ) DATA_TYPE_JSON )
        {
            streamDataApiSuffix = MQTT_API_DATA_JSON;
        }
        else
        {
            streamDataApiSuffix = MQTT_API_DATA_CBOR;
        }

        context->topicStreamDataLength = createTopic(
            context->topicStreamData,
            TOPIC_STREAM_DATA_BUFFER_SIZE,
            streamName,
            streamNameLength,
            thingName,
            thingNameLength,
            streamDataApiSuffix );

        if( context->topicStreamDataLength == 0U )
        {
            initStatus = MQTTFileDownloaderInitFailed;
        }
    }

    if( initStatus == MQTTFileDownloaderSuccess )
    {
        if( dataType == DATA_TYPE_JSON )
        {
            getStreamApiSuffix = MQTT_API_GET_JSON;
        }
        else
        {
            getStreamApiSuffix = MQTT_API_GET_CBOR;
        }

        context
           ->topicGetStreamLength = createTopic( context->topicGetStream,
                                                 TOPIC_GET_STREAM_BUFFER_SIZE,
                                                 streamName,
                                                 streamNameLength,
                                                 thingName,
                                                 thingNameLength,
                                                 getStreamApiSuffix );

        if( context->topicGetStreamLength == 0U )
        {
            initStatus = MQTTFileDownloaderInitFailed;
        }
    }

    return initStatus;
}

size_t mqttDownloader_createGetDataBlockRequest( DataType_t dataType,
                                                 uint16_t fileId,
                                                 uint32_t blockSize,
                                                 uint16_t blockOffset,
                                                 uint32_t numberOfBlocksRequested,
                                                 char * getStreamRequest,
                                                 size_t getStreamRequestLength )
{
    size_t requestLength = 0U;

    /*
     * Get stream request format
     *
     *   "{ \"s\" : 1, \"f\": 1, \"l\": 256, \"o\": 0, \"n\": 1 }";
     */
    if( ( getStreamRequestLength >= GET_STREAM_REQUEST_BUFFER_SIZE ) &&
        ( getStreamRequest != NULL ) )
    {
        ( void ) memset( getStreamRequest, ( int32_t ) '\0', GET_STREAM_REQUEST_BUFFER_SIZE );

        if( dataType == DATA_TYPE_JSON )
        {
            /* MISRA Ref 21.6.1 [Use of snprintf] */
            /* More details at: https://github.com/aws/aws-iot-core-mqtt-file-streams-embedded-c//blob/main/MISRA.md#rule-216 */
            /* coverity[misra_c_2012_rule_21_6_violation] */
            ( void ) snprintf( getStreamRequest,
                               GET_STREAM_REQUEST_BUFFER_SIZE,
                               "{"
                               "\"s\": 1,"
                               "\"f\": %u,"
                               "\"l\": %u,"
                               "\"o\": %u,"
                               "\"n\": %u"
                               "}",
                               fileId,
                               blockSize,
                               blockOffset,
                               numberOfBlocksRequested );

            requestLength = strnlen( getStreamRequest,
                                     GET_STREAM_REQUEST_BUFFER_SIZE );
        }
        else
        {
            /* MISRA Ref 7.4.1 [Use of string literal] */
            /* More details at: https://github.com/aws/aws-iot-core-mqtt-file-streams-embedded-c//blob/main/MISRA.md#rule-74 */
            ( void ) CBOR_Encode_GetStreamRequestMessage( ( uint8_t * ) getStreamRequest,
                                                          GET_STREAM_REQUEST_BUFFER_SIZE,
                                                          &requestLength,
                                                          "rdy",
                                                          fileId,
                                                          blockSize,
                                                          blockOffset,
                                                          /* coverity[misra_c_2012_rule_7_4_violation] */
                                                          ( const uint8_t * ) "MQ==",
                                                          strlen( "MQ==" ),
                                                          numberOfBlocksRequested );
        }
    }

    return requestLength;
}

static MQTTFileDownloaderStatus_t handleCborMessage( const uint8_t * message,
                                                     size_t messageLength,
                                                     int32_t * fileId,
                                                     int32_t * blockId,
                                                     int32_t * blockSize,
                                                     uint8_t * decodedData,
                                                     size_t * decodedDataLength )
{
    bool cborDecodeRet = false;
    uint8_t * payload = decodedData;
    size_t payloadSize = mqttFileDownloader_CONFIG_BLOCK_SIZE;
    MQTTFileDownloaderStatus_t handleStatus = MQTTFileDownloaderSuccess;

    cborDecodeRet = CBOR_Decode_GetStreamResponseMessage( message,
                                                          messageLength,
                                                          fileId,
                                                          blockId,
                                                          blockSize,
                                                          &payload,
                                                          &payloadSize );

    if( cborDecodeRet )
    {
        *decodedDataLength = payloadSize;
    }
    else
    {
        handleStatus = MQTTFileDownloaderDataDecodingFailed;
    }

    return handleStatus;
}

static bool getNumberFromString( const char * str,
                                 size_t len,
                                 int32_t * num )
{
    int32_t out = 0;
    int32_t digit;
    bool retVal = true;
    const int32_t maxValue = 2147483647;

    /* Biggest number which can fit in an int32_t is 2147483647 which has 10 digits. */
    assert( len <= 10 );

    for( size_t uxIndex = 0U; uxIndex < len; uxIndex++ )
    {
        if( IS_CHAR_DIGIT( str[ uxIndex ] ) == true )
        {
            digit = CHAR_TO_DIGIT( str[ uxIndex ] );

            if( ( maxValue / 10 ) < out )
            {
                /* The out value will overflow on multiplication with 10. */
                retVal = false;
            }
            else if( ( maxValue - digit ) < ( out * 10 ) )
            {
                /* The value ( out * 10 ) will overflow when the digit is
                 * added to it. */
                retVal = false;
            }
            else
            {
                out = ( out * 10 ) + digit;
            }
        }
        else
        {
            retVal = false;
        }

        if( retVal == false )
        {
            break;
        }
    }

    if( retVal == true )
    {
        *num = out;
    }

    return retVal;
}

static MQTTFileDownloaderStatus_t handleJsonMessage( uint8_t * message,
                                                     size_t messageLength,
                                                     int32_t * fileId,
                                                     int32_t * blockId,
                                                     int32_t * blockSize,
                                                     uint8_t * decodedData,
                                                     size_t * decodedDataLength )
{
    const char fileIdQuery[] = "f";
    size_t fileIdQueryLength = sizeof( fileIdQuery ) - 1U;
    const char blockIdQuery[] = "i";
    size_t blockIdQueryLength = sizeof( blockIdQuery ) - 1U;
    const char blockSizeQuery[] = "l";
    size_t blockSizeQueryLength = sizeof( blockSizeQuery ) - 1U;
    const char dataQuery[] = "p";
    size_t dataQueryLength = sizeof( dataQuery ) - 1U;
    char * dataValue;
    size_t dataValueLength;
    size_t fileBlockLength;
    char * value;
    JSONStatus_t result = JSONSuccess;
    MQTTFileDownloaderStatus_t handleStatus = MQTTFileDownloaderDataDecodingFailed;

    Base64Status_t base64Status = Base64Success;

    result = JSON_Search( ( char * ) message,
                          messageLength,
                          fileIdQuery,
                          fileIdQueryLength,
                          &value,
                          &fileBlockLength );

    if( result == JSONSuccess )
    {
        if( getNumberFromString( value, fileBlockLength, fileId ) == true )
        {
            handleStatus = MQTTFileDownloaderSuccess;
        }
    }

    if( handleStatus == MQTTFileDownloaderSuccess )
    {
        result = JSON_Search( ( char * ) message,
                              messageLength,
                              blockIdQuery,
                              blockIdQueryLength,
                              &value,
                              &fileBlockLength );

        if( result == JSONSuccess )
        {
            if( getNumberFromString( value, fileBlockLength, blockId ) == false )
            {
                handleStatus = MQTTFileDownloaderDataDecodingFailed;
            }
        }
        else
        {
            handleStatus = MQTTFileDownloaderDataDecodingFailed;
        }
    }

    if( handleStatus == MQTTFileDownloaderSuccess )
    {
        result = JSON_Search( ( char * ) message,
                              messageLength,
                              blockSizeQuery,
                              blockSizeQueryLength,
                              &value,
                              &fileBlockLength );

        if( result == JSONSuccess )
        {
            if( getNumberFromString( value, fileBlockLength, blockSize ) == false )
            {
                handleStatus = MQTTFileDownloaderDataDecodingFailed;
            }
        }
        else
        {
            handleStatus = MQTTFileDownloaderDataDecodingFailed;
        }
    }

    if( handleStatus == MQTTFileDownloaderSuccess )
    {
        result = JSON_Search( ( char * ) message,
                              messageLength,
                              dataQuery,
                              dataQueryLength,
                              &dataValue,
                              &dataValueLength );

        if( result != JSONSuccess )
        {
            handleStatus = MQTTFileDownloaderDataDecodingFailed;
        }
    }

    if( handleStatus == MQTTFileDownloaderSuccess )
    {
        base64Status = base64_Decode( decodedData,
                                      mqttFileDownloader_CONFIG_BLOCK_SIZE,
                                      decodedDataLength,
                                      ( const uint8_t * ) dataValue,
                                      dataValueLength );

        if( base64Status != Base64Success )
        {
            handleStatus = MQTTFileDownloaderDataDecodingFailed;
        }
    }

    return handleStatus;
}

MQTTFileDownloaderStatus_t mqttDownloader_isDataBlockReceived( const MqttFileDownloaderContext_t * context,
                                                               const char * topic,
                                                               size_t topicLength )
{
    MQTTFileDownloaderStatus_t status = MQTTFileDownloaderFailure;

    if( ( topic == NULL ) || ( topicLength == 0U ) )
    {
        status = MQTTFileDownloaderBadParameter;
    }
    else if( ( topicLength == context->topicStreamDataLength ) &&
             ( 0 == strncmp( context->topicStreamData, topic, topicLength ) ) )
    {
        status = MQTTFileDownloaderSuccess;
    }
    else
    {
        /* Empty MISRA body */
    }

    return status;
}

MQTTFileDownloaderStatus_t mqttDownloader_processReceivedDataBlock( const MqttFileDownloaderContext_t * context,
                                                                    uint8_t * message,
                                                                    size_t messageLength,
                                                                    int32_t * fileId,
                                                                    int32_t * blockId,
                                                                    int32_t * blockSize,
                                                                    uint8_t * data,
                                                                    size_t * dataLength )
{
    MQTTFileDownloaderStatus_t decodingStatus = MQTTFileDownloaderFailure;

    if( ( message != NULL ) && ( messageLength != 0U ) &&
        ( data != NULL ) && ( dataLength != NULL ) &&
        ( fileId != NULL ) && ( blockId != NULL ) &&
        ( blockSize != NULL ) )
    {
        ( void ) memset( data, ( int32_t ) '\0', mqttFileDownloader_CONFIG_BLOCK_SIZE );

        if( context->dataType == ( uint8_t ) DATA_TYPE_JSON )
        {
            decodingStatus = handleJsonMessage( message,
                                                messageLength,
                                                fileId,
                                                blockId,
                                                blockSize,
                                                data,
                                                dataLength );
        }
        else
        {
            decodingStatus = handleCborMessage( message,
                                                messageLength,
                                                fileId,
                                                blockId,
                                                blockSize,
                                                data,
                                                dataLength );
        }
    }

    return decodingStatus;
}
