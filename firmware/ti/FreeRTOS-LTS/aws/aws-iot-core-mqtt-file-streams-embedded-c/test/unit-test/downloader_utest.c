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

#include "mock_MQTTFileDownloader_cbor.h"

#include "MQTTFileDownloader.h"
#include "MQTTFileDownloader_defaults.h"

#define GET_STREAM_REQUEST_BUFFER_SIZE    256U

/* ============================   TEST GLOBALS ============================= */

char * thingName = "thingname";
size_t thingNameLength = strlen( "thingname" );
char * streamName = "stream-name";
size_t streamNameLength = strlen( "stream-name" );
char * getStreamTopic = "get-stream-topic";
size_t getStreamTopicLength = strlen( "get-stream-topic" );

size_t requestLength;
/* ===========================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
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

/* =============================   CALLBACKS   ============================= */

bool mqtt_subscribe_stream_json_true( char * topic,
                                      size_t topicLength )
{
    TEST_ASSERT_EQUAL_MEMORY( "$aws/things/thingname/streams/stream-name/data/json", topic, strlen( "$aws/things/thingname/streams/stream-name/data/json" ) );
    TEST_ASSERT_EQUAL_INT( strlen( "$aws/things/thingname/streams/stream-name/data/json" ), topicLength );
    return true;
}

bool mqtt_subscribe_stream_json_false( char * topic,
                                       size_t topicLength )
{
    TEST_ASSERT_EQUAL_MEMORY( "$aws/things/thingname/streams/stream-name/data/json", topic, strlen( "$aws/things/thingname/streams/stream-name/data/json" ) );
    TEST_ASSERT_EQUAL_INT( strlen( "$aws/things/thingname/streams/stream-name/data/json" ), topicLength );
    return false;
}


bool mqtt_subscribe_stream_cbor_true( char * topic,
                                      size_t topicLength )
{
    TEST_ASSERT_EQUAL_MEMORY( "$aws/things/thingname/streams/stream-name/data/cbor", topic, strlen( "$aws/things/thingname/streams/stream-name/data/cbor" ) );
    TEST_ASSERT_EQUAL_INT( strlen( "$aws/things/thingname/streams/stream-name/data/cbor" ), topicLength );
    return true;
}

bool mqtt_subscribe_stream_cbor_false( char * topic,
                                       size_t topicLength )
{
    TEST_ASSERT_EQUAL_MEMORY( "$aws/things/thingname/streams/stream-name/data/cbor", topic, strlen( "$aws/things/thingname/streams/stream-name/data/cbor" ) );
    TEST_ASSERT_EQUAL_INT( strlen( "$aws/things/thingname/streams/stream-name/data/cbor" ), topicLength );
    return false;
}

bool mqtt_publish_request_json_true( char * topic,
                                     size_t topicLength,
                                     uint8_t * message,
                                     size_t messageLength )
{
    TEST_ASSERT_EQUAL_MEMORY( getStreamTopic, topic, getStreamTopicLength );
    TEST_ASSERT_EQUAL_INT( getStreamTopicLength, topicLength );
    TEST_ASSERT_EQUAL_MEMORY( "{\"s\": 1,\"f\": 4,\"l\": 3,\"o\": 2,\"n\": 1}", message, strlen( "{\"s\": 1,\"f\": 4,\"l\": 3,\"o\": 2,\"n\": 1}" ) );
    TEST_ASSERT_EQUAL_INT( strlen( "{\"s\": 1,\"f\": 4,\"l\": 3,\"o\": 2,\"n\": 1}" ), messageLength );
    return true;
}

bool mqtt_publish_request_json_false( char * topic,
                                      size_t topicLength,
                                      uint8_t * message,
                                      size_t messageLength )
{
    TEST_ASSERT_EQUAL_MEMORY( getStreamTopic, topic, getStreamTopicLength );
    TEST_ASSERT_EQUAL_INT( getStreamTopicLength, topicLength );
    TEST_ASSERT_EQUAL_MEMORY( "{\"s\": 1,\"f\": 4,\"l\": 3,\"o\": 2,\"n\": 1}", message, strlen( "{\"s\": 1,\"f\": 4,\"l\": 3,\"o\": 2,\"n\": 1}" ) );
    TEST_ASSERT_EQUAL_INT( strlen( "{\"s\": 1,\"f\": 4,\"l\": 3,\"o\": 2,\"n\": 1}" ), messageLength );
    return false;
}

/* ===============================   TESTS   =============================== */

void test_init_returnsSuccess_forJSONDataType( void )
{
    MqttFileDownloaderContext_t context;

    MQTTFileDownloaderStatus_t result = mqttDownloader_init( &context, streamName, streamNameLength, thingName, thingNameLength, DATA_TYPE_JSON );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderSuccess, result );
    TEST_ASSERT_EQUAL_MEMORY( "$aws/things/thingname/streams/stream-name/data/json", context.topicStreamData, strlen( "$aws/things/thingname/streams/stream-name/data/json" ) );
    TEST_ASSERT_EQUAL_INT( strlen( "$aws/things/thingname/streams/stream-name/data/json" ), context.topicStreamDataLength );
    TEST_ASSERT_EQUAL_MEMORY( "$aws/things/thingname/streams/stream-name/get/json", context.topicGetStream, strlen( "$aws/things/thingname/streams/stream-name/get/json" ) );
    TEST_ASSERT_EQUAL_INT( strlen( "$aws/things/thingname/streams/stream-name/get/json" ), context.topicGetStreamLength );
}

void test_init_returnsSuccess_forCBORDataType( void )
{
    MqttFileDownloaderContext_t context;

    MQTTFileDownloaderStatus_t result = mqttDownloader_init( &context, streamName, streamNameLength, thingName, thingNameLength, DATA_TYPE_CBOR );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderSuccess, result );
    TEST_ASSERT_EQUAL_MEMORY( "$aws/things/thingname/streams/stream-name/data/cbor", context.topicStreamData, strlen( "$aws/things/thingname/streams/stream-name/data/cbor" ) );
    TEST_ASSERT_EQUAL_INT( strlen( "$aws/things/thingname/streams/stream-name/data/cbor" ), context.topicStreamDataLength );
    TEST_ASSERT_EQUAL_MEMORY( "$aws/things/thingname/streams/stream-name/get/cbor", context.topicGetStream, strlen( "$aws/things/thingname/streams/stream-name/get/cbor" ) );
    TEST_ASSERT_EQUAL_INT( strlen( "$aws/things/thingname/streams/stream-name/get/cbor" ), context.topicGetStreamLength );
}

void test_init_returnsBadParam_givenNullContext( void )
{
    MQTTFileDownloaderStatus_t result = mqttDownloader_init( NULL, streamName, streamNameLength, thingName, thingNameLength, DATA_TYPE_JSON );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderBadParameter, result );
}

void test_init_returnsBadParam_givenNullStreamName( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    MQTTFileDownloaderStatus_t result = mqttDownloader_init( &context, NULL, streamNameLength, thingName, thingNameLength, DATA_TYPE_JSON );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderBadParameter, result );
}

void test_init_returnsBadParam_givenZeroStreamNameLength( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    MQTTFileDownloaderStatus_t result = mqttDownloader_init( &context, streamName, 0, thingName, thingNameLength, DATA_TYPE_JSON );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderBadParameter, result );
}

void test_init_returnsBadParam_givenNullThingName( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    MQTTFileDownloaderStatus_t result = mqttDownloader_init( &context, streamName, streamNameLength, NULL, thingNameLength, DATA_TYPE_JSON );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderBadParameter, result );
}

void test_init_returnsBadParam_givenZeroThingNameLength( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    MQTTFileDownloaderStatus_t result = mqttDownloader_init( &context, streamName, streamNameLength, thingName, 0, DATA_TYPE_JSON );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderBadParameter, result );
}

void test_createGetDataBlockRequest_succeedsForJSONDataType( void )
{
    char getStreamRequest[ GET_STREAM_REQUEST_BUFFER_SIZE ];
    size_t getStreamRequestLength = GET_STREAM_REQUEST_BUFFER_SIZE;

    requestLength = mqttDownloader_createGetDataBlockRequest( DATA_TYPE_JSON, 4U, 3U, 2U, 1U, getStreamRequest, getStreamRequestLength );
    TEST_ASSERT_EQUAL_INT( strlen( "{\"s\": 1,\"f\": 4,\"l\": 3,\"o\": 2,\"n\": 1}" ), requestLength );
    TEST_ASSERT_EQUAL_MEMORY( getStreamRequest, "{\"s\": 1,\"f\": 4,\"l\": 3,\"o\": 2,\"n\": 1}", strlen( "{\"s\": 1,\"f\": 4,\"l\": 3,\"o\": 2,\"n\": 1}" ) );
}

void test_createGetDataBlockRequest_succeedsForCBORDataType( void )
{
    char getStreamRequest[ GET_STREAM_REQUEST_BUFFER_SIZE ];
    size_t getStreamRequestLength = GET_STREAM_REQUEST_BUFFER_SIZE;

    char * encodedMessage = "expected-message";
    size_t expectedCborSize = 9999U;

    CBOR_Encode_GetStreamRequestMessage_ExpectAndReturn( ( uint8_t * ) &getStreamRequest,
                                                         GET_STREAM_REQUEST_BUFFER_SIZE,
                                                         NULL,
                                                         "rdy",
                                                         4,
                                                         3,
                                                         2,
                                                         ( const uint8_t * ) "MQ==",
                                                         strlen( "MQ==" ),
                                                         1,
                                                         true );

    CBOR_Encode_GetStreamRequestMessage_IgnoreArg_encodedMessageSize();
    CBOR_Encode_GetStreamRequestMessage_IgnoreArg_messageBuffer();
    CBOR_Encode_GetStreamRequestMessage_ReturnThruPtr_encodedMessageSize( &expectedCborSize );
    CBOR_Encode_GetStreamRequestMessage_ReturnThruPtr_messageBuffer( ( uint8_t * ) encodedMessage );

    requestLength = mqttDownloader_createGetDataBlockRequest( DATA_TYPE_CBOR, 4U, 3U, 2U, 1U, getStreamRequest, getStreamRequestLength );
    TEST_ASSERT_EQUAL( expectedCborSize, requestLength );
    TEST_ASSERT_EQUAL_MEMORY( encodedMessage, "expected-message", strlen( encodedMessage ) );
}

void test_createGetDataBlockRequest_FailsWhenGetStreamRequestLengthTooSmall( void )
{
    char getStreamRequest[ GET_STREAM_REQUEST_BUFFER_SIZE ];
    size_t getStreamRequestLength = 0;

    requestLength = mqttDownloader_createGetDataBlockRequest( DATA_TYPE_JSON, 4U, 3U, 2U, 1U, getStreamRequest, getStreamRequestLength );
    TEST_ASSERT_EQUAL( 0, requestLength );
}

void test_createGetDataBlockRequest_FailsWhenGetStreamRequestBufferIsNull( void )
{
    size_t getStreamRequestLength = GET_STREAM_REQUEST_BUFFER_SIZE;

    requestLength = mqttDownloader_createGetDataBlockRequest( DATA_TYPE_JSON, 4U, 3U, 2U, 1U, NULL, getStreamRequestLength );
    TEST_ASSERT_EQUAL( 0, requestLength );
}

void test_isDataBlockReceived_returnTrue( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    memcpy( context.topicStreamData, "topic", strlen( "topic" ) );
    context.topicStreamDataLength = strlen( "topic" );
    TEST_ASSERT_TRUE( mqttDownloader_isDataBlockReceived( &context, "topic", strlen( "topic" ) ) );
}

void test_isDataBlockReceived_returnsFalse_whenTopicIsDifferent( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    memcpy( context.topicStreamData, "topic", strlen( "topic" ) );
    context.topicStreamDataLength = strlen( "topic" );
    TEST_ASSERT_FALSE( mqttDownloader_isDataBlockReceived( &context, "different-topic", strlen( "topic" ) ) );
}

void test_isDataBlockReceived_returnsFalse_whenLengthIsDifferent( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    memcpy( context.topicStreamData, "topic", strlen( "topic" ) );
    context.topicStreamDataLength = strlen( "topic" );
    TEST_ASSERT_FALSE( mqttDownloader_isDataBlockReceived( &context, "topic", 10 ) );
}

void test_isDataBlockReceived_returnsFalse_whenTopicAndLengthIsDifferent( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    memcpy( context.topicStreamData, "topic", strlen( "topic" ) );
    context.topicStreamDataLength = strlen( "topic" );
    TEST_ASSERT_FALSE( mqttDownloader_isDataBlockReceived( &context, "completely-different-topic", strlen( "completely-different-topic" ) ) );
}


void test_isDataBlockReceived_returnsBadParam_whenTopicIsNull( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    TEST_ASSERT_EQUAL( MQTTFileDownloaderBadParameter, mqttDownloader_isDataBlockReceived( &context, NULL, strlen( "topic" ) ) );
}

void test_isDataBlockReceived_returnsBadParam_whenTopicLengthIsZero( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    TEST_ASSERT_EQUAL( MQTTFileDownloaderBadParameter, mqttDownloader_isDataBlockReceived( &context, "topic", 0 ) );
}

void test_processReceivedDataBlock_processesJSONBlock( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"f\": \"12\", \"i\": \"1\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    bool result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_TRUE( result );
    TEST_ASSERT_EQUAL( 12, fileId );
    TEST_ASSERT_EQUAL( 1, blockId );
    TEST_ASSERT_EQUAL( 512, blockSize );
    TEST_ASSERT_EQUAL( 4, dataLength );
}

void test_processReceivedDataBlock__invalidJSONBlock_fileIdNotANumber( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"f\": \"file\", \"i\": \"1\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 0, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock__invalidJSONBlock_blockIdNotANumber( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"f\": \"0\", \"i\": \"block\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 0, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock__invalidJSONBlock_blockSizeNotANumber( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"f\": \"10\", \"i\": \"1\", \"l\": \"size\", \"p\": \"dGVzdA==\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 10, fileId );
    TEST_ASSERT_EQUAL( 1, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock__invalidJSONBlock_blockSizeNegative( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"f\": \"10\", \"i\": \"1\", \"l\": \"-123\", \"p\": \"dGVzdA==\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 10, fileId );
    TEST_ASSERT_EQUAL( 1, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock__invalidJSONBlock_fileIdNegative( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"f\": \"-10\", \"i\": \"1\", \"l\": \"16\", \"p\": \"dGVzdA==\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 0, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock__invalidJSONBlock_blockIdNegative( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"f\": \"10\", \"i\": \"-11\", \"l\": \"12\", \"p\": \"dGVzdA==\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 10, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

/* This test is meant to test the internal getNumberFromString function. It should fail as the
 * number being passed to it will not fit in an int32_t. */
void test_processReceivedDataBlock__invalidJSONBlock_blockSizeIsTooBig( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;

    const char * message1 = "{\"f\": \"20\", \"i\": \"56\", \"l\": \"5147483647\", \"p\": \"dGVzdA==\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message1, strlen( message1 ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 20, fileId );
    TEST_ASSERT_EQUAL( 56, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );

    const char * message2 = "{\"f\": \"20\", \"i\": \"56\", \"l\": \"2147483649\", \"p\": \"dGVzdA==\"}";

    result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message2, strlen( message2 ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 20, fileId );
    TEST_ASSERT_EQUAL( 56, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock_invalidJSONBlock( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    const char * message = "{\"wrongKey\": \"dGVzdA==\"}";

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 0, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock_invalidJSONBlock_fileIdNotPresent( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"i\": \"1\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 0, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock_invalidJSONBlock_blockIdNotPresent( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"f\": \"1\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 1, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock_invalidJSONBlock_blockSizeNotPresent( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"f\": \"1\", \"i\": \"12\", \"p\": \"dGVzdA==\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 1, fileId );
    TEST_ASSERT_EQUAL( 12, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock_invalidJSONBlock_payloadNotPresent( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"f\": \"1\", \"l\": \"512\", \"i\": \"12\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 1, fileId );
    TEST_ASSERT_EQUAL( 12, blockId );
    TEST_ASSERT_EQUAL( 512, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock_invalidEncodingJSONBlock( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    const char * message = "{\"f\": \"12\", \"i\": \"1\", \"l\": \"512\", \"p\": \"notEncoded\"}";

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 12, fileId );
    TEST_ASSERT_EQUAL( 1, blockId );
    TEST_ASSERT_EQUAL( 512, blockSize );
    TEST_ASSERT_EQUAL( 0, dataLength );
}

void test_processReceivedDataBlock_processesCBORBlock( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_CBOR;

    char * validCBORMsg = "aValidCBORMsg";
    size_t expectedProcessedDataLength = 12345U;
    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;
    int32_t expectedFileId = 20;
    int32_t expectedBlockId = 30;
    int32_t expectedBlockSize = 40;

    CBOR_Decode_GetStreamResponseMessage_ExpectAndReturn( ( const uint8_t * ) validCBORMsg, strlen( validCBORMsg ), NULL, NULL, NULL, NULL, NULL, true );
    CBOR_Decode_GetStreamResponseMessage_IgnoreArg_fileId();
    CBOR_Decode_GetStreamResponseMessage_IgnoreArg_blockSize();
    CBOR_Decode_GetStreamResponseMessage_IgnoreArg_blockId();
    CBOR_Decode_GetStreamResponseMessage_IgnoreArg_payload();
    CBOR_Decode_GetStreamResponseMessage_IgnoreArg_payloadSize();
    CBOR_Decode_GetStreamResponseMessage_ReturnThruPtr_fileId( &expectedFileId );
    CBOR_Decode_GetStreamResponseMessage_ReturnThruPtr_blockId( &expectedBlockId );
    CBOR_Decode_GetStreamResponseMessage_ReturnThruPtr_blockSize( &expectedBlockSize );
    CBOR_Decode_GetStreamResponseMessage_ReturnThruPtr_payloadSize( &expectedProcessedDataLength );

    bool result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) validCBORMsg, strlen( validCBORMsg ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_TRUE( result );
    TEST_ASSERT_EQUAL( expectedFileId, fileId );
    TEST_ASSERT_EQUAL( expectedBlockId, blockId );
    TEST_ASSERT_EQUAL( expectedBlockSize, blockSize );
    TEST_ASSERT_EQUAL( expectedProcessedDataLength, dataLength );
}

void test_processReceivedDataBlock_invalidCBORBlock( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_CBOR;

    char * invalidCBORMsg = "invalidCBORMsg";
    size_t notExpectedProcessedDataLength = 12345U;
    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;

    CBOR_Decode_GetStreamResponseMessage_ExpectAndReturn( ( const uint8_t * ) invalidCBORMsg, strlen( invalidCBORMsg ), NULL, NULL, NULL, NULL, NULL, false );
    CBOR_Decode_GetStreamResponseMessage_IgnoreArg_fileId();
    CBOR_Decode_GetStreamResponseMessage_IgnoreArg_blockSize();
    CBOR_Decode_GetStreamResponseMessage_IgnoreArg_blockId();
    CBOR_Decode_GetStreamResponseMessage_IgnoreArg_payload();
    CBOR_Decode_GetStreamResponseMessage_IgnoreArg_payloadSize();
    CBOR_Decode_GetStreamResponseMessage_ReturnThruPtr_payloadSize( &notExpectedProcessedDataLength );

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) invalidCBORMsg, strlen( invalidCBORMsg ), &fileId, &blockId, &blockSize, decodedData, &dataLength );

    TEST_ASSERT_EQUAL( MQTTFileDownloaderDataDecodingFailed, result );
    TEST_ASSERT_EQUAL( 0, dataLength );
    TEST_ASSERT_EQUAL( 0, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
}

void test_processReceivedDataBlock_returnsFailureWhenMessageIsNull( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    const char * message = "{\"f\": \"0\", \"i\": \"1\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, NULL, strlen( message ), &fileId, &blockId, &blockSize, decodedData, &dataLength );
    TEST_ASSERT_EQUAL( MQTTFileDownloaderFailure, result );
    TEST_ASSERT_EQUAL( 0, dataLength );
    TEST_ASSERT_EQUAL( 0, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
}

void test_processReceivedDataBlock_returnsFailureWhenMessageLengthZero( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    const char * message = "{\"f\": \"0\", \"i\": \"1\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, 0U, &fileId, &blockId, &blockSize, decodedData, &dataLength );
    TEST_ASSERT_EQUAL( MQTTFileDownloaderFailure, result );
    TEST_ASSERT_EQUAL( 0, dataLength );
    TEST_ASSERT_EQUAL( 0, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
}

void test_processReceivedDataBlock_returnsFailureWhenDataIsNull( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    const char * message = "{\"f\": \"0\", \"i\": \"1\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, NULL, &dataLength );
    TEST_ASSERT_EQUAL( MQTTFileDownloaderFailure, result );
    TEST_ASSERT_EQUAL( 0, dataLength );
    TEST_ASSERT_EQUAL( 0, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
}

void test_processReceivedDataBlock_returnsFailureWhenDataLengthIsNull( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    const char * message = "{\"f\": \"0\", \"i\": \"1\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t * dataLength = NULL;
    int32_t fileId = 0;
    int32_t blockId = 0;
    int32_t blockSize = 0;

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, &blockSize, decodedData, dataLength );
    TEST_ASSERT_EQUAL( MQTTFileDownloaderFailure, result );
}

void test_processReceivedDataBlock_returnsFailureWhenFileIdIsNull( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    const char * message = "{\"f\": \"0\", \"i\": \"1\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t blockId = 0;
    int32_t blockSize = 0;

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), NULL, &blockId, &blockSize, decodedData, &dataLength );
    TEST_ASSERT_EQUAL( MQTTFileDownloaderFailure, result );
    TEST_ASSERT_EQUAL( 0, dataLength );
    TEST_ASSERT_EQUAL( 0, blockId );
    TEST_ASSERT_EQUAL( 0, blockSize );
}

void test_processReceivedDataBlock_returnsFailureWhenBlockIdIsNull( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    const char * message = "{\"f\": \"0\", \"i\": \"1\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockSize = 0;

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, NULL, &blockSize, decodedData, &dataLength );
    TEST_ASSERT_EQUAL( MQTTFileDownloaderFailure, result );
    TEST_ASSERT_EQUAL( 0, dataLength );
    TEST_ASSERT_EQUAL( 0, fileId );
    TEST_ASSERT_EQUAL( 0, blockSize );
}

void test_processReceivedDataBlock_returnsFailureWhenBlockSizeIsNull( void )
{
    MqttFileDownloaderContext_t context = { 0 };

    context.dataType = DATA_TYPE_JSON;

    const char * message = "{\"f\": \"0\", \"i\": \"1\", \"l\": \"512\", \"p\": \"dGVzdA==\"}";

    uint8_t decodedData[ mqttFileDownloader_CONFIG_BLOCK_SIZE ];
    size_t dataLength = 0U;
    int32_t fileId = 0;
    int32_t blockId = 0;

    MQTTFileDownloaderStatus_t result = mqttDownloader_processReceivedDataBlock( &context, ( uint8_t * ) message, strlen( message ), &fileId, &blockId, NULL, decodedData, &dataLength );
    TEST_ASSERT_EQUAL( MQTTFileDownloaderFailure, result );
    TEST_ASSERT_EQUAL( 0, dataLength );
    TEST_ASSERT_EQUAL( 0, fileId );
    TEST_ASSERT_EQUAL( 0, blockId );
}
