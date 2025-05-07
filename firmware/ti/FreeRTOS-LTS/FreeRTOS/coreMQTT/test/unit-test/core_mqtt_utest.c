/*
 * coreMQTT v2.3.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 */

/**
 * @file core_mqtt_utest.c
 * @brief Unit tests for functions in core_mqtt.h.
 */
#include <string.h>
#include <stdbool.h>
#include <stdint.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "core_mqtt.h"

#include "mock_core_mqtt_serializer.h"
#include "mock_core_mqtt_state.h"

#include "core_mqtt_config_defaults.h"

/* Set network context to double pointer to buffer (uint8_t**). */
struct NetworkContext
{
    uint8_t ** buffer;
};

/**
 * @brief MQTT client identifier.
 */
#define MQTT_CLIENT_IDENTIFIER                 "testclient"

/**
 * @brief A valid starting packet ID per MQTT spec. Start from 1.
 */
#define MQTT_FIRST_VALID_PACKET_ID             ( 1 )

/**
 * @brief A PINGREQ packet is always 2 bytes in size, defined by MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_PINGREQ_SIZE               ( 2U )

/**
 * @brief A packet type not handled by MQTT_ProcessLoop.
 */
#define MQTT_PACKET_TYPE_INVALID               ( 0U )

/**
 * @brief Number of milliseconds in a second.
 */
#define MQTT_ONE_SECOND_TO_MS                  ( 1000U )

/**
 * @brief Length of the MQTT network buffer.
 */
#define MQTT_TEST_BUFFER_LENGTH                ( 128 )

/**
 * @brief Sample keep-alive interval that should be greater than 0.
 */
#define MQTT_SAMPLE_KEEPALIVE_INTERVAL_S       ( 1U )

/**
 * @brief Length of time spent for single test case with
 * multiple iterations spent in the process loop for coverage.
 */
#define MQTT_SAMPLE_PROCESS_LOOP_TIMEOUT_MS    ( 1U )

/**
 * @brief Zero timeout in the process loop implies one iteration.
 */
#define MQTT_NO_TIMEOUT_MS                     ( 0U )

/**
 * @brief Sample length of remaining serialized data.
 */
#define MQTT_SAMPLE_REMAINING_LENGTH           ( 64 )

/**
 * @brief Subtract this value from max value of global entry time
 * for the timer overflow test.
 */
#define MQTT_OVERFLOW_OFFSET                   ( 3 )

/**
 * @brief The number of times the "getTime()" function is called
 * within a single iteration of the #MQTT_ProcessLoop.
 *
 * This constant is used for the timer overflow test which checks
 * that the API can support normal behavior even if the timer
 * overflows.
 *
 * @note Currently, there are 6 calls within a single iteration.
 * This can change when the implementation changes which would be
 * caught through unit test failure.
 */
#define MQTT_TIMER_CALLS_PER_ITERATION         ( 6 )

/**
 * @brief Timeout for the timer overflow test.
 */
#define MQTT_TIMER_OVERFLOW_TIMEOUT_MS         ( 10 )

/**
 * @brief A sample network context that we set to NULL.
 */
#define MQTT_SAMPLE_NETWORK_CONTEXT            ( NULL )

/**
 * @brief Sample topic filter to subscribe to.
 */
#define MQTT_SAMPLE_TOPIC_FILTER               "iot"

/**
 * @brief Length of sample topic filter.
 */
#define MQTT_SAMPLE_TOPIC_FILTER_LENGTH        ( sizeof( MQTT_SAMPLE_TOPIC_FILTER ) - 1 )

/**
 * @brief Sample topic filter to subscribe to.
 */
#define MQTT_SAMPLE_TOPIC_FILTER1              "TopicFilter2"

/**
 * @brief Length of sample topic filter.
 */
#define MQTT_SAMPLE_TOPIC_FILTER_LENGTH1       ( sizeof( MQTT_SAMPLE_TOPIC_FILTER1 ) - 1 )

/**
 * @brief Sample topic filter to subscribe to.
 */
#define MQTT_SAMPLE_TOPIC_FILTER2              "SomeTopic"

/**
 * @brief Length of sample topic filter.
 */
#define MQTT_SAMPLE_TOPIC_FILTER_LENGTH2       ( sizeof( MQTT_SAMPLE_TOPIC_FILTER2 ) - 1 )

/**
 * @brief Sample topic filter to subscribe to.
 */
#define MQTT_SAMPLE_TOPIC_FILTER3              "iotTopicFilter"

/**
 * @brief Length of sample topic filter.
 */
#define MQTT_SAMPLE_TOPIC_FILTER_LENGTH3       ( sizeof( MQTT_SAMPLE_TOPIC_FILTER3 ) - 1 )

/**
 * @brief Return values of mocked calls in MQTT_ProcessLoop(). Used by
 * `expectProcessLoopCalls`
 */
typedef struct ProcessLoopReturns
{
    MQTTStatus_t deserializeStatus;           /**< @brief Status after deserializing incoming packet. */
    MQTTPublishState_t stateAfterDeserialize; /**< @brief Publish state after deserializing incoming packet. */
    MQTTStatus_t updateStateStatus;           /**< @brief Status after updating publish state. */
    MQTTStatus_t serializeStatus;             /**< @brief Status after serializing a publish ack to send. */
    MQTTPublishState_t stateAfterSerialize;   /**< @brief Publish state after serializing an ack to send. */
    MQTTStatus_t processLoopStatus;           /**< @brief Return value of the process loop. */
    bool incomingPublish;                     /**< @brief Whether the incoming packet is a publish. */
    MQTTPublishInfo_t * pPubInfo;             /**< @brief Publish information to be returned by the deserializer. */
    uint32_t timeoutMs;                       /**< @brief The timeout value to call MQTT_ProcessLoop API with. */
} ProcessLoopReturns_t;

/**
 * @brief The packet type to be received by the process loop.
 * IMPORTANT: Make sure this is set before calling expectProcessLoopCalls(...).
 */
static uint8_t currentPacketType = MQTT_PACKET_TYPE_INVALID;

/**
 * @brief The return value of modifyIncomingPacket(...) CMock callback that
 * replaces a call to MQTT_GetIncomingPacketTypeAndLength.
 * IMPORTANT: Make sure this is set before calling expectProcessLoopCalls(...).
 */
static MQTTStatus_t modifyIncomingPacketStatus = MQTTSuccess;

/**
 * @brief Time at the beginning of each test. Note that this is not updated with
 * a real clock. Instead, we simply increment this variable.
 */
static uint32_t globalEntryTime = 0;

/**
 * @brief A static buffer used by the MQTT library for storing packet data.
 */
static uint8_t mqttBuffer[ MQTT_TEST_BUFFER_LENGTH ] = { 0 };

/**
 * @brief A flag to indicate whether event callback is called from
 * MQTT_ProcessLoop.
 */
static bool isEventCallbackInvoked = false;
static bool receiveOnce = false;

static const uint8_t SubscribeHeader[] =
{
    MQTT_PACKET_TYPE_SUBSCRIBE,                  /* Subscribe header. */
    0x10, 0x10,                                  /* Packet Length. */
    ( MQTT_FIRST_VALID_PACKET_ID >> 8 ),
    ( ( MQTT_FIRST_VALID_PACKET_ID ) & 0x00ffU ) /* Packet ID. */
};
static const size_t SubscribeHeaderLength = 5U;

static const uint8_t UnsubscribeHeader[] =
{
    MQTT_PACKET_TYPE_UNSUBSCRIBE,                /* Subscribe header. */
    0x12, 0x15,                                  /* Packet Length. */
    ( MQTT_FIRST_VALID_PACKET_ID >> 8 ),
    ( ( MQTT_FIRST_VALID_PACKET_ID ) & 0x00ffU ) /* Packet ID. */
};
static const size_t UnsubscribeHeaderLength = 5U;

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    memset( mqttBuffer, 0x0, sizeof( mqttBuffer ) );
    MQTT_State_strerror_IgnoreAndReturn( "DUMMY_MQTT_STATE" );

    globalEntryTime = 0;
}

/* Called after each test method. */
void tearDown()
{
}

/* Called at the beginning of the whole suite. */
void suiteSetUp()
{
    receiveOnce = 0;
}

/* Called at the end of the whole suite. */
int suiteTearDown( int numFailures )
{
    return numFailures;
}


/* ========================================================================== */

/**
 * @brief Mock successful transport send, and write data into buffer for
 * verification.
 */
static int32_t mockSend( NetworkContext_t * pNetworkContext,
                         const void * pMessage,
                         size_t bytesToSend )
{
    const uint8_t * buffer = ( const uint8_t * ) pMessage;
    /* Treat network context as pointer to buffer for mocking. */
    uint8_t * mockNetwork = *( pNetworkContext->buffer );
    size_t bytesSent = 0;

    while( bytesSent++ < bytesToSend )
    {
        /* Write single byte and advance buffer. */
        *mockNetwork++ = *buffer++;
    }

    /* Move stream by bytes sent. */
    *( pNetworkContext->buffer ) = mockNetwork;

    return bytesToSend;
}

/**
 * @brief Initialize pNetworkBuffer using static buffer.
 *
 * @param[in] pNetworkBuffer Network buffer provided for the context.
 */
static void setupNetworkBuffer( MQTTFixedBuffer_t * const pNetworkBuffer )
{
    pNetworkBuffer->pBuffer = mqttBuffer;
    pNetworkBuffer->size = MQTT_TEST_BUFFER_LENGTH;
}

/**
 * @brief Mocked MQTT event callback.
 *
 * @param[in] pContext MQTT context pointer.
 * @param[in] pPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] pDeserializedInfo Deserialized information from the incoming packet.
 */
static void eventCallback( MQTTContext_t * pContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           MQTTDeserializedInfo_t * pDeserializedInfo )
{
    ( void ) pContext;
    ( void ) pPacketInfo;
    ( void ) pDeserializedInfo;

    /* Update the global state to indicate that event callback is invoked. */
    isEventCallbackInvoked = true;
}

/**
 * @brief A mocked timer query function that increments on every call. This
 * guarantees that only a single iteration runs in the ProcessLoop for ease
 * of testing.
 */
static uint32_t getTime( void )
{
    return globalEntryTime++;
}

static int32_t getTimeMockCallLimit = -1;

/**
 * @brief A mocked timer query function that increments on every call. This
 * guarantees that only a single iteration runs in the ProcessLoop for ease
 * of testing. Additionally, this tests whether the number of calls to this
 * function have exceeded than the set limit and asserts.
 */
static uint32_t getTimeMock( void )
{
    TEST_ASSERT_GREATER_THAN_INT32( -1, getTimeMockCallLimit-- );
    return globalEntryTime++;
}

static int32_t getTimeMockBigTimeStepCallLimit = -1;

/**
 * @brief A mocked timer query function that increments by MQTT_SEND_TIMEOUT_MS
 * to simulate the time consumed by a long running high priority task on every
 * call. Additionally, this tests whether the number of calls to this function
 * have exceeded than the set limit and asserts.
 */
static uint32_t getTimeMockBigTimeStep( void )
{
    TEST_ASSERT_GREATER_THAN_INT32( -1, getTimeMockBigTimeStepCallLimit-- );

    globalEntryTime += MQTT_SEND_TIMEOUT_MS;
    return globalEntryTime;
}


/**
 * @brief A mocked timer function that could be used on a device with no system
 * time.
 */
static uint32_t getTimeDummy( void )
{
    return 0;
}

/**
 * @brief Mocked successful transport writev.
 *
 * @param[in] tcpSocket TCP socket.
 * @param[in] pMessage vectors to send
 * @param[in] bytesToWrite number of vectors
 *
 * @return Number of bytes sent; negative value on error;
 * 0 for timeout or 0 bytes sent.
 */
static int32_t transportWritevSuccess( NetworkContext_t * pNetworkContext,
                                       TransportOutVector_t * pIoVectorIterator,
                                       size_t vectorsToBeSent )
{
    TEST_ASSERT_EQUAL( MQTT_SAMPLE_NETWORK_CONTEXT, pNetworkContext );
    int32_t bytesToWrite = 0;
    size_t i;

    for( i = 0; i < vectorsToBeSent; ++i )
    {
        bytesToWrite += pIoVectorIterator->iov_len;
        pIoVectorIterator++;
    }

    return bytesToWrite;
}

static void verifyEncodedTopicString( TransportOutVector_t * pIoVectorIterator,
                                      char * pTopicFilter,
                                      size_t topicFilterLength,
                                      MQTTQoS_t topicQos,
                                      int32_t * pBytesToWrite )
{
    /* Encoded topic length. */
    uint8_t serializedLength[ 2 ];
    const uint8_t * buffer;
    size_t length;

    serializedLength[ 0 ] = ( uint8_t ) ( topicFilterLength >> 8 );
    serializedLength[ 1 ] = ( uint8_t ) ( topicFilterLength & 0x00ffU );

    buffer = pIoVectorIterator[ 0 ].iov_base;
    length = pIoVectorIterator[ 0 ].iov_len;

    TEST_ASSERT_EQUAL( 2U, length );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( serializedLength, buffer, 2U );
    ( *pBytesToWrite ) += length;

    buffer = pIoVectorIterator[ 1 ].iov_base;
    length = pIoVectorIterator[ 1 ].iov_len;

    /* Encoded topic string. */
    TEST_ASSERT_EQUAL( topicFilterLength, length );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( pTopicFilter, buffer, topicFilterLength );
    ( *pBytesToWrite ) += length;

    buffer = pIoVectorIterator[ 2 ].iov_base;
    length = pIoVectorIterator[ 2 ].iov_len;

    /* Encoded QoS. */
    TEST_ASSERT_EQUAL( 1U, length );
    TEST_ASSERT_EQUAL_UINT8( topicQos, *buffer );
    ( *pBytesToWrite ) += length;
}

static void verifyEncodedTopicStringUnsubscribe( TransportOutVector_t * pIoVectorIterator,
                                                 char * pTopicFilter,
                                                 size_t topicFilterLength,
                                                 int32_t * pBytesToWrite )
{
    /* Encoded topic length. */
    uint8_t serializedLength[ 2 ];
    const uint8_t * buffer;
    size_t length;

    serializedLength[ 0 ] = ( uint8_t ) ( topicFilterLength >> 8 );
    serializedLength[ 1 ] = ( uint8_t ) ( topicFilterLength & 0x00ffU );

    buffer = pIoVectorIterator[ 0 ].iov_base;
    length = pIoVectorIterator[ 0 ].iov_len;

    TEST_ASSERT_EQUAL( 2U, length );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( serializedLength, buffer, 2U );
    ( *pBytesToWrite ) += length;

    buffer = pIoVectorIterator[ 1 ].iov_base;
    length = pIoVectorIterator[ 1 ].iov_len;

    /* Encoded topic string. */
    TEST_ASSERT_EQUAL( topicFilterLength, length );
    TEST_ASSERT_EQUAL_UINT8_ARRAY( pTopicFilter, buffer, topicFilterLength );
    ( *pBytesToWrite ) += length;
}

/**
 * @brief Mocked transport writev to verify correct subscription
 * packet.
 *
 * @param[in] tcpSocket TCP socket.
 * @param[in] pMessage vectors to send
 * @param[in] bytesToWrite number of vectors
 *
 * @return Number of bytes sent; negative value on error;
 * 0 for timeout or 0 bytes sent.
 */
static int32_t transportWritevSubscribeSuccess( NetworkContext_t * pNetworkContext,
                                                TransportOutVector_t * pIoVectorIterator,
                                                size_t vectorsToBeSent )
{
    TEST_ASSERT_EQUAL( MQTT_SAMPLE_NETWORK_CONTEXT, pNetworkContext );
    int32_t bytesToWrite = 0;
    static int writeCount = 0;
    const uint8_t * buffer;
    size_t length;

    /* The header. */
    if( writeCount == 0 )
    {
        TEST_ASSERT_EQUAL( 4, vectorsToBeSent );

        buffer = pIoVectorIterator->iov_base;
        length = pIoVectorIterator->iov_len;

        TEST_ASSERT_EQUAL( length, SubscribeHeaderLength );
        TEST_ASSERT_EQUAL_UINT8_ARRAY( ( uint8_t * ) SubscribeHeader, buffer, SubscribeHeaderLength );

        bytesToWrite += length;
        pIoVectorIterator++;

        /* First topic filter. */
        verifyEncodedTopicString( pIoVectorIterator,
                                  MQTT_SAMPLE_TOPIC_FILTER,
                                  MQTT_SAMPLE_TOPIC_FILTER_LENGTH,
                                  MQTTQoS1,
                                  &bytesToWrite );

        writeCount++;

        pIoVectorIterator += 4;
    }
    else if( writeCount == 1 )
    {
        TEST_ASSERT_EQUAL( 6, vectorsToBeSent );

        /* Second topic filter. */
        verifyEncodedTopicString( pIoVectorIterator,
                                  MQTT_SAMPLE_TOPIC_FILTER1,
                                  MQTT_SAMPLE_TOPIC_FILTER_LENGTH1,
                                  MQTTQoS2,
                                  &bytesToWrite );

        pIoVectorIterator += 3;

        /* Third topic filter. */
        verifyEncodedTopicString( pIoVectorIterator,
                                  MQTT_SAMPLE_TOPIC_FILTER2,
                                  MQTT_SAMPLE_TOPIC_FILTER_LENGTH2,
                                  MQTTQoS0,
                                  &bytesToWrite );

        writeCount++;
    }
    else if( writeCount == 2 )
    {
        TEST_ASSERT_EQUAL( 3, vectorsToBeSent );

        /* Fourth topic filter. */
        verifyEncodedTopicString( pIoVectorIterator,
                                  MQTT_SAMPLE_TOPIC_FILTER3,
                                  MQTT_SAMPLE_TOPIC_FILTER_LENGTH3,
                                  MQTTQoS1,
                                  &bytesToWrite );

        writeCount++;
    }
    else
    {
        bytesToWrite = -1;
    }

    return bytesToWrite;
}

/**
 * @brief Mocked transport writev to verify correct subscription
 * packet.
 *
 * @param[in] tcpSocket TCP socket.
 * @param[in] pMessage vectors to send
 * @param[in] bytesToWrite number of vectors
 *
 * @return Number of bytes sent; negative value on error;
 * 0 for timeout or 0 bytes sent.
 */
static int32_t transportWritevUnsubscribeSuccess( NetworkContext_t * pNetworkContext,
                                                  TransportOutVector_t * pIoVectorIterator,
                                                  size_t vectorsToBeSent )
{
    TEST_ASSERT_EQUAL( MQTT_SAMPLE_NETWORK_CONTEXT, pNetworkContext );
    int32_t bytesToWrite = 0;
    static int writeCount = 0;
    const uint8_t * buffer;
    size_t length;

    /* The header. */
    if( writeCount == 0 )
    {
        TEST_ASSERT_EQUAL( 5, vectorsToBeSent );

        buffer = pIoVectorIterator->iov_base;
        length = pIoVectorIterator->iov_len;

        TEST_ASSERT_EQUAL( length, UnsubscribeHeaderLength );
        TEST_ASSERT_EQUAL_UINT8_ARRAY( ( uint8_t * ) UnsubscribeHeader, buffer, UnsubscribeHeaderLength );

        bytesToWrite += length;
        pIoVectorIterator++;

        /* First topic filter. */
        verifyEncodedTopicStringUnsubscribe( pIoVectorIterator,
                                             MQTT_SAMPLE_TOPIC_FILTER,
                                             MQTT_SAMPLE_TOPIC_FILTER_LENGTH,
                                             &bytesToWrite );

        pIoVectorIterator += 2;

        /* Second topic filter. */
        verifyEncodedTopicStringUnsubscribe( pIoVectorIterator,
                                             MQTT_SAMPLE_TOPIC_FILTER1,
                                             MQTT_SAMPLE_TOPIC_FILTER_LENGTH1,
                                             &bytesToWrite );

        writeCount++;
    }
    else if( writeCount == 1 )
    {
        TEST_ASSERT_EQUAL( 4, vectorsToBeSent );

        /* Third topic filter. */
        verifyEncodedTopicStringUnsubscribe( pIoVectorIterator,
                                             MQTT_SAMPLE_TOPIC_FILTER2,
                                             MQTT_SAMPLE_TOPIC_FILTER_LENGTH2,
                                             &bytesToWrite );

        pIoVectorIterator += 2;

        /* Fourth topic filter. */
        verifyEncodedTopicStringUnsubscribe( pIoVectorIterator,
                                             MQTT_SAMPLE_TOPIC_FILTER3,
                                             MQTT_SAMPLE_TOPIC_FILTER_LENGTH3,
                                             &bytesToWrite );

        writeCount++;
    }
    else
    {
        bytesToWrite = -1;
    }

    return bytesToWrite;
}

/**
 * @brief Mocked failed transport writev.
 *
 * @param[in] tcpSocket TCP socket.
 * @param[in] pMessage vectors to send
 * @param[in] bytesToWrite number of vectors
 *
 * @return Number of bytes sent; negative value on error;
 * 0 for timeout or 0 bytes sent.
 */
static int32_t transportWritevFail( NetworkContext_t * pNetworkContext,
                                    TransportOutVector_t * pIoVectorIterator,
                                    size_t vectorsToBeSent )
{
    TEST_ASSERT_EQUAL( MQTT_SAMPLE_NETWORK_CONTEXT, pNetworkContext );
    int32_t bytesToWrite = 0;
    size_t i;

    for( i = 0; i < vectorsToBeSent; ++i )
    {
        bytesToWrite += pIoVectorIterator->iov_len;
        pIoVectorIterator++;
    }

    return bytesToWrite + 3;
}

static int32_t transportWritevError( NetworkContext_t * pNetworkContext,
                                     TransportOutVector_t * pIoVectorIterator,
                                     size_t vectorsToBeSent )
{
    ( void ) vectorsToBeSent;
    ( void ) pIoVectorIterator;

    TEST_ASSERT_EQUAL( MQTT_SAMPLE_NETWORK_CONTEXT, pNetworkContext );

    return -1;
}

/**
 * @brief Mocked successful transport send.
 *
 * @param[in] tcpSocket TCP socket.
 * @param[in] pMessage Data to send.
 * @param[in] bytesToWrite Length of data to send.
 *
 * @return Number of bytes sent; negative value on error;
 * 0 for timeout or 0 bytes sent.
 */
static int32_t transportSendSuccess( NetworkContext_t * pNetworkContext,
                                     const void * pBuffer,
                                     size_t bytesToWrite )
{
    TEST_ASSERT_EQUAL( MQTT_SAMPLE_NETWORK_CONTEXT, pNetworkContext );
    ( void ) pBuffer;
    return bytesToWrite;
}

/**
 * @brief Mocked failed transport send.
 */
static int32_t transportSendFailure( NetworkContext_t * pNetworkContext,
                                     const void * pBuffer,
                                     size_t bytesToWrite )
{
    ( void ) pNetworkContext;
    ( void ) pBuffer;
    ( void ) bytesToWrite;
    return -1;
}

/**
 * @brief Mocked transport send that always returns 0 bytes sent.
 */
static int32_t transportSendNoBytes( NetworkContext_t * pNetworkContext,
                                     const void * pBuffer,
                                     size_t bytesToWrite )
{
    ( void ) pNetworkContext;
    ( void ) pBuffer;
    ( void ) bytesToWrite;
    return 0;
}

/**
 * @brief Mocked transport send that succeeds then fails.
 */
static int32_t transportSendSucceedThenFail( NetworkContext_t * pNetworkContext,
                                             const void * pMessage,
                                             size_t bytesToSend )
{
    int32_t retVal = bytesToSend;
    static int counter = 0;

    ( void ) pNetworkContext;
    ( void ) pMessage;

    if( counter++ )
    {
        retVal = -1;
        counter = 0;
    }

    return retVal;
}

/**
 * @brief Mocked transport send that only sends half of the bytes.
 */
static int32_t transportWritevPartialByte( NetworkContext_t * pNetworkContext,
                                           TransportOutVector_t * pIoVectorIterator,
                                           size_t vectorsToBeSent )
{
    int32_t bytesToWrite = 0;
    size_t i;

    ( void ) pNetworkContext;

    for( i = 0; i < vectorsToBeSent; ++i )
    {
        bytesToWrite += pIoVectorIterator->iov_len;
        pIoVectorIterator++;
    }

    if( bytesToWrite > 1 )
    {
        bytesToWrite /= 2;
    }

    return bytesToWrite;
}

/**
 * @brief Mocked successful transport read.
 *
 * @param[in] tcpSocket TCP socket.
 * @param[out] pBuffer Buffer for receiving data.
 * @param[in] bytesToRead Size of pBuffer.
 *
 * @return Number of bytes received; negative value on error.
 */
static int32_t transportRecvSuccess( NetworkContext_t * pNetworkContext,
                                     void * pBuffer,
                                     size_t bytesToRead )
{
    TEST_ASSERT_EQUAL( MQTT_SAMPLE_NETWORK_CONTEXT, pNetworkContext );
    ( void ) pBuffer;
    return bytesToRead;
}

static int32_t transportRecvOneSuccessOneFail( NetworkContext_t * pNetworkContext,
                                               void * pBuffer,
                                               size_t bytesToRead )
{
    TEST_ASSERT_EQUAL( MQTT_SAMPLE_NETWORK_CONTEXT, pNetworkContext );
    ( void ) pBuffer;

    if( receiveOnce == false )
    {
        receiveOnce = true;
        return bytesToRead;
    }
    else
    {
        return -1;
    }
}

/**
 * @brief Mocked failed transport read.
 */
static int32_t transportRecvFailure( NetworkContext_t * pNetworkContext,
                                     void * pBuffer,
                                     size_t bytesToRead )
{
    ( void ) pNetworkContext;
    ( void ) pBuffer;
    ( void ) bytesToRead;
    return -1;
}

/**
 * @brief Mocked transport reading one byte at a time.
 */
static int32_t transportRecvOneByte( NetworkContext_t * pNetworkContext,
                                     void * pBuffer,
                                     size_t bytesToRead )
{
    ( void ) pNetworkContext;
    ( void ) pBuffer;
    ( void ) bytesToRead;
    return 1;
}

/**
 * @brief Mocked transport returning zero bytes to simulate reception
 * of no data over network.
 */
static int32_t transportRecvNoData( NetworkContext_t * pNetworkContext,
                                    void * pBuffer,
                                    size_t bytesToRead )
{
    ( void ) pNetworkContext;
    ( void ) pBuffer;
    ( void ) bytesToRead;
    return 0;
}

/**
 * @brief Initialize the transport interface with the mocked functions for
 * send and receive.
 *
 * @brief param[in] pTransport The transport interface to use with the context.
 */
static void setupTransportInterface( TransportInterface_t * pTransport )
{
    pTransport->pNetworkContext = MQTT_SAMPLE_NETWORK_CONTEXT;
    pTransport->send = transportSendSuccess;
    pTransport->recv = transportRecvSuccess;
    pTransport->writev = transportWritevSuccess;
}

/**
 * @brief Initialize pSubscribeInfo using test-defined macros.
 *
 * @param[in] pSubscribeInfo Pointer to MQTT subscription info.
 */
static void setupSubscriptionInfo( MQTTSubscribeInfo_t * pSubscribeInfo )
{
    pSubscribeInfo->qos = MQTTQoS1;
    pSubscribeInfo->pTopicFilter = MQTT_SAMPLE_TOPIC_FILTER;
    pSubscribeInfo->topicFilterLength = MQTT_SAMPLE_TOPIC_FILTER_LENGTH;
}

/**
 * @brief Zero out a #ProcessLoopReturns_t.
 *
 * @param[in] pExpectParams Pointer to struct to reset.
 */
static void resetProcessLoopParams( ProcessLoopReturns_t * pExpectParams )
{
    pExpectParams->deserializeStatus = MQTTSuccess;
    pExpectParams->stateAfterDeserialize = MQTTStateNull;
    pExpectParams->updateStateStatus = MQTTSuccess;
    pExpectParams->serializeStatus = MQTTSuccess;
    pExpectParams->stateAfterSerialize = MQTTStateNull;
    pExpectParams->processLoopStatus = MQTTSuccess;
    pExpectParams->incomingPublish = false;
    pExpectParams->pPubInfo = NULL;
    pExpectParams->timeoutMs = MQTT_NO_TIMEOUT_MS;
}

/**
 * @brief create default context
 *
 * @param[out] context to initialize
 */
static void setUPContext( MQTTContext_t * mqttContext )
{
    MQTTStatus_t mqttStatus;
    static TransportInterface_t transport = { 0 };
    static MQTTFixedBuffer_t networkBuffer = { 0 };
    static MQTTPubAckInfo_t incomingRecords[ 10 ] = { 0 };
    static MQTTPubAckInfo_t outgoingRecords[ 10 ] = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( mqttContext, 0x0, sizeof( MQTTContext_t ) );

    mqttStatus = MQTT_Init( mqttContext,
                            &transport,
                            getTime,
                            eventCallback,
                            &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( mqttContext,
                                       outgoingRecords,
                                       10,
                                       incomingRecords,
                                       10 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This helper function is used to expect any calls from the process loop
 * to mocked functions belonging to an external header file. Its parameters
 * are used to provide return values for these mocked functions.
 */
static void expectProcessLoopCalls( MQTTContext_t * const pContext,
                                    ProcessLoopReturns_t * pExpectParams )
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    MQTTPacketInfo_t incomingPacket = { 0 };
    size_t pingreqSize = MQTT_PACKET_PINGREQ_SIZE;
    bool expectMoreCalls = true;
    /* Copy values passed in the parameter struct. */
    MQTTStatus_t deserializeStatus = pExpectParams->deserializeStatus;
    MQTTPublishState_t stateAfterDeserialize = pExpectParams->stateAfterDeserialize;
    MQTTStatus_t updateStateStatus = pExpectParams->updateStateStatus;
    MQTTStatus_t serializeStatus = pExpectParams->serializeStatus;
    MQTTPublishState_t stateAfterSerialize = pExpectParams->stateAfterSerialize;
    MQTTStatus_t processLoopStatus = pExpectParams->processLoopStatus;
    bool incomingPublish = pExpectParams->incomingPublish;
    MQTTPublishInfo_t * pPubInfo = pExpectParams->pPubInfo;
    uint32_t packetTxTimeoutMs = 0U;

    /* Modify incoming packet depending on type to be tested. */
    incomingPacket.type = currentPacketType;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );

    /* More calls are expected only with the following packet types. */
    if( ( currentPacketType != MQTT_PACKET_TYPE_PUBLISH ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_PUBACK ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_PUBREC ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_PUBREL ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_PUBCOMP ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_PINGRESP ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_SUBACK ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_UNSUBACK ) )
    {
        expectMoreCalls = false;
    }

    /* When no data is available, the process loop tries to send a PINGREQ. */
    if( modifyIncomingPacketStatus == MQTTNoDataAvailable )
    {
        packetTxTimeoutMs = 1000U * ( uint32_t ) pContext->keepAliveIntervalSec;

        if( PACKET_TX_TIMEOUT_MS < packetTxTimeoutMs )
        {
            packetTxTimeoutMs = PACKET_TX_TIMEOUT_MS;
        }

        if( pContext->waitingForPingResp == false )
        {
            if( ( ( packetTxTimeoutMs != 0U ) &&
                  ( ( globalEntryTime - pContext->lastPacketTxTime ) >= packetTxTimeoutMs ) ) ||
                ( ( PACKET_RX_TIMEOUT_MS != 0U ) &&
                  ( ( globalEntryTime - pContext->lastPacketRxTime ) >= PACKET_RX_TIMEOUT_MS ) ) )
            {
                MQTT_GetPingreqPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
                /* Replace pointer parameter being passed to the method. */
                MQTT_GetPingreqPacketSize_ReturnThruPtr_pPacketSize( &pingreqSize );
                MQTT_SerializePingreq_ExpectAnyArgsAndReturn( serializeStatus );
            }
        }

        expectMoreCalls = false;
    }

    /* Deserialize based on the packet type (PUB or ACK) being received. */
    if( expectMoreCalls )
    {
        if( incomingPublish )
        {
            MQTT_DeserializePublish_ExpectAnyArgsAndReturn( deserializeStatus );

            if( pPubInfo != NULL )
            {
                MQTT_DeserializePublish_ReturnThruPtr_pPublishInfo( pPubInfo );
            }
        }
        else
        {
            MQTT_DeserializeAck_ExpectAnyArgsAndReturn( deserializeStatus );
        }

        if( ( deserializeStatus != MQTTSuccess ) ||
            ( currentPacketType == MQTT_PACKET_TYPE_PINGRESP ) ||
            ( currentPacketType == MQTT_PACKET_TYPE_SUBACK ) ||
            ( currentPacketType == MQTT_PACKET_TYPE_UNSUBACK ) )
        {
            expectMoreCalls = false;
        }
    }

    /* Update state based on the packet type (PUB or ACK) being received. */
    if( expectMoreCalls )
    {
        if( incomingPublish )
        {
            MQTT_UpdateStatePublish_ExpectAnyArgsAndReturn( updateStateStatus );
            MQTT_UpdateStatePublish_ReturnThruPtr_pNewState( &stateAfterDeserialize );
        }
        else
        {
            MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( updateStateStatus );
            MQTT_UpdateStateAck_ReturnThruPtr_pNewState( &stateAfterDeserialize );
        }

        if( stateAfterDeserialize == MQTTPublishDone )
        {
            expectMoreCalls = false;
        }
        else
        {
            switch( updateStateStatus )
            {
                case MQTTSuccess:
                    expectMoreCalls = true;
                    break;

                case MQTTStateCollision:
                    /* Execution will continue regardless of the dup flag. */
                    expectMoreCalls = true;
                    MQTT_CalculateStatePublish_ExpectAnyArgsAndReturn( stateAfterDeserialize );
                    break;

                default:
                    expectMoreCalls = false;
            }
        }
    }

    /* Serialize the packet to be sent in response to the received packet. */
    if( expectMoreCalls )
    {
        MQTT_SerializeAck_ExpectAnyArgsAndReturn( serializeStatus );

        if( serializeStatus != MQTTSuccess )
        {
            expectMoreCalls = false;
        }
    }

    /* Update the state based on the sent packet. */
    if( expectMoreCalls )
    {
        MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( ( stateAfterSerialize == MQTTStateNull ) ?
                                                    MQTTIllegalState : MQTTSuccess );
        MQTT_UpdateStateAck_ReturnThruPtr_pNewState( &stateAfterSerialize );
    }

    /* Expect the above calls when running MQTT_ProcessLoop. */

    mqttStatus = MQTT_ProcessLoop( pContext );
    TEST_ASSERT_EQUAL( processLoopStatus, mqttStatus );

    /* Any final assertions to end the test. */
    if( mqttStatus == MQTTSuccess )
    {
        if( currentPacketType == MQTT_PACKET_TYPE_PUBLISH )
        {
            TEST_ASSERT_TRUE( pContext->controlPacketSent );
        }

        if( currentPacketType == MQTT_PACKET_TYPE_PINGRESP )
        {
            TEST_ASSERT_FALSE( pContext->waitingForPingResp );
        }
    }
}

/* ========================================================================== */

/**
 * @brief Test that MQTT_Init is able to update the context object correctly.
 */
void test_MQTT_Init_Happy_Path( void )
{
    MQTTStatus_t mqttStatus = { 0 };
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL( MQTTNotConnected, context.connectStatus );
    TEST_ASSERT_EQUAL( MQTT_FIRST_VALID_PACKET_ID, context.nextPacketId );
    TEST_ASSERT_EQUAL_PTR( getTime, context.getTime );
    TEST_ASSERT_EQUAL_PTR( eventCallback, context.appCallback );
    /* These Unity assertions take pointers and compare their contents. */
    TEST_ASSERT_EQUAL_MEMORY( &transport, &context.transportInterface, sizeof( transport ) );
    TEST_ASSERT_EQUAL_MEMORY( &networkBuffer, &context.networkBuffer, sizeof( networkBuffer ) );
}

/**
 * @brief Test that any NULL parameter causes MQTT_Init to return MQTTBadParameter.
 */
void test_MQTT_Init_Invalid_Params( void )
{
    MQTTStatus_t mqttStatus = { 0 };
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    /* Check that MQTTBadParameter is returned if any NULL parameters are passed. */
    mqttStatus = MQTT_Init( NULL, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTT_Init( &context, NULL, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Test if NULL is passed for any of the function pointers. */
    mqttStatus = MQTT_Init( &context, &transport, NULL, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTT_Init( &context, &transport, getTime, NULL, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    transport.recv = NULL;
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    transport.recv = transportRecvSuccess;
    transport.send = NULL;
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/* ========================================================================== */

static uint8_t * MQTT_SerializeConnectFixedHeader_cb( uint8_t * pIndex,
                                                      const MQTTConnectInfo_t * pConnectInfo,
                                                      const MQTTPublishInfo_t * pWillInfo,
                                                      size_t remainingLength,
                                                      int numcallbacks )
{
    ( void ) pConnectInfo;
    ( void ) pWillInfo;
    ( void ) remainingLength;
    ( void ) numcallbacks;

    return pIndex;
}

/**
 * @brief Test MQTT_Connect, except for receiving the CONNACK.
 */
void test_MQTT_Connect_sendConnect_writev_error( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t remainingLength;
    size_t packetSize;

    setupTransportInterface( &transport );
    transport.writev = transportWritevError;
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Test network send failure from timeout in calling transport send. */
    mqttContext.transportInterface.send = transportSendNoBytes; /* Use mock send that always returns zero bytes. */
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreArg_pPacketSize();
    MQTT_GetConnectPacketSize_IgnoreArg_pRemainingLength();
    MQTT_GetConnectPacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );

    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
}

/**
 * @brief Test MQTT_Connect, except for receiving the CONNACK.
 */
void test_MQTT_Connect_sendConnect1( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t remainingLength;
    size_t packetSize;

    setupTransportInterface( &transport );
    transport.writev = transportWritevFail;
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Test network send failure from timeout in calling transport send. */
    mqttContext.transportInterface.send = transportSendNoBytes; /* Use mock send that always returns zero bytes. */
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreArg_pPacketSize();
    MQTT_GetConnectPacketSize_IgnoreArg_pRemainingLength();
    MQTT_GetConnectPacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );

    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
}

/**
 * @brief Test MQTT_Connect, except for receiving the CONNACK.
 */
void test_MQTT_Connect_WillInfoWrong( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t remainingLength;
    size_t packetSize;
    MQTTPublishInfo_t willInfo;

    setupTransportInterface( &transport );
    transport.writev = transportWritevFail;
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &willInfo, 0, sizeof( MQTTPublishInfo_t ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Test network send failure from timeout in calling transport send. */
    mqttContext.transportInterface.send = transportSendNoBytes; /* Use mock send that always returns zero bytes. */
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreArg_pPacketSize();
    MQTT_GetConnectPacketSize_IgnoreArg_pRemainingLength();
    MQTT_GetConnectPacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );

    status = MQTT_Connect( &mqttContext, &connectInfo, &willInfo, timeout, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
}

/**
 * @brief Test MQTT_Connect, except for receiving the CONNACK.
 */
void test_MQTT_Connect_sendConnect2( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t remainingLength;
    size_t packetSize;

    setupTransportInterface( &transport );
    transport.writev = transportWritevFail;
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Transport send failed when sending CONNECT. */

    /* Choose 10 bytes variable header + 1 byte payload for the remaining
     * length of the CONNECT. The packet size needs to be nonzero for this test
     * as that is the amount of bytes used in the call to send the packet. */
    packetSize = 13;
    remainingLength = 11;
    mqttContext.transportInterface.send = transportSendFailure;
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreArg_pPacketSize();
    MQTT_GetConnectPacketSize_IgnoreArg_pRemainingLength();
    MQTT_GetConnectPacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );

    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
}

/**
 * @brief Test MQTT_Connect, except for receiving the CONNACK.
 */
void test_MQTT_Connect_ProperWIllInfo( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t remainingLength;
    size_t packetSize;
    MQTTPublishInfo_t willInfo;

    setupTransportInterface( &transport );
    transport.writev = transportWritevFail;
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &willInfo, 0, sizeof( MQTTPublishInfo_t ) );

    willInfo.pTopicName = "MQTTTopic";
    willInfo.topicNameLength = strlen( willInfo.pTopicName );
    willInfo.pPayload = "MQTTPayload";
    willInfo.payloadLength = strlen( willInfo.pPayload );

    connectInfo.pUserName = "MQTTUser";
    connectInfo.userNameLength = strlen( connectInfo.pUserName );
    connectInfo.pPassword = "NotSafePassword";
    connectInfo.passwordLength = strlen( connectInfo.pPassword );

    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Transport send failed when sending CONNECT. */

    /* Choose 10 bytes variable header + 1 byte payload for the remaining
     * length of the CONNECT. The packet size needs to be nonzero for this test
     * as that is the amount of bytes used in the call to send the packet. */
    packetSize = 13;
    remainingLength = 11;
    mqttContext.transportInterface.send = transportSendFailure;
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreArg_pPacketSize();
    MQTT_GetConnectPacketSize_IgnoreArg_pRemainingLength();
    MQTT_GetConnectPacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );

    status = MQTT_Connect( &mqttContext, &connectInfo, &willInfo, timeout, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
}

/**
 * @brief Test MQTT_Connect, with no payload in will message.
 */
void test_MQTT_Connect_ProperWIllInfoWithNoPayload( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t remainingLength;
    size_t packetSize;
    MQTTPublishInfo_t willInfo;

    setupTransportInterface( &transport );
    transport.writev = transportWritevFail;
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &willInfo, 0, sizeof( MQTTPublishInfo_t ) );

    willInfo.pTopicName = "MQTTTopic";
    willInfo.topicNameLength = strlen( willInfo.pTopicName );

    connectInfo.pUserName = "MQTTUser";
    connectInfo.userNameLength = strlen( connectInfo.pUserName );
    connectInfo.pPassword = "NotSafePassword";
    connectInfo.passwordLength = strlen( connectInfo.pPassword );

    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Transport send failed when sending CONNECT. */

    /* Choose 10 bytes variable header + 1 byte payload for the remaining
     * length of the CONNECT. The packet size needs to be nonzero for this test
     * as that is the amount of bytes used in the call to send the packet. */
    packetSize = 13;
    remainingLength = 11;
    mqttContext.transportInterface.send = transportSendFailure;
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreArg_pPacketSize();
    MQTT_GetConnectPacketSize_IgnoreArg_pRemainingLength();
    MQTT_GetConnectPacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );

    status = MQTT_Connect( &mqttContext, &connectInfo, &willInfo, timeout, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
}

/**
 * @brief Test MQTT_Connect, with payload in will message but the length is
 * zero.
 */
void test_MQTT_Connect_ProperWIllInfoWithPayloadButZeroLength( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t remainingLength;
    size_t packetSize;
    MQTTPublishInfo_t willInfo;

    setupTransportInterface( &transport );
    transport.writev = transportWritevFail;
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &willInfo, 0, sizeof( MQTTPublishInfo_t ) );

    willInfo.pTopicName = "MQTTTopic";
    willInfo.topicNameLength = strlen( willInfo.pTopicName );
    willInfo.pPayload = "Payload";
    willInfo.payloadLength = 0;

    connectInfo.pUserName = "MQTTUser";
    connectInfo.userNameLength = strlen( connectInfo.pUserName );
    connectInfo.pPassword = "NotSafePassword";
    connectInfo.passwordLength = strlen( connectInfo.pPassword );

    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Transport send failed when sending CONNECT. */

    /* Choose 10 bytes variable header + 1 byte payload for the remaining
     * length of the CONNECT. The packet size needs to be nonzero for this test
     * as that is the amount of bytes used in the call to send the packet. */
    packetSize = 13;
    remainingLength = 11;
    mqttContext.transportInterface.send = transportSendFailure;
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreArg_pPacketSize();
    MQTT_GetConnectPacketSize_IgnoreArg_pRemainingLength();
    MQTT_GetConnectPacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );

    status = MQTT_Connect( &mqttContext, &connectInfo, &willInfo, timeout, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
}

/**
 * @brief Test MQTT_Connect, except for receiving the CONNACK.
 */
void test_MQTT_Connect_sendConnect3( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Empty connect info fails. */
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTBadParameter );
    memset( &connectInfo, 0x0, sizeof( connectInfo ) );

    status = MQTT_Connect( &mqttContext,
                           &connectInfo,
                           NULL,
                           timeout,
                           &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
}

/**
 * @brief Test MQTT_Connect, except for receiving the CONNACK.
 */
void test_MQTT_Connect_sendConnect4( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Check parameters */
    status = MQTT_Connect( NULL, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    status = MQTT_Connect( &mqttContext, NULL, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, NULL );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
}

/**
 * @brief Test MQTT_Connect, except for receiving the CONNACK.
 */
void test_MQTT_Connect_sendConnect5( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t remainingLength;
    size_t packetSize;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Send the CONNECT successfully. This provides branch coverage for sendPacket. */
    mqttContext.transportInterface.send = transportSendSuccess;
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );

    /* We know the send was successful if MQTT_GetIncomingPacketTypeAndLength()
     * is called. */
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTRecvFailed );

    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );
}

/**
 * @brief Test MQTT_Connect, except for receiving the CONNACK.
 */
void test_MQTT_Connect_sendConnect6( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    connectInfo.pClientIdentifier = MQTT_CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = sizeof( MQTT_CLIENT_IDENTIFIER ) - 1;

    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( 2 );

    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTNoMemory, status );
}

/**
 * @brief Test CONNACK reception in MQTT_Connect.
 */
void test_MQTT_Connect_receiveConnack( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 0;
    bool sessionPresent, sessionPresentExpected;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.recv = transportRecvFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Everything before receiving the CONNACK should succeed. */
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );

    /* Nothing received from transport interface. Set timeout to 2 for branch coverage. */
    timeout = 2;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTNoDataAvailable );
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTNoDataAvailable );
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTNoDataAvailable, status );

    /* Did not receive a CONNACK. */
    incomingPacket.type = MQTT_PACKET_TYPE_PINGRESP;
    incomingPacket.remainingLength = 0;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadResponse, status );

    /* Transport receive failure when receiving rest of packet. */
    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    incomingPacket.remainingLength = 2;
    timeout = 2;
    mqttContext.transportInterface.recv = transportRecvFailure;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );

    /* Bad response when deserializing CONNACK. */
    mqttContext.transportInterface.recv = transportRecvSuccess;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTBadResponse );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadResponse, status );

    /* Test case when broker sends session present flag in response to a
     * clean session connection request. */
    mqttContext.transportInterface.recv = transportRecvSuccess;
    connectInfo.cleanSession = true;
    sessionPresentExpected = true;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_DeserializeAck_ReturnThruPtr_pSessionPresent( &sessionPresentExpected );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadResponse, status );
}

/**
 * @brief Test CONNACK reception in MQTT_Connect.
 */
void test_MQTT_Connect_receiveConnack_retries( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };

    /* Same set of tests with retries. MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT is 2*/
    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.recv = transportRecvFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Everything before receiving the CONNACK should succeed. */
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );

    /* Test with retries. MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT is 2.
     * Nothing received from transport interface. */
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTNoDataAvailable );
    /* 2 retries. */
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTNoDataAvailable );
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTNoDataAvailable );
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, 0U, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTNoDataAvailable, status );

    /* Did not receive a CONNACK. */
    incomingPacket.type = MQTT_PACKET_TYPE_PINGRESP;
    incomingPacket.remainingLength = 0;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, 0U, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadResponse, status );

    /* Transport receive failure when receiving rest of packet. */
    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    incomingPacket.remainingLength = 2;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, 0U, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );

    /* Bad response when deserializing CONNACK. */
    mqttContext.transportInterface.recv = transportRecvSuccess;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTBadResponse );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, 0U, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadResponse, status );
}

/**
 * @brief Test error cases for MQTT_Connect when a timeout occurs or the packet
 * needs to be discarded in MQTT_Connect.
 */
void test_MQTT_Connect_partial_receive( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 0;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.recv = transportRecvNoData;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Everything before receiving the CONNACK should succeed. */
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );
    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    incomingPacket.remainingLength = 2;

    /* Timeout in receiving entire packet, for branch coverage. This is due to the fact that the mocked
     * receive function always returns 0 bytes read. */
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );

    /* Update to use mock receive function that receives one byte at a time for the
     * rest of the test. */
    mqttContext.transportInterface.recv = transportRecvOneByte;
    timeout = 10;

    /* Not enough space for packet, discard it. */
    mqttContext.networkBuffer.size = 2;
    incomingPacket.remainingLength = 3;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTNoDataAvailable, status );

    /* Discard packet, no timeout provided. This should fail since multiple
     * iterations of the discard loop are required to discard the packet, but only
     * one will run. */
    mqttContext.transportInterface.recv = transportRecvSuccess;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, 0, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );

    /* Timeout while discarding packet. */
    /* (Mocked) read only one byte at a time to ensure timeout will occur. */
    mqttContext.transportInterface.recv = transportRecvOneByte;
    incomingPacket.remainingLength = 20;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );

    /* Receive failure while discarding packet. */
    mqttContext.transportInterface.recv = transportRecvFailure;
    /* Test with dummy get time function to make sure there are no infinite loops. */
    mqttContext.getTime = getTimeDummy;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, MQTT_NO_TIMEOUT_MS, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );
}

/**
 * @brief Test resend of pending acks in MQTT_Connect.
 */
void test_MQTT_Connect_resendPendingAcks( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent, sessionPresentResult;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };
    uint16_t packetIdentifier = 1;
    MQTTPublishState_t pubRelState = MQTTPubRelSend;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &connectInfo, 0x00, sizeof( connectInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );
    connectInfo.keepAliveSeconds = MQTT_SAMPLE_KEEPALIVE_INTERVAL_S;

    /* Test 1. No packets to resend reestablishing a session. */
    /* successful receive CONNACK packet. */
    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    incomingPacket.remainingLength = 2;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    /* Return with a session present flag. */
    sessionPresent = true;
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_DeserializeAck_ReturnThruPtr_pSessionPresent( &sessionPresent );
    /* No packets to resend. */
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( MQTT_PACKET_TYPE_INVALID );
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresentResult );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_INT( MQTTConnected, mqttContext.connectStatus );
    TEST_ASSERT_EQUAL_INT( connectInfo.keepAliveSeconds, mqttContext.keepAliveIntervalSec );
    TEST_ASSERT_TRUE( sessionPresentResult );

    /* Test 2. One packet found in ack pending state, but Sending ack failed. */
    sessionPresentResult = false;
    mqttContext.connectStatus = MQTTNotConnected;
    mqttContext.keepAliveIntervalSec = 0;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_DeserializeAck_ReturnThruPtr_pSessionPresent( &sessionPresent );
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( packetIdentifier );
    MQTT_PubrelToResend_ReturnThruPtr_pState( &pubRelState );
    /* Serialize Ack failure. */
    MQTT_SerializeAck_ExpectAnyArgsAndReturn( MQTTBadParameter );
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( MQTT_PACKET_TYPE_INVALID );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresentResult );
    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
    TEST_ASSERT_EQUAL_INT( MQTTNotConnected, mqttContext.connectStatus );
    TEST_ASSERT_TRUE( sessionPresentResult );

    /* Test 3. One packet found in ack pending state, Sent
     * PUBREL successfully. */
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_DeserializeAck_ReturnThruPtr_pSessionPresent( &sessionPresent );
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( packetIdentifier );
    MQTT_PubrelToResend_ReturnThruPtr_pState( &pubRelState );
    /* Serialize Ack successful. */
    MQTT_SerializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    /* Query for any remaining packets pending to ack. */
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( MQTT_PACKET_ID_INVALID );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_INT( MQTTConnected, mqttContext.connectStatus );
    TEST_ASSERT_EQUAL_INT( connectInfo.keepAliveSeconds, mqttContext.keepAliveIntervalSec );

    /* Test 4. Three packets found in ack pending state. Sent PUBREL successfully
     * for first and failed for second and no attempt for third. */
    mqttContext.keepAliveIntervalSec = 0;
    mqttContext.connectStatus = MQTTNotConnected;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_DeserializeAck_ReturnThruPtr_pSessionPresent( &sessionPresent );
    /* First packet. */
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( packetIdentifier );
    MQTT_PubrelToResend_ReturnThruPtr_pState( &pubRelState );
    /* Serialize Ack successful. */
    MQTT_SerializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    /* Second packet. */
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( packetIdentifier + 1 );
    MQTT_PubrelToResend_ReturnThruPtr_pState( &pubRelState );
    /* Serialize Ack failed. */
    MQTT_SerializeAck_ExpectAnyArgsAndReturn( MQTTBadParameter );
    /* Query for any remaining packets pending to ack. */
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( packetIdentifier + 2 );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
    TEST_ASSERT_EQUAL_INT( MQTTNotConnected, mqttContext.connectStatus );

    /* Test 5. Two packets found in ack pending state. Sent PUBREL successfully
     * for first and failed for second. */
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_DeserializeAck_ReturnThruPtr_pSessionPresent( &sessionPresent );
    /* First packet. */
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( packetIdentifier );
    MQTT_PubrelToResend_ReturnThruPtr_pState( &pubRelState );
    /* Serialize Ack successful. */
    MQTT_SerializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    /* Second packet. */
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( packetIdentifier + 1 );
    MQTT_PubrelToResend_ReturnThruPtr_pState( &pubRelState );
    /* Serialize Ack successful. */
    MQTT_SerializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    /* Query for any remaining packets pending to ack. */
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( MQTT_PACKET_ID_INVALID );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_INT( MQTTConnected, mqttContext.connectStatus );
    TEST_ASSERT_EQUAL_INT( connectInfo.keepAliveSeconds, mqttContext.keepAliveIntervalSec );
}

/**
 * @brief Test success case for MQTT_Connect().
 */

#define MQTT_STATE_ARRAY_MAX_COUNT    1

void test_MQTT_Connect_happy_path1()
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );


    /* CONNACK receive with timeoutMs=0. Retry logic will be used. */
    mqttContext.connectStatus = MQTTNotConnected;
    mqttContext.keepAliveIntervalSec = 0;
    sessionPresent = false;
    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    incomingPacket.remainingLength = 2;
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_IgnoreAndReturn( MQTTSuccess );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, 0U, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_INT( MQTTConnected, mqttContext.connectStatus );
    TEST_ASSERT_EQUAL_INT( connectInfo.keepAliveSeconds, mqttContext.keepAliveIntervalSec );
    TEST_ASSERT_FALSE( mqttContext.waitingForPingResp );
}

/**
 * @brief Test success case for MQTT_Connect().
 */
void test_MQTT_Connect_happy_path2()
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    connectInfo.keepAliveSeconds = MQTT_SAMPLE_KEEPALIVE_INTERVAL_S;
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    /* Success. */
    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    incomingPacket.remainingLength = 2;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_IgnoreAndReturn( MQTTSuccess );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_INT( MQTTConnected, mqttContext.connectStatus );
    TEST_ASSERT_EQUAL_INT( connectInfo.keepAliveSeconds, mqttContext.keepAliveIntervalSec );
}

/**
 * @brief Test success case for MQTT_Connect().
 */
void test_MQTT_Connect_happy_path3()
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    MQTTPublishInfo_t willInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &willInfo, 0x0, sizeof( MQTTPublishInfo_t ) );
    memset( &connectInfo, 0x0, sizeof( MQTTConnectInfo_t ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* With non-NULL Will. */
    mqttContext.connectStatus = MQTTNotConnected;
    mqttContext.keepAliveIntervalSec = 0;

    willInfo.pTopicName = "test";
    willInfo.topicNameLength = 4;
    willInfo.pPayload = "Payload";
    willInfo.payloadLength = 7;
    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );

    status = MQTT_Connect( &mqttContext, &connectInfo, &willInfo, timeout, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_INT( MQTTConnected, mqttContext.connectStatus );
    TEST_ASSERT_EQUAL_INT( connectInfo.keepAliveSeconds, mqttContext.keepAliveIntervalSec );
}

/**
 * @brief Test success case for MQTT_Connect().
 */
void test_MQTT_Connect_happy_path4()
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent;
    bool sessionPresentExpected;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };
    MQTTPubAckInfo_t incomingRecords[ 10 ] = { 0 };
    MQTTPubAckInfo_t outgoingRecords[ 10 ] = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );
    MQTT_InitStatefulQoS( &mqttContext,
                          outgoingRecords, 10,
                          incomingRecords, 10 );

    /* Request to establish a clean session. */
    mqttContext.connectStatus = MQTTNotConnected;
    mqttContext.keepAliveIntervalSec = 0;
    connectInfo.cleanSession = true;
    sessionPresentExpected = false;

    /* Populate some state records to make sure they are cleared since a clean session
     * will be established. */
    mqttContext.outgoingPublishRecords[ 0 ].packetId = 1;
    mqttContext.outgoingPublishRecords[ 0 ].qos = MQTTQoS2;
    mqttContext.outgoingPublishRecords[ 0 ].publishState = MQTTPublishSend;
    mqttContext.incomingPublishRecords[ MQTT_STATE_ARRAY_MAX_COUNT - 1 ].packetId = 1;
    mqttContext.networkBuffer.size = 5000;

    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    incomingPacket.remainingLength = 2;

    /* Set ping response flag to true to ensure it will be cleared. */
    mqttContext.waitingForPingResp = true;
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_DeserializeAck_ReturnThruPtr_pSessionPresent( &sessionPresentExpected );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_INT( MQTTConnected, mqttContext.connectStatus );
    TEST_ASSERT_EQUAL_INT( connectInfo.keepAliveSeconds, mqttContext.keepAliveIntervalSec );
    TEST_ASSERT_FALSE( mqttContext.waitingForPingResp );
    TEST_ASSERT_FALSE( sessionPresent );
    /* Test old records were cleared. */
    TEST_ASSERT_EQUAL_MEMORY( &outgoingRecords,
                              mqttContext.outgoingPublishRecords,
                              sizeof( outgoingRecords ) );
    TEST_ASSERT_EQUAL_MEMORY( &incomingRecords,
                              mqttContext.incomingPublishRecords,
                              sizeof( incomingRecords ) );
}

/**
 * @brief Test success case for MQTT_Connect().
 */
void test_MQTT_Connect_happy_path5()
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    uint32_t timeout = 2;
    bool sessionPresent, sessionPresentExpected;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };


    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Request to establish a session if present and session present is received
     * from broker. */
    mqttContext.connectStatus = MQTTNotConnected;
    mqttContext.keepAliveIntervalSec = 0;
    mqttContext.waitingForPingResp = true;
    connectInfo.cleanSession = false;
    sessionPresentExpected = true;

    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;

    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_DeserializeAck_ReturnThruPtr_pSessionPresent( &sessionPresentExpected );
    MQTT_PubrelToResend_ExpectAnyArgsAndReturn( MQTT_PACKET_TYPE_INVALID );

    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_INT( MQTTConnected, mqttContext.connectStatus );
    TEST_ASSERT_EQUAL_INT( connectInfo.keepAliveSeconds, mqttContext.keepAliveIntervalSec );
    TEST_ASSERT_TRUE( sessionPresent );
    TEST_ASSERT_FALSE( mqttContext.waitingForPingResp );
}

/**
 * @brief Test success case for MQTT_Connect().
 */
void test_MQTT_Connect_happy_path6()
{
    MQTTContext_t mqttContext = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };
    bool sessionPresent = false;
    MQTTStatus_t status;
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* CONNACK receive with timeoutMs=0. Retry logic will  be used.
     * #MQTTNoDataAvailable for first #MQTT_GetIncomingPacketTypeAndLength
     * and success in the second time. */
    mqttContext.connectStatus = MQTTNotConnected;
    mqttContext.keepAliveIntervalSec = 0;
    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    incomingPacket.remainingLength = 2;

    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );
    MQTT_SerializeConnectFixedHeader_Stub( MQTT_SerializeConnectFixedHeader_cb );
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTNoDataAvailable );
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_IgnoreAndReturn( MQTTSuccess );

    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, 0U, &sessionPresent );

    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_INT( MQTTConnected, mqttContext.connectStatus );
    TEST_ASSERT_EQUAL_INT( connectInfo.keepAliveSeconds, mqttContext.keepAliveIntervalSec );
    TEST_ASSERT_FALSE( mqttContext.waitingForPingResp );
}

/* ========================================================================== */

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    const uint16_t PACKET_ID = 1;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Verify parameters. */
    status = MQTT_Publish( NULL, &publishInfo, PACKET_ID );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish2( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    const uint16_t PACKET_ID = 1;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    status = MQTT_Publish( &mqttContext, NULL, PACKET_ID );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish3( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    publishInfo.qos = MQTTQoS1;
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish4( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    const uint16_t PACKET_ID = 1;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    publishInfo.payloadLength = 1;
    publishInfo.pPayload = NULL;
    status = MQTT_Publish( &mqttContext, &publishInfo, PACKET_ID );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish5( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Bad Parameter when getting packet size. */
    publishInfo.qos = MQTTQoS0;
    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTBadParameter );
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish6( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Always return success from now on. */
    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTNoMemory );
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTNoMemory, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish_DuplicatePublish( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;
    MQTTPubAckInfo_t outgoingPublishRecord[ 10 ];

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Always return success from now on. */
    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ReserveState_ExpectAnyArgsAndReturn( MQTTStateCollision );
    MQTT_UpdateStatePublish_ExpectAnyArgsAndReturn( MQTTSuccess );

    mqttContext.outgoingPublishRecordMaxCount = 10;
    mqttContext.outgoingPublishRecords = outgoingPublishRecord;

    publishInfo.qos = MQTTQoS1;
    publishInfo.dup = true;
    publishInfo.pPayload = "TestPublish";
    publishInfo.payloadLength = strlen( publishInfo.pPayload );
    publishInfo.pTopicName = "TestTopic";
    publishInfo.topicNameLength = strlen( publishInfo.pTopicName );

    status = MQTT_Publish( &mqttContext, &publishInfo, 10 );

    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish_DuplicatePublish_UpdateFailed( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;
    MQTTPubAckInfo_t outgoingPublishRecord[ 10 ];

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Always return success from now on. */
    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ReserveState_ExpectAnyArgsAndReturn( MQTTStateCollision );
    MQTT_UpdateStatePublish_ExpectAnyArgsAndReturn( MQTTSendFailed );

    mqttContext.outgoingPublishRecordMaxCount = 10;
    mqttContext.outgoingPublishRecords = outgoingPublishRecord;

    publishInfo.qos = MQTTQoS1;
    publishInfo.dup = true;
    publishInfo.pPayload = "TestPublish";
    publishInfo.payloadLength = strlen( publishInfo.pPayload );
    publishInfo.pTopicName = "TestTopic";
    publishInfo.topicNameLength = strlen( publishInfo.pTopicName );

    status = MQTT_Publish( &mqttContext, &publishInfo, 10 );

    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish_WriteVSendsPartialBytes( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;
    MQTTPubAckInfo_t outgoingPublishRecord[ 10 ];
    size_t headerLen = 5;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.writev = transportWritevPartialByte;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Always return success from now on. */
    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ReturnThruPtr_headerSize( &headerLen );
    MQTT_ReserveState_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStatePublish_ExpectAnyArgsAndReturn( MQTTSuccess );

    mqttContext.outgoingPublishRecordMaxCount = 10;
    mqttContext.outgoingPublishRecords = outgoingPublishRecord;

    publishInfo.qos = MQTTQoS1;
    publishInfo.dup = false;
    publishInfo.pPayload = "TestPublish";
    publishInfo.payloadLength = strlen( publishInfo.pPayload );
    publishInfo.pTopicName = "TestTopic";
    publishInfo.topicNameLength = strlen( publishInfo.pTopicName );

    status = MQTT_Publish( &mqttContext, &publishInfo, 10 );

    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish7( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.writev = transportWritevFail;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );

    /* We need sendPacket to be called with at least 1 byte to send, so that
     * it can return failure. This argument is the output of serializing the
     * publish header. */
    publishInfo.pPayload = "Test";
    publishInfo.payloadLength = 4;
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish8( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.writev = transportWritevFail;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* We want to test the first call to sendPacket within sendPublish succeeding,
     * and the second one failing. */
    mqttContext.transportInterface.send = transportSendSucceedThenFail;
    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );
    publishInfo.pPayload = "Test";
    publishInfo.payloadLength = 4;
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish9( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );
    mqttContext.transportInterface.send = transportSendSuccess;
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish10( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Test that sending a publish without a payload succeeds. */
    publishInfo.pPayload = NULL;
    publishInfo.payloadLength = 0;
    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish11( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;
    const uint16_t PACKET_ID = 1;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Restore the test payload and length. */
    publishInfo.pPayload = "Test";
    publishInfo.payloadLength = 4;
    /* Now for non zero QoS, which uses state engine. */
    publishInfo.qos = MQTTQoS2;

    status = MQTT_Publish( &mqttContext, &publishInfo, PACKET_ID );

    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish12( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;
    MQTTPublishState_t expectedState = { 0 };

    MQTTPubAckInfo_t incomingRecords = { 0 };
    MQTTPubAckInfo_t outgoingRecords = { 0 };

    const uint16_t PACKET_ID = 1;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    publishInfo.qos = MQTTQoS1;

    MQTT_InitStatefulQoS( &mqttContext,
                          &outgoingRecords, 4,
                          &incomingRecords, 4 );

    mqttContext.outgoingPublishRecords[ 0 ].packetId = 1;
    mqttContext.outgoingPublishRecords[ 0 ].qos = MQTTQoS2;
    mqttContext.outgoingPublishRecords[ 0 ].publishState = MQTTPublishSend;
    mqttContext.outgoingPublishRecords->packetId = 1;

    mqttContext.outgoingPublishRecords->qos = MQTTQoS2;

    expectedState = MQTTPublishSend;

    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ReserveState_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStatePublish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStatePublish_ReturnThruPtr_pNewState( &expectedState );

    status = MQTT_Publish( &mqttContext, &publishInfo, PACKET_ID );

    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish13( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;
    MQTTPubAckInfo_t incomingRecords = { 0 };
    MQTTPubAckInfo_t outgoingRecords = { 0 };

    const uint16_t PACKET_ID = 1;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    MQTT_InitStatefulQoS( &mqttContext,
                          &outgoingRecords, 4,
                          &incomingRecords, 4 );

    publishInfo.qos = MQTTQoS1;

    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );
    /* Duplicate publish. dup flag is not marked by application. */
    MQTT_ReserveState_ExpectAnyArgsAndReturn( MQTTStateCollision );
    status = MQTT_Publish( &mqttContext, &publishInfo, PACKET_ID );
    TEST_ASSERT_EQUAL_INT( MQTTStateCollision, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish14( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    const uint16_t PACKET_ID = 1;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Duplicate publish. dup flag is marked by application. */
    publishInfo.dup = true;

    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );

    status = MQTT_Publish( &mqttContext, &publishInfo, PACKET_ID );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
}

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish15( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;
    const uint16_t PACKET_ID = 1;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.writev = transportWritevSuccess;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Duplicate publish. dup flag is marked by application.
     * State record is not present. */
    publishInfo.dup = true;
    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );

    status = MQTT_Publish( &mqttContext, &publishInfo, PACKET_ID );

    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
}

/**
 * @brief Test that verifies that the MQTT_Publish API detects a timeout
 * and returns failure when the transport send function is unable to send any data
 * over the network.
 */
void test_MQTT_Publish_Send_Timeout( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t status;

    setupNetworkBuffer( &networkBuffer );
    setupTransportInterface( &transport );
    transport.writev = transportWritevFail;

    /* Set the transport send function to the mock that always returns zero
     * bytes for the test. */
    transport.send = transportSendNoBytes;

    /* Initialize the MQTT context. */
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Setup for making sure that the test results in calling sendPacket function
     * where calls to transport send function are made (repeatedly to send packet
     * over the network).*/
    memset( &publishInfo, 0, sizeof( MQTTPublishInfo_t ) );
    publishInfo.pPayload = "Test";
    publishInfo.payloadLength = 4;
    MQTT_GetPublishPacketSize_IgnoreAndReturn( MQTTSuccess );
    MQTT_SerializePublishHeaderWithoutTopic_ExpectAnyArgsAndReturn( MQTTSuccess );

    /* Call the API function under test and expect that it detects a timeout in sending
     * MQTT packet over the network. */
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );
}

/* ========================================================================== */

/**
 * @brief Test that MQTT_Disconnect works as intended.
 */
void test_MQTT_Disconnect1( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTStatus_t status;
    uint8_t buffer[ 10 ];
    uint8_t * bufPtr = buffer;
    NetworkContext_t networkContext = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    networkContext.buffer = &bufPtr;
    transport.pNetworkContext = &networkContext;
    transport.recv = transportRecvSuccess;
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );
    mqttContext.connectStatus = MQTTConnected;

    /* Verify parameters. */
    status = MQTT_Disconnect( NULL );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
}

/**
 * @brief Test that MQTT_Disconnect works as intended.
 */
void test_MQTT_Disconnect2( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTStatus_t status;
    uint8_t buffer[ 10 ];
    uint8_t * bufPtr = buffer;
    NetworkContext_t networkContext = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t disconnectSize = 2;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    networkContext.buffer = &bufPtr;
    transport.pNetworkContext = &networkContext;
    transport.recv = transportRecvSuccess;
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );
    mqttContext.connectStatus = MQTTConnected;

    /* Send failure with network error. */
    MQTT_GetDisconnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetDisconnectPacketSize_ReturnThruPtr_pPacketSize( &disconnectSize );
    MQTT_SerializeDisconnect_ExpectAnyArgsAndReturn( MQTTSuccess );
    status = MQTT_Disconnect( &mqttContext );
    TEST_ASSERT_EQUAL( MQTTSendFailed, status );
}

/**
 * @brief Test that MQTT_Disconnect works as intended.
 */
void test_MQTT_Disconnect3( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTStatus_t status;
    uint8_t buffer[ 10 ];
    uint8_t * bufPtr = buffer;
    NetworkContext_t networkContext = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t disconnectSize = 2;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    networkContext.buffer = &bufPtr;
    transport.pNetworkContext = &networkContext;
    transport.recv = transportRecvSuccess;
    transport.send = transportSendFailure;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );
    mqttContext.connectStatus = MQTTConnected;

    /* Send failure with timeout in calling transport send. */
    transport.send = transportSendNoBytes;
    MQTT_GetDisconnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetDisconnectPacketSize_ReturnThruPtr_pPacketSize( &disconnectSize );
    MQTT_SerializeDisconnect_ExpectAnyArgsAndReturn( MQTTSuccess );
    status = MQTT_Disconnect( &mqttContext );
    TEST_ASSERT_EQUAL( MQTTSendFailed, status );
}

MQTTStatus_t MQTT_SerializeDisconnect_stub( const MQTTFixedBuffer_t * pFixedBuffer,
                                            int numcalls )
{
    ( void ) numcalls;

    pFixedBuffer->pBuffer[ 0 ] = MQTT_PACKET_TYPE_DISCONNECT;
    pFixedBuffer->pBuffer[ 1 ] = 0;

    return MQTTSuccess;
}

/**
 * @brief Test that MQTT_Disconnect works as intended.
 */
void test_MQTT_Disconnect4( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTStatus_t status;
    uint8_t buffer[ 10 ];
    uint8_t * bufPtr = buffer;
    NetworkContext_t networkContext = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t disconnectSize = 2;

    /* Fill the buffer with garbage data. */
    memset( mqttBuffer, 0xAB, MQTT_TEST_BUFFER_LENGTH );

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    networkContext.buffer = &bufPtr;
    transport.pNetworkContext = &networkContext;
    transport.recv = transportRecvSuccess;
    transport.send = transportSendFailure;
    transport.writev = NULL;

    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );
    mqttContext.connectStatus = MQTTConnected;

    /* Successful send. */
    mqttContext.transportInterface.send = mockSend;
    MQTT_GetDisconnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetDisconnectPacketSize_ReturnThruPtr_pPacketSize( &disconnectSize );
    MQTT_SerializeDisconnect_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializeDisconnect_Stub( MQTT_SerializeDisconnect_stub );
    /* Write a disconnect packet into the buffer. */
    mqttBuffer[ 0 ] = MQTT_PACKET_TYPE_DISCONNECT;

    status = MQTT_Disconnect( &mqttContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTNotConnected, mqttContext.connectStatus );
    /* At disconnect, the buffer is cleared of any pending packets. */
    TEST_ASSERT_EACH_EQUAL_UINT8( 0, mqttBuffer, MQTT_TEST_BUFFER_LENGTH );
}
/* ========================================================================== */

/**
 * @brief Test that MQTT_GetPacketId works as intended.
 */
void test_MQTT_GetPacketId( void )
{
    MQTTContext_t mqttContext = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    uint16_t packetId;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    memset( &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, getTime, eventCallback, &networkBuffer );

    /* Verify parameters. */
    packetId = MQTT_GetPacketId( NULL );
    TEST_ASSERT_EQUAL_INT( 0, packetId );

    packetId = MQTT_GetPacketId( &mqttContext );
    TEST_ASSERT_EQUAL_INT( 1, packetId );
    TEST_ASSERT_EQUAL_INT( 2, mqttContext.nextPacketId );

    mqttContext.nextPacketId = UINT16_MAX;
    packetId = MQTT_GetPacketId( &mqttContext );
    TEST_ASSERT_EQUAL_INT( UINT16_MAX, packetId );
    TEST_ASSERT_EQUAL_INT( 1, mqttContext.nextPacketId );
}

/* ========================================================================== */

/**
 * @brief Test that NULL pContext causes MQTT_ProcessLoop to return MQTTBadParameter.
 */
void test_MQTT_ProcessLoop_Invalid_Params( void )
{
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t mqttStatus = MQTT_ProcessLoop( NULL );

    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    setupTransportInterface( &transport );
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Get time function cannot be NULL. */
    context.getTime = NULL;
    mqttStatus = MQTT_ProcessLoop( &context );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
    /* Restore the time function for the next test. */
    context.getTime = getTime;

    /* The fixed network buffer cannot be NULL. */
    context.networkBuffer.pBuffer = NULL;

    mqttStatus = MQTT_ProcessLoop( &context );

    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

void test_MQTT_ProcessLoop_discardPacket( void )
{
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };
    MQTTStatus_t mqttStatus;

    setupNetworkBuffer( &networkBuffer );
    setupTransportInterface( &transport );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    context.networkBuffer.size = 20;

    incomingPacket.type = currentPacketType;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );

    mqttStatus = MQTT_ProcessLoop( &context );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

void test_MQTT_ProcessLoop_IncomingBufferNotInit( void )
{
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t mqttStatus;
    MQTTPacketInfo_t incomingPacket = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );

    /* First byte shows that it is a publish type packet. */
    mqttBuffer[ 0 ] = MQTT_PACKET_TYPE_PUBLISH;
    /* Length of the packet. */
    mqttBuffer[ 1 ] = 20;

    incomingPacket.type = MQTT_PACKET_TYPE_PUBLISH;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );

    /* Assume QoS = 1. */
    publishInfo.qos = MQTTQoS1;

    MQTT_DeserializePublish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_DeserializePublish_ReturnThruPtr_pPublishInfo( &publishInfo );

    mqttStatus = MQTT_ProcessLoop( &context );

    TEST_ASSERT_EQUAL( MQTTRecvFailed, mqttStatus );
}

void test_MQTT_ProcessLoop_IncomingBufferNotInitQoS0( void )
{
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t mqttStatus;
    MQTTPacketInfo_t incomingPacket = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    isEventCallbackInvoked = false;

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );

    /* First byte shows that it is a publish type packet. */
    mqttBuffer[ 0 ] = MQTT_PACKET_TYPE_PUBLISH;
    /* Length of the packet. */
    mqttBuffer[ 1 ] = 20;

    incomingPacket.type = MQTT_PACKET_TYPE_PUBLISH;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );

    /* Assume QoS = 1. */
    publishInfo.qos = MQTTQoS0;

    MQTT_DeserializePublish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_DeserializePublish_ReturnThruPtr_pPublishInfo( &publishInfo );

    MQTT_UpdateStatePublish_ExpectAnyArgsAndReturn( MQTTSuccess );

    mqttStatus = MQTT_ProcessLoop( &context );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL( true, isEventCallbackInvoked );
}

void test_MQTT_ProcessLoop_HandleKeepAlive( void )
{
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t mqttStatus;

    setupTransportInterface( &transport );
    transport.recv = transportRecvNoData;
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );

    /* Set this value such that the library will be forced to send keep alive. */
    context.waitingForPingResp = true;
    /* Update the time so that there is timeout. */
    globalEntryTime = MQTT_PINGRESP_TIMEOUT_MS;
    mqttStatus = MQTT_ProcessLoop( &context );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

void test_MQTT_ProcessLoop_HandleKeepAlive1( void )
{
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t mqttStatus;
    size_t pingreqSize = MQTT_PACKET_PINGREQ_SIZE;

    setupTransportInterface( &transport );
    transport.recv = transportRecvNoData;
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );

    /* Verify MQTTSuccess is returned. */
    MQTT_GetPingreqPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetPingreqPacketSize_ReturnThruPtr_pPacketSize( &pingreqSize );
    MQTT_SerializePingreq_ExpectAnyArgsAndReturn( MQTTSuccess );

    /* Set this value such that the library will be forced to send keep alive. */
    context.waitingForPingResp = false;
    context.keepAliveIntervalSec = 1;
    /* Update the time so that there is timeout. */
    globalEntryTime = MQTT_PINGRESP_TIMEOUT_MS;
    mqttStatus = MQTT_ProcessLoop( &context );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

void test_MQTT_ProcessLoop_HandleKeepAlive2( void )
{
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t mqttStatus;

    setupTransportInterface( &transport );
    transport.recv = transportRecvNoData;
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );

    /* Set this value such that the library will be forced to send keep alive. */
    context.waitingForPingResp = false;
    context.keepAliveIntervalSec = 1;

    /* Update the time so that timeout does not occur and the ping is not sent. */
    globalEntryTime = 0;

    mqttStatus = MQTT_ProcessLoop( &context );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

void test_MQTT_ProcessLoop_RecvFailed( void )
{
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTStatus_t mqttStatus;

    setupTransportInterface( &transport );
    transport.recv = transportRecvFailure;
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );

    mqttStatus = MQTT_ProcessLoop( &context );

    TEST_ASSERT_EQUAL( MQTTRecvFailed, mqttStatus );
}

void test_MQTT_ReceiveLoop_KeepAliveACK( void )
{
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };
    MQTTStatus_t mqttStatus;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    context.networkBuffer.size = MQTT_TEST_BUFFER_LENGTH;

    incomingPacket.type = MQTT_PACKET_TYPE_PINGRESP;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );

    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );

    mqttStatus = MQTT_ReceiveLoop( &context );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

void test_MQTT_ProcessLoop_discardPacket_second_recv_fail( void )
{
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };
    MQTTStatus_t mqttStatus;

    setupTransportInterface( &transport );
    transport.recv = transportRecvOneSuccessOneFail;
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    context.networkBuffer.size = 20;

    incomingPacket.type = currentPacketType;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );

    mqttStatus = MQTT_ProcessLoop( &context );

    TEST_ASSERT_EQUAL( MQTTRecvFailed, mqttStatus );
}

/**
 * @brief This test case covers one call to the private method,
 * handleIncomingPublish(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleIncomingPublish_Happy_Path1( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };
    MQTTPubAckInfo_t pIncomingCallback[ 10 ];

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context, NULL, 0, pIncomingCallback, 10 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Assume QoS = 1 so that a PUBACK will be sent after receiving PUBLISH.
     * That is, expectProcessLoopCalls will take on the following parameters:
     * incomingPublish=true and stateAfterDeserialize=MQTTPubAckSend. */
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    /* Set expected return values during the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTPubAckSend;
    expectParams.stateAfterSerialize = MQTTPublishDone;
    expectParams.incomingPublish = true;
    expectProcessLoopCalls( &context, &expectParams );
}

/**
 * @brief This test case covers one call to the private method,
 * handleIncomingPublish(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleIncomingPublish_Happy_Path2( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };
    MQTTPubAckInfo_t pIncomingPublish[ 10 ];

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context, NULL, 0, pIncomingPublish, 10 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Assume QoS = 2 so that a PUBREC will be sent after receiving PUBLISH.
     * That is, expectProcessLoopCalls will take on the following parameters:
     * incomingPublish=true and stateAfterDeserialize=MQTTPubRecSend. */
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    /* Set expected return values during the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTPubRecSend;
    expectParams.stateAfterSerialize = MQTTPubRelPending;
    expectParams.incomingPublish = true;
    expectProcessLoopCalls( &context, &expectParams );
}

/**
 * @brief This test case covers one call to the private method,
 * handleIncomingPublish(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleIncomingPublish_Happy_Path3( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPublishInfo_t pubInfo = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };
    MQTTPubAckInfo_t incomingRecords = { 0 };
    MQTTPubAckInfo_t outgoingRecords = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context,
                            &transport,
                            getTime,
                            eventCallback,
                            &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    MQTT_InitStatefulQoS( &context,
                          &outgoingRecords, 4,
                          &incomingRecords, 4 );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Duplicate QoS1 publish received.
     * expectProcessLoopCalls will take on the following parameters:
     * incomingPublish=true, stateAfterDeserialize=MQTTPubAckSend,
     * updateStateStatus=MQTTStateCollision and pPubInfo is passed with
     * dup flag set. The event callback should not be invoked. */
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    pubInfo.dup = true;
    pubInfo.qos = MQTTQoS1;
    isEventCallbackInvoked = false;
    /* Set expected return values during the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTPubAckSend;
    expectParams.updateStateStatus = MQTTStateCollision;
    expectParams.stateAfterSerialize = MQTTPublishDone;
    expectParams.deserializeStatus = MQTTSuccess;
    expectParams.incomingPublish = true;
    expectParams.pPubInfo = &pubInfo;
    expectProcessLoopCalls( &context, &expectParams );
    TEST_ASSERT_FALSE( isEventCallbackInvoked );
}

/**
 * @brief This test case covers one call to the private method,
 * handleIncomingPublish(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleIncomingPublish_Happy_Path4( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };
    MQTTPubAckInfo_t pIncomingPublish[ 10 ];

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context, NULL, 0, pIncomingPublish, 10 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Duplicate QoS2 publish received.
     * expectProcessLoopCalls will take on the following parameters:
     * incomingPublish=true, stateAfterDeserialize=MQTTPubRecSend,
     * updateStateStatus=MQTTStateCollision and pPubInfo is passed with
     * dup flag set. The event callback should not be invoked. */
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    isEventCallbackInvoked = false;
    /* Only changes are for QoS 2, no need to reset. */
    expectParams.stateAfterDeserialize = MQTTPubRecSend;
    expectParams.stateAfterSerialize = MQTTPubRelPending;
    expectParams.incomingPublish = true;
    expectParams.updateStateStatus = MQTTStateCollision;
    expectProcessLoopCalls( &context, &expectParams );
    TEST_ASSERT_FALSE( isEventCallbackInvoked );
}

/**
 * @brief This test case covers one call to the private method,
 * handleIncomingPublish(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleIncomingPublish_Happy_Path5( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };
    MQTTPubAckInfo_t pIncomingPublish[ 10 ];

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context, NULL, 0, pIncomingPublish, 10 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* A publish is received when already a state record exists, but dup
     * flag is not set. */
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    isEventCallbackInvoked = false;
    expectParams.incomingPublish = true;
    expectParams.updateStateStatus = MQTTStateCollision;
    expectParams.stateAfterDeserialize = MQTTPubAckSend;
    expectParams.stateAfterSerialize = MQTTPublishDone;
    /* No loop statuses have changed from before. */
    expectProcessLoopCalls( &context, &expectParams );
    TEST_ASSERT_FALSE( isEventCallbackInvoked );
}

/**
 * @brief This test case covers one call to the private method,
 * handleIncomingPublish(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleIncomingPublish_Happy_Path6( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };
    MQTTPubAckInfo_t pIncomingPublish[ 10 ];

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context, NULL, 0, pIncomingPublish, 10 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Duplicate QoS2 publish received with no collision.
     * expectProcessLoopCalls will take on the following parameters:
     * incomingPublish=true, stateAfterDeserialize=MQTTPubRecSend,
     * updateStateStatus=MQTTSuccess and pPubInfo is passed with
     * dup flag set. The event callback should be invoked. */
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    isEventCallbackInvoked = false;
    expectParams.incomingPublish = true;
    /* The only expect parameter to change is the update status. */
    expectParams.updateStateStatus = MQTTSuccess;
    expectParams.stateAfterDeserialize = MQTTPubAckSend;
    expectParams.stateAfterSerialize = MQTTPublishDone;
    expectProcessLoopCalls( &context, &expectParams );
    TEST_ASSERT_TRUE( isEventCallbackInvoked );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleIncomingPublish(...),
 * that result in the process loop returning an error.
 */
void test_MQTT_ProcessLoop_handleIncomingPublish_Error_Paths( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };
    MQTTPubAckInfo_t incomingRecords = { 0 };
    MQTTPubAckInfo_t outgoingRecords = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    MQTT_InitStatefulQoS( &context,
                          &outgoingRecords, 4,
                          &incomingRecords, 4 );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Verify that an error is propagated when deserialization fails by returning
     * MQTTBadResponse. Any parameters beyond that are actually irrelevant
     * because they are only used as return values for non-expected calls. */
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    /* Set expected return values during the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.deserializeStatus = MQTTBadResponse;
    expectParams.updateStateStatus = MQTTIllegalState;
    expectParams.serializeStatus = MQTTBadResponse;
    expectParams.processLoopStatus = MQTTBadResponse;
    expectParams.incomingPublish = true;
    expectProcessLoopCalls( &context, &expectParams );

    /* A publish is received and dup flag is set, but state update failed. */
    publishInfo.dup = true;
    publishInfo.qos = MQTTQoS2;
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    isEventCallbackInvoked = false;
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTPubAckSend;
    expectParams.updateStateStatus = MQTTIllegalState;
    expectParams.processLoopStatus = MQTTIllegalState;
    expectParams.incomingPublish = true;
    expectParams.pPubInfo = &publishInfo;
    /* The other loop parameter fields are irrelevant. */
    expectProcessLoopCalls( &context, &expectParams );
    TEST_ASSERT_FALSE( isEventCallbackInvoked );
}

/**
 * @brief This test checks that the ProcessLoop API function is able to
 * support receiving an entire incoming MQTT packet over the network when
 * the transport recv function only reads less than requested bytes at a
 * time, and the timeout passed to the API is "0ms".
 */
void test_MQTT_ProcessLoop_Zero_Duration_And_Partial_Network_Read( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    setupNetworkBuffer( &networkBuffer );

    transport.send = transportSendSuccess;

    /* Set the transport recv function for the test to the mock function that represents
     * partial read of data from network (i.e. less than requested number of bytes)
     * at a time. */
    transport.recv = transportRecvOneByte;

    /* Initialize the context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Set flag required for configuring behavior of expectProcessLoopCalls()
     * helper function. */
    modifyIncomingPacketStatus = MQTTNoDataAvailable;

    /* Test the ProcessLoop() call with zero duration timeout to verify that it
     * will be able to support reading the packet over network over multiple calls to
     * the transport receive function. */
    expectParams.timeoutMs = MQTT_NO_TIMEOUT_MS;

    /* Test with an incoming PUBLISH packet whose payload is read only one byte
     * per call to the transport recv function. */
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    /* Set expected return values during the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTPubAckSend;
    expectParams.stateAfterSerialize = MQTTPublishDone;
    expectParams.incomingPublish = true;
    expectParams.processLoopStatus = MQTTNeedMoreBytes;
    expectParams.updateStateStatus = MQTTNeedMoreBytes;
    expectProcessLoopCalls( &context, &expectParams );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleIncomingAck(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleIncomingAck_Happy_Paths( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Mock the receiving of a PUBACK packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_PUBACK;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTPublishDone;
    expectParams.stateAfterSerialize = MQTTPublishDone;
    expectProcessLoopCalls( &context, &expectParams );

    /* Mock the receiving of a PUBREC packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_PUBREC;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTPubRelSend;
    expectParams.stateAfterSerialize = MQTTPubCompPending;
    expectProcessLoopCalls( &context, &expectParams );

    /* Mock the receiving of a PUBREL packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_PUBREL;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTPubCompSend;
    expectParams.stateAfterSerialize = MQTTPublishDone;
    expectProcessLoopCalls( &context, &expectParams );

    /* Duplicate PUBREL, but no record exists. */
    currentPacketType = MQTT_PACKET_TYPE_PUBREL;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTStateNull;
    expectParams.updateStateStatus = MQTTBadParameter;
    expectParams.processLoopStatus = MQTTBadParameter;
    expectProcessLoopCalls( &context, &expectParams );

    /* Mock the receiving of a PUBCOMP packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_PUBCOMP;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTPublishDone;
    expectParams.stateAfterSerialize = MQTTPublishDone;
    expectProcessLoopCalls( &context, &expectParams );

    /* Mock the receiving of a PINGRESP packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_PINGRESP;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectProcessLoopCalls( &context, &expectParams );

    /* Mock the receiving of a SUBACK packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_SUBACK;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectProcessLoopCalls( &context, &expectParams );

    /* Verify that process loop is still successful when SUBACK indicates a
     * server refusal. */
    currentPacketType = MQTT_PACKET_TYPE_SUBACK;
    isEventCallbackInvoked = false;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.deserializeStatus = MQTTServerRefused;
    expectProcessLoopCalls( &context, &expectParams );
    TEST_ASSERT_TRUE( isEventCallbackInvoked );

    /* Mock the receiving of an UNSUBACK packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_UNSUBACK;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectProcessLoopCalls( &context, &expectParams );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleIncomingAck(...),
 * that result in the process loop returning an error.
 */
void test_MQTT_ProcessLoop_handleIncomingAck_Error_Paths( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Verify that MQTTBadResponse is propagated when deserialization fails upon
     * receiving an unknown packet type. */
    currentPacketType = MQTT_PACKET_TYPE_INVALID;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.deserializeStatus = MQTTBadResponse;
    expectParams.processLoopStatus = MQTTBadResponse;
    expectProcessLoopCalls( &context, &expectParams );

    /* Verify that MQTTSendFailed is propagated when receiving a PUBREC
     * then failing when serializing a PUBREL to send in response. */
    currentPacketType = MQTT_PACKET_TYPE_PUBREC;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTPubRelSend;
    expectParams.serializeStatus = MQTTNoMemory;
    expectParams.stateAfterSerialize = MQTTStateNull;
    expectParams.processLoopStatus = MQTTSendFailed;
    expectProcessLoopCalls( &context, &expectParams );

    /* Verify that MQTTBadResponse is propagated when deserialization fails upon
     * receiving a PUBACK. */
    currentPacketType = MQTT_PACKET_TYPE_PUBACK;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.deserializeStatus = MQTTBadResponse;
    expectParams.stateAfterDeserialize = MQTTStateNull;
    expectParams.processLoopStatus = MQTTBadResponse;
    /* The other loop parameter fields are irrelevant. */
    expectProcessLoopCalls( &context, &expectParams );

    /* Verify that MQTTBadResponse is propagated when deserialization fails upon
     * receiving a PINGRESP. */
    currentPacketType = MQTT_PACKET_TYPE_PINGRESP;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.deserializeStatus = MQTTBadResponse;
    expectParams.stateAfterDeserialize = MQTTStateNull;
    expectParams.processLoopStatus = MQTTBadResponse;
    /* The other loop parameter fields are irrelevant. */
    expectProcessLoopCalls( &context, &expectParams );

    /* Verify that MQTTBadResponse is propagated when deserialization fails upon
     * receiving a SUBACK. */
    currentPacketType = MQTT_PACKET_TYPE_SUBACK;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.deserializeStatus = MQTTBadResponse;
    expectParams.processLoopStatus = MQTTBadResponse;
    /* The other loop parameter fields are irrelevant. */
    expectProcessLoopCalls( &context, &expectParams );

    /* Verify that MQTTIllegalState is returned if MQTT_UpdateStateAck(...)
     * provides an unknown state such as MQTTStateNull to sendPublishAcks(...). */
    currentPacketType = MQTT_PACKET_TYPE_PUBREC;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.stateAfterDeserialize = MQTTPubRelSend;
    expectParams.stateAfterSerialize = MQTTStateNull;
    expectParams.processLoopStatus = MQTTIllegalState;
    expectProcessLoopCalls( &context, &expectParams );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleKeepAlive(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleKeepAlive_Happy_Paths1( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    resetProcessLoopParams( &expectParams );
    setupNetworkBuffer( &networkBuffer );
    setupTransportInterface( &transport );

    modifyIncomingPacketStatus = MQTTNoDataAvailable;
    globalEntryTime = MQTT_ONE_SECOND_TO_MS;

    /* Coverage for the branch path where keep alive interval is 0. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    context.waitingForPingResp = false;
    context.keepAliveIntervalSec = 0;
    expectParams.incomingPublish = false;
    expectParams.updateStateStatus = MQTTSuccess;
    expectParams.processLoopStatus = MQTTSuccess;
    expectParams.stateAfterDeserialize = MQTTPubRelSend;
    /* Set expected return values in the loop. All success. */
    MQTTPacketInfo_t incomingPacket = { 0 };
    /* Modify incoming packet depending on type to be tested. */
    incomingPacket.type = currentPacketType;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;


    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );

    MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( expectParams.updateStateStatus );
    MQTT_UpdateStateAck_ReturnThruPtr_pNewState( &expectParams.stateAfterDeserialize );

    MQTT_SerializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );

    MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( expectParams.updateStateStatus );
    MQTT_UpdateStateAck_ReturnThruPtr_pNewState( &expectParams.stateAfterDeserialize );

    mqttStatus = MQTT_ProcessLoop( &context );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleKeepAlive(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleKeepAlive_Happy_Paths2( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    setupNetworkBuffer( &networkBuffer );
    setupTransportInterface( &transport );
    resetProcessLoopParams( &expectParams );

    modifyIncomingPacketStatus = MQTTNoDataAvailable;
    globalEntryTime = MQTT_ONE_SECOND_TO_MS;

    /* Coverage for the branch path where keep alive interval is 0. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Coverage for the branch path where keep alive interval is greater than 0,
     * and the interval has not expired. PINGREQ should not be sent. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    context.keepAliveIntervalSec = MQTT_SAMPLE_KEEPALIVE_INTERVAL_S;
    context.lastPacketTxTime = getTime();
    /* Set expected return values in the loop. All success. */

    MQTTPacketInfo_t incomingPacket = { 0 };
    /* Modify incoming packet depending on type to be tested. */
    incomingPacket.type = currentPacketType;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );

    MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( expectParams.updateStateStatus );
    MQTT_UpdateStateAck_ReturnThruPtr_pNewState( &expectParams.stateAfterDeserialize );

    mqttStatus = MQTT_ProcessLoop( &context );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleKeepAlive(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleKeepAlive_Happy_Paths3( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    resetProcessLoopParams( &expectParams );
    setupNetworkBuffer( &networkBuffer );
    setupTransportInterface( &transport );

    modifyIncomingPacketStatus = MQTTNoDataAvailable;
    globalEntryTime = MQTT_ONE_SECOND_TO_MS;

    /* Coverage for the branch path where keep alive interval is 0. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Coverage for the branch path where PINGRESP timeout interval hasn't expired. */
    context.waitingForPingResp = true;
    context.keepAliveIntervalSec = MQTT_SAMPLE_KEEPALIVE_INTERVAL_S;
    context.lastPacketTxTime = MQTT_ONE_SECOND_TO_MS;
    context.pingReqSendTimeMs = MQTT_ONE_SECOND_TO_MS;
    /* Set expected return values in the loop. All success. */


    MQTTPacketInfo_t incomingPacket = { 0 };
    /* Modify incoming packet depending on type to be tested. */
    incomingPacket.type = currentPacketType;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );

    MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( expectParams.updateStateStatus );
    MQTT_UpdateStateAck_ReturnThruPtr_pNewState( &expectParams.stateAfterDeserialize );

    mqttStatus = MQTT_ProcessLoop( &context );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleKeepAlive(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleKeepAlive_Happy_Paths4( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    resetProcessLoopParams( &expectParams );
    setupNetworkBuffer( &networkBuffer );
    setupTransportInterface( &transport );

    modifyIncomingPacketStatus = MQTTNoDataAvailable;
    globalEntryTime = MQTT_ONE_SECOND_TO_MS;

    /* Coverage for the branch path where keep alive interval is 0. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    context.waitingForPingResp = false;
    context.keepAliveIntervalSec = MQTT_SAMPLE_KEEPALIVE_INTERVAL_S;
    context.lastPacketTxTime = 0;
    /* Set expected return values in the loop. All success. */

    MQTTPacketInfo_t incomingPacket = { 0 };
    /* Modify incoming packet depending on type to be tested. */
    incomingPacket.type = currentPacketType;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );

    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );


    MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( expectParams.updateStateStatus );
    MQTT_UpdateStateAck_ReturnThruPtr_pNewState( &expectParams.stateAfterDeserialize );

    mqttStatus = MQTT_ProcessLoop( &context );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleKeepAlive(...),
 * that result in the process loop returning an error.
 */
void test_MQTT_ProcessLoop_handleKeepAlive_Error_Paths1( void )
{
    MQTTStatus_t mqttStatus = { 0 };
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    setupNetworkBuffer( &networkBuffer );
    setupTransportInterface( &transport );
    transport.writev = transportWritevSuccess;
    transport.recv = transportRecvNoData;

    globalEntryTime = MQTT_PINGRESP_TIMEOUT_MS + 1;

    /* Coverage for the branch path where PINGRESP timeout interval has expired. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    context.keepAliveIntervalSec = MQTT_SAMPLE_KEEPALIVE_INTERVAL_S;
    context.lastPacketTxTime = 0;
    context.lastPacketRxTime = 0;
    context.pingReqSendTimeMs = 0;
    context.waitingForPingResp = true;

    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );
    expectParams.processLoopStatus = MQTTKeepAliveTimeout;

    mqttStatus = MQTT_ProcessLoop( &context );
    TEST_ASSERT_EQUAL( MQTTKeepAliveTimeout, mqttStatus );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleKeepAlive(...),
 * that result in the process loop returning an error.
 */
void test_MQTT_ProcessLoop_handleKeepAlive_Error_Paths2( void )
{
    MQTTStatus_t mqttStatus = { 0 };
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    modifyIncomingPacketStatus = MQTTNoDataAvailable;
    globalEntryTime = MQTT_PINGRESP_TIMEOUT_MS + 1;

    /* Coverage for the branch path where PINGRESP timeout interval has expired. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    context.keepAliveIntervalSec = PACKET_TX_TIMEOUT_MS + 1;
    context.lastPacketTxTime = 0;
    context.lastPacketRxTime = 0;
    context.pingReqSendTimeMs = 0;
    context.waitingForPingResp = false;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );

    expectParams.processLoopStatus = MQTTKeepAliveTimeout;

    MQTTPacketInfo_t incomingPacket = { 0 };
    /* Modify incoming packet depending on type to be tested. */
    currentPacketType = MQTT_PACKET_TYPE_PINGRESP;
    incomingPacket.type = currentPacketType;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTNoDataAvailable );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );

    mqttStatus = MQTT_ProcessLoop( &context );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleKeepAlive(...),
 * that result in the process loop returning an error.
 */
void test_MQTT_ProcessLoop_handleKeepAlive_Error_Paths3( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    transport.recv = transportRecvNoData;

    modifyIncomingPacketStatus = MQTTNoDataAvailable;
    globalEntryTime = MQTT_PINGRESP_TIMEOUT_MS + 1;

    /* Coverage for the branch path where PINGRESP timeout interval has expired. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    globalEntryTime = PACKET_RX_TIMEOUT_MS + 1;
    context.keepAliveIntervalSec = 0;
    context.lastPacketTxTime = 0;
    context.lastPacketRxTime = 0;
    context.pingReqSendTimeMs = 0;
    context.waitingForPingResp = false;
    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );

    MQTT_GetPingreqPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePingreq_ExpectAnyArgsAndReturn( MQTTSuccess );

    mqttStatus = MQTT_ProcessLoop( &context );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleKeepAlive(...),
 * that result in the process loop returning an error.
 */
void test_MQTT_ProcessLoop_handleKeepAlive_Error_Paths4( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    setupTransportInterface( &transport );
    transport.recv = transportRecvNoData;

    setupNetworkBuffer( &networkBuffer );

    modifyIncomingPacketStatus = MQTTNoDataAvailable;
    globalEntryTime = MQTT_PINGRESP_TIMEOUT_MS + 1;

    /* Coverage for the branch path where PINGRESP timeout interval has expired. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    globalEntryTime = PACKET_RX_TIMEOUT_MS + 1;
    context.keepAliveIntervalSec = ( PACKET_TX_TIMEOUT_MS / 1000 ) + 1U;
    context.lastPacketTxTime = 0;
    context.lastPacketRxTime = 0;
    context.pingReqSendTimeMs = 0;
    context.waitingForPingResp = false;

    /* Set the index to non-zero value to show that there is some data in the buffer
     * to be processed. */
    context.index = 12;

    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );

    MQTTPacketInfo_t incomingPacket = { 0 };
    /* Modify incoming packet depending on type to be tested. */
    currentPacketType = MQTT_PACKET_TYPE_PINGRESP;
    incomingPacket.type = currentPacketType;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTNeedMoreBytes );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );

    MQTT_GetPingreqPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializePingreq_ExpectAnyArgsAndReturn( MQTTSuccess );

    mqttStatus = MQTT_ProcessLoop( &context );
    TEST_ASSERT_EQUAL( MQTTNeedMoreBytes, mqttStatus );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleKeepAlive(...),
 * that result in the process loop returning an error.
 */
void test_MQTT_ProcessLoop_handleKeepAlive_Error_Paths5( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    ProcessLoopReturns_t expectParams = { 0 };

    setupTransportInterface( &transport );
    transport.recv = transportRecvNoData;

    setupNetworkBuffer( &networkBuffer );

    modifyIncomingPacketStatus = MQTTNoDataAvailable;
    globalEntryTime = MQTT_PINGRESP_TIMEOUT_MS + 1;

    /* Coverage for the branch path where PINGRESP timeout interval has expired. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    globalEntryTime = PACKET_RX_TIMEOUT_MS - 1U;
    context.keepAliveIntervalSec = ( PACKET_TX_TIMEOUT_MS / 1000 ) + 1U;
    context.lastPacketTxTime = 0;
    context.lastPacketRxTime = 0;
    context.pingReqSendTimeMs = 0;
    context.waitingForPingResp = false;

    /* Set the index to non-zero value to show that there is some data in the buffer
     * to be processed. */
    context.index = 12;

    /* Set expected return values in the loop. */
    resetProcessLoopParams( &expectParams );

    MQTTPacketInfo_t incomingPacket = { 0 };
    /* Modify incoming packet depending on type to be tested. */
    currentPacketType = MQTT_PACKET_TYPE_PINGRESP;
    incomingPacket.type = currentPacketType;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    incomingPacket.headerLength = MQTT_SAMPLE_REMAINING_LENGTH;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTNeedMoreBytes );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );

    mqttStatus = MQTT_ProcessLoop( &context );
    TEST_ASSERT_EQUAL( MQTTNeedMoreBytes, mqttStatus );
}

/**
 * @brief This test mocks a failing transport receive and runs multiple
 * iterations of the process loop, resulting in returning MQTTRecvFailed.
 */
void test_MQTT_ProcessLoop_Receive_Failed( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };

    setupNetworkBuffer( &networkBuffer );
    setupTransportInterface( &transport );
    transport.writev = transportWritevFail;

    mqttStatus = MQTT_Init( &context, &transport,
                            getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    incomingPacket.type = MQTT_PACKET_TYPE_PUBCOMP;

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTRecvFailed );

    mqttStatus = MQTT_ProcessLoop( &context );

    TEST_ASSERT_EQUAL( MQTTRecvFailed, mqttStatus );
}

/**
 * @brief Set the initial entry time close to the maximum value, causing
 * an overflow. This test then checks that the process loop still runs for the
 * expected number of iterations in spite of this.
 */
void test_MQTT_ProcessLoop_Timer_Overflow( void )
{
    MQTTStatus_t mqttStatus = { 0 };
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTPacketInfo_t incomingPacket = { 0 };
    MQTTPublishState_t publishState = MQTTPubAckSend;
    MQTTPublishState_t ackState = MQTTPublishDone;
    MQTTPubAckInfo_t incomingPublishRecords[ 10 ];

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    networkBuffer.size = 1000;
    incomingPacket.type = MQTT_PACKET_TYPE_PUBLISH;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;

    globalEntryTime = UINT32_MAX - MQTT_OVERFLOW_OFFSET;

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context, NULL, 0, incomingPublishRecords, 10 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_ProcessIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    /* Assume QoS = 1 so that a PUBACK will be sent after receiving PUBLISH. */
    MQTT_DeserializePublish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStatePublish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStatePublish_ReturnThruPtr_pNewState( &publishState );
    MQTT_SerializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStateAck_ReturnThruPtr_pNewState( &ackState );

    mqttStatus = MQTT_ProcessLoop( &context );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/* ========================================================================== */

/**
 * @brief Test that MQTT_ReceiveLoop() works as intended. Since the only difference
 * between this and the process loop is keep alive, we only need to test the
 * differences for coverage.
 */
void test_MQTT_ReceiveLoop( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Verify that a NULL Context returns an error. */
    mqttStatus = MQTT_ReceiveLoop( NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Verify that a NULL time function returns an error. */
    context.getTime = NULL;
    mqttStatus = MQTT_ReceiveLoop( &context );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
    context.getTime = getTime;

    /* Verify that a null fixed network buffer returns an error. */
    context.networkBuffer.pBuffer = NULL;
    mqttStatus = MQTT_ReceiveLoop( &context );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
    setupNetworkBuffer( &( context.networkBuffer ) );

    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTBadResponse );
    /* Error case, for branch coverage. */
    mqttStatus = MQTT_ReceiveLoop( &context );
    TEST_ASSERT_EQUAL( MQTTBadResponse, mqttStatus );

    /* This will cover the case when there is data available in the buffer to be processed but
     * no additional bytes have been received by the transport interface. */
    context.transportInterface.recv = transportRecvNoData;
    MQTT_ProcessIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTBadResponse );
    /* Error case, for branch coverage. */
    mqttStatus = MQTT_ReceiveLoop( &context );
    TEST_ASSERT_EQUAL( MQTTBadResponse, mqttStatus );

    /* Reset the index to clear the buffer of any remaining data. */
    context.index = 0;
    /* Keep Alive should not trigger.*/
    context.keepAliveIntervalSec = 1;
    mqttStatus = MQTT_ReceiveLoop( &context );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_FALSE( context.controlPacketSent );

    /* Test with a dummy getTime to ensure there's no infinite loops. */
    context.getTime = getTimeDummy;
    mqttStatus = MQTT_ReceiveLoop( &context );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    context.getTime = getTime;

    /* Receive a PINGRESP. */
    mqttStatus = MQTT_ReceiveLoop( &context );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/* ========================================================================== */

/**
 * @brief This test case verifies that MQTT_Subscribe returns MQTTBadParameter
 * with an invalid parameter. This test case also gives us coverage over
 * the private method, validateSubscribeUnsubscribeParams(...).
 */
void test_MQTT_Subscribe_invalid_params( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };

    /* Call subscribe with a NULL context. */
    mqttStatus = MQTT_Subscribe( NULL, &subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Call subscribe with a NULL subscription list. */
    mqttStatus = MQTT_Subscribe( &context, NULL, 1, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Call subscribe with 0 subscriptions. */
    mqttStatus = MQTT_Subscribe( &context, &subscribeInfo, 0, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Packet ID cannot be 0 per MQTT 3.1.1 spec. */
    mqttStatus = MQTT_Subscribe( &context, &subscribeInfo, 1, 0 );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Incoming publish records NULL but QoS > 0. */
    subscribeInfo.qos = MQTTQoS1;
    mqttStatus = MQTT_Subscribe( &context, &subscribeInfo, 1, 10 );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

static uint8_t * MQTT_SerializeSubscribedHeader_cb( size_t remainingLength,
                                                    uint8_t * pIndex,
                                                    uint16_t packetId,
                                                    int numcallbacks )
{
    ( void ) remainingLength;
    ( void ) pIndex;
    ( void ) packetId;
    ( void ) numcallbacks;

    return pIndex;
}

static uint8_t * MQTT_SerializeSubscribedHeader_cb1( size_t remainingLength,
                                                     uint8_t * pIndex,
                                                     uint16_t packetId,
                                                     int numcallbacks )
{
    ( void ) remainingLength;
    ( void ) pIndex;
    ( void ) packetId;
    ( void ) numcallbacks;

    return pIndex + 5;
}

static uint8_t * MQTT_SerializeSubscribedHeader_cb2( size_t remainingLength,
                                                     uint8_t * pIndex,
                                                     uint16_t packetId,
                                                     int numcallbacks )
{
    ( void ) remainingLength;
    ( void ) pIndex;
    ( void ) packetId;
    ( void ) numcallbacks;

    memcpy( pIndex, SubscribeHeader, SubscribeHeaderLength );

    return pIndex + SubscribeHeaderLength;
}

static uint8_t * MQTT_SerializeUnsubscribedHeader_cb2( size_t remainingLength,
                                                       uint8_t * pIndex,
                                                       uint16_t packetId,
                                                       int numcallbacks )
{
    ( void ) remainingLength;
    ( void ) pIndex;
    ( void ) packetId;
    ( void ) numcallbacks;

    memcpy( pIndex, UnsubscribeHeader, UnsubscribeHeaderLength );

    return pIndex + UnsubscribeHeaderLength;
}

/**
 * @brief This test case verifies that MQTT_Subscribe returns successfully
 * when valid parameters are passed and all bytes are sent.
 */
void test_MQTT_Subscribe_happy_path( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;
    MQTTPubAckInfo_t incomingRecords = { 0 };
    MQTTPubAckInfo_t outgoingRecords = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo );

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context,
                                       &outgoingRecords, 4,
                                       &incomingRecords, 4 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Verify MQTTSuccess is returned with the following mocks. */
    MQTT_GetSubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeSubscribeHeader_Stub( MQTT_SerializeSubscribedHeader_cb );

    /* Expect the above calls when running MQTT_Subscribe. */
    mqttStatus = MQTT_Subscribe( &context, &subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case verifies that MQTT_Subscribe returns successfully
 * when valid parameters are passed and all bytes are sent.
 */
void test_MQTT_Subscribe_happy_path1( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo[ 2 ];
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;
    MQTTPubAckInfo_t incomingRecords = { 0 };
    MQTTPubAckInfo_t outgoingRecords = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo[ 0 ] );

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context,
                                       &outgoingRecords, 4,
                                       &incomingRecords, 4 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Verify MQTTSuccess is returned with the following mocks. */
    MQTT_GetSubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeSubscribeHeader_Stub( MQTT_SerializeSubscribedHeader_cb );

    /* Expect the above calls when running MQTT_Subscribe. */
    mqttStatus = MQTT_Subscribe( &context, subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case verifies that MQTT_Subscribe returns successfully
 * when valid parameters are passed and all bytes are sent.
 */
void test_MQTT_Subscribe_happy_path2( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo[ 2 ];
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;
    MQTTPubAckInfo_t incomingRecords = { 0 };
    MQTTPubAckInfo_t outgoingRecords = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo[ 0 ] );
    setupSubscriptionInfo( &subscribeInfo[ 1 ] );

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context,
                                       &outgoingRecords, 4,
                                       &incomingRecords, 4 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Verify MQTTSuccess is returned with the following mocks. */
    MQTT_GetSubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeSubscribeHeader_Stub( MQTT_SerializeSubscribedHeader_cb1 );

    /* Expect the above calls when running MQTT_Subscribe. */
    mqttStatus = MQTT_Subscribe( &context, subscribeInfo, 2, MQTT_FIRST_VALID_PACKET_ID );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

void test_MQTT_Subscribe_MultipleSubscriptions( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo[ 5 ];
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;
    MQTTPubAckInfo_t incomingRecords = { 0 };
    MQTTPubAckInfo_t outgoingRecords = { 0 };

    TEST_ASSERT_EQUAL_MESSAGE( 6U, MQTT_SUB_UNSUB_MAX_VECTORS,
                               "This test is configured to work with MQTT_SUB_UNSUB_MAX_VECTORS defined as 6." );

    setupTransportInterface( &transport );
    transport.writev = transportWritevSubscribeSuccess;

    setupNetworkBuffer( &networkBuffer );

    subscribeInfo[ 0 ].qos = MQTTQoS1;
    subscribeInfo[ 0 ].pTopicFilter = MQTT_SAMPLE_TOPIC_FILTER;
    subscribeInfo[ 0 ].topicFilterLength = MQTT_SAMPLE_TOPIC_FILTER_LENGTH;

    subscribeInfo[ 1 ].qos = MQTTQoS2;
    subscribeInfo[ 1 ].pTopicFilter = MQTT_SAMPLE_TOPIC_FILTER1;
    subscribeInfo[ 1 ].topicFilterLength = MQTT_SAMPLE_TOPIC_FILTER_LENGTH1;

    subscribeInfo[ 2 ].qos = MQTTQoS0;
    subscribeInfo[ 2 ].pTopicFilter = MQTT_SAMPLE_TOPIC_FILTER2;
    subscribeInfo[ 2 ].topicFilterLength = MQTT_SAMPLE_TOPIC_FILTER_LENGTH2;

    subscribeInfo[ 3 ].qos = MQTTQoS1;
    subscribeInfo[ 3 ].pTopicFilter = MQTT_SAMPLE_TOPIC_FILTER3;
    subscribeInfo[ 3 ].topicFilterLength = MQTT_SAMPLE_TOPIC_FILTER_LENGTH3;

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context,
                                       &outgoingRecords, 4,
                                       &incomingRecords, 4 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Verify MQTTSuccess is returned with the following mocks. */
    MQTT_GetSubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeSubscribeHeader_Stub( MQTT_SerializeSubscribedHeader_cb2 );

    /* Expect the above calls when running MQTT_Subscribe. */
    mqttStatus = MQTT_Subscribe( &context, subscribeInfo, 4, MQTT_FIRST_VALID_PACKET_ID );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case verifies that MQTT_Subscribe returns MQTTSendFailed
 * if transport interface send returns an error.
 */
void test_MQTT_Subscribe_error_paths1( void )
{
    MQTTStatus_t mqttStatus = { 0 };
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;

    /* Verify that an error is propagated when transport interface returns an error. */
    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo );
    subscribeInfo.qos = MQTTQoS0;
    setupTransportInterface( &transport );
    transport.send = transportSendFailure;
    transport.writev = transportWritevFail;

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Verify MQTTSendFailed is propagated when transport interface returns an error. */
    MQTT_GetSubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeSubscribeHeader_Stub( MQTT_SerializeSubscribedHeader_cb );
    /* Expect the above calls when running MQTT_Subscribe. */
    mqttStatus = MQTT_Subscribe( &context, &subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTSendFailed, mqttStatus );
}

/**
 * @brief This test case verifies that MQTT_Subscribe returns MQTTSendFailed
 * if transport interface send returns an error.
 */
void test_MQTT_Subscribe_error_paths2( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;

    /* Verify that an error is propagated when transport interface returns an error. */
    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo );
    subscribeInfo.qos = MQTTQoS0;
    setupTransportInterface( &transport );
    transport.writev = NULL;
    /* Case when there is timeout in sending data through transport send. */
    transport.send = transportSendNoBytes; /* Use the mock function that returns zero bytes sent. */

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    MQTT_GetSubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeSubscribeHeader_Stub( MQTT_SerializeSubscribedHeader_cb );
    mqttStatus = MQTT_Subscribe( &context, &subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTSendFailed, mqttStatus );
}

/**
 * @brief This test case verifies that MQTT_Subscribe returns MQTTSendFailed
 * if transport interface send fails and timer overflows.
 */
void test_MQTT_Subscribe_error_paths_timerOverflowCheck( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;

    globalEntryTime = UINT32_MAX - 2U;

    /* The timer function can be called a maximum of these many times
     * (which is way less than UINT32_MAX). This ensures that if overflow
     * check is not correct, then the timer mock call will fail and assert. */
    getTimeMockCallLimit = MQTT_SEND_TIMEOUT_MS + 1;

    /* Verify that an error is propagated when transport interface returns an error. */
    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo );
    subscribeInfo.qos = MQTTQoS0;
    setupTransportInterface( &transport );
    transport.writev = NULL;
    /* Case when there is timeout in sending data through transport send. */
    transport.send = transportSendNoBytes; /* Use the mock function that returns zero bytes sent. */

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTimeMock, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    MQTT_GetSubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeSubscribeHeader_Stub( MQTT_SerializeSubscribedHeader_cb );
    mqttStatus = MQTT_Subscribe( &context, &subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTSendFailed, mqttStatus );
    TEST_ASSERT_EQUAL( -1, getTimeMockCallLimit );
}

/**
 * @brief This test case verifies that MQTT_Subscribe returns MQTTSendFailed
 * if transport interface send fails and timer overflows.
 */
void test_MQTT_Subscribe_error_paths_timerOverflowCheck1( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;

    globalEntryTime = UINT32_MAX - MQTT_SEND_TIMEOUT_MS + 1;

    /* The timer function can be called a exactly 2 times. First when setting
     * the initial time, next time when checking for timeout.
     */
    getTimeMockBigTimeStepCallLimit = 2;

    /* Verify that an error is propagated when transport interface returns an error. */
    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo );
    subscribeInfo.qos = MQTTQoS0;
    setupTransportInterface( &transport );
    transport.writev = NULL;
    /* Case when there is timeout in sending data through transport send. */
    transport.send = transportSendNoBytes; /* Use the mock function that returns zero bytes sent. */

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTimeMockBigTimeStep, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    MQTT_GetSubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetSubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeSubscribeHeader_Stub( MQTT_SerializeSubscribedHeader_cb );
    mqttStatus = MQTT_Subscribe( &context, &subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTSendFailed, mqttStatus );
    TEST_ASSERT_EQUAL( -1, getTimeMockBigTimeStepCallLimit );
}

/* ========================================================================== */

/**
 * @brief This test case verifies that MQTT_Unsubscribe returns MQTTBadParameter
 * with an invalid parameter. This test case also gives us coverage over
 * the private method, validateSubscribeUnsubscribeParams(...).
 */
void test_MQTT_Unsubscribe_invalid_params( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };

    /* Call subscribe with a NULL context. */
    mqttStatus = MQTT_Unsubscribe( NULL, &subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Call subscribe with a NULL subscription list. */
    mqttStatus = MQTT_Unsubscribe( &context, NULL, 1, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Call subscribe with 0 subscriptions. */
    mqttStatus = MQTT_Unsubscribe( &context, &subscribeInfo, 0, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Packet ID cannot be 0 per MQTT 3.1.1 spec. */
    mqttStatus = MQTT_Unsubscribe( &context, &subscribeInfo, 1, 0 );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

static uint8_t * MQTT_SerializeUnsubscribeHeader_cb( size_t remainingLength,
                                                     uint8_t * pIndex,
                                                     uint16_t packetId,
                                                     int numcallbacks )
{
    ( void ) remainingLength;
    ( void ) pIndex;
    ( void ) packetId;
    ( void ) numcallbacks;

    return pIndex;
}

/**
 * @brief This test case verifies that MQTT_Unsubscribe returns successfully
 * when valid parameters are passed and all bytes are sent.
 */
void test_MQTT_Unsubscribe_happy_path( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo );
    subscribeInfo.qos = MQTTQoS0;

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Verify MQTTSuccess is returned with the following mocks. */
    MQTT_SerializeUnsubscribeHeader_Stub( MQTT_SerializeUnsubscribeHeader_cb );
    MQTT_GetUnsubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );

    /* Expect the above calls when running MQTT_Unsubscribe. */
    mqttStatus = MQTT_Unsubscribe( &context, &subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case verifies that MQTT_Subscribe returns successfully
 * when valid parameters are passed and all bytes are sent.
 */
void test_MQTT_Unsubscribe_happy_path1( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo[ 2 ];
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;
    MQTTPubAckInfo_t incomingRecords = { 0 };
    MQTTPubAckInfo_t outgoingRecords = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo[ 0 ] );

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context,
                                       &outgoingRecords, 4,
                                       &incomingRecords, 4 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Verify MQTTSuccess is returned with the following mocks. */
    MQTT_GetUnsubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeUnsubscribeHeader_Stub( MQTT_SerializeSubscribedHeader_cb );

    /* Expect the above calls when running MQTT_Subscribe. */
    mqttStatus = MQTT_Unsubscribe( &context, subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case verifies that MQTT_Subscribe returns successfully
 * when valid parameters are passed and all bytes are sent.
 */
void test_MQTT_unsubscribe_happy_path2( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo[ 3 ];
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;
    MQTTPubAckInfo_t incomingRecords = { 0 };
    MQTTPubAckInfo_t outgoingRecords = { 0 };

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo[ 0 ] );
    setupSubscriptionInfo( &subscribeInfo[ 1 ] );
    setupSubscriptionInfo( &subscribeInfo[ 2 ] );

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context,
                                       &outgoingRecords, 4,
                                       &incomingRecords, 4 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Verify MQTTSuccess is returned with the following mocks. */
    MQTT_GetUnsubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeUnsubscribeHeader_Stub( MQTT_SerializeSubscribedHeader_cb1 );

    /* Expect the above calls when running MQTT_Subscribe. */
    mqttStatus = MQTT_Unsubscribe( &context, subscribeInfo, 3, MQTT_FIRST_VALID_PACKET_ID );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

void test_MQTT_Unsubscribe_MultipleSubscriptions( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo[ 5 ];
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;
    MQTTPubAckInfo_t incomingRecords = { 0 };
    MQTTPubAckInfo_t outgoingRecords = { 0 };

    TEST_ASSERT_EQUAL_MESSAGE( 6U, MQTT_SUB_UNSUB_MAX_VECTORS,
                               "This test is configured to work with MQTT_SUB_UNSUB_MAX_VECTORS defined as 6." );

    setupTransportInterface( &transport );
    transport.writev = transportWritevUnsubscribeSuccess;

    setupNetworkBuffer( &networkBuffer );

    subscribeInfo[ 0 ].qos = MQTTQoS1;
    subscribeInfo[ 0 ].pTopicFilter = MQTT_SAMPLE_TOPIC_FILTER;
    subscribeInfo[ 0 ].topicFilterLength = MQTT_SAMPLE_TOPIC_FILTER_LENGTH;

    subscribeInfo[ 1 ].qos = MQTTQoS2;
    subscribeInfo[ 1 ].pTopicFilter = MQTT_SAMPLE_TOPIC_FILTER1;
    subscribeInfo[ 1 ].topicFilterLength = MQTT_SAMPLE_TOPIC_FILTER_LENGTH1;

    subscribeInfo[ 2 ].qos = MQTTQoS0;
    subscribeInfo[ 2 ].pTopicFilter = MQTT_SAMPLE_TOPIC_FILTER2;
    subscribeInfo[ 2 ].topicFilterLength = MQTT_SAMPLE_TOPIC_FILTER_LENGTH2;

    subscribeInfo[ 3 ].qos = MQTTQoS1;
    subscribeInfo[ 3 ].pTopicFilter = MQTT_SAMPLE_TOPIC_FILTER3;
    subscribeInfo[ 3 ].topicFilterLength = MQTT_SAMPLE_TOPIC_FILTER_LENGTH3;

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    mqttStatus = MQTT_InitStatefulQoS( &context,
                                       &outgoingRecords, 4,
                                       &incomingRecords, 4 );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Verify MQTTSuccess is returned with the following mocks. */
    MQTT_GetUnsubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_SerializeUnsubscribeHeader_Stub( MQTT_SerializeUnsubscribedHeader_cb2 );

    /* Expect the above calls when running MQTT_Subscribe. */
    mqttStatus = MQTT_Unsubscribe( &context, subscribeInfo, 4, MQTT_FIRST_VALID_PACKET_ID );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief This test case verifies that MQTT_Unsubscribe returns MQTTSendFailed
 * if transport interface send returns an error.
 */
void test_MQTT_Unsubscribe_error_path1( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;

    /* Verify that an error is propagated when transport interface returns an error. */
    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo );
    subscribeInfo.qos = MQTTQoS0;

    transport.send = transportSendFailure;
    transport.recv = transportRecvFailure;
    transport.writev = transportWritevFail;

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    MQTT_SerializeUnsubscribeHeader_Stub( MQTT_SerializeUnsubscribeHeader_cb );
    /* Verify MQTTSendFailed is propagated when transport interface returns an error. */
    MQTT_GetUnsubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    /* Expect the above calls when running MQTT_Unsubscribe. */
    mqttStatus = MQTT_Unsubscribe( &context, &subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTSendFailed, mqttStatus );

    /* Case when there is timeout in sending data through transport send. */
}

/**
 * @brief This test case verifies that MQTT_Unsubscribe returns MQTTSendFailed
 * if transport interface send returns an error.
 */
void test_MQTT_Unsubscribe_error_path2( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    size_t remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    size_t packetSize = MQTT_SAMPLE_REMAINING_LENGTH;

    setupNetworkBuffer( &networkBuffer );
    setupSubscriptionInfo( &subscribeInfo );
    subscribeInfo.qos = MQTTQoS0;

    /* Verify that an error is propagated when transport interface returns an error. */
    setupTransportInterface( &transport );
    transport.send = transportSendFailure;
    transport.recv = transportRecvFailure;
    transport.writev = transportWritevFail;

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    MQTT_SerializeUnsubscribeHeader_Stub( MQTT_SerializeUnsubscribeHeader_cb );
    transport.send = transportSendNoBytes; /* Use the mock function that returns zero bytes sent. */
    MQTT_GetUnsubscribePacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetUnsubscribePacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    /* Expect the above calls when running MQTT_Unsubscribe. */
    mqttStatus = MQTT_Unsubscribe( &context, &subscribeInfo, 1, MQTT_FIRST_VALID_PACKET_ID );
    TEST_ASSERT_EQUAL( MQTTSendFailed, mqttStatus );
}

/* ========================================================================== */

/**
 * @brief This test case verifies that MQTT_Ping returns MQTTBadParameter
 * with context parameter is NULL.
 */
void test_MQTT_Ping_invalid_params( void )
{
    MQTTStatus_t mqttStatus;

    /* Call ping with a NULL context. */
    mqttStatus = MQTT_Ping( NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/**
 * @brief This test case verifies that MQTT_Ping returns successfully
 * when valid parameters are passed and all bytes are sent.
 */
void test_MQTT_Ping_happy_path( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t pingreqSize = MQTT_PACKET_PINGREQ_SIZE;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Verify MQTTSuccess is returned. */
    MQTT_GetPingreqPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetPingreqPacketSize_ReturnThruPtr_pPacketSize( &pingreqSize );
    MQTT_SerializePingreq_ExpectAnyArgsAndReturn( MQTTSuccess );
    /* Expect the above calls when running MQTT_Ping. */
    mqttStatus = MQTT_Ping( &context );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    TEST_ASSERT_EQUAL( context.lastPacketTxTime, context.pingReqSendTimeMs );
    TEST_ASSERT_TRUE( context.waitingForPingResp );
}

/**
 * @brief This test case verifies that MQTT_Ping returns MQTTSendFailed
 * if transport interface send returns an error.
 */
void test_MQTT_Ping_error_path( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context = { 0 };
    TransportInterface_t transport = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    size_t pingreqSize = MQTT_PACKET_PINGREQ_SIZE;

    setupTransportInterface( &transport );
    setupNetworkBuffer( &networkBuffer );

    /* Test a network error is returned from sending the PING packet over the
     * transport send . */
    transport.send = transportSendFailure;
    transport.recv = transportRecvFailure;

    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Verify MQTTSendFailed is propagated when transport interface returns an error. */
    MQTT_GetPingreqPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetPingreqPacketSize_ReturnThruPtr_pPacketSize( &pingreqSize );
    MQTT_SerializePingreq_ExpectAnyArgsAndReturn( MQTTSuccess );
    /* Expect the above calls when running MQTT_Ping. */
    mqttStatus = MQTT_Ping( &context );
    TEST_ASSERT_EQUAL( MQTTSendFailed, mqttStatus );

    /* Case when there is timeout in sending data through transport send. */
    transport.recv = transportRecvSuccess;
    transport.send = transportSendNoBytes; /* Use the mock function that returns zero bytes sent. */
    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    MQTT_GetPingreqPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetPingreqPacketSize_ReturnThruPtr_pPacketSize( &pingreqSize );
    MQTT_SerializePingreq_ExpectAnyArgsAndReturn( MQTTSuccess );
    /* Verify that the API returns failure. */
    mqttStatus = MQTT_Ping( &context );
    TEST_ASSERT_EQUAL( MQTTSendFailed, mqttStatus );


    /* Initialize context. */
    mqttStatus = MQTT_Init( &context, &transport, getTime, eventCallback, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Verify MQTTBadParameter is propagated when getting PINGREQ packet size fails. */
    MQTT_GetPingreqPacketSize_ExpectAnyArgsAndReturn( MQTTBadParameter );
    MQTT_GetPingreqPacketSize_ReturnThruPtr_pPacketSize( &pingreqSize );
    /* Expect the above calls when running MQTT_Ping. */
    mqttStatus = MQTT_Ping( &context );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/* ========================================================================== */

/**
 * @brief Test MQTT_MatchTopic for invalid input parameters.
 */
void test_MQTT_MatchTopic_InvalidInput( void )
{
    bool matchResult = false;

    /* NULL topic name. */
    TEST_ASSERT_EQUAL( MQTTBadParameter, MQTT_MatchTopic( NULL,
                                                          MQTT_SAMPLE_TOPIC_FILTER_LENGTH,
                                                          MQTT_SAMPLE_TOPIC_FILTER,
                                                          MQTT_SAMPLE_TOPIC_FILTER_LENGTH,
                                                          &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Invalid topic name length. */
    TEST_ASSERT_EQUAL( MQTTBadParameter, MQTT_MatchTopic( MQTT_SAMPLE_TOPIC_FILTER,
                                                          0u,
                                                          MQTT_SAMPLE_TOPIC_FILTER,
                                                          MQTT_SAMPLE_TOPIC_FILTER_LENGTH,
                                                          &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* NULL topic filter. */
    TEST_ASSERT_EQUAL( MQTTBadParameter, MQTT_MatchTopic( MQTT_SAMPLE_TOPIC_FILTER,
                                                          MQTT_SAMPLE_TOPIC_FILTER_LENGTH,
                                                          NULL,
                                                          MQTT_SAMPLE_TOPIC_FILTER_LENGTH,
                                                          &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Invalid topic filter length. */
    TEST_ASSERT_EQUAL( MQTTBadParameter, MQTT_MatchTopic( MQTT_SAMPLE_TOPIC_FILTER,
                                                          MQTT_SAMPLE_TOPIC_FILTER_LENGTH,
                                                          MQTT_SAMPLE_TOPIC_FILTER,
                                                          0u,
                                                          &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Invalid output parameter. */
    TEST_ASSERT_EQUAL( MQTTBadParameter, MQTT_MatchTopic( MQTT_SAMPLE_TOPIC_FILTER,
                                                          MQTT_SAMPLE_TOPIC_FILTER_LENGTH,
                                                          MQTT_SAMPLE_TOPIC_FILTER,
                                                          MQTT_SAMPLE_TOPIC_FILTER_LENGTH,
                                                          NULL ) );
}

/**
 * @brief Verifies that MQTT_MatchTopic is able to determine an exact match between the
 * topic name and topic filter.
 */
void test_MQTT_MatchTopic_ExactMatch( void )
{
    const char * pTopicFilter = NULL;
    const char * pTopicName = NULL;
    bool matchResult = false;

    /* Test for topic filter and topic name having exact match. */
    pTopicName = "/test/match";
    pTopicFilter = "/test/match";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Test for exact match when topic name and filter start with '$' .*/
    pTopicName = "$///";
    pTopicFilter = "$///";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Test for no match (with no wildcard in the topic filter). */
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     MQTT_SAMPLE_TOPIC_FILTER,
                                                     MQTT_SAMPLE_TOPIC_FILTER_LENGTH,
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Edge case tests (for branch coverage) to match at end with no wildcards. */
    pTopicName = "/test/match/";
    pTopicFilter = "/test/match/a";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    pTopicName = "a";
    pTopicFilter = "a/";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Edge case test (for branch coverage) when topic name has more levels
     * than topic filter. */
    pTopicName = "test/match";
    pTopicFilter = "test";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );
}

/**
 * @brief Verifies that MQTT_MatchTopic meets the MQTT 3.1.1 specification of all
 * cases of matching topic filters that contain the single-level '+' wildcard.
 */
void test_MQTT_MatchTopic_Wildcard_SingleLevel_Match_Cases( void )
{
    const char * pTopicName = NULL;
    const char * pTopicFilter = NULL;
    bool matchResult = false;

    /* Nominal case of topic filter ending with '+' .*/
    pTopicName = "/test/match/level1";
    pTopicFilter = "/test/match/+";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Test for match with a topic name starting with '$' .*/
    pTopicName = "$test/match/level1";
    pTopicFilter = "$test/match/+";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Test with '+' as the topic filter. */
    pTopicName = "test";
    pTopicFilter = "+";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Test that '+' in topic filter matches topic name containing consecutive
     * level separators, "//" in the corresponding level. */
    pTopicName = "/test//level1";
    pTopicFilter = "/test/+/level1";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Test with multiple placements of wildcard in topic filter. */
    pTopicName = "/test/match/level1";
    pTopicFilter = "/+/match/+";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    pTopicName = "/test/match/level1";
    pTopicFilter = "+/+/+/+";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    pTopicName = "/test///level1";
    pTopicFilter = "/test/+/+/level1";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Test that match fails when topic name has more levels than topic filter. */
    pTopicName = "/test/match/level1/level2";
    pTopicFilter = "/test/match/+";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    pTopicName = "/";
    pTopicFilter = "+";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Edge case where filter ending with '/+' matches topic ending with '/'. */
    pTopicName = "/test/match/";
    pTopicFilter = "/test/match/+";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );
}

/**
 * @brief Verifies that MQTT_MatchTopic meets the MQTT 3.1.1 specification for
 * cases of where topic filter containing '+' wildcard do not match topic name.
 */
void test_MQTT_MatchTopic_Wildcard_SingleLevel_No_Match_Cases( void )
{
    const char * pTopicName = NULL;
    const char * pTopicFilter = NULL;
    bool matchResult = false;

    /* Edge case where filter ending with '/+' should not match a topic ending with
     * at parent level. */
    pTopicName = "/test/match";
    pTopicFilter = "/test/match/+";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Edge case where topic filter starts with '+' and topic name starts with '$'. */
    pTopicName = "$/test/match";
    pTopicFilter = "+/test/match";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Topic name matches all characters with topic filter, but topic filter is invalid. */
    pTopicName = "test/match/level";
    pTopicFilter = "test/match/level+";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Invalid topic filter where non-starting '+' is not placed after '/'.*/
    pTopicName = "test/match/level1";
    pTopicFilter = "test/match/level+";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Invalid topic filter where intermediate '+' is not followed by '/'.*/
    pTopicName = "test/match/level";
    pTopicFilter = "test/+?level";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );
}

/**
 * @brief Verifies that MQTT_MatchTopic meets the MQTT 3.1.1 specification of all
 * cases of matching topic filters that contain the multi-level '#' wildcard.
 */
void test_MQTT_MatchTopic_Wildcard_MultiLevel_Match_Cases( void )
{
    const char * pTopicName = NULL;
    const char * pTopicFilter = NULL;
    bool matchResult = false;

    /* Match topic filter ending with '#' with a single level .*/
    pTopicName = "/test/match/level1";
    pTopicFilter = "/test/match/#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Match topic filter ending with '#' with multiple levels in topic name.*/
    pTopicName = "/test/match/level1/level2/level3";
    pTopicFilter = "/test/match/#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    pTopicName = "/test/match/level1/level2/level3";
    pTopicFilter = "/#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Match when topic filter is "#" */
    pTopicName = "test/match/level";
    pTopicFilter = "#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Test for match with a topic name starting with '$' .*/
    pTopicName = "$test/match/level1";
    pTopicFilter = "$test/match/#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Match '#' with topic name ending at the parent level. */
    pTopicName = "/test/match";
    pTopicFilter = "/test/match/#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Edge case where filter ending with '/#' matches topic ending with '/'. */
    pTopicName = "/test/match/";
    pTopicFilter = "/test/match/#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    /* Test for topic filters containing both '+' and '#' wildcard characters. */
    pTopicName = "/test/match";
    pTopicFilter = "+/test/match/#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );

    pTopicName = "/test/match/level";
    pTopicFilter = "+/+/+/#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( true, matchResult );
}

/**
 * @brief Verifies that MQTT_MatchTopic meets the MQTT 3.1.1 specification for
 * cases of where topic filter containing '#' wildcard do not match topic name.
 */
void test_MQTT_MatchTopic_Wildcard_MultiLevel_No_Match_Cases( void )
{
    const char * pTopicName = NULL;
    const char * pTopicFilter = NULL;
    bool matchResult = false;

    /* Edge case where topic filter starts with '#' and topic name starts with '$'. */
    pTopicName = "$/test/match";
    pTopicFilter = "#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Invalid topic filter where non-starting '#' is not placed after '/'.*/
    pTopicName = "test/match/level1";
    pTopicFilter = "test/match/level#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Topic name matches all characters with topic filter, but topic filter is invalid. */
    pTopicName = "test/match/level";
    pTopicFilter = "test/match/level?#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    pTopicName = "test/match/level";
    pTopicFilter = "test/match/level#";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    /* Invalid topic filters that contain '#' at a non-ending position .*/
    pTopicName = "test/match/level1/level2";
    pTopicFilter = "test/match/#/level2";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );

    pTopicName = "test/match/level2";
    pTopicFilter = "#/match/level2";
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_MatchTopic( pTopicName,
                                                     strlen( pTopicName ),
                                                     pTopicFilter,
                                                     strlen( pTopicFilter ),
                                                     &matchResult ) );
    TEST_ASSERT_EQUAL( false, matchResult );
}

/* ========================================================================== */

/**
 * @brief Tests that MQTT_GetSubAckStatusCodes works as expected in parsing the
 * payload information of a SUBACK packet.
 */
void test_MQTT_GetSubAckStatusCodes( void )
{
    MQTTPacketInfo_t mqttPacketInfo = { 0 };
    size_t payloadSize;
    uint8_t * pPayloadStart;
    MQTTStatus_t status = MQTTSuccess;
    uint8_t buffer[ 10 ] = { 0 };

    buffer[ 0 ] = 0;
    buffer[ 1 ] = 1;
    buffer[ 2 ] = 0x00;
    buffer[ 3 ] = 0x01;
    buffer[ 4 ] = 0x02;
    buffer[ 5 ] = 0x80;

    /* Process a valid SUBACK packet containing whole range of server response codes. */
    mqttPacketInfo.type = MQTT_PACKET_TYPE_SUBACK;
    mqttPacketInfo.pRemainingData = buffer;
    mqttPacketInfo.remainingLength = 6;
    status = MQTT_GetSubAckStatusCodes( &mqttPacketInfo, &pPayloadStart, &payloadSize );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_PTR( &buffer[ 2 ], pPayloadStart );
    TEST_ASSERT_EQUAL_INT( MQTTSubAckSuccessQos0, pPayloadStart[ 0 ] );
    TEST_ASSERT_EQUAL_INT( MQTTSubAckSuccessQos1, pPayloadStart[ 1 ] );
    TEST_ASSERT_EQUAL_INT( MQTTSubAckSuccessQos2, pPayloadStart[ 2 ] );
    TEST_ASSERT_EQUAL_INT( MQTTSubAckFailure, pPayloadStart[ 3 ] );
    TEST_ASSERT_EQUAL_INT( 4, payloadSize );

    /* Packet is NULL. */
    status = MQTT_GetSubAckStatusCodes( NULL, &pPayloadStart, &payloadSize );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    /* Output parameter, pPayloadStart, is NULL. */
    status = MQTT_GetSubAckStatusCodes( &mqttPacketInfo, NULL, &payloadSize );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    /* Output parameter, pPayloadSize, is NULL. */
    status = MQTT_GetSubAckStatusCodes( &mqttPacketInfo, &pPayloadStart, NULL );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    /* Remaining Data is NULL. */
    mqttPacketInfo.pRemainingData = NULL;
    status = MQTT_GetSubAckStatusCodes( &mqttPacketInfo, &pPayloadStart, &payloadSize );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    /* non-SUBACK packet type. */
    mqttPacketInfo.type = MQTT_PACKET_TYPE_CONNACK;
    mqttPacketInfo.pRemainingData = buffer;
    status = MQTT_GetSubAckStatusCodes( &mqttPacketInfo, &pPayloadStart, &payloadSize );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    /* Invalid remaining length value in packet. */
    mqttPacketInfo.remainingLength = 0;
    mqttPacketInfo.type = MQTT_PACKET_TYPE_SUBACK;
    status = MQTT_GetSubAckStatusCodes( &mqttPacketInfo, &pPayloadStart, &payloadSize );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
}

/* ========================================================================== */

/**
 * @brief Test MQTT_Status_strerror returns correct strings.
 */
void test_MQTT_Status_strerror( void )
{
    MQTTStatus_t status;
    const char * str = NULL;

    status = MQTTSuccess;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTSuccess", str );

    status = MQTTBadParameter;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTBadParameter", str );

    status = MQTTNoMemory;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTNoMemory", str );

    status = MQTTSendFailed;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTSendFailed", str );

    status = MQTTRecvFailed;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTRecvFailed", str );

    status = MQTTBadResponse;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTBadResponse", str );

    status = MQTTServerRefused;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTServerRefused", str );

    status = MQTTNoDataAvailable;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTNoDataAvailable", str );

    status = MQTTIllegalState;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTIllegalState", str );

    status = MQTTStateCollision;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTStateCollision", str );

    status = MQTTKeepAliveTimeout;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTKeepAliveTimeout", str );

    status = MQTTNeedMoreBytes;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "MQTTNeedMoreBytes", str );

    status = MQTTNeedMoreBytes + 1;
    str = MQTT_Status_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "Invalid MQTT Status code", str );
}

/* ========================================================================== */
void test_MQTT_GetPacketId_NULL_Context( void )
{
    uint16_t packetId = 0U;

    packetId = MQTT_GetPacketId( NULL );

    TEST_ASSERT_EQUAL( 0, packetId );
}
/* ========================================================================== */

void test_MQTT_GetPacketId_happy_path( void )
{
    uint16_t packetId = 0U;
    MQTTContext_t mqttContext = { 0 };

    mqttContext.nextPacketId = 5;

    packetId = MQTT_GetPacketId( &mqttContext );

    TEST_ASSERT_EQUAL( 5, packetId );
    TEST_ASSERT_EQUAL( 6, mqttContext.nextPacketId );
}

/* ========================================================================== */
void test_MQTT_GetPacketId_happy_path_uint16_max( void )
{
    uint16_t packetId = 0U;
    MQTTContext_t mqttContext = { 0 };

    mqttContext.nextPacketId = UINT16_MAX;

    packetId = MQTT_GetPacketId( &mqttContext );

    TEST_ASSERT_EQUAL( UINT16_MAX, packetId );
    TEST_ASSERT_EQUAL( 1, mqttContext.nextPacketId );
}
/* ========================================================================== */

void test_MQTT_CancelCallback_null_context( void )
{
    uint16_t packetId = 0U;
    MQTTStatus_t mqttStatus;

    mqttStatus = MQTT_CancelCallback( NULL, packetId );

    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}
/* ========================================================================== */

void test_MQTT_CancelCallback_null_outgoingPublishRecords( void )
{
    uint16_t packetId = 0U;
    MQTTStatus_t mqttStatus;
    MQTTContext_t mqttContext = { 0 };

    mqttContext.outgoingPublishRecords = NULL;

    mqttStatus = MQTT_CancelCallback( &mqttContext, packetId );

    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}
/* ========================================================================== */

void test_MQTT_CancelCallback_happy_path( void )
{
    uint16_t packetId = 0U;
    MQTTStatus_t mqttStatus;
    MQTTContext_t mqttContext = { 0 };

    mqttContext.outgoingPublishRecords = NULL;
    setUPContext( &mqttContext );

    MQTT_RemoveStateRecord_ExpectAndReturn( &mqttContext, packetId, MQTTSuccess );

    mqttStatus = MQTT_CancelCallback( &mqttContext, packetId );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}
/* ========================================================================== */

void test_MQTT_InitStatefulQoS_fail_null_context( void )
{
    MQTTStatus_t mqttStatus;
    MQTTPubAckInfo_t pOutgoingPublishRecords[ 10 ] = { 0 };
    MQTTPubAckInfo_t pIncomingPublishRecords[ 10 ] = { 0 };

    mqttStatus = MQTT_InitStatefulQoS( NULL,
                                       pOutgoingPublishRecords,
                                       10,
                                       pIncomingPublishRecords,
                                       10 );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}
/* ========================================================================== */

void test_MQTT_InitStatefulQoS_zero_outgoing_size( void )
{
    MQTTStatus_t mqttStatus;
    MQTTPubAckInfo_t pOutgoingPublishRecords[ 10 ] = { 0 };
    MQTTPubAckInfo_t pIncomingPublishRecords[ 10 ] = { 0 };

    MQTTContext_t mqttContext = { 0 };

    mqttStatus = MQTT_InitStatefulQoS( &mqttContext,
                                       pOutgoingPublishRecords,
                                       0,
                                       pIncomingPublishRecords,
                                       10 );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}
/* ========================================================================== */
void test_MQTT_InitStatefulQoS_zero_incoming_size( void )
{
    MQTTStatus_t mqttStatus;
    MQTTPubAckInfo_t pOutgoingPublishRecords[ 10 ] = { 0 };
    MQTTPubAckInfo_t pIncomingPublishRecords[ 10 ] = { 0 };

    MQTTContext_t mqttContext = { 0 };

    mqttStatus = MQTT_InitStatefulQoS( &mqttContext,
                                       pOutgoingPublishRecords,
                                       10,
                                       pIncomingPublishRecords,
                                       0 );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}
/* ========================================================================== */

void test_MQTT_InitStatefulQoS_callback_is_null( void )
{
    MQTTStatus_t mqttStatus;
    MQTTPubAckInfo_t pOutgoingPublishRecords[ 10 ] = { 0 };
    MQTTPubAckInfo_t pIncomingPublishRecords[ 10 ] = { 0 };

    MQTTContext_t mqttContext = { 0 };

    mqttContext.appCallback = NULL;

    mqttStatus = MQTT_InitStatefulQoS( &mqttContext,
                                       pOutgoingPublishRecords,
                                       10,
                                       pIncomingPublishRecords,
                                       10 );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}
/* ========================================================================== */
