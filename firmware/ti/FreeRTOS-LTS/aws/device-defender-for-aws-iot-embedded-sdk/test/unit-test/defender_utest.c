/*
 * AWS IoT Device Defender Client v1.4.0
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
 * @file defender_utest.c
 * @brief Unit tests for the Device Defender library.
 */

/* Standard includes. */
#include <string.h>

/* Test framework include. */
#include "unity.h"

/* Defender API include. */
#include "defender.h"

/* Thing name used in the tests. */
#define TEST_THING_NAME                          "TestThing"
#define TEST_THING_NAME_LENGTH                   STRING_LITERAL_LENGTH( TEST_THING_NAME )

/* Topics used in the tests. */
#define TEST_JSON_PUBLISH_TOPIC                  "$aws/things/" TEST_THING_NAME "/defender/metrics/json"
#define TEST_JSON_PUBLISH_TOPIC_LENGTH           STRING_LITERAL_LENGTH( TEST_JSON_PUBLISH_TOPIC )

#define TEST_JSON_ACCEPTED_TOPIC                 "$aws/things/" TEST_THING_NAME "/defender/metrics/json/accepted"
#define TEST_JSON_ACCEPTED_TOPIC_LENGTH          STRING_LITERAL_LENGTH( TEST_JSON_ACCEPTED_TOPIC )

#define TEST_JSON_REJECTED_TOPIC                 "$aws/things/" TEST_THING_NAME "/defender/metrics/json/rejected"
#define TEST_JSON_REJECTED_TOPIC_LENGTH          STRING_LITERAL_LENGTH( TEST_JSON_REJECTED_TOPIC )

#define TEST_CBOR_PUBLISH_TOPIC                  "$aws/things/" TEST_THING_NAME "/defender/metrics/cbor"
#define TEST_CBOR_PUBLISH_TOPIC_LENGTH           STRING_LITERAL_LENGTH( TEST_CBOR_PUBLISH_TOPIC )

#define TEST_CBOR_ACCEPTED_TOPIC                 "$aws/things/" TEST_THING_NAME "/defender/metrics/cbor/accepted"
#define TEST_CBOR_ACCEPTED_TOPIC_LENGTH          STRING_LITERAL_LENGTH( TEST_CBOR_ACCEPTED_TOPIC )

#define TEST_CBOR_REJECTED_TOPIC                 "$aws/things/" TEST_THING_NAME "/defender/metrics/cbor/rejected"
#define TEST_CBOR_REJECTED_TOPIC_LENGTH          STRING_LITERAL_LENGTH( TEST_CBOR_REJECTED_TOPIC )

/* Length of the topic buffer used in tests. Guard buffers are placed before and
 * after the topic buffer to verify that defender APIs do not write out of
 * bounds. The memory layout is:
 *
 *     +--------------+-------------------------------+------------+
 *     |    Guard     |    Writable Topic Buffer      |   Guard    |
 *     +--------------+-------------------------------+------------+
 *
 * Both guard buffers are filled with a known pattern before each test and are
 * verified to remain unchanged after each test.
 */
#define TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH    32
#define TEST_TOPIC_BUFFER_WRITABLE_LENGTH        256
#define TEST_TOPIC_BUFFER_SUFFIX_GUARD_LENGTH    32
#define TEST_TOPIC_BUFFER_TOTAL_LENGTH        \
    ( TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH + \
      TEST_TOPIC_BUFFER_WRITABLE_LENGTH +     \
      TEST_TOPIC_BUFFER_SUFFIX_GUARD_LENGTH )
/*-----------------------------------------------------------*/

/**
 * @brief Topic buffer used in tests.
 */
static char testTopicBuffer[ TEST_TOPIC_BUFFER_TOTAL_LENGTH ];
/*-----------------------------------------------------------*/

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    /* Initialize the topic buffer with 0xA5. */
    memset( &( testTopicBuffer[ 0 ] ), 0xA5, TEST_TOPIC_BUFFER_TOTAL_LENGTH );
}

/* Called after each test method. */
void tearDown()
{
    /* Prefix and Suffix guard buffers must never change. */
    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ 0 ] ),
                                 TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH );
    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH +
                                                     TEST_TOPIC_BUFFER_WRITABLE_LENGTH ] ),
                                 TEST_TOPIC_BUFFER_SUFFIX_GUARD_LENGTH );
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
/*-----------------------------------------------------------*/

/**
 * @brief Test that macros generates expected strings.
 */
void test_Defender_MacrosString( void )
{
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_JSON_PUBLISH_TOPIC,
                                  DEFENDER_API_JSON_PUBLISH( TEST_THING_NAME ),
                                  TEST_JSON_PUBLISH_TOPIC_LENGTH );

    TEST_ASSERT_EQUAL_STRING_LEN( TEST_JSON_ACCEPTED_TOPIC,
                                  DEFENDER_API_JSON_ACCEPTED( TEST_THING_NAME ),
                                  TEST_JSON_ACCEPTED_TOPIC_LENGTH );

    TEST_ASSERT_EQUAL_STRING_LEN( TEST_JSON_REJECTED_TOPIC,
                                  DEFENDER_API_JSON_REJECTED( TEST_THING_NAME ),
                                  TEST_JSON_REJECTED_TOPIC_LENGTH );

    TEST_ASSERT_EQUAL_STRING_LEN( TEST_CBOR_PUBLISH_TOPIC,
                                  DEFENDER_API_CBOR_PUBLISH( TEST_THING_NAME ),
                                  TEST_CBOR_PUBLISH_TOPIC_LENGTH );

    TEST_ASSERT_EQUAL_STRING_LEN( TEST_CBOR_ACCEPTED_TOPIC,
                                  DEFENDER_API_CBOR_ACCEPTED( TEST_THING_NAME ),
                                  TEST_CBOR_ACCEPTED_TOPIC_LENGTH );

    TEST_ASSERT_EQUAL_STRING_LEN( TEST_CBOR_REJECTED_TOPIC,
                                  DEFENDER_API_CBOR_REJECTED( TEST_THING_NAME ),
                                  TEST_CBOR_REJECTED_TOPIC_LENGTH );
}
/*-----------------------------------------------------------*/

/**
 * @brief Test that macros generates expected string lengths.
 */
void test_Defender_MacrosLength( void )
{
    TEST_ASSERT_EQUAL( TEST_JSON_PUBLISH_TOPIC_LENGTH,
                       DEFENDER_API_LENGTH_JSON_PUBLISH( TEST_THING_NAME_LENGTH ) );

    TEST_ASSERT_EQUAL( TEST_JSON_ACCEPTED_TOPIC_LENGTH,
                       DEFENDER_API_LENGTH_JSON_ACCEPTED( TEST_THING_NAME_LENGTH ) );

    TEST_ASSERT_EQUAL( TEST_JSON_REJECTED_TOPIC_LENGTH,
                       DEFENDER_API_LENGTH_JSON_REJECTED( TEST_THING_NAME_LENGTH ) );

    TEST_ASSERT_EQUAL( TEST_CBOR_PUBLISH_TOPIC_LENGTH,
                       DEFENDER_API_LENGTH_CBOR_PUBLISH( TEST_THING_NAME_LENGTH ) );

    TEST_ASSERT_EQUAL( TEST_CBOR_ACCEPTED_TOPIC_LENGTH,
                       DEFENDER_API_LENGTH_CBOR_ACCEPTED( TEST_THING_NAME_LENGTH ) );

    TEST_ASSERT_EQUAL( TEST_CBOR_REJECTED_TOPIC_LENGTH,
                       DEFENDER_API_LENGTH_CBOR_REJECTED( TEST_THING_NAME_LENGTH ) );
}
/*-----------------------------------------------------------*/

void test_Defender_GetTopic_BadParams( void )
{
    DefenderStatus_t ret;
    uint16_t topicLength;

    /* Null buffer. */
    ret = Defender_GetTopic( NULL,
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             TEST_THING_NAME_LENGTH,
                             DefenderJsonReportPublish,
                             &( topicLength ) );
    TEST_ASSERT_EQUAL( DefenderBadParameter, ret );
    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH );

    /* NULL thing name. */
    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             NULL,
                             TEST_THING_NAME_LENGTH,
                             DefenderJsonReportPublish,
                             &( topicLength ) );
    TEST_ASSERT_EQUAL( DefenderBadParameter, ret );
    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH );

    /* Zero length thing name. */
    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             0,
                             DefenderJsonReportPublish,
                             &( topicLength ) );
    TEST_ASSERT_EQUAL( DefenderBadParameter, ret );
    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH );

    /* Thing name length more than the maximum allowed. */
    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             DEFENDER_THINGNAME_MAX_LENGTH + 1,
                             DefenderJsonReportPublish,
                             &( topicLength ) );
    TEST_ASSERT_EQUAL( DefenderBadParameter, ret );
    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH );

    /* Invalid api. */
    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             TEST_THING_NAME_LENGTH,
                             DefenderInvalidTopic,
                             &( topicLength ) );
    TEST_ASSERT_EQUAL( DefenderBadParameter, ret );
    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH );

    /* Invalid api. */
    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             TEST_THING_NAME_LENGTH,
                             DefenderMaxTopic,
                             &( topicLength ) );
    TEST_ASSERT_EQUAL( DefenderBadParameter, ret );
    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH );

    /* NULL output parameter. */
    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             TEST_THING_NAME_LENGTH,
                             DefenderJsonReportPublish,
                             NULL );
    TEST_ASSERT_EQUAL( DefenderBadParameter, ret );
    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH );
}
/*-----------------------------------------------------------*/

void test_Defender_GetTopic_BufferTooSmall( void )
{
    DefenderStatus_t ret;
    uint16_t topicLength;

    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             5, /* Length too small to fit the entire topic. */
                             TEST_THING_NAME,
                             TEST_THING_NAME_LENGTH,
                             DefenderJsonReportPublish,
                             &( topicLength ) );
    TEST_ASSERT_EQUAL( DefenderBufferTooSmall, ret );
    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH );
}
/*-----------------------------------------------------------*/

void test_Defender_GetTopic_JsonPublishHappyPath( void )
{
    DefenderStatus_t ret;
    uint16_t topicLength;

    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             TEST_THING_NAME_LENGTH,
                             DefenderJsonReportPublish,
                             &( topicLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( TEST_JSON_PUBLISH_TOPIC_LENGTH, topicLength );

    TEST_ASSERT_EQUAL_STRING_LEN( TEST_JSON_PUBLISH_TOPIC,
                                  &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                  topicLength );

    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH + topicLength ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH - topicLength );
}
/*-----------------------------------------------------------*/

void test_Defender_GetTopic_JsonAcceptedHappyPath( void )
{
    DefenderStatus_t ret;
    uint16_t topicLength;

    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             TEST_THING_NAME_LENGTH,
                             DefenderJsonReportAccepted,
                             &( topicLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( TEST_JSON_ACCEPTED_TOPIC_LENGTH, topicLength );

    TEST_ASSERT_EQUAL_STRING_LEN( TEST_JSON_ACCEPTED_TOPIC,
                                  &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                  topicLength );

    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH + topicLength ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH - topicLength );
}
/*-----------------------------------------------------------*/

void test_Defender_GetTopic_JsonRejectedHappyPath( void )
{
    DefenderStatus_t ret;
    uint16_t topicLength;

    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             TEST_THING_NAME_LENGTH,
                             DefenderJsonReportRejected,
                             &( topicLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( TEST_JSON_REJECTED_TOPIC_LENGTH, topicLength );

    TEST_ASSERT_EQUAL_STRING_LEN( TEST_JSON_REJECTED_TOPIC,
                                  &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                  topicLength );

    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH + topicLength ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH - topicLength );
}
/*-----------------------------------------------------------*/

void test_Defender_GetTopic_CborPublishHappyPath( void )
{
    DefenderStatus_t ret;
    uint16_t topicLength;

    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             TEST_THING_NAME_LENGTH,
                             DefenderCborReportPublish,
                             &( topicLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( TEST_CBOR_PUBLISH_TOPIC_LENGTH, topicLength );

    TEST_ASSERT_EQUAL_STRING_LEN( TEST_CBOR_PUBLISH_TOPIC,
                                  &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                  topicLength );

    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH + topicLength ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH - topicLength );
}
/*-----------------------------------------------------------*/

void test_Defender_GetTopic_CborAcceptedHappyPath( void )
{
    DefenderStatus_t ret;
    uint16_t topicLength;

    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             TEST_THING_NAME_LENGTH,
                             DefenderCborReportAccepted,
                             &( topicLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( TEST_CBOR_ACCEPTED_TOPIC_LENGTH, topicLength );

    TEST_ASSERT_EQUAL_STRING_LEN( TEST_CBOR_ACCEPTED_TOPIC,
                                  &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                  topicLength );

    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH + topicLength ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH - topicLength );
}
/*-----------------------------------------------------------*/

void test_Defender_GetTopic_CborRejectedHappyPath( void )
{
    DefenderStatus_t ret;
    uint16_t topicLength;

    ret = Defender_GetTopic( &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                             TEST_TOPIC_BUFFER_WRITABLE_LENGTH,
                             TEST_THING_NAME,
                             TEST_THING_NAME_LENGTH,
                             DefenderCborReportRejected,
                             &( topicLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( TEST_CBOR_REJECTED_TOPIC_LENGTH, topicLength );

    TEST_ASSERT_EQUAL_STRING_LEN( TEST_CBOR_REJECTED_TOPIC,
                                  &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH ] ),
                                  topicLength );

    TEST_ASSERT_EACH_EQUAL_HEX8( 0xA5,
                                 &( testTopicBuffer[ TEST_TOPIC_BUFFER_PREFIX_GUARD_LENGTH + topicLength ] ),
                                 TEST_TOPIC_BUFFER_WRITABLE_LENGTH - topicLength );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_BadParams( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    /* NULL topic. */
    ret = Defender_MatchTopic( NULL,
                               TEST_JSON_PUBLISH_TOPIC_LENGTH,
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderBadParameter, ret );

    /* NULL output parameter. */
    ret = Defender_MatchTopic( TEST_JSON_PUBLISH_TOPIC,
                               TEST_JSON_PUBLISH_TOPIC_LENGTH,
                               NULL,
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderBadParameter, ret );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_IncompletePrefix( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( "$aws/things",
                               STRING_LITERAL_LENGTH( "$aws/things" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_InvalidPrefix( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( "$aws/jobs/things/TestThing/defender/metrics/json",
                               STRING_LITERAL_LENGTH( "$aws/jobs/things/TestThing/defender/metrics/json" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );

    ret = Defender_MatchTopic( "$aws/things/jobs/TestThing/defender/metrics/json",
                               STRING_LITERAL_LENGTH( "$aws/jobs/TestThing/defender/metrics/json" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_MissingThingName( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( "$aws/things/",
                               STRING_LITERAL_LENGTH( "$aws/things/" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_IncompleteBridge( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( "$aws/things/TestThing",
                               STRING_LITERAL_LENGTH( "$aws/things/TestThing" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );

    ret = Defender_MatchTopic( "$aws/things/TestThing/",
                               STRING_LITERAL_LENGTH( "$aws/things/TestThing/" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );

    ret = Defender_MatchTopic( "$aws/things/TestThing/defender",
                               STRING_LITERAL_LENGTH( "$aws/things/TestThing/defender" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_InvalidBridge( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( "$aws/things/TestThing/shadow/metrics/json",
                               STRING_LITERAL_LENGTH( "$aws/things/TestThing/shadow/metrics/json" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );

    ret = Defender_MatchTopic( "$aws/things/TestThing/defender/defender/metrics/json",
                               STRING_LITERAL_LENGTH( "$aws/things/TestThing/defender/defender/metrics/json" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_IncompleteFormat( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( "$aws/things/TestThing/defender/metrics",
                               STRING_LITERAL_LENGTH( "$aws/things/TestThing/defender/metrics" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );

    ret = Defender_MatchTopic( "$aws/things/TestThing/defender/metrics/",
                               STRING_LITERAL_LENGTH( "$aws/things/TestThing/defender/metrics/" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_InvalidFormat( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( "$aws/things/TestThing/defender/metrics/xml",
                               STRING_LITERAL_LENGTH( "$aws/things/TestThing/defender/metrics/xml" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_InvalidSuffix( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( "$aws/things/TestThing/defender/metrics/json/delta",
                               STRING_LITERAL_LENGTH( "$aws/things/TestThing/defender/metrics/json/delta" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_ExtraData( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( "$aws/things/TestThing/defender/metrics/json/gibberish",
                               STRING_LITERAL_LENGTH( "$aws/things/TestThing/defender/metrics/json/gibberish" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );

    ret = Defender_MatchTopic( "$aws/things/TestThing/defender/metrics/json/accepted/gibberish",
                               STRING_LITERAL_LENGTH( "$aws/things/TestThing/defender/metrics/json/accepted/gibberish" ),
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );
    TEST_ASSERT_EQUAL( DefenderNoMatch, ret );
    TEST_ASSERT_EQUAL( DefenderInvalidTopic, api );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_JsonPublishHappyPath( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( TEST_JSON_PUBLISH_TOPIC,
                               TEST_JSON_PUBLISH_TOPIC_LENGTH,
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( DefenderJsonReportPublish, api );
    TEST_ASSERT_EQUAL_PTR( TEST_JSON_PUBLISH_TOPIC + DEFENDER_API_LENGTH_PREFIX, pThingName );
    TEST_ASSERT_EQUAL( TEST_THING_NAME_LENGTH, thingNameLength );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_JsonAcceptedHappyPath( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( TEST_JSON_ACCEPTED_TOPIC,
                               TEST_JSON_ACCEPTED_TOPIC_LENGTH,
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( DefenderJsonReportAccepted, api );
    TEST_ASSERT_EQUAL_PTR( TEST_JSON_ACCEPTED_TOPIC + DEFENDER_API_LENGTH_PREFIX, pThingName );
    TEST_ASSERT_EQUAL( TEST_THING_NAME_LENGTH, thingNameLength );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_JsonRejectedHappyPath( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( TEST_JSON_REJECTED_TOPIC,
                               TEST_JSON_REJECTED_TOPIC_LENGTH,
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( DefenderJsonReportRejected, api );
    TEST_ASSERT_EQUAL_PTR( TEST_JSON_REJECTED_TOPIC + DEFENDER_API_LENGTH_PREFIX, pThingName );
    TEST_ASSERT_EQUAL( TEST_THING_NAME_LENGTH, thingNameLength );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_CborPublishHappyPath( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( TEST_CBOR_PUBLISH_TOPIC,
                               TEST_CBOR_PUBLISH_TOPIC_LENGTH,
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( DefenderCborReportPublish, api );
    TEST_ASSERT_EQUAL_PTR( TEST_CBOR_PUBLISH_TOPIC + DEFENDER_API_LENGTH_PREFIX, pThingName );
    TEST_ASSERT_EQUAL( TEST_THING_NAME_LENGTH, thingNameLength );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_CborAcceptedHappyPath( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( TEST_CBOR_ACCEPTED_TOPIC,
                               TEST_CBOR_ACCEPTED_TOPIC_LENGTH,
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( DefenderCborReportAccepted, api );
    TEST_ASSERT_EQUAL_PTR( TEST_CBOR_ACCEPTED_TOPIC + DEFENDER_API_LENGTH_PREFIX, pThingName );
    TEST_ASSERT_EQUAL( TEST_THING_NAME_LENGTH, thingNameLength );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_CborRejectedHappyPath( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    ret = Defender_MatchTopic( TEST_CBOR_REJECTED_TOPIC,
                               TEST_CBOR_REJECTED_TOPIC_LENGTH,
                               &( api ),
                               &( pThingName ),
                               &( thingNameLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( DefenderCborReportRejected, api );
    TEST_ASSERT_EQUAL_PTR( TEST_CBOR_REJECTED_TOPIC + DEFENDER_API_LENGTH_PREFIX, pThingName );
    TEST_ASSERT_EQUAL( TEST_THING_NAME_LENGTH, thingNameLength );
}
/*-----------------------------------------------------------*/

void test_Defender_MatchTopic_MissingOptionalParams( void )
{
    DefenderStatus_t ret;
    const char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;

    /* Missing output param for returning thing name. */
    ret = Defender_MatchTopic( TEST_JSON_PUBLISH_TOPIC,
                               TEST_JSON_PUBLISH_TOPIC_LENGTH,
                               &( api ),
                               NULL,
                               &( thingNameLength ) );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( DefenderJsonReportPublish, api );
    TEST_ASSERT_EQUAL( TEST_THING_NAME_LENGTH, thingNameLength );

    /* Missing output param for returning thing name length. */
    ret = Defender_MatchTopic( TEST_JSON_PUBLISH_TOPIC,
                               TEST_JSON_PUBLISH_TOPIC_LENGTH,
                               &( api ),
                               &( pThingName ),
                               NULL );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( DefenderJsonReportPublish, api );
    TEST_ASSERT_EQUAL_PTR( TEST_JSON_PUBLISH_TOPIC + DEFENDER_API_LENGTH_PREFIX, pThingName );

    /* Missing output param for returning both thing name and thing name
     * length. */
    ret = Defender_MatchTopic( TEST_JSON_PUBLISH_TOPIC,
                               TEST_JSON_PUBLISH_TOPIC_LENGTH,
                               &( api ),
                               NULL,
                               NULL );

    TEST_ASSERT_EQUAL( DefenderSuccess, ret );
    TEST_ASSERT_EQUAL( DefenderJsonReportPublish, api );
}
/*-----------------------------------------------------------*/
