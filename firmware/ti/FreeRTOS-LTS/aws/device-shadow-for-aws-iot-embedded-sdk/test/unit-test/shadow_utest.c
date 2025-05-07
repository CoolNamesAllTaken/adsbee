/*
 * AWS IoT Device Shadow v1.4.1
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
 *
 */

/**
 * @file shadow_utest.c
 * @brief Tests for the user-facing API functions (declared in shadow.h).
 */

/* Standard includes. */
#include <stdint.h>
#include <string.h>

/* Test framework includes. */
#include "unity.h"

/* Shadow include. */
#include "shadow.h"


/*-----------------------------------------------------------*/

/**
 * @brief The Thing Name shared among all the tests.
 */
#define TEST_THING_NAME                                        "TestThingName"

/**
 * @brief The length of #TEST_THING_NAME.
 */
#define TEST_THING_NAME_LENGTH                                 ( sizeof( TEST_THING_NAME ) - 1 )

/**
 * @brief The shadow topic string "update" shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_STRING_UPDATE                       "$aws/things/TestThingName/shadow/update"

/**
 * @brief The shadow topic string "update/accepted" shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_STRING_UPDATE_ACCEPTED              "$aws/things/TestThingName/shadow/update/accepted"

/**
 * @brief The shadow topic string "update/rejected" shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_STRING_UPDATE_REJECTED              "$aws/things/TestThingName/shadow/update/rejected"

/**
 * @brief The shadow topic string "update/documents" shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_STRING_UPDATE_DOCUMENTS             "$aws/things/TestThingName/shadow/update/documents"

/**
 * @brief The shadow topic string "update/delta" shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_STRING_UPDATE_DELTA                 "$aws/things/TestThingName/shadow/update/delta"

/**
 * @brief The shadow topic string "get" shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_STRING_GET                          "$aws/things/TestThingName/shadow/get"

/**
 * @brief The shadow topic string "get/accepted" shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_STRING_GET_ACCEPTED                 "$aws/things/TestThingName/shadow/get/accepted"

/**
 * @brief The shadow topic string "get/rejected" shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_STRING_GET_REJECTED                 "$aws/things/TestThingName/shadow/get/rejected"

/**
 * @brief The shadow topic string "delete" shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_STRING_DELETE                       "$aws/things/TestThingName/shadow/delete"

/**
 * @brief The shadow topic string "delete/accepted" shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_STRING_DELETE_ACCEPTED              "$aws/things/TestThingName/shadow/delete/accepted"

/**
 * @brief The shadow topic string "delete/rejected" shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_STRING_DELETE_REJECTED              "$aws/things/TestThingName/shadow/delete/rejected"

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_UPDATE shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_UPDATE                       ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_UPDATE ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_UPDATE_ACCEPTED shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_UPDATE_ACCEPTED              ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_UPDATE_ACCEPTED ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_UPDATE_REJECTED shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_UPDATE_REJECTED              ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_UPDATE_REJECTED ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_UPDATE_DOCUMENTS shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_UPDATE_DOCUMENTS             ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_UPDATE_DOCUMENTS ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_UPDATE_DELTA shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_UPDATE_DELTA                 ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_UPDATE_DELTA ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_GET shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_GET                          ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_GET ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_GET_ACCEPTED shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_GET_ACCEPTED                 ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_GET_ACCEPTED ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_GET_REJECTED shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_GET_REJECTED                 ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_GET_REJECTED ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_DELETE shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_DELETE                       ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_DELETE ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_DELETE_ACCEPTED shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_DELETE_ACCEPTED              ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_DELETE_ACCEPTED ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_DELETE_REJECTED shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_DELETE_REJECTED              ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_DELETE_REJECTED ) - 1U )

/**
 * @brief A topic string with an empty thing name.
 */
#define TEST_TOPIC_STRING_EMPTY_THINGNAME                      "$aws/things/"

/**
 * @brief A topic string with an invalid thing name.
 */
#define TEST_TOPIC_STRING_INVALID_THINGNAME                    "$aws/things//"

/**
 * @brief A topic string with an un-terminated thing name
 */
#define TEST_TOPIC_STRING_UNTERMINATED_THINGNAME               "$aws/things/TestThingName"

/**
 * @brief A topic string with an empty shadow root.
 */
#define TEST_TOPIC_STRING_EMPTY_SHADOW_ROOT                    "$aws/things/TestThingName/"

/**
 * @brief A topic string with an invalid shadow root.
 */
#define TEST_TOPIC_STRING_INVALID_SHADOW_ROOT                  "$aws/things/TestThingName/invalid"

/**
 * @brief A topic string with an empty shadow message type.
 */
#define TEST_CLASSIC_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE    "$aws/things/TestThingName/shadow"

/**
 * @brief A topic string that is not related to Shadow.
 */
#define TEST_CLASSIC_TOPIC_STRING_INVALID_SHADOW_RESPONSE      "$aws/things/TestThingName/shadow/invalid/invalid"

/**
 * @brief A topic string that is not related to Shadow.
 */
#define TEST_CLASSIC_TOPIC_STRING_INVALID_GET_REJECTED         "$aws/things/TestThingName/shadow/get/rejected/gibberish"

/**
 * @brief A topic string that is not related to Shadow.
 */
#define TEST_TOPIC_STRING_INVALID_PREFIX                       "$aws/jobs/TestThingName/shadow/get/rejected"

/**
 * @brief The length of #TEST_TOPIC_STRING_INVALID_PREFIX shared among all shadow test cases.
 */
#define TEST_TOPIC_LENGTH_INVALID_PREFIX                       ( ( uint16_t ) sizeof( TEST_TOPIC_STRING_INVALID_PREFIX ) - 1U )

/**
 * @brief The length of #TEST_TOPIC_STRING_EMPTY_THINGNAME shared among all shadow test cases.
 */
#define TEST_TOPIC_LENGTH_EMPTY_THINGNAME                      ( ( uint16_t ) sizeof( TEST_TOPIC_STRING_EMPTY_THINGNAME ) - 1U )

/**
 * @brief The length of #TEST_TOPIC_STRING_INVALID_THINGNAME shared among all shadow test cases.
 */
#define TEST_TOPIC_LENGTH_INVALID_THINGNAME                    ( ( uint16_t ) sizeof( TEST_TOPIC_STRING_INVALID_THINGNAME ) - 1U )

/**
 * @brief The length of #TEST_TOPIC_STRING_UNTERMINATED_THINGNAME shared among all shadow test cases.
 */
#define TEST_TOPIC_LENGTH_UNTERMINATED_THINGNAME               ( ( uint16_t ) sizeof( TEST_TOPIC_STRING_UNTERMINATED_THINGNAME ) - 1U )

/**
 * @brief The length of #TEST_TOPIC_STRING_EMPTY_SHADOW_ROOT shared among all shadow test cases.
 */
#define TEST_TOPIC_LENGTH_EMPTY_SHADOW_ROOT                    ( ( uint16_t ) sizeof( TEST_TOPIC_STRING_EMPTY_SHADOW_ROOT ) - 1U )

/**
 * @brief The length of #TEST_TOPIC_STRING_INVALID_SHADOW_ROOT shared among all shadow test cases.
 */
#define TEST_TOPIC_LENGTH_INVALID_SHADOW_ROOT                  ( ( uint16_t ) sizeof( TEST_TOPIC_STRING_INVALID_SHADOW_ROOT ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_EMPTY_SHADOW_MESSAGE_TYPE    ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_INVALID_SHADOW_RESPONSE shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_INVALID_SHADOW_RESPONSE      ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_INVALID_SHADOW_RESPONSE ) - 1U )

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_INVALID_GET_REJECTED shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_LENGTH_INVALID_GET_REJECTED         ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_STRING_INVALID_GET_REJECTED ) - 1U )

/**
 * @brief The init value for a topic buffer.
 */
#define TEST_CLASSIC_TOPIC_BUFFER_INITIALIZE                   "ABCDEFGHIJKLMNOPQRSTUVWXYZ123456789abcdefghijklmno"

/**
 * @brief The init value for a topic buffer.
 */
#define TEST_CLASSIC_TOPIC_BUFFER_MODIFIED                     "$aws/things/TestThingName/shadow/get/acceptedklmno"

/**
 * @brief The length of #TEST_CLASSIC_TOPIC_STRING_DELETE_REJECTED shared among all Classic shadow test cases.
 */
#define TEST_CLASSIC_TOPIC_BUFFER_LENGTH                       ( ( uint16_t ) sizeof( TEST_CLASSIC_TOPIC_BUFFER_INITIALIZE ) - 1U )


/**
 * @brief The Shadow Name shared among all the named shadow tests.
 */
#define TEST_SHADOW_NAME                                     "TestShadowName"

/**
 * @brief The length of #TEST_SHADOW_NAME.
 */
#define TEST_SHADOW_NAME_LENGTH                              ( sizeof( TEST_SHADOW_NAME ) - 1 )

/**
 * @brief The shadow topic string "update" shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_STRING_UPDATE                       "$aws/things/TestThingName/shadow/name/TestShadowName/update"

/**
 * @brief The shadow topic string "update/accepted" shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_STRING_UPDATE_ACCEPTED              "$aws/things/TestThingName/shadow/name/TestShadowName/update/accepted"

/**
 * @brief The shadow topic string "update/rejected" shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_STRING_UPDATE_REJECTED              "$aws/things/TestThingName/shadow/name/TestShadowName/update/rejected"

/**
 * @brief The shadow topic string "update/documents" shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_STRING_UPDATE_DOCUMENTS             "$aws/things/TestThingName/shadow/name/TestShadowName/update/documents"

/**
 * @brief The shadow topic string "update/delta" shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_STRING_UPDATE_DELTA                 "$aws/things/TestThingName/shadow/name/TestShadowName/update/delta"

/**
 * @brief The shadow topic string "get" shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_STRING_GET                          "$aws/things/TestThingName/shadow/name/TestShadowName/get"

/**
 * @brief The shadow topic string "get/accepted" shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_STRING_GET_ACCEPTED                 "$aws/things/TestThingName/shadow/name/TestShadowName/get/accepted"

/**
 * @brief The shadow topic string "get/rejected" shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_STRING_GET_REJECTED                 "$aws/things/TestThingName/shadow/name/TestShadowName/get/rejected"

/**
 * @brief The shadow topic string "delete" shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_STRING_DELETE                       "$aws/things/TestThingName/shadow/name/TestShadowName/delete"

/**
 * @brief The shadow topic string "delete/accepted" shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_STRING_DELETE_ACCEPTED              "$aws/things/TestThingName/shadow/name/TestShadowName/delete/accepted"

/**
 * @brief The shadow topic string "delete/rejected" shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_STRING_DELETE_REJECTED              "$aws/things/TestThingName/shadow/name/TestShadowName/delete/rejected"

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_UPDATE shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_UPDATE                       ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_UPDATE ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_UPDATE_ACCEPTED shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_UPDATE_ACCEPTED              ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_UPDATE_ACCEPTED ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_UPDATE_REJECTED shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_UPDATE_REJECTED              ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_UPDATE_REJECTED ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_UPDATE_DOCUMENTS shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_UPDATE_DOCUMENTS             ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_UPDATE_DOCUMENTS ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_UPDATE_DELTA shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_UPDATE_DELTA                 ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_UPDATE_DELTA ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_GET shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_GET                          ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_GET ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_GET_ACCEPTED shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_GET_ACCEPTED                 ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_GET_ACCEPTED ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_GET_REJECTED shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_GET_REJECTED                 ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_GET_REJECTED ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_DELETE shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_DELETE                       ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_DELETE ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_DELETE_ACCEPTED shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_DELETE_ACCEPTED              ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_DELETE_ACCEPTED ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_DELETE_REJECTED shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_DELETE_REJECTED              ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_DELETE_REJECTED ) - 1U )

/**
 * @brief A topic string with an empty shadow name.
 */
#define TEST_NAMED_TOPIC_STRING_EMPTY_SHADOWNAME             "$aws/things/TestThingName/shadow/name/"

/**
 * @brief A topic string with an invalid shadow name.
 */
#define TEST_NAMED_TOPIC_STRING_INVALID_SHADOWNAME           "$aws/things/TestThingName/shadow/name//"

/**
 * @brief A topic string with an un-terminated shadow name
 */
#define TEST_NAMED_TOPIC_STRING_UNTERMINATED_SHADOWNAME      "$aws/things/TestThingName/shadow/name/TestShadowName"

/**
 * @brief A topic string with an empty shadow message type.
 */
#define TEST_NAMED_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE    "$aws/things/TestThingName/shadow/name/TestShadowName/"

/**
 * @brief A topic string that is not related to Shadow.
 */
#define TEST_NAMED_TOPIC_STRING_INVALID_SHADOW_RESPONSE      "$aws/things/TestThingName/shadow/name/TestShadowName/invalid/invalid"

/**
 * @brief A topic string that is not related to Shadow.
 */
#define TEST_NAMED_TOPIC_STRING_INVALID_GET_REJECTED         "$aws/things/TestThingName/shadow/name/TestShadowName/get/rejected/gibberish"

/**
 * @brief A topic string that exceeds the maximum Thing name length.
 */
#define TEST_NAMED_TOPIC_STRING_EXCEEDS_MAX_THING_NAME       "$aws/things/TestThingName12345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890/shadow/name/TestShadowName/delete/rejected"

/**
 * @brief A topic string that exceeds the maximum Shadow name length.
 */
#define TEST_NAMED_TOPIC_STRING_EXCEEDS_MAX_SHADOW_NAME      "$aws/things/TestThingName/shadow/name/TestShadowName123456789012345678901234567890123456789012345678901234567890/delete/rejected"

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_EMPTY_SHADOWNAME shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_EMPTY_SHADOWNAME             ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_EMPTY_SHADOWNAME ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_INVALID_SHADOWNAME shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_INVALID_SHADOWNAME           ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_INVALID_SHADOWNAME ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_UNTERMINATED_SHADOWNAME shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_UNTERMINATED_SHADOWNAME      ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_UNTERMINATED_SHADOWNAME ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_EMPTY_SHADOW_MESSAGE_TYPE    ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_INVALID_SHADOW_RESPONSE shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_INVALID_SHADOW_RESPONSE      ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_INVALID_SHADOW_RESPONSE ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_INVALID_GET_REJECTED shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_LENGTH_INVALID_GET_REJECTED         ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_INVALID_GET_REJECTED ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_EXCEEDS_MAX_THING_NAME.
 */
#define TEST_NAMED_TOPIC_LENGTH_EXCEEDS_MAX_THING_NAME       ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_EXCEEDS_MAX_THING_NAME ) - 1U )

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_EXCEEDS_MAX_SHADOW_NAME.
 */
#define TEST_NAMED_TOPIC_LENGTH_EXCEEDS_MAX_SHADOW_NAME      ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_STRING_EXCEEDS_MAX_SHADOW_NAME ) - 1U )

/**
 * @brief The init value for a topic buffer.
 */
#define TEST_NAMED_TOPIC_BUFFER_INITIALIZE                   "ABCDEFGHIJKLMNOPQRSTUVWXYZ123456789abcdefghijklmnopqrstuvwxyz123456789"

/**
 * @brief The init value for a topic buffer.
 */
#define TEST_NAMED_TOPIC_BUFFER_MODIFIED                     "$aws/things/TestThingName/shadow/name/TestShadowName/get/accepted56789"

/**
 * @brief The length of #TEST_NAMED_TOPIC_STRING_DELETE_REJECTED shared among all named shadow test cases.
 */
#define TEST_NAMED_TOPIC_BUFFER_LENGTH                       ( ( uint16_t ) sizeof( TEST_NAMED_TOPIC_BUFFER_INITIALIZE ) - 1U )

/**
 * @brief Maximum shadow name length.
 * Refer to https://docs.aws.amazon.com/general/latest/gr/iot-core.html#device-shadow-limits
 * for more details about the Device Shadow limits.
 */
#define SHADOW_NAME_MAX_LENGTH                               ( 64U )

/**
 * @brief Maximum thing name length.
 * Refer to https://docs.aws.amazon.com/general/latest/gr/iot-core.html#device-shadow-limits
 * for more details about the Device Shadow limits.
 */
#define SHADOW_THINGNAME_MAX_LENGTH                          ( 128U )

/*-----------------------------------------------------------*/

/* ============================   UNITY FIXTURES ============================ */

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
/*-----------------------------------------------------------*/

/**
 * @brief Tests the macros generate the expected strings for Classic shadows.
 */
void test_Shadow_Classic_MacrosString( void )
{
    /* Test Classic shadow topic strings through the deprecated legacy macros, to verify the legacy macros. */
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_STRING_UPDATE, SHADOW_TOPIC_STRING_UPDATE( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_STRING_UPDATE_ACCEPTED, SHADOW_TOPIC_STRING_UPDATE_ACCEPTED( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_STRING_UPDATE_REJECTED, SHADOW_TOPIC_STRING_UPDATE_REJECTED( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_STRING_UPDATE_DOCUMENTS, SHADOW_TOPIC_STRING_UPDATE_DOCUMENTS( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_STRING_UPDATE_DELTA, SHADOW_TOPIC_STRING_UPDATE_DELTA( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_STRING_GET, SHADOW_TOPIC_STRING_GET( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_STRING_GET_ACCEPTED, SHADOW_TOPIC_STRING_GET_ACCEPTED( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_STRING_GET_REJECTED, SHADOW_TOPIC_STRING_GET_REJECTED( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_STRING_DELETE, SHADOW_TOPIC_STRING_DELETE( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_STRING_DELETE_ACCEPTED, SHADOW_TOPIC_STRING_DELETE_ACCEPTED( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_STRING_DELETE_REJECTED, SHADOW_TOPIC_STRING_DELETE_REJECTED( TEST_THING_NAME ) );
}

/**
 * @brief Tests the macros generate the expected strings for named shadows.
 */
void test_Shadow_Named_MacrosString( void )
{
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_STRING_UPDATE, SHADOW_TOPIC_STR_UPDATE( TEST_THING_NAME, TEST_SHADOW_NAME ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_STRING_UPDATE_ACCEPTED, SHADOW_TOPIC_STR_UPDATE_ACC( TEST_THING_NAME, TEST_SHADOW_NAME ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_STRING_UPDATE_REJECTED, SHADOW_TOPIC_STR_UPDATE_REJ( TEST_THING_NAME, TEST_SHADOW_NAME ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_STRING_UPDATE_DOCUMENTS, SHADOW_TOPIC_STR_UPDATE_DOCS( TEST_THING_NAME, TEST_SHADOW_NAME ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_STRING_UPDATE_DELTA, SHADOW_TOPIC_STR_UPDATE_DELTA( TEST_THING_NAME, TEST_SHADOW_NAME ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_STRING_GET, SHADOW_TOPIC_STR_GET( TEST_THING_NAME, TEST_SHADOW_NAME ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_STRING_GET_ACCEPTED, SHADOW_TOPIC_STR_GET_ACC( TEST_THING_NAME, TEST_SHADOW_NAME ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_STRING_GET_REJECTED, SHADOW_TOPIC_STR_GET_REJ( TEST_THING_NAME, TEST_SHADOW_NAME ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_STRING_DELETE, SHADOW_TOPIC_STR_DELETE( TEST_THING_NAME, TEST_SHADOW_NAME ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_STRING_DELETE_ACCEPTED, SHADOW_TOPIC_STR_DELETE_ACC( TEST_THING_NAME, TEST_SHADOW_NAME ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_STRING_DELETE_REJECTED, SHADOW_TOPIC_STR_DELETE_REJ( TEST_THING_NAME, TEST_SHADOW_NAME ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the macros generate the expected strings length for Classic shadows.
 */
void test_Shadow_Classic_MacrosLength( void )
{
    /* Test Classic shadow topic lengths through the deprecated legacy macros, to verify the legacy macros. */
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_LENGTH_UPDATE, SHADOW_TOPIC_LENGTH_UPDATE( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_LENGTH_UPDATE_ACCEPTED, SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_LENGTH_UPDATE_REJECTED, SHADOW_TOPIC_LENGTH_UPDATE_REJECTED( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_LENGTH_UPDATE_DOCUMENTS, SHADOW_TOPIC_LENGTH_UPDATE_DOCUMENTS( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_LENGTH_UPDATE_DELTA, SHADOW_TOPIC_LENGTH_UPDATE_DELTA( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_LENGTH_GET, SHADOW_TOPIC_LENGTH_GET( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_LENGTH_GET_ACCEPTED, SHADOW_TOPIC_LENGTH_GET_ACCEPTED( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_LENGTH_GET_REJECTED, SHADOW_TOPIC_LENGTH_GET_REJECTED( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_LENGTH_DELETE, SHADOW_TOPIC_LENGTH_DELETE( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_LENGTH_DELETE_ACCEPTED, SHADOW_TOPIC_LENGTH_DELETE_ACCEPTED( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_CLASSIC_TOPIC_LENGTH_DELETE_REJECTED, SHADOW_TOPIC_LENGTH_DELETE_REJECTED( TEST_THING_NAME_LENGTH ) );
}

/**
 * @brief Tests the macros generate the expected strings length for named shadows.
 */
void test_Shadow_Named_MacrosLength( void )
{
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_LENGTH_UPDATE, SHADOW_TOPIC_LEN_UPDATE( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_LENGTH_UPDATE_ACCEPTED, SHADOW_TOPIC_LEN_UPDATE_ACC( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_LENGTH_UPDATE_REJECTED, SHADOW_TOPIC_LEN_UPDATE_REJ( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_LENGTH_UPDATE_DOCUMENTS, SHADOW_TOPIC_LEN_UPDATE_DOCS( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_LENGTH_UPDATE_DELTA, SHADOW_TOPIC_LEN_UPDATE_DELTA( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_LENGTH_GET, SHADOW_TOPIC_LEN_GET( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_LENGTH_GET_ACCEPTED, SHADOW_TOPIC_LEN_GET_ACC( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_LENGTH_GET_REJECTED, SHADOW_TOPIC_LEN_GET_REJ( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_LENGTH_DELETE, SHADOW_TOPIC_LEN_DELETE( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_LENGTH_DELETE_ACCEPTED, SHADOW_TOPIC_LEN_DELETE_ACC( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_NAMED_TOPIC_LENGTH_DELETE_REJECTED, SHADOW_TOPIC_LEN_DELETE_REJ( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Shadow_AssembleTopicString() for Classic shadows,
 * with valid parameters. Tests Classic shadows through the deprecated legacy API macro
 * Shadow_GetTopicString(), to verify the legacy macro.
 */
void test_Shadow_AssembleTopicString_Classic_Happy_Path( void )
{
    ShadowStatus_t shadowStatus = SHADOW_SUCCESS;
    uint16_t outLength = 0U;
    char topicBufferExceeded[ TEST_CLASSIC_TOPIC_BUFFER_LENGTH ] = TEST_CLASSIC_TOPIC_BUFFER_INITIALIZE;
    uint16_t bufferSizeExceeded = TEST_CLASSIC_TOPIC_BUFFER_LENGTH;
    char topicBufferGetAccepted[ SHADOW_TOPIC_LENGTH_GET_ACCEPTED( TEST_THING_NAME_LENGTH ) ] = { 0 };
    uint16_t bufferSizeGetAccepted = TEST_CLASSIC_TOPIC_LENGTH_GET_ACCEPTED;
    char topicBuffer[ SHADOW_TOPIC_LENGTH_MAX( TEST_THING_NAME_LENGTH ) ] = { 0 };
    uint16_t bufferSize = SHADOW_TOPIC_LENGTH_MAX( TEST_THING_NAME_LENGTH );
    uint16_t index = 0U;

    /* Lookup table for Shadow message string. */
    static const uint16_t expectedBuffersSize[ ShadowTopicStringTypeMaxNum ] =
    {
        TEST_CLASSIC_TOPIC_LENGTH_UPDATE,
        TEST_CLASSIC_TOPIC_LENGTH_UPDATE_ACCEPTED,
        TEST_CLASSIC_TOPIC_LENGTH_UPDATE_REJECTED,
        TEST_CLASSIC_TOPIC_LENGTH_UPDATE_DOCUMENTS,
        TEST_CLASSIC_TOPIC_LENGTH_UPDATE_DELTA,
        TEST_CLASSIC_TOPIC_LENGTH_GET,
        TEST_CLASSIC_TOPIC_LENGTH_GET_ACCEPTED,
        TEST_CLASSIC_TOPIC_LENGTH_GET_REJECTED,
        TEST_CLASSIC_TOPIC_LENGTH_DELETE,
        TEST_CLASSIC_TOPIC_LENGTH_DELETE_ACCEPTED,
        TEST_CLASSIC_TOPIC_LENGTH_DELETE_REJECTED
    };

    /* Lookup table for Shadow message string. */
    static const char * const expectedBuffers[ ShadowTopicStringTypeMaxNum ] =
    {
        TEST_CLASSIC_TOPIC_STRING_UPDATE,
        TEST_CLASSIC_TOPIC_STRING_UPDATE_ACCEPTED,
        TEST_CLASSIC_TOPIC_STRING_UPDATE_REJECTED,
        TEST_CLASSIC_TOPIC_STRING_UPDATE_DOCUMENTS,
        TEST_CLASSIC_TOPIC_STRING_UPDATE_DELTA,
        TEST_CLASSIC_TOPIC_STRING_GET,
        TEST_CLASSIC_TOPIC_STRING_GET_ACCEPTED,
        TEST_CLASSIC_TOPIC_STRING_GET_REJECTED,
        TEST_CLASSIC_TOPIC_STRING_DELETE,
        TEST_CLASSIC_TOPIC_STRING_DELETE_ACCEPTED,
        TEST_CLASSIC_TOPIC_STRING_DELETE_REJECTED
    };

    static const ShadowTopicStringType_t topicTypes[ ShadowTopicStringTypeMaxNum ] =
    {
        ShadowTopicStringTypeUpdate,
        ShadowTopicStringTypeUpdateAccepted,
        ShadowTopicStringTypeUpdateRejected,
        ShadowTopicStringTypeUpdateDocuments,
        ShadowTopicStringTypeUpdateDelta,
        ShadowTopicStringTypeGet,
        ShadowTopicStringTypeGetAccepted,
        ShadowTopicStringTypeGetRejected,
        ShadowTopicStringTypeDelete,
        ShadowTopicStringTypeDeleteAccepted,
        ShadowTopicStringTypeDeleteRejected
    };

    /* Call Shadow_GetTopicString() with valid parameters but bufferSize exceeds topic string length
     * and verify result. */
    shadowStatus = Shadow_GetTopicString( ShadowTopicStringTypeGetAccepted,
                                          TEST_THING_NAME,
                                          TEST_THING_NAME_LENGTH,
                                          &( topicBufferExceeded[ 0 ] ),
                                          bufferSizeExceeded,
                                          &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( TEST_CLASSIC_TOPIC_LENGTH_GET_ACCEPTED, outLength );
    TEST_ASSERT_LESS_THAN( bufferSizeExceeded, outLength );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_CLASSIC_TOPIC_BUFFER_MODIFIED,
                                  topicBufferExceeded,
                                  bufferSizeExceeded );

    /* Call Shadow_GetTopicString() with valid parameters, bufferSize = expected outLength
     * and verify result. */
    shadowStatus = Shadow_GetTopicString( ShadowTopicStringTypeGetAccepted,
                                          TEST_THING_NAME,
                                          TEST_THING_NAME_LENGTH,
                                          &( topicBufferGetAccepted[ 0 ] ),
                                          bufferSizeGetAccepted,
                                          &outLength );
    TEST_ASSERT_EQUAL_INT( TEST_CLASSIC_TOPIC_LENGTH_GET_ACCEPTED, outLength );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_CLASSIC_TOPIC_STRING_GET_ACCEPTED,
                                  topicBufferGetAccepted,
                                  bufferSizeGetAccepted );

    for( index = 0U; index < ShadowTopicStringTypeMaxNum; index++ )
    {
        /* Call Shadow_GetTopicString() with valid parameters with all types of topic string
         * and verify result. */
        shadowStatus = Shadow_GetTopicString( topicTypes[ index ],
                                              TEST_THING_NAME,
                                              TEST_THING_NAME_LENGTH,
                                              &( topicBuffer[ 0 ] ),
                                              bufferSize,
                                              &outLength );
        TEST_ASSERT_EQUAL_INT( expectedBuffersSize[ index ], outLength );
        TEST_ASSERT_EQUAL_STRING_LEN( expectedBuffers[ index ],
                                      topicBuffer,
                                      outLength );
    }

    /* Call Shadow_AssembleTopicString() with valid parameters.
     * Use classic shadow by passing NULL for shadow name and 0 for shadow name length. */
    shadowStatus = Shadow_AssembleTopicString( ShadowTopicStringTypeGetAccepted,
                                               TEST_THING_NAME,
                                               TEST_THING_NAME_LENGTH,
                                               NULL,
                                               0,
                                               &( topicBufferGetAccepted[ 0 ] ),
                                               bufferSizeGetAccepted,
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( TEST_CLASSIC_TOPIC_LENGTH_GET_ACCEPTED, outLength );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_CLASSIC_TOPIC_STRING_GET_ACCEPTED,
                                  topicBufferGetAccepted,
                                  bufferSizeGetAccepted );
}

/**
 * @brief Tests the behavior of Shadow_AssembleTopicString() for named shadows, with valid parameters.
 */
void test_Shadow_AssembleTopicString_Named_Happy_Path( void )
{
    ShadowStatus_t shadowStatus = SHADOW_SUCCESS;
    uint16_t outLength = 0U;
    char topicBufferExceeded[ TEST_NAMED_TOPIC_BUFFER_LENGTH ] = TEST_NAMED_TOPIC_BUFFER_INITIALIZE;
    uint16_t bufferSizeExceeded = TEST_NAMED_TOPIC_BUFFER_LENGTH;
    char topicBufferGetAccepted[ SHADOW_TOPIC_LEN_GET_ACC( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) ] = { 0 };
    uint16_t bufferSizeGetAccepted = TEST_NAMED_TOPIC_LENGTH_GET_ACCEPTED;
    char topicBuffer[ SHADOW_TOPIC_LEN_MAX( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH ) ] = { 0 };
    uint16_t bufferSize = SHADOW_TOPIC_LEN_MAX( TEST_THING_NAME_LENGTH, TEST_SHADOW_NAME_LENGTH );
    uint16_t index = 0U;

    /* Lookup table for Shadow message string. */
    static const uint16_t expectedBuffersSize[ ShadowTopicStringTypeMaxNum ] =
    {
        TEST_NAMED_TOPIC_LENGTH_UPDATE,
        TEST_NAMED_TOPIC_LENGTH_UPDATE_ACCEPTED,
        TEST_NAMED_TOPIC_LENGTH_UPDATE_REJECTED,
        TEST_NAMED_TOPIC_LENGTH_UPDATE_DOCUMENTS,
        TEST_NAMED_TOPIC_LENGTH_UPDATE_DELTA,
        TEST_NAMED_TOPIC_LENGTH_GET,
        TEST_NAMED_TOPIC_LENGTH_GET_ACCEPTED,
        TEST_NAMED_TOPIC_LENGTH_GET_REJECTED,
        TEST_NAMED_TOPIC_LENGTH_DELETE,
        TEST_NAMED_TOPIC_LENGTH_DELETE_ACCEPTED,
        TEST_NAMED_TOPIC_LENGTH_DELETE_REJECTED
    };

    /* Lookup table for Shadow message string. */
    static const char * const expectedBuffers[ ShadowTopicStringTypeMaxNum ] =
    {
        TEST_NAMED_TOPIC_STRING_UPDATE,
        TEST_NAMED_TOPIC_STRING_UPDATE_ACCEPTED,
        TEST_NAMED_TOPIC_STRING_UPDATE_REJECTED,
        TEST_NAMED_TOPIC_STRING_UPDATE_DOCUMENTS,
        TEST_NAMED_TOPIC_STRING_UPDATE_DELTA,
        TEST_NAMED_TOPIC_STRING_GET,
        TEST_NAMED_TOPIC_STRING_GET_ACCEPTED,
        TEST_NAMED_TOPIC_STRING_GET_REJECTED,
        TEST_NAMED_TOPIC_STRING_DELETE,
        TEST_NAMED_TOPIC_STRING_DELETE_ACCEPTED,
        TEST_NAMED_TOPIC_STRING_DELETE_REJECTED
    };

    static const ShadowTopicStringType_t topicTypes[ ShadowTopicStringTypeMaxNum ] =
    {
        ShadowTopicStringTypeUpdate,
        ShadowTopicStringTypeUpdateAccepted,
        ShadowTopicStringTypeUpdateRejected,
        ShadowTopicStringTypeUpdateDocuments,
        ShadowTopicStringTypeUpdateDelta,
        ShadowTopicStringTypeGet,
        ShadowTopicStringTypeGetAccepted,
        ShadowTopicStringTypeGetRejected,
        ShadowTopicStringTypeDelete,
        ShadowTopicStringTypeDeleteAccepted,
        ShadowTopicStringTypeDeleteRejected
    };

    /* Call Shadow_AssembleTopicString() with valid parameters but bufferSize exceeds topic string length
     * and verify result. */
    shadowStatus = Shadow_AssembleTopicString( ShadowTopicStringTypeGetAccepted,
                                               TEST_THING_NAME,
                                               TEST_THING_NAME_LENGTH,
                                               TEST_SHADOW_NAME,
                                               TEST_SHADOW_NAME_LENGTH,
                                               &( topicBufferExceeded[ 0 ] ),
                                               bufferSizeExceeded,
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( TEST_NAMED_TOPIC_LENGTH_GET_ACCEPTED, outLength );
    TEST_ASSERT_LESS_THAN( bufferSizeExceeded, outLength );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_NAMED_TOPIC_BUFFER_MODIFIED,
                                  topicBufferExceeded,
                                  bufferSizeExceeded );

    /* Call Shadow_AssembleTopicString() with valid parameters, bufferSize = expected outLength
     * and verify result. */
    shadowStatus = Shadow_AssembleTopicString( ShadowTopicStringTypeGetAccepted,
                                               TEST_THING_NAME,
                                               TEST_THING_NAME_LENGTH,
                                               TEST_SHADOW_NAME,
                                               TEST_SHADOW_NAME_LENGTH,
                                               &( topicBufferGetAccepted[ 0 ] ),
                                               bufferSizeGetAccepted,
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( TEST_NAMED_TOPIC_LENGTH_GET_ACCEPTED, outLength );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_NAMED_TOPIC_STRING_GET_ACCEPTED,
                                  topicBufferGetAccepted,
                                  bufferSizeGetAccepted );

    for( index = 0U; index < ShadowTopicStringTypeMaxNum; index++ )
    {
        /* Call Shadow_AssembleTopicString() with valid parameters with all types of topic string
         * and verify result. */
        shadowStatus = Shadow_AssembleTopicString( topicTypes[ index ],
                                                   TEST_THING_NAME,
                                                   TEST_THING_NAME_LENGTH,
                                                   TEST_SHADOW_NAME,
                                                   TEST_SHADOW_NAME_LENGTH,
                                                   &( topicBuffer[ 0 ] ),
                                                   bufferSize,
                                                   &outLength );
        TEST_ASSERT_EQUAL_INT( expectedBuffersSize[ index ], outLength );
        TEST_ASSERT_EQUAL_STRING_LEN( expectedBuffers[ index ],
                                      topicBuffer,
                                      outLength );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Shadow_AssembleTopicString() with invalid parameters
 */
void test_Shadow_AssembleTopicString_Invalid_Parameters( void )
{
    ShadowStatus_t shadowStatus = SHADOW_SUCCESS;
    uint16_t outLength = 0U;
    ShadowTopicStringType_t topicType = ShadowTopicStringTypeGetAccepted;
    char classicTopicBuffer[ TEST_CLASSIC_TOPIC_LENGTH_GET_ACCEPTED ];
    uint16_t classicBufferSize = TEST_CLASSIC_TOPIC_LENGTH_GET_ACCEPTED;
    char namedTopicBuffer[ TEST_NAMED_TOPIC_LENGTH_GET_ACCEPTED ];
    uint16_t namedBufferSize = TEST_NAMED_TOPIC_LENGTH_GET_ACCEPTED;

    /* Call Shadow_AssembleTopicString() with various combinations of
     * incorrect parameters. */
    shadowStatus = Shadow_AssembleTopicString( 0,
                                               "",
                                               0,
                                               SHADOW_NAME_CLASSIC,
                                               0,
                                               classicTopicBuffer,
                                               classicBufferSize,
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_AssembleTopicString( 0,
                                               NULL,
                                               0,
                                               SHADOW_NAME_CLASSIC,
                                               0,
                                               classicTopicBuffer,
                                               classicBufferSize,
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_AssembleTopicString( topicType,
                                               TEST_THING_NAME,
                                               TEST_THING_NAME_LENGTH,
                                               SHADOW_NAME_CLASSIC,
                                               0,
                                               NULL,
                                               0,
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_AssembleTopicString( ShadowTopicStringTypeMaxNum + 1,
                                               TEST_THING_NAME,
                                               TEST_THING_NAME_LENGTH,
                                               SHADOW_NAME_CLASSIC,
                                               0,
                                               classicTopicBuffer,
                                               classicBufferSize,
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_AssembleTopicString( topicType,
                                               TEST_THING_NAME,
                                               TEST_THING_NAME_LENGTH,
                                               SHADOW_NAME_CLASSIC,
                                               0,
                                               classicTopicBuffer,
                                               classicBufferSize,
                                               NULL );
    TEST_ASSERT_EQUAL_INT( SHADOW_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_AssembleTopicString( topicType,
                                               TEST_THING_NAME,
                                               TEST_THING_NAME_LENGTH,
                                               NULL,
                                               1,
                                               namedTopicBuffer,
                                               namedBufferSize,
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_AssembleTopicString( topicType,
                                               TEST_THING_NAME,
                                               SHADOW_THINGNAME_MAX_LENGTH + 1,
                                               TEST_SHADOW_NAME,
                                               TEST_SHADOW_NAME_LENGTH,
                                               namedTopicBuffer,
                                               namedBufferSize,
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_AssembleTopicString( topicType,
                                               TEST_THING_NAME,
                                               TEST_THING_NAME_LENGTH,
                                               TEST_SHADOW_NAME,
                                               SHADOW_NAME_MAX_LENGTH + 1,
                                               namedTopicBuffer,
                                               namedBufferSize,
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_AssembleTopicString( topicType,
                                               TEST_THING_NAME,
                                               TEST_THING_NAME_LENGTH,
                                               SHADOW_NAME_CLASSIC,
                                               0,
                                               classicTopicBuffer,
                                               0,
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BUFFER_TOO_SMALL, shadowStatus );

    shadowStatus = Shadow_AssembleTopicString( topicType,
                                               TEST_THING_NAME,
                                               TEST_THING_NAME_LENGTH,
                                               SHADOW_NAME_CLASSIC,
                                               0,
                                               classicTopicBuffer,
                                               ( classicBufferSize - 1 ),
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BUFFER_TOO_SMALL, shadowStatus );

    shadowStatus = Shadow_AssembleTopicString( topicType,
                                               TEST_THING_NAME,
                                               TEST_THING_NAME_LENGTH,
                                               TEST_SHADOW_NAME,
                                               TEST_SHADOW_NAME_LENGTH,
                                               namedTopicBuffer,
                                               ( namedBufferSize - 1 ),
                                               &outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BUFFER_TOO_SMALL, shadowStatus );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Shadow_MatchTopicString() for classic shadow with valid parameters. Tests Classic
 * shadows through the deprecated legacy API Shadow_MatchTopic().
 */
void test_Shadow_MatchTopicString_Classic_Happy_Path( void )
{
    ShadowStatus_t shadowStatus = SHADOW_SUCCESS;
    ShadowMessageType_t messageType = ShadowMessageTypeMaxNum;
    const char * pThingName = NULL;
    uint16_t thingNameLength = 0U;
    const char topicBuffer[ TEST_CLASSIC_TOPIC_LENGTH_UPDATE_ACCEPTED ] = TEST_CLASSIC_TOPIC_STRING_UPDATE_ACCEPTED;
    uint16_t bufferSize = TEST_CLASSIC_TOPIC_LENGTH_UPDATE_ACCEPTED;

    /* Call Shadow_MatchTopic() with valid parameters and verify result. */
    shadowStatus = Shadow_MatchTopic( &( topicBuffer[ 0 ] ),
                                      bufferSize,
                                      &messageType,
                                      &pThingName,
                                      &thingNameLength );

    TEST_ASSERT_EQUAL_INT( SHADOW_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( TEST_THING_NAME_LENGTH, thingNameLength );
    TEST_ASSERT_EQUAL_INT( ShadowMessageTypeUpdateAccepted, messageType );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_THING_NAME, pThingName, TEST_THING_NAME_LENGTH );

    shadowStatus = Shadow_MatchTopic( &( topicBuffer[ 0 ] ),
                                      bufferSize,
                                      &messageType,
                                      NULL,
                                      &thingNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( TEST_THING_NAME_LENGTH, thingNameLength );
    TEST_ASSERT_EQUAL_INT( ShadowMessageTypeUpdateAccepted, messageType );

    shadowStatus = Shadow_MatchTopic( &( topicBuffer[ 0 ] ),
                                      bufferSize,
                                      &messageType,
                                      &pThingName,
                                      NULL );
    TEST_ASSERT_EQUAL_INT( SHADOW_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( ShadowMessageTypeUpdateAccepted, messageType );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_THING_NAME, pThingName, TEST_THING_NAME_LENGTH );

    shadowStatus = Shadow_MatchTopic( &( topicBuffer[ 0 ] ),
                                      bufferSize,
                                      &messageType,
                                      NULL,
                                      NULL );
    TEST_ASSERT_EQUAL_INT( SHADOW_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( ShadowMessageTypeUpdateAccepted, messageType );
}

/**
 * @brief Tests the behavior of Shadow_MatchTopicString() for named shadows with valid parameters.
 */
void test_Shadow_MatchTopicString_Named_Happy_Path( void )
{
    ShadowStatus_t shadowStatus = SHADOW_SUCCESS;
    ShadowMessageType_t messageType = ShadowMessageTypeMaxNum;
    const char * pThingName = NULL;
    uint8_t thingNameLength = 0U;
    const char * pShadowName = NULL;
    uint8_t shadowNameLength = 0U;
    const char topicBuffer[ TEST_NAMED_TOPIC_LENGTH_UPDATE_ACCEPTED ] = TEST_NAMED_TOPIC_STRING_UPDATE_ACCEPTED;
    uint16_t bufferSize = TEST_NAMED_TOPIC_LENGTH_UPDATE_ACCEPTED;

    /* Call Shadow_MatchTopicString() with valid parameters and verify result. */
    shadowStatus = Shadow_MatchTopicString( &( topicBuffer[ 0 ] ),
                                            bufferSize,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );

    TEST_ASSERT_EQUAL_INT( SHADOW_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( TEST_THING_NAME_LENGTH, thingNameLength );
    TEST_ASSERT_EQUAL_INT( ShadowMessageTypeUpdateAccepted, messageType );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_THING_NAME, pThingName, TEST_THING_NAME_LENGTH );
    TEST_ASSERT_EQUAL_INT( TEST_SHADOW_NAME_LENGTH, shadowNameLength );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_SHADOW_NAME, pShadowName, TEST_SHADOW_NAME_LENGTH );

    shadowStatus = Shadow_MatchTopicString( &( topicBuffer[ 0 ] ),
                                            bufferSize,
                                            &messageType,
                                            &pThingName,
                                            NULL,
                                            &pShadowName,
                                            &shadowNameLength );

    TEST_ASSERT_EQUAL_INT( SHADOW_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( ShadowMessageTypeUpdateAccepted, messageType );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_THING_NAME, pThingName, TEST_THING_NAME_LENGTH );
    TEST_ASSERT_EQUAL_INT( TEST_SHADOW_NAME_LENGTH, shadowNameLength );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_SHADOW_NAME, pShadowName, TEST_SHADOW_NAME_LENGTH );

    shadowStatus = Shadow_MatchTopicString( &( topicBuffer[ 0 ] ),
                                            bufferSize,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            NULL,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( TEST_THING_NAME_LENGTH, thingNameLength );
    TEST_ASSERT_EQUAL_INT( ShadowMessageTypeUpdateAccepted, messageType );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_THING_NAME, pThingName, TEST_THING_NAME_LENGTH );
    TEST_ASSERT_EQUAL_INT( TEST_SHADOW_NAME_LENGTH, shadowNameLength );

    shadowStatus = Shadow_MatchTopicString( &( topicBuffer[ 0 ] ),
                                            bufferSize,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            NULL );
    TEST_ASSERT_EQUAL_INT( SHADOW_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( TEST_THING_NAME_LENGTH, thingNameLength );
    TEST_ASSERT_EQUAL_INT( ShadowMessageTypeUpdateAccepted, messageType );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_THING_NAME, pThingName, TEST_THING_NAME_LENGTH );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_SHADOW_NAME, pShadowName, TEST_SHADOW_NAME_LENGTH );

    shadowStatus = Shadow_MatchTopicString( &( topicBuffer[ 0 ] ),
                                            bufferSize,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            NULL,
                                            NULL );
    TEST_ASSERT_EQUAL_INT( SHADOW_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( TEST_THING_NAME_LENGTH, thingNameLength );
    TEST_ASSERT_EQUAL_INT( ShadowMessageTypeUpdateAccepted, messageType );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_THING_NAME, pThingName, TEST_THING_NAME_LENGTH );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Shadow_MatchTopicString() with various
 *        invalid parameters
 */
void test_Shadow_MatchTopicString_Invalid_Parameters( void )
{
    ShadowStatus_t shadowStatus = SHADOW_SUCCESS;
    ShadowMessageType_t messageType = ShadowMessageTypeMaxNum;
    const char * pThingName = NULL;
    uint8_t thingNameLength = 0U;
    const char * pShadowName = NULL;
    uint8_t shadowNameLength = 0U;
    const char classicTopicBuffer[ TEST_CLASSIC_TOPIC_LENGTH_UPDATE_ACCEPTED ] = TEST_CLASSIC_TOPIC_STRING_UPDATE_ACCEPTED;
    uint16_t classicBufferSize = TEST_CLASSIC_TOPIC_LENGTH_UPDATE_ACCEPTED;
    const char namedTopicBuffer[ TEST_NAMED_TOPIC_LENGTH_UPDATE_ACCEPTED ] = TEST_NAMED_TOPIC_STRING_UPDATE_ACCEPTED;
    uint16_t namedBufferSize = TEST_NAMED_TOPIC_LENGTH_UPDATE_ACCEPTED;

    /* Call Shadow_MatchTopicString() with various combinations of
     * incorrect parameters. */
    shadowStatus = Shadow_MatchTopicString( NULL,
                                            classicBufferSize,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( classicTopicBuffer,
                                            0,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( classicTopicBuffer,
                                            classicBufferSize,
                                            NULL,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_TOPIC_STRING_INVALID_PREFIX,
                                            TEST_TOPIC_LENGTH_INVALID_PREFIX,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_FAIL, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_TOPIC_STRING_EMPTY_THINGNAME,
                                            TEST_TOPIC_LENGTH_EMPTY_THINGNAME,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_THINGNAME_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_TOPIC_STRING_INVALID_THINGNAME,
                                            TEST_TOPIC_LENGTH_INVALID_THINGNAME,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_THINGNAME_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_TOPIC_STRING_UNTERMINATED_THINGNAME,
                                            TEST_TOPIC_LENGTH_UNTERMINATED_THINGNAME,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_THINGNAME_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_NAMED_TOPIC_STRING_EXCEEDS_MAX_THING_NAME,
                                            TEST_NAMED_TOPIC_LENGTH_EXCEEDS_MAX_THING_NAME,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_THINGNAME_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_TOPIC_STRING_EMPTY_SHADOW_ROOT,
                                            TEST_TOPIC_LENGTH_EMPTY_SHADOW_ROOT,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_ROOT_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_TOPIC_STRING_INVALID_SHADOW_ROOT,
                                            TEST_TOPIC_LENGTH_INVALID_SHADOW_ROOT,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_ROOT_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_NAMED_TOPIC_STRING_EMPTY_SHADOWNAME,
                                            TEST_NAMED_TOPIC_LENGTH_EMPTY_SHADOWNAME,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_SHADOWNAME_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_NAMED_TOPIC_STRING_INVALID_SHADOWNAME,
                                            TEST_NAMED_TOPIC_LENGTH_INVALID_SHADOWNAME,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_SHADOWNAME_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_NAMED_TOPIC_STRING_UNTERMINATED_SHADOWNAME,
                                            TEST_NAMED_TOPIC_LENGTH_UNTERMINATED_SHADOWNAME,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_SHADOWNAME_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_NAMED_TOPIC_STRING_EXCEEDS_MAX_SHADOW_NAME,
                                            TEST_NAMED_TOPIC_LENGTH_EXCEEDS_MAX_SHADOW_NAME,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_SHADOWNAME_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_CLASSIC_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE,
                                            TEST_CLASSIC_TOPIC_LENGTH_EMPTY_SHADOW_MESSAGE_TYPE,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_NAMED_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE,
                                            TEST_NAMED_TOPIC_LENGTH_EMPTY_SHADOW_MESSAGE_TYPE,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_CLASSIC_TOPIC_STRING_INVALID_SHADOW_RESPONSE,
                                            TEST_CLASSIC_TOPIC_LENGTH_INVALID_SHADOW_RESPONSE,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_NAMED_TOPIC_STRING_INVALID_SHADOW_RESPONSE,
                                            TEST_NAMED_TOPIC_LENGTH_INVALID_SHADOW_RESPONSE,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_CLASSIC_TOPIC_STRING_INVALID_GET_REJECTED,
                                            TEST_CLASSIC_TOPIC_LENGTH_INVALID_GET_REJECTED,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( TEST_NAMED_TOPIC_STRING_INVALID_GET_REJECTED,
                                            TEST_NAMED_TOPIC_LENGTH_INVALID_GET_REJECTED,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( classicTopicBuffer,
                                            classicBufferSize - 1,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( namedTopicBuffer,
                                            namedBufferSize - 1,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( classicTopicBuffer,
                                            classicBufferSize + 1,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopicString( namedTopicBuffer,
                                            namedBufferSize + 1,
                                            &messageType,
                                            &pThingName,
                                            &thingNameLength,
                                            &pShadowName,
                                            &shadowNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );
}

/*-----------------------------------------------------------*/
