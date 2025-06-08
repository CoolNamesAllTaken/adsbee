/*
 * SigV4 Library v1.3.0
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#include <string.h>
#include <stdlib.h>
#include <openssl/sha.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "sigv4.h"
/* We include the internal SigV4 macros so that they don't have to be redefined for these tests. */
#include "sigv4_internal.h"

#define STR_LIT_LEN( LIT )    ( sizeof( LIT ) - 1U )

/* The number of invalid date inputs tested in
 * test_SigV4_AwsIotDateToIso8601_Formatting_Error() */
#define SIGV4_TEST_INVALID_DATE_COUNT                         24U

#define AUTH_BUF_LENGTH                                       1000

#define PATH                                                  "/"
#define PRECANON_PATH                                         "/path-%20"

/* Iterator must not read beyond the null-terminator. */
#define NULL_TERMINATED_PATH                                  "/pa\0th"
#define NULL_TERMINATED_PATH_LEN                              ( sizeof( NULL_TERMINATED_PATH ) - 1U )
/* An equal in the query string value must be double-encoded. */
#define QUERY_VALUE_HAS_EQUALS                                "quantum==value"
/* A query string with parameter count exceeding SIGV4_MAX_HTTP_HEADER_COUNT=5. */
#define QUERY_GT_MAX_PARAMS                                   "params&allowed&to&have&no&values"

/* Query strings that represent different cases matching parameter names and values */
#define QUERY_MATCHING_PARAMS                                 "param=value2&param=value1&param1=test"
#define QUERY_MATCHING_PARAMS_AND_MATCHING_VALUES_PREFIX_1    "param=valueXY&param=value&param1=test"
#define QUERY_MATCHING_PARAMS_AND_MATCHING_VALUES_PREFIX_2    "param=value&param=valueXY&param1=test"
#define QUERY_MATCHING_PARAMS_AND_VALUES                      "param=valueXY&param=valueXY&param1=test"
#define QUERY_WITH_MATCHING_PARAM_PREFIX                      "para=value1&param1=&value2&param=value3"

/* Examples of Query Strings containing non-alphanumeric characters. */
#define QUERY_WITH_NON_ALPHA_NUMBERIC_CHARS                   "param=-_.~/"
#define QUERY_WITH_SPECIAL_CHARS                              "param=/"

#define QUERY_STRING_NO_PARAM_VALUE                           "param=&param2="
#define QUERY_STRING_WITH_TRAILING_N_LEADING_AMPERSAND        "&&param2=&&"
#define QUERY_STRING_WITH_REPEATED_AMPERSAND                  "param1=val&&param2=val"

#define QUERY                                                 "Action=ListUsers&Version=2010-05-08"
#define QUERY_LENGTH                                          ( sizeof( QUERY ) - 1U )
#define ACCESS_KEY_ID                                         "AKIAIOSFODNN7EXAMPLE"
#define SECRET_KEY                                            "wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY"
#define SECRET_KEY_LEN                                        ( sizeof( SECRET_KEY ) - 1U )
#define SECRET_KEY_LONGER_THAN_HASH_BLOCK                     "wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEYwJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEYwJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEYwJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY"
#define SECRET_KEY_LONGER_THAN_HASH_BLOCK_LEN                 ( sizeof( SECRET_KEY_LONGER_THAN_HASH_BLOCK ) - 1U )
#define DATE                                                  "20210811T001558Z"
#define REGION                                                "us-east-1"
#define SERVICE                                               "iam"
#define HEADERS                                               "Host: iam.amazonaws.com\r\nContent-Type: application/x-www-form-urlencoded; charset=utf-8\r\nX-Amz-Date: "DATE "\r\n\r\n"
#define HEADERS_LENGTH                                        ( sizeof( HEADERS ) - 1U )
#define PRECANON_HEADER                                       "content-type:application/json;\nhost:iam.amazonaws.com\n"
#define HEADERS_WITH_X_AMZ_CONTENT_SHA256                     "Host: iam.amazonaws.com\r\nContent-Type: application/x-www-form-urlencoded; charset=utf-8\r\nx-amz-content-sha256: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\r\nX-Amz-Date: "DATE "\r\n\r\n"
#define HEADERS_WITHOUT_X_AMZ_CONTENT_SHA256                  "Host: iam.amazonaws.com\r\nContent-Type: application/x-www-form-urlencoded; charset=utf-8\r\nx-amz-content-sha512: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\r\nX-Amz-Date: "DATE "\r\n\r\n"

/* Header data containing leading, trailing and sequential trimmable spaces. */
#define HEADERS_WITH_TRIMMABLE_SPACES                         "  Header-1 :  Value \t - \t 1  \r\n"

/* Examples with more header pairs than SIGV4_MAX_HTTP_HEADER_COUNT=5. */
#define PRECAN_HEADERS_PAIRS_GT_THAN_MAX                      "H1:a\nH2:b\nH3:c\nH4:d\nH5:e\nH6:\nH7:\nH8:\n"
#define HEADERS_PAIRS_GT_THAN_MAX                             "H1:a\r\nH2:b\r\nH3:c\r\nH4:d\r\nH5:e\r\nH6:\r\nH7:\r\n:H8:\r\n\r\n"

/* Examples of invalid HTTP headers data. */
#define INVALID_HEADERS_NO_HEADER_VAL                         "Header1: Value1\r\nHeader2: Value2\n"
#define INVALID_HEADERS_NO_HEADER_KEY                         "Header=Value\r\n"
#define INVALID_PRECANON_HEADERS_NO_HEADER_KEY                "Header=Value\n"

#define HEADERS_SORTED_COVERAGE_1                             "A:a\r\nB:b\r\nC:c\r\nE:e\r\nF:f\r\nD:d\r\n\r\n"
#define HEADERS_SORTED_COVERAGE_2                             "A:a\r\nC:c\r\nE:e\r\nF:f\r\nD:d\r\n\r\n"


#define STRING_TO_SIGN_LEN_WITH_DEFAULT_REGION                              \
    SIGV4_AWS4_HMAC_SHA256_LENGTH + 1U +                                    \
    SIGV4_ISO_STRING_LEN + 1U +                                             \
    ISO_DATE_SCOPE_LEN +                                                    \
    CREDENTIAL_SCOPE_SEPARATOR_LEN + sizeof( REGION ) - 1U +                \
    CREDENTIAL_SCOPE_SEPARATOR_LEN + sizeof( SERVICE ) - 1U +               \
    CREDENTIAL_SCOPE_SEPARATOR_LEN + CREDENTIAL_SCOPE_TERMINATOR_LEN + 1U + \
    SIGV4_HASH_MAX_DIGEST_LENGTH * 2

#define EXPECTED_AUTH_DATA_NOMINAL
#define EXPECTED_AUTH_DATA_SECRET_KEY_LONGER_THAN_DIGEST

/* Insufficient memory parameters for SIGV4_PROCESSING_BUFFER_LENGTH=350. In the comments below,
 * + means concatenation, OOM means "Out of Memory", LF means newline character */

/* HTTP method + URI-encoded variant of this string must be greater than SIGV4_PROCESSING_BUFFER_LENGTH. */
#define PATH_FIRST_ENCODE_OOM                                                           \
    "/path-to-victory-will-soon-come-to-a-close-and-then-we-can-finally-eat-our-errors" \
    "-even-though-this-is-not-a-good-practice-at-all-so-obviously-this-is-just-a-joke-" \
    "so-why-are-you-still-reading-this-i-mean-im-crazy-enough-to-type-this-very-"       \
    "long-string-instead-of-using-a-lorem-ipsum-website-maybe-i-should-be-a-comedian-"  \
    "instead-be-a-programmer-really"
/* HTTP method + URI-encoded variant of this string + \n must be greater than SIGV4_PROCESSING_BUFFER_LENGTH. */
#define PATH_FIRST_ENCODE_AND_LF_OOM                                                    \
    "/path-to-victory-will-soon-come-to-a-close-and-then-we-can-finally-eat-our-errors" \
    "-even-though-this-is-not-a-good-practice-at-all-so-obviously-this-is-just-a-joke-" \
    "so-why-are-you-still-reading-this-i-mean-im-crazy-enough-to-type-this-very-xchjsd" \
    "chjdsvchjdvhjcdhjsckhdsvchdks-sfdghfdfahgsdhfgjsgfjkgfsdgkdgfdjkgdggdjfsjkgjksgkj" \
    "sdgfdfgdshfgsjdhfdhfkhdkfhjdgfgdfgdfg-sdvfdvfhdvfhvdhfvdsfdsgfgdsjfgjdsfqwertyuio" \
    "pasdfghwsshasdfghjk"

/* HTTP method + this URI-encoded variant of this string + double-encoded variant must be greater than SIGV4_PROCESSING_BUFFER_LENGTH. */
#define PATH_SECOND_ENCODE_OOM    "/path-to-victory-will-soon-come-to-a-close-and-then-we-can-finally-eat-our-errors-even-though-this-is-not-a-good-practice-at-all-so-obviously-this-is-just-a-joke-so-why-are-you-still-reading-this-i-mean-im-crazy-enough-to-type-this-very-long-string-instead-of-using-a-lorem-ipsum-website-maybe-i-should-be-a-comedian-instead"

/* Encoding query string field in canonicalized query string causes OOM. */
#define QUERY_ENCODE_FIELD_OOM                                                          \
    "path-to-victory-will-soon-come-to-a-close-and-then-we-can-finally-eat-our-errors"  \
    "-even-though-this-is-not-a-good-practice-at-all-so-obviously-this-is-just-a-joke-" \
    "so-why-are-you-still-&m=reading-this-i-mean-im-crazy-enough-to-type-this-very-"    \
    "long-string-instead-of-using-a-lorem-ipsum-website-maybe-i-should-be-a-comedian-"  \
    "instead-be-a-programmer-reall&ymxchykldfghiwbdcjhjdddkkgddsdhshdkshdhsskgfkjgfggc" \
    "gjfhjxgxghsgfdwfdfdfdffhfdhdhfhdfhd=3"

/* '=' before query string value in canonicalized query string causes OOM. */
#define QUERY_EQUAL_BEFORE_VALUE_OOM                                                      \
    "VwngXGfGGHUJcXAyjrfZapvWrAizcaCSSzWFgWVajgcHvPjiypSRThwgvGicnakSutzyFUNpFPXTtGp"     \
    "XNNdzbbpmapMikCuizEKHXLqWWXwHbLhDRajbw"                                              \
    "mlkzxncvlknlkanlkqwlerknlasdflkzxcnvklnlksqwerasdfklqwenrklnfsad"                    \
    "reading-this-i-mean-im-crazy-enough-to-type-this-very-qCdrPnpyimHMDLPcQwxhNGYYTyyUG" \
    "cApPMQygPCRMeVHpxdrFycVuEGZaFtGvdTXgMnPbzWvGNhLkecRqFGBgza=3"

/* '&' before next query string field in canonicalized query string causes OOM. */
#define QUERY_AMPERSAND_BEFORE_FIELD_OOM                                                  \
    "VwngXGfGGHUJcXAyjrfZapvWrAizcaCSSzWFgWVajgcHvPjiypSRThwgvGicnakSutzyFUNpFPXTtGp"     \
    "XNNdzbbpmapMikCuizEKHXLqWWXwHbLhDRajbw"                                              \
    "mlkzxncvlknlkanlkqwlerknlasdflkzxcnvklnlksqwerasdfklqwenrklnfsad"                    \
    "reading-this-i-mean-im-crazy-enough-to-type-this-very-qCdrPnpyimHMDLPcQwxhNGYYTyyUG" \
    "cApPMQygPCRMeVHpxdrFycVuEGZaFtGvdTXgMnPbzWvGNhLkecRqFGBg=3&a"

/* Encoding query string value in canonicalized query string causes OOM. */
#define QUERY_ENCODE_VALUE_OOM                                                                       \
    "hello-world&y=path-to-victory-will-soon-come-to-a-close-and-then-we-can-finally-eat-our-errors" \
    "-even-though-this-is-not-a-good-practice-at-all-so-obviously-this-is-just-a-joke-"              \
    "so-why-are-you-still-&m=reading-this-i-mean-im-crazy-enough-to-type-this-very-"                 \
    "long-string-instead-of-using-a-lorem-ipsum-website-maybe-i-should-be-a-comedian-"               \
    "instead-be-a-programmer-reall"

/* Precanonicalized query string causes OOM. */
#define PRECANON_QUERY_TOO_LONG                                                                                              \
    "wnqjNXBkZXXQvpwaHryRkLQuCQnMqQYAaXLFAUQGCnpbfiBUHkJKWgvGbUGrEcjuveUijcfxvFvUXKcedDbHwSdWqTTeLRwnVZapMEKrYprSdYgVGzSUG=" \
    "wnqjNXBkZXXQvpwaHryRkLQuCQnMqQYAaXLFAUQGCnpbfiBUHkJKWgvGbUGrEcjuveUijcfxvFvUXKcedDbHwSdWqTTeLRwnVZapMEKrYprSdYgVGzSUG&" \
    "wnqjNXBkZXXQvpwaHryRkLQuCQnMqQYAaXLFAUQGCnpb=fiBUHkJKWgvGbUGrEcjuveUijcfxvFvUXKcedDbHwSdWqTTeLRwnVZapMEKrYprSdYgVGzSUG" \

/* File-scoped global variables */
static char pTestBufferValid[ SIGV4_ISO_STRING_LEN ] = { 0 };

/* Input parameters. */
static SigV4Parameters_t params;
static SigV4HttpParameters_t httpParams;
static SigV4CryptoInterface_t cryptoInterface;
static SigV4Credentials_t creds;
static SHA256_CTX sha256;

static char authBuf[ AUTH_BUF_LENGTH ];
static size_t authBufLen = AUTH_BUF_LENGTH;
static char * signature = NULL;
static size_t signatureLen;

/* ============================ HELPER FUNCTIONS ============================ */

/**
 * @brief Format a date input with SigV4_AwsIotDateToIso8601(), and verify the
 * output against the expected result, if no errors occurred.
 */
void formatAndVerifyInputDate( const char * pInputDate,
                               SigV4Status_t expectedStatus,
                               const char * pExpectedOutputDate )
{
    TEST_ASSERT_NOT_NULL( pInputDate );

    SigV4Status_t returnVal = SigV4_AwsIotDateToIso8601( pInputDate,
                                                         strlen( pInputDate ),
                                                         pTestBufferValid,
                                                         SIGV4_ISO_STRING_LEN );

    TEST_ASSERT_EQUAL( expectedStatus, returnVal );

    if( returnVal == SigV4Success )
    {
        TEST_ASSERT_NOT_NULL( pExpectedOutputDate );
        TEST_ASSERT_EQUAL_STRING_LEN( pExpectedOutputDate,
                                      pTestBufferValid,
                                      SIGV4_ISO_STRING_LEN );
    }

    tearDown();
}

/*==================== OpenSSL Based implementation of Crypto Interface ===================== */

static int32_t valid_sha256_init( void * pHashContext )
{
    if( SHA256_Init( ( SHA256_CTX * ) pHashContext ) == 1 )
    {
        return 0;
    }

    return -1;
}

static int32_t valid_sha256_update( void * pHashContext,
                                    const uint8_t * pInput,
                                    size_t inputLen )
{
    if( SHA256_Update( ( SHA256_CTX * ) pHashContext, pInput, inputLen ) )
    {
        return 0;
    }

    return -1;
}

static int32_t valid_sha256_final( void * pHashContext,
                                   uint8_t * pOutput,
                                   size_t outputLen )
{
    ( void ) outputLen;

    if( SHA256_Final( ( uint8_t * ) pOutput, ( SHA256_CTX * ) pHashContext ) )
    {
        return 0;
    }

    return -1;
}

/*==================== Failable Implementation of Crypto Interface ===================== */

#define HASH_ERROR_BRANCH_COVERAGE_ITERATIONS    12U

static size_t hashInitCalledCount = 0U, hashInitCallToFail = SIZE_MAX;
static size_t updateHashCalledCount = 0U, updateHashCallToFail = SIZE_MAX;
static size_t finalHashCalledCount = 0U, finalHashCallToFail = SIZE_MAX;

static int32_t hash_init_failable( void * pHashContext )
{
    ( void ) pHashContext;

    int32_t ret = 0;

    if( hashInitCalledCount++ == hashInitCallToFail )
    {
        ret = 1;
    }

    return ret;
}

static int32_t hash_update_failable( void * pHashContext,
                                     const uint8_t * pInput,
                                     size_t inputLen )
{
    ( void ) pHashContext;
    ( void ) pInput;
    ( void ) inputLen;

    int32_t ret = 0;

    if( updateHashCalledCount++ == updateHashCallToFail )
    {
        ret = 1;
    }

    return ret;
}

static int32_t hash_final_failable( void * pHashContext,
                                    uint8_t * pOutput,
                                    size_t outputLen )
{
    ( void ) pHashContext;
    ( void ) pOutput;
    ( void ) outputLen;

    int32_t ret = 0;

    if( finalHashCalledCount++ == finalHashCallToFail )
    {
        ret = 1;
    }

    return ret;
}

/*============================ Test Helpers ========================== */

static void resetFailableHashParams()
{
    hashInitCalledCount = 0U;
    hashInitCallToFail = SIZE_MAX;
    updateHashCalledCount = 0U;
    updateHashCallToFail = SIZE_MAX;
    finalHashCalledCount = 0U;
    finalHashCallToFail = SIZE_MAX;

    params.pCryptoInterface->hashInit = hash_init_failable;
    params.pCryptoInterface->hashUpdate = hash_update_failable;
    params.pCryptoInterface->hashFinal = hash_final_failable;
}

static void resetInputParams()
{
    /* Fill the input parameters with the happy path. */
    memset( &params, 0, sizeof( params ) );
    memset( &httpParams, 0, sizeof( httpParams ) );
    memset( &cryptoInterface, 0, sizeof( cryptoInterface ) );
    memset( &creds, 0, sizeof( creds ) );
    memset( &sha256, 0, sizeof( sha256 ) );
    memset( authBuf, 0, AUTH_BUF_LENGTH );
    authBufLen = AUTH_BUF_LENGTH;
    signature = NULL;
    httpParams.pHttpMethod = "GET";
    httpParams.httpMethodLen = 3;
    httpParams.pPath = PATH;
    httpParams.pathLen = sizeof( PATH ) - 1U;
    httpParams.pQuery = QUERY;
    httpParams.queryLen = QUERY_LENGTH;
    httpParams.flags = 0;
    httpParams.pHeaders = HEADERS;
    httpParams.headersLen = HEADERS_LENGTH;
    httpParams.pPayload = NULL;
    httpParams.payloadLen = 0U;
    params.pHttpParameters = &httpParams;
    creds.pAccessKeyId = ACCESS_KEY_ID;
    creds.accessKeyIdLen = sizeof( ACCESS_KEY_ID ) - 1U;
    creds.pSecretAccessKey = SECRET_KEY;
    creds.secretAccessKeyLen = SECRET_KEY_LEN;
    params.pAlgorithm = SIGV4_AWS4_HMAC_SHA256;
    params.algorithmLen = SIGV4_AWS4_HMAC_SHA256_LENGTH;
    params.pCredentials = &creds;
    params.pDateIso8601 = DATE;
    params.pRegion = REGION;
    params.regionLen = sizeof( REGION ) - 1U;
    params.pService = SERVICE;
    params.serviceLen = sizeof( SERVICE ) - 1U;
    cryptoInterface.pHashContext = &sha256;
    cryptoInterface.hashInit = valid_sha256_init;
    cryptoInterface.hashUpdate = valid_sha256_update;
    cryptoInterface.hashFinal = valid_sha256_final;
    cryptoInterface.hashBlockLen = SIGV4_HASH_MAX_BLOCK_LENGTH;
    cryptoInterface.hashDigestLen = SIGV4_HASH_MAX_DIGEST_LENGTH;
    params.pCryptoInterface = &cryptoInterface;
}

/* ============================ UNITY FIXTURES ============================== */

/* Called before each test method. */
void setUp()
{
    resetInputParams();
}

/* Called after each test method. */
void tearDown()
{
    memset( &pTestBufferValid, 0, sizeof( pTestBufferValid ) );
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

/* ==================== Testing SigV4_AwsIotDateToIso8601 =================== */

/**
 * @brief Test happy path with zero-initialized and adequately sized input and
 * output buffers.
 */
void test_SigV4_AwsIotDateToIso8601_Happy_Path()
{
    /* Test unformatted inputs against their final expected values, in both RFC
     * 3339 and 5322 formats. */
    /* Valid non-leap year date. */
    formatAndVerifyInputDate( "2018-01-18T09:18:06Z",
                              SigV4Success,
                              "20180118T091806Z" );

    formatAndVerifyInputDate( "Wed, 18 Jan 2018 09:18:06 GMT",
                              SigV4Success,
                              "20180118T091806Z" );

    /* Valid leap year date (not divisible by 400). */
    formatAndVerifyInputDate( "2004-02-29T11:04:59Z",
                              SigV4Success,
                              "20040229T110459Z" );

    formatAndVerifyInputDate( "Sun, 29 Feb 2004 11:04:59 GMT",
                              SigV4Success,
                              "20040229T110459Z" );

    /* Valid leap year date (divisible by 400, a property of leap years). */
    formatAndVerifyInputDate( "2000-02-29T11:04:59Z",
                              SigV4Success,
                              "20000229T110459Z" );

    formatAndVerifyInputDate( "Tue, 29 Feb 2000 11:04:59 GMT",
                              SigV4Success,
                              "20000229T110459Z" );
}

/**
 * @brief Test NULL and invalid parameters.
 */
void test_SigV4_AwsIotDateToIso8601_Invalid_Params()
{
    /* Output buffer of insufficient length. */
    char testBufferShort[ SIGV4_ISO_STRING_LEN - 1U ] = { 0 };

    /* Test pDate == NULL. */
    SigV4Status_t returnVal = SigV4_AwsIotDateToIso8601( NULL,
                                                         SIGV4_EXPECTED_LEN_RFC_3339,
                                                         pTestBufferValid,
                                                         SIGV4_ISO_STRING_LEN );

    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnVal );
    tearDown();

    /* Test pDateISO8601 == NULL. */
    returnVal = SigV4_AwsIotDateToIso8601( "2018-01-18T09:18:06Z",
                                           SIGV4_EXPECTED_LEN_RFC_3339,
                                           NULL,
                                           SIGV4_ISO_STRING_LEN );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnVal );

    /* Test dateISO8601Len < SIGV4_ISO_STRING_LEN. */
    returnVal = SigV4_AwsIotDateToIso8601( "Wed, 18 Jan 2018 09:18:06 GMT",
                                           SIGV4_EXPECTED_LEN_RFC_5322,
                                           testBufferShort,
                                           SIGV4_ISO_STRING_LEN - 1U );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnVal );

    /* There are no 'expected output values' for invalid parameters, as
     * SigV4_AwsIotDateToIso8601() will return with an error prior to any
     * further execution. */
    /* dateLen < SIGV4_EXPECTED_LEN_RFC_3339. */
    formatAndVerifyInputDate( "2018-01T09:18Z",
                              SigV4InvalidParameter,
                              NULL );

    /* dateLen > SIGV4_EXPECTED_LEN_RFC_3339 */
    formatAndVerifyInputDate( "2018-01-18T09:18:06Z00:00",
                              SigV4InvalidParameter,
                              NULL );

    /* dateLen < SIGV4_EXPECTED_LEN_RFC_5322 */
    formatAndVerifyInputDate( "Wed, 18 Jan 2018 09:18:06",
                              SigV4InvalidParameter,
                              NULL );

    /* dateLen > SIGV4_EXPECTED_LEN_RFC_5322 */
    formatAndVerifyInputDate( "Wed, 18 Jan 2018 09:18:06 GMT+8",
                              SigV4InvalidParameter,
                              NULL );
}

/**
 * @brief Test valid input parameters representing invalid dates.
 */
void test_SigV4_AwsIotDateToIso8601_Formatting_Error()
{
    size_t index = 0U;

    /* Test parameters of acceptable size and format, with flawed date
     * representations, in both RFC3339 and RFC5322 form. */
    const char * pInvalidDateInputs[] =
    {
        "1776-01-18T09:18:06Z", "Thu, 18 Jan 1776 09:18:06 GMT", /* year < YEAR_MIN */
        "2018-00-18T03:21:09Z", "Wed, 18 Air 2018 09:18:06 GMT", /* month < 1 */
        "2018-15-18T03:21:09Z", "Wed, 18 a01 2018 09:18:06 GMT", /* month > 12 */
        "2018-01-00T03:21:09Z", "Mon, 31 Feb 2018 09:18:06 GMT", /* day < 1 */
        "1973-09-31T23:59:59Z", "Mon, 31 Sep 1973 23:59:59 GMT", /* day > days in month (28-31) */
        "1998-02-29T03:21:09Z", "Thu, 29 Feb 1900 09:18:06 GMT", /* Leap day in a non-leap year. */
        "2018-01-18T25:18:06Z", "Wed, 18 Jan 2018 61:18:06 GMT", /* hour > 23 */
        "1800-02-28T03:61:09Z", "Wed, 18 Jan 2018 09:99:06 GMT", /* minute > 59 */
        "1800-01-29T03:21:70Z", "Wed, 18 Jan 2018 09:18:75 GMT", /* seconds > 60 */
        "2018-01-18X09:18:06Z", "Wed. 31 Apr 2018T09:18:06 GMT", /* Unexpected character 'X'. */
        "2018-01-1@X09:18:06Z", "Wed. 31 Apr 2018T0A:18:06 GMT", /* Unexpected non-digit found in date element. */
        "2018-01-1!X09:18:06Z", "Wed. 31 Apr 2018T!9:18:06 GMT"  /* Unexpected non-digit found in date element. */
    };

    for( index = 0U; index < SIGV4_TEST_INVALID_DATE_COUNT - 1; index += 2 )
    {
        /* Test equivalent RFC 3339 and RFC 5322 representations of an invalid
         * date, and ensure that a formatting error code is received. */
        formatAndVerifyInputDate( pInvalidDateInputs[ index ], SigV4ISOFormattingError, NULL );
        formatAndVerifyInputDate( pInvalidDateInputs[ index + 1 ], SigV4ISOFormattingError, NULL );
    }
}

/* ======================= Testing SigV4_GenerateHTTPAuthorization =========================== */

void test_SigV4_GenerateHTTPAuthorization_Invalid_Params()
{
    SigV4Status_t returnStatus;

    /******* All cases of NULL input parameters. ******/
    returnStatus = SigV4_GenerateHTTPAuthorization( NULL, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, NULL, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, NULL, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, NULL, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, NULL );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    /******** All cases of invalid HTTP parameters. *********/
    resetInputParams();
    params.pHttpParameters = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pHttpParameters->pHttpMethod = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
    resetInputParams();
    params.pHttpParameters->httpMethodLen = 0U;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pHttpParameters->pHeaders = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
    resetInputParams();
    params.pHttpParameters->headersLen = 0U;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    /******** All cases of invalid Credential Parameters. *********/
    resetInputParams();
    params.pCredentials = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pCredentials->pAccessKeyId = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
    resetInputParams();
    params.pCredentials->accessKeyIdLen = 0U;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pCredentials->pSecretAccessKey = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
    resetInputParams();
    params.pCredentials->secretAccessKeyLen = 0U;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    /******** All cases of invalid Crypto interface members. *********/
    resetInputParams();
    params.pCryptoInterface = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pCryptoInterface->hashInit = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pCryptoInterface->hashUpdate = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pCryptoInterface->hashFinal = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pCryptoInterface->hashBlockLen = SIGV4_HASH_MAX_BLOCK_LENGTH + 1;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pCryptoInterface->hashDigestLen = SIGV4_HASH_MAX_DIGEST_LENGTH + 1;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    /******** All remaining cases of invalid SigV4Params_t members. *********/
    resetInputParams();
    params.pDateIso8601 = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pRegion = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
    resetInputParams();
    params.regionLen = 0U;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pService = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
    resetInputParams();
    params.serviceLen = 0U;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );

    resetInputParams();
    params.pAlgorithm = "Test-Algo";
    params.algorithmLen = 0U;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
}

void test_SigV4_GenerateHTTPAuthorization_Happy_Paths()
{
    SigV4Status_t returnStatus;

    const char * pExpectedSignature = "20fdb62349e7104f9ce4184a444fedfbd19e40a5e31d57d433689c5a5138fa99";

    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    TEST_ASSERT_EQUAL_MEMORY( pExpectedSignature, signature, signatureLen );

    /* Attempt to generate the signature with a secret longer than the digest length. This
     * causes the inner-most HMAC key of the signing key to be hashed down. */
    creds.pSecretAccessKey = SECRET_KEY_LONGER_THAN_HASH_BLOCK;
    creds.secretAccessKeyLen = SECRET_KEY_LONGER_THAN_HASH_BLOCK_LEN;
    pExpectedSignature = "842f14580889c0d25727eee03310b17dcb3811a2e915172ba2f0db42a6c5b0e8";
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    TEST_ASSERT_EQUAL_MEMORY( pExpectedSignature, signature, signatureLen );

    /* Test case when the first step of the Signing Key generation HMAC operation encounters a key that is
     * less than hash block in length. */
    char secretKeyGeneratingBlockLenHMACKey[ SIGV4_HASH_MAX_BLOCK_LENGTH - strlen( SIGV4_HMAC_SIGNING_KEY_PREFIX ) ];

    memset( secretKeyGeneratingBlockLenHMACKey, ( int ) 'K', sizeof( secretKeyGeneratingBlockLenHMACKey ) );
    creds.pSecretAccessKey = secretKeyGeneratingBlockLenHMACKey;
    creds.secretAccessKeyLen = sizeof( secretKeyGeneratingBlockLenHMACKey );
    pExpectedSignature = "35a27666bdb88c391c47017927d4f9bd5b7c7dbc63b1ab348b4ee73f1ff3cdb2";
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    TEST_ASSERT_EQUAL_MEMORY( pExpectedSignature, signature, signatureLen );

    /* S3 is the only service in which the URI is only encoded once. */
    params.serviceLen = S3_SERVICE_NAME_LEN;
    params.pService = S3_SERVICE_NAME;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    printf( "%.*s\n", ( int ) ( authBufLen ), authBuf );

    /* Coverage for the case where the service name has the same length as "s3". */
    params.serviceLen = S3_SERVICE_NAME_LEN;
    params.pService = SERVICE;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    printf( "%.*s\n", ( int ) ( authBufLen ), authBuf );

    /* Coverage for the null-terminated path. */
    resetInputParams();
    params.pHttpParameters->pPath = NULL_TERMINATED_PATH;
    params.pHttpParameters->pathLen = NULL_TERMINATED_PATH_LEN;
    pExpectedSignature = "81bb660522155dc9038c37c2fbcbc7379d7eb8a987d6e42ac10bf08b1c37db1e";
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    TEST_ASSERT_EQUAL_MEMORY( pExpectedSignature, signature, signatureLen );

    /* Coverage for double-encoded equals in query string value. */
    resetInputParams();
    params.pHttpParameters->pQuery = QUERY_VALUE_HAS_EQUALS;
    params.pHttpParameters->queryLen = STR_LIT_LEN( QUERY_VALUE_HAS_EQUALS );
    pExpectedSignature = "2e005dbe8d1223309467fc3f3b14310110bd45358a4f598e9f5e32723036461d";
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    TEST_ASSERT_EQUAL_MEMORY( pExpectedSignature, signature, signatureLen );

    /* Coverage for NON double-encoded equals in query string value for presigned URL. */
    resetInputParams();
    params.pHttpParameters->pQuery = QUERY_VALUE_HAS_EQUALS;
    params.pHttpParameters->queryLen = STR_LIT_LEN( QUERY_VALUE_HAS_EQUALS );
    params.pHttpParameters->flags = SIGV4_HTTP_IS_PRESIGNED_URL;
    pExpectedSignature = "6759e09cf532c4f9b5190873cb4c43305180f5d4d3418d65b6c0affce827dbc4";
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    TEST_ASSERT_EQUAL_MEMORY( pExpectedSignature, signature, signatureLen );
}

/* Test the API for handling corner cases of sorting the Query Parameters (when generating Canonical Query) */
void test_SigV4_GenerateHTTPAuthorization_Sorting_Query_Params_Corner_Cases()
{
    SigV4Status_t returnStatus;

    /* Test when the query string contains query parameters with exactly matching names. */
    params.pHttpParameters->pQuery = QUERY_MATCHING_PARAMS;
    params.pHttpParameters->queryLen = strlen( QUERY_MATCHING_PARAMS );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );

    /* Test when the query string contains query parameters which do not match in name length but match in
     * the name data for the common length between 2 parameters. */
    params.pHttpParameters->pQuery = QUERY_WITH_MATCHING_PARAM_PREFIX;
    params.pHttpParameters->queryLen = strlen( QUERY_WITH_MATCHING_PARAM_PREFIX );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );

    /* Test when the query string contains query parameters with exactly matching parameter names as well
     * as matching values for those parameters. The query values of matching parameters differ in length though. */
    params.pHttpParameters->pQuery = QUERY_MATCHING_PARAMS_AND_MATCHING_VALUES_PREFIX_1;
    params.pHttpParameters->queryLen = strlen( QUERY_MATCHING_PARAMS_AND_MATCHING_VALUES_PREFIX_1 );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
    params.pHttpParameters->pQuery = QUERY_MATCHING_PARAMS_AND_MATCHING_VALUES_PREFIX_2;
    params.pHttpParameters->queryLen = strlen( QUERY_MATCHING_PARAMS_AND_MATCHING_VALUES_PREFIX_2 );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );

    /* Test when the query string contains query parameters with exactly matching parameter names as well
     * as matching values for those parameters. The query values of matching parameters differ in length though. */
    params.pHttpParameters->pQuery = QUERY_MATCHING_PARAMS_AND_VALUES;
    params.pHttpParameters->queryLen = strlen( QUERY_MATCHING_PARAMS_AND_VALUES );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
}

/* Test that the library can handle HTTP headers data containing trimmable spaces. */
void test_SigV4_GenerateAuthorization_Headers_With_Trimmable_Spaces()
{
    params.pHttpParameters->pHeaders = HEADERS_WITH_TRIMMABLE_SPACES;
    params.pHttpParameters->headersLen = strlen( HEADERS_WITH_TRIMMABLE_SPACES );

    const char * pExpectedSignature = "41dfba73a35f6cff18fc02e991f6499d4e0fb1209a4d42e9155a623ae0f36831";

    TEST_ASSERT_EQUAL( SigV4Success, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    TEST_ASSERT_EQUAL_MEMORY( pExpectedSignature, signature, signatureLen );
}

/* Test that the library can handle query string that contains empty values for its parameters. */
void test_SigV4_GenerateAuthorization_Query_Strings_Special_Cases()
{
    params.pHttpParameters->pQuery = QUERY_STRING_NO_PARAM_VALUE;
    params.pHttpParameters->queryLen = strlen( QUERY_STRING_NO_PARAM_VALUE );

    const char * pExpectedSignature = "9eed8862e36ac9861f0ea0be863ef6d825de854c8eb9da072637dcc64e5ef919";

    TEST_ASSERT_EQUAL( SigV4Success, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    printf( "%.*s\n", ( int ) ( authBufLen ), authBuf );
    TEST_ASSERT_EQUAL_MEMORY( pExpectedSignature, signature, signatureLen );

    params.pHttpParameters->pQuery = QUERY_STRING_WITH_TRAILING_N_LEADING_AMPERSAND;
    params.pHttpParameters->queryLen = strlen( QUERY_STRING_WITH_TRAILING_N_LEADING_AMPERSAND );

    pExpectedSignature = "576a0348d54591e15bed920586936f9263656470197adf7ce79c5fc8ef44d825";

    TEST_ASSERT_EQUAL( SigV4Success, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    TEST_ASSERT_EQUAL_MEMORY( pExpectedSignature, signature, signatureLen );

    params.pHttpParameters->pQuery = QUERY_STRING_WITH_REPEATED_AMPERSAND;
    params.pHttpParameters->queryLen = strlen( QUERY_STRING_WITH_REPEATED_AMPERSAND );

    pExpectedSignature = "4fcf6c89d5ddb944c0e386817d52835f578769e100d7e92d433bf4a946b7e6c3";
    TEST_ASSERT_EQUAL( SigV4Success, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );
    TEST_ASSERT_EQUAL( SIGV4_HASH_MAX_DIGEST_LENGTH * 2U, signatureLen );
    TEST_ASSERT_EQUAL_MEMORY( pExpectedSignature, signature, signatureLen );
}

/* Test that the library can handle an empty query string. */
void test_SigV4_GenerateAuthorization_Empty_Query()
{
    /* Happy path when both query and length are NULL and 0 respectively. */
    params.pHttpParameters->pQuery = NULL;
    params.pHttpParameters->queryLen = 0U;
    TEST_ASSERT_EQUAL( SigV4Success, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );

    /* The query is NULL, length is greater than 0, and the query is precanonicalized. */
    params.pHttpParameters->flags = SIGV4_HTTP_QUERY_IS_CANONICAL_FLAG;
    params.pHttpParameters->pQuery = NULL;
    params.pHttpParameters->queryLen = 3U;
    TEST_ASSERT_EQUAL( SigV4Success, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );

    /* The query is non-NULL but length is 0. */
    params.pHttpParameters->pQuery = QUERY;
    params.pHttpParameters->queryLen = 0U;
    TEST_ASSERT_EQUAL( SigV4Success, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );
}

void test_SigV4_GenerateHTTPAuthorization_Default_Arguments()
{
    SigV4Status_t returnStatus;

    /* Default algorithm is the macro defined by SIGV4_AWS4_HMAC_SHA256. */
    params.pAlgorithm = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
    /* Default path is "/". */
    params.pHttpParameters->pPath = NULL;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
    params.pHttpParameters->pPath = "/";
    params.pHttpParameters->pathLen = 0;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
}

/**
 * @brief Test the case when some input parameters are precanonicalized.
 */
void test_SigV4_GenerateHTTPAuthorization_Precanonicalized()
{
    SigV4Status_t returnStatus;

    params.pHttpParameters->pPath = PRECANON_PATH;
    params.pHttpParameters->pathLen = strlen( PRECANON_PATH );
    params.pHttpParameters->flags = SIGV4_HTTP_PATH_IS_CANONICAL_FLAG;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );

    params.pHttpParameters->pHeaders = PRECANON_HEADER;
    params.pHttpParameters->headersLen = STR_LIT_LEN( PRECANON_HEADER );
    params.pHttpParameters->flags |= SIGV4_HTTP_HEADERS_ARE_CANONICAL_FLAG;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
}

/* Test that the library fails when invalid HTTP headers are passed. */
void test_SigV4_GenerateHTTPAuthorization_InvalidHTTPHeaders()
{
    SigV4Status_t returnStatus;

    params.pHttpParameters->pHeaders = INVALID_HEADERS_NO_HEADER_VAL;
    params.pHttpParameters->headersLen = strlen( INVALID_HEADERS_NO_HEADER_VAL );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidHttpHeaders, returnStatus );

    params.pHttpParameters->pHeaders = INVALID_HEADERS_NO_HEADER_KEY;
    params.pHttpParameters->headersLen = strlen( INVALID_HEADERS_NO_HEADER_KEY );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidHttpHeaders, returnStatus );

    params.pHttpParameters->pHeaders = INVALID_PRECANON_HEADERS_NO_HEADER_KEY;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidHttpHeaders, returnStatus );

    params.pHttpParameters->pHeaders = INVALID_PRECANON_HEADERS_NO_HEADER_KEY;
    params.pHttpParameters->headersLen = strlen( INVALID_PRECANON_HEADERS_NO_HEADER_KEY );
    params.pHttpParameters->flags = SIGV4_HTTP_HEADERS_ARE_CANONICAL_FLAG;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidHttpHeaders, returnStatus );
}

/**
 * @brief Test for all cases where the processing buffer runs out of space.
 * @note While writing these tests, the inputs were deliberately crafted for
 * a buffer with 350 bytes as its maximum length.
 */
void test_SigV4_GenerateHTTPAuthorization_InsufficientMemory()
{
    SigV4Status_t returnStatus;

    authBufLen = params.pCryptoInterface->hashDigestLen * 2;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );

    /* Insufficient memory error when there is not enough space to write the
     * Method data in the processing buffer. This case is created by using a method string
     * longer than the processing buffer length. */
    char * pMethodData = malloc( SIGV4_PROCESSING_BUFFER_LENGTH );

    memset( pMethodData, ( int ) 'M', SIGV4_PROCESSING_BUFFER_LENGTH );
    params.pHttpParameters->pHttpMethod = pMethodData;
    params.pHttpParameters->httpMethodLen = SIGV4_PROCESSING_BUFFER_LENGTH;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    free( pMethodData );

    /* BEGIN: Coverage for generateCanonicalURI(). */
    /* The path here will cause the error for the first time the path is encoded. */
    resetInputParams();
    params.pHttpParameters->pPath = PATH_FIRST_ENCODE_OOM;
    params.pHttpParameters->pathLen = STR_LIT_LEN( PATH_FIRST_ENCODE_OOM );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );

    /* Same as previous but need for adding a linefeed character causes the error. We also explicitly use S3
     * service so that out of memory does not occur when double encoding. */
    resetInputParams();
    params.pService = S3_SERVICE_NAME;
    params.serviceLen = S3_SERVICE_NAME_LEN;
    params.pHttpParameters->pPath = PATH_FIRST_ENCODE_AND_LF_OOM;
    params.pHttpParameters->pathLen = STR_LIT_LEN( PATH_FIRST_ENCODE_AND_LF_OOM );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );

    /* The path here will cause the error for the second time the path is encoded. */
    resetInputParams();
    params.pHttpParameters->pPath = PATH_SECOND_ENCODE_OOM;
    params.pHttpParameters->pathLen = STR_LIT_LEN( PATH_SECOND_ENCODE_OOM );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    /* END: Coverage for generateCanonicalURI(). */

    /* BEGIN: Coverage for writeCanonicalQueryParameters(). */
    /* The attempt to encode the query field causes OOM (out of memory). */
    resetInputParams();
    params.pHttpParameters->pQuery = QUERY_ENCODE_FIELD_OOM;
    params.pHttpParameters->queryLen = STR_LIT_LEN( QUERY_ENCODE_FIELD_OOM );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );

    /* The attempt to encode the query value causes OOM (out of memory). */
    resetInputParams();
    params.pHttpParameters->pQuery = QUERY_ENCODE_VALUE_OOM;
    params.pHttpParameters->queryLen = STR_LIT_LEN( QUERY_ENCODE_VALUE_OOM );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );

    /* The attempt to write the '=' character before a value causes OOM (out of memory). */
    resetInputParams();
    params.pHttpParameters->pQuery = QUERY_EQUAL_BEFORE_VALUE_OOM;
    params.pHttpParameters->queryLen = STR_LIT_LEN( QUERY_EQUAL_BEFORE_VALUE_OOM );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );

    /* The attempt to write the '&' character before a field causes OOM (out of memory). */
    resetInputParams();
    params.pHttpParameters->pQuery = QUERY_AMPERSAND_BEFORE_FIELD_OOM;
    params.pHttpParameters->queryLen = STR_LIT_LEN( QUERY_AMPERSAND_BEFORE_FIELD_OOM );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    /* END: Coverage for writeCanonicalQueryParameters(). */

    /* BEGIN: Coverage for writeLineToCanonicalRequest(). */
    /* Writing a precanonicalized query to the processing buffer causes OOM. */
    resetInputParams();
    params.pHttpParameters->pQuery = PRECANON_QUERY_TOO_LONG;
    params.pHttpParameters->queryLen = STR_LIT_LEN( PRECANON_QUERY_TOO_LONG );
    params.pHttpParameters->flags = SIGV4_HTTP_QUERY_IS_CANONICAL_FLAG;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    /* END: Coverage for writeLineToCanonicalRequest(). */

    /* Test case of insufficient memory when "String to Sign" cannot be stored in processing buffer.
     * This scenario is produced by using a long AWS Region string (which is one of the parameters of String To Sign). */
    char * longRegion = malloc( SIGV4_PROCESSING_BUFFER_LENGTH );

    /* Fill gibberish string data in the buffer for region. */
    memset( longRegion, 'x', SIGV4_PROCESSING_BUFFER_LENGTH );
    resetInputParams();
    params.pRegion = longRegion;
    params.regionLen = SIGV4_PROCESSING_BUFFER_LENGTH;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    free( longRegion );

    /* Test case of insufficient memory when hexstring of hash cannot be stored in processing buffer.
     * This case is created by using long pre-canonicalized headers that does not leave space for Payload
     * hash in the processing buffer. */
    size_t headersLen = SIGV4_PROCESSING_BUFFER_LENGTH - ( SIGV4_HASH_MAX_DIGEST_LENGTH * 2 );
    char * longPrecanonHeader = malloc( headersLen );

    TEST_ASSERT_NOT_NULL( longPrecanonHeader );
    longPrecanonHeader[ 0 ] = 'H';
    longPrecanonHeader[ 1 ] = ':';
    /* Fill gibberish string data in the buffer for the precanonical header. */
    memset( longPrecanonHeader + 2, ( char ) 'V', headersLen - 3 );
    longPrecanonHeader[ headersLen - 1 ] = '\n';
    resetInputParams();
    params.pHttpParameters->pPath = NULL;
    params.pHttpParameters->pathLen = 0;
    params.pHttpParameters->pHeaders = longPrecanonHeader;
    params.pHttpParameters->headersLen = headersLen;
    params.pHttpParameters->pQuery = NULL;
    params.pHttpParameters->queryLen = 0;
    params.pHttpParameters->flags = SIGV4_HTTP_HEADERS_ARE_CANONICAL_FLAG;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    free( longPrecanonHeader );

    /* Test case of insufficient memory from failure to encode a special character when
     * writing canonical path. This is achieved by using a long path that ends with the special
     * character for which there doesn't exist space in the processing buffer. */
    size_t longPathLen = SIGV4_PROCESSING_BUFFER_LENGTH - httpParams.httpMethodLen - LINEFEED_CHAR_LEN;
    char specialCharAtEndOfLongPath[ longPathLen ];

    specialCharAtEndOfLongPath[ 0 ] = '/';
    memset( specialCharAtEndOfLongPath + 1, ( int ) '-', longPathLen );
    specialCharAtEndOfLongPath[ longPathLen - 1 ] = '*';
    resetInputParams();
    params.pHttpParameters->pPath = specialCharAtEndOfLongPath;
    params.pHttpParameters->pathLen = longPathLen;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );

    /* Test case of insufficient memory when there is no space in the processing buffer for
     * double encoding '=' character, that is part of query parameter value, while creating
     * canonical query. */
    size_t longQueryLen = SIGV4_PROCESSING_BUFFER_LENGTH - httpParams.httpMethodLen -
                          LINEFEED_CHAR_LEN - HTTP_EMPTY_PATH_LEN - LINEFEED_CHAR_LEN;
    char * longQuery = malloc( longQueryLen );

    TEST_ASSERT_NOT_NULL( longQuery );
    longQuery[ 0 ] = 'P';
    longQuery[ 1 ] = '=';
    memset( longQuery + 2, ( int ) 'V', longQueryLen - 2 );
    /* Use '=' as the second last URI query value character. */
    longQuery[ longQueryLen - 2 ] = '=';
    resetInputParams();
    params.pHttpParameters->pPath = NULL;
    params.pHttpParameters->pathLen = 0;
    params.pHttpParameters->pQuery = longQuery;
    params.pHttpParameters->queryLen = longQueryLen;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    free( longQuery );

    /* Case of insufficient memory when adding Header part of Canonical Header to processing buffer.
     * This case is created by using a long header name that causes space to run out when adding
     * Canonical Headers.  */
    headersLen = ( SIGV4_PROCESSING_BUFFER_LENGTH - httpParams.httpMethodLen - LINEFEED_CHAR_LEN -
                   HTTP_EMPTY_PATH_LEN - LINEFEED_CHAR_LEN -
                   /* Empty Query*/
                   LINEFEED_CHAR_LEN ) +

                 /* Extra characters to complete the Precanonicalized Headers with
                  * empty value and newline character. */
                 4U;
    char * longHeader = malloc( headersLen );

    TEST_ASSERT_NOT_NULL( longHeader );
    /* Set gibberish header key data. */
    memset( longHeader, ( int ) 'H', headersLen - 4 );
    longHeader[ headersLen - 4 ] = ':';
    longHeader[ headersLen - 3 ] = 'V';
    longHeader[ headersLen - 2 ] = '\r';
    longHeader[ headersLen - 1 ] = LINEFEED_CHAR;
    resetInputParams();
    params.pHttpParameters->pPath = NULL;
    params.pHttpParameters->pathLen = 0U;
    params.pHttpParameters->pQuery = NULL;
    params.pHttpParameters->queryLen = 0U;
    params.pHttpParameters->pHeaders = longHeader;
    params.pHttpParameters->headersLen = headersLen;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    free( longHeader );

    /* Case of insufficient memory when newline character after Canonical Headers to processing buffer.
     * This case is created by using a long header name that causes no space availability for the
     * new line character after the Canonical headers in the processing buffer .  */
    headersLen = SIGV4_PROCESSING_BUFFER_LENGTH - httpParams.httpMethodLen - LINEFEED_CHAR_LEN -
                 HTTP_EMPTY_PATH_LEN - LINEFEED_CHAR_LEN -
                 /* Empty Query*/
                 LINEFEED_CHAR_LEN +
                 /* The carriage return character that is trimmed in canonical form. */
                 1U;
    longHeader = malloc( headersLen );
    TEST_ASSERT_NOT_NULL( longHeader );
    /* Set gibberish header key data. */
    memset( longHeader, ( int ) 'H', headersLen - 4 );
    longHeader[ headersLen - 4 ] = ':';
    longHeader[ headersLen - 3 ] = 'V';
    longHeader[ headersLen - 2 ] = '\r';
    longHeader[ headersLen - 1 ] = LINEFEED_CHAR;
    resetInputParams();
    params.pHttpParameters->pPath = NULL;
    params.pHttpParameters->pathLen = 0U;
    params.pHttpParameters->pQuery = NULL;
    params.pHttpParameters->queryLen = 0U;
    params.pHttpParameters->pHeaders = longHeader;
    params.pHttpParameters->headersLen = headersLen;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    free( longHeader );

    /* Case of insufficient memory when adding signed headers to processing buffer.
     * This case is created by using a long header name that causes the Signed Header part of the
     * Canonical Request run out of memory.  */
    headersLen = SIGV4_PROCESSING_BUFFER_LENGTH - httpParams.httpMethodLen - LINEFEED_CHAR_LEN -
                 HTTP_EMPTY_PATH_LEN - LINEFEED_CHAR_LEN -
                 /* Empty Query*/
                 LINEFEED_CHAR_LEN -
                 /* New line after Canonical Headers just before writing Signed Headers. */
                 LINEFEED_CHAR_LEN;
    longPrecanonHeader = malloc( headersLen );
    TEST_ASSERT_NOT_NULL( longPrecanonHeader );
    /* Set gibberish header key data. */
    memset( longPrecanonHeader, ( int ) 'H', headersLen - 2 );
    longPrecanonHeader[ headersLen - 2 ] = ':';
    longPrecanonHeader[ headersLen - 1 ] = LINEFEED_CHAR;
    resetInputParams();
    params.pHttpParameters->pPath = NULL;
    params.pHttpParameters->pathLen = 0U;
    params.pHttpParameters->pQuery = NULL;
    params.pHttpParameters->queryLen = 0U;
    params.pHttpParameters->pHeaders = longPrecanonHeader;
    params.pHttpParameters->headersLen = headersLen;
    params.pHttpParameters->flags = SIGV4_HTTP_HEADERS_ARE_CANONICAL_FLAG;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    free( longPrecanonHeader );

    /* Case of insufficient memory when adding '=' character between query parameter and value.
    * This case is created by using a long query parameter that causes the processing buffer
    * to have no space when writing the equals to separator after the query parameter name.  */
    longQueryLen = SIGV4_PROCESSING_BUFFER_LENGTH - httpParams.httpMethodLen - LINEFEED_CHAR_LEN -
                   HTTP_EMPTY_PATH_LEN - LINEFEED_CHAR_LEN +
                   /* '=' separate and parameter value. */
                   2U;
    longQuery = malloc( longQueryLen );
    TEST_ASSERT_NOT_NULL( longQuery );
    /* Set gibberish query parameter name data. */
    memset( longQuery, ( int ) 'P', longQueryLen - 2 );
    longQuery[ longQueryLen - 2 ] = '=';
    longQuery[ longQueryLen - 1 ] = 'V';
    resetInputParams();
    params.pHttpParameters->pPath = NULL;
    params.pHttpParameters->pathLen = 0U;
    params.pHttpParameters->pQuery = longQuery;
    params.pHttpParameters->queryLen = longQueryLen;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    free( longQuery );

    /* Case of insufficient memory when adding '&' character between query parameter entries.
     * This case is created by using a long query parameter that causes the processing buffer
     * to have no space when encoding the '&' character for the second query parameter.  */
    longQueryLen = SIGV4_PROCESSING_BUFFER_LENGTH - httpParams.httpMethodLen - LINEFEED_CHAR_LEN -
                   HTTP_EMPTY_PATH_LEN - LINEFEED_CHAR_LEN +
                   /* 2nd query parameter entry. */
                   4U;
    longQuery = malloc( longQueryLen );
    TEST_ASSERT_NOT_NULL( longQuery );
    /* Populate a long query parameter name for 1st entry. */
    memset( longQuery, ( int ) 'P', longQueryLen - 6 );
    /* Populate the value for the 1st param and a second parameter entry. */
    memcpy( longQuery + longQueryLen - 6, "=V&Q=X", 6 );
    resetInputParams();
    params.pHttpParameters->pPath = NULL;
    params.pHttpParameters->pathLen = 0U;
    params.pHttpParameters->pQuery = longQuery;
    params.pHttpParameters->queryLen = longQueryLen;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    free( longQuery );

    /* Case of insufficient memory when adding newline character after query canonical data in processing
     * buffer.
     * This case is created by using a long query parameter that leaves no space for the newline character
     * after the canonical query data. */
    longQueryLen = SIGV4_PROCESSING_BUFFER_LENGTH - httpParams.httpMethodLen - LINEFEED_CHAR_LEN -
                   HTTP_EMPTY_PATH_LEN - LINEFEED_CHAR_LEN;
    longQuery = malloc( longQueryLen );
    TEST_ASSERT_NOT_NULL( longQuery );
    /* Populate a long query parameter name. */
    memset( longQuery, ( int ) 'P', longQueryLen - 1 );
    longQuery[ longQueryLen - 1U ] = '=';
    resetInputParams();
    params.pHttpParameters->pPath = NULL;
    params.pHttpParameters->pathLen = 0U;
    params.pHttpParameters->pQuery = longQuery;
    params.pHttpParameters->queryLen = longQueryLen;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    free( longQuery );

    /* Test case when there is insufficient processing buffer space for writing signing key.
     * This case is created by using a long Region value that causes the "String to Sign" data
     * to crowd out space for the Signing Key. */
    size_t lenOfStringToSignWithoutRegion = ( STRING_TO_SIGN_LEN_WITH_DEFAULT_REGION ) -strlen( REGION );
    size_t longRegionLen = SIGV4_PROCESSING_BUFFER_LENGTH - lenOfStringToSignWithoutRegion;

    /*size_t longRegionLen = SIGV4_PROCESSING_BUFFER_LENGTH - 4 * SIGV4_HASH_MAX_DIGEST_LENGTH; */
    longRegion = malloc( longRegionLen );
    /* Fill gibberish in the long region name. */
    memset( longRegion, ( int ) 'R', longRegionLen );
    resetInputParams();
    params.pRegion = longRegion;
    params.regionLen = longRegionLen;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InsufficientMemory, returnStatus );
    free( longRegion );
}

/* Test that the library can encode non-alphanumeric characters in a query string. */
void test_SigV4_GenerateHTTPAuthorization_Encode_URI_Non_AlphaNumeric()
{
    SigV4Status_t returnStatus;

    resetInputParams();
    params.pHttpParameters->pQuery = QUERY_WITH_NON_ALPHA_NUMBERIC_CHARS;
    params.pHttpParameters->queryLen = strlen( QUERY_WITH_NON_ALPHA_NUMBERIC_CHARS );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );

    params.pHttpParameters->pQuery = QUERY_WITH_SPECIAL_CHARS;
    params.pHttpParameters->queryLen = strlen( QUERY_WITH_SPECIAL_CHARS );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4Success, returnStatus );
}

/**
 * @brief Coverage for cases when the hashing functions return errors.
 */
void test_SigV4_GenerateHTTPAuthorization_Hash_Errors()
{
    SigV4Status_t returnStatus;
    size_t i;

    params.pCredentials->pSecretAccessKey = SECRET_KEY_LONGER_THAN_HASH_BLOCK;
    params.pCredentials->secretAccessKeyLen = strlen( SECRET_KEY_LONGER_THAN_HASH_BLOCK );
    char failureMessage[ 250 ];

    for( i = 0U; i < HASH_ERROR_BRANCH_COVERAGE_ITERATIONS; i++ )
    {
        resetFailableHashParams();
        hashInitCallToFail = i;
        params.pCryptoInterface->hashInit = hash_init_failable;
        returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
        snprintf( failureMessage, sizeof( failureMessage ), "Expected SigV4HashError from hashInit failure at call count %ld", i );
        TEST_ASSERT_EQUAL_MESSAGE( SigV4HashError, returnStatus, failureMessage );

        resetFailableHashParams();
        updateHashCallToFail = i;
        returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
        snprintf( failureMessage, sizeof( failureMessage ), "Expected SigV4HashError from hashUpdate failure at call count %ld", i );
        TEST_ASSERT_EQUAL_MESSAGE( SigV4HashError, returnStatus, failureMessage );

        resetFailableHashParams();
        finalHashCallToFail = i;
        returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
        snprintf( failureMessage, sizeof( failureMessage ), "Expected SigV4HashError from hashFinal failure at call count %ld", i );
        TEST_ASSERT_EQUAL_MESSAGE( SigV4HashError, returnStatus, failureMessage );
    }
}

/**
 * @brief Coverage for the case when hashing the SigV4 signing key prefix fails.
 */
void test_SigV4_Hash_Key_Prefix_Small_Than_Block_Size()
{
    SigV4Status_t returnStatus;

    resetFailableHashParams();

    /* By keeping the block size smaller than the length of the key prefix,
     * we are able to attain coverage in the case when hashing the key prefix fails. */
    params.pCryptoInterface->hashBlockLen = SIGV4_HMAC_SIGNING_KEY_PREFIX_LEN - 1U;
    hashInitCallToFail = 2U;
    params.pCryptoInterface->hashInit = hash_init_failable;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL_MESSAGE( SigV4HashError, returnStatus, "2nd call to hashInit should fail when hashing SigV4 key prefix." );
}

/**
 * @brief Test the case when the query string or header parameters exceed the max.
 */
void test_SigV4_GenerateHTTPAuthorization_Greater_Than_Max_Header_Query_Count()
{
    SigV4Status_t returnStatus;

    params.pHttpParameters->pQuery = QUERY_GT_MAX_PARAMS;
    params.pHttpParameters->queryLen = STR_LIT_LEN( QUERY_GT_MAX_PARAMS );
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4MaxQueryPairCountExceeded, returnStatus );
}


/* Test that the library returns error when the HTTP request data contains more Headers
 * the configured maximum threshold in SIGV4_MAX_HTTP_HEADER_COUNT. */
void test_SigV4_GenerateAuthorization_Headers_Greater_Than_Configured_Max()
{
    params.pHttpParameters->pHeaders = HEADERS_PAIRS_GT_THAN_MAX;
    params.pHttpParameters->headersLen = strlen( HEADERS_PAIRS_GT_THAN_MAX );

    TEST_ASSERT_EQUAL( SigV4MaxHeaderPairCountExceeded, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );

    params.pHttpParameters->pHeaders = PRECAN_HEADERS_PAIRS_GT_THAN_MAX;
    params.pHttpParameters->headersLen = strlen( PRECAN_HEADERS_PAIRS_GT_THAN_MAX );
    params.pHttpParameters->flags = SIGV4_HTTP_HEADERS_ARE_CANONICAL_FLAG;
    TEST_ASSERT_EQUAL( SigV4MaxHeaderPairCountExceeded, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );
}

void test_SigV4_GenerateAuthorization_Sorting_Algorithm_Coverage()
{
    params.pHttpParameters->pHeaders = HEADERS_SORTED_COVERAGE_1;
    params.pHttpParameters->headersLen = strlen( HEADERS_SORTED_COVERAGE_1 );
    TEST_ASSERT_EQUAL( SigV4Success, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );

    params.pHttpParameters->pPath = NULL;
    params.pHttpParameters->pathLen = 0U;
    params.pHttpParameters->pQuery = NULL;
    params.pHttpParameters->queryLen = 0U;
    params.pHttpParameters->pHeaders = HEADERS_SORTED_COVERAGE_2;
    params.pHttpParameters->headersLen = strlen( HEADERS_SORTED_COVERAGE_2 );
    TEST_ASSERT_EQUAL( SigV4Success, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );
}

/* Test that the library does not calculate the HTTP hash of the request payload if it is already hashed by the application. */
void test_SigV4_GenerateAuthorization_Headers_With_X_Amz_Content_Sha256_Header()
{
    params.pHttpParameters->pHeaders = HEADERS_WITH_X_AMZ_CONTENT_SHA256;
    params.pHttpParameters->headersLen = strlen( HEADERS_WITH_X_AMZ_CONTENT_SHA256 );

    params.pHttpParameters->flags = SIGV4_HTTP_PAYLOAD_IS_HASH;

    TEST_ASSERT_EQUAL( SigV4Success, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );
}

/* Test that the library calculates the hash of the HTTP request payload if it is not already hashed by the application. */
void test_SigV4_GenerateAuthorization_Headers_Without_X_Amz_Content_Sha256_Header()
{
    params.pHttpParameters->pHeaders = HEADERS_WITHOUT_X_AMZ_CONTENT_SHA256;
    params.pHttpParameters->headersLen = strlen( HEADERS_WITHOUT_X_AMZ_CONTENT_SHA256 );

    TEST_ASSERT_EQUAL( SigV4Success, SigV4_GenerateHTTPAuthorization(
                           &params, authBuf, &authBufLen, &signature, &signatureLen ) );
}

/* Test that the library returns SigV4InvalidParameter if Header Key or value contains all white spaces. */
void test_SigV4_GenerateAuthorization_Header_Key_Or_Value_With_All_White_Spaces()
{
    SigV4Status_t returnStatus;
    size_t headersLen = SIGV4_PROCESSING_BUFFER_LENGTH - httpParams.httpMethodLen - LINEFEED_CHAR_LEN -
                        HTTP_EMPTY_PATH_LEN - LINEFEED_CHAR_LEN -
                        /* Empty Query*/
                        LINEFEED_CHAR_LEN +
                        /* The carriage return character that is trimmed in canonical form. */
                        1U;
    char * longHeader = malloc( headersLen );

    TEST_ASSERT_NOT_NULL( longHeader );

    memset( longHeader, ( int ) 'H', headersLen - 4 );
    longHeader[ headersLen - 4 ] = ':';
    /* Set Header value containing all white spaces. */
    longHeader[ headersLen - 3 ] = ' ';
    longHeader[ headersLen - 2 ] = '\r';
    longHeader[ headersLen - 1 ] = LINEFEED_CHAR;
    resetInputParams();
    params.pHttpParameters->pPath = NULL;
    params.pHttpParameters->pathLen = 0U;
    params.pHttpParameters->pQuery = NULL;
    params.pHttpParameters->queryLen = 0U;
    params.pHttpParameters->pHeaders = longHeader;
    params.pHttpParameters->headersLen = headersLen;
    returnStatus = SigV4_GenerateHTTPAuthorization( &params, authBuf, &authBufLen, &signature, &signatureLen );
    TEST_ASSERT_EQUAL( SigV4InvalidParameter, returnStatus );
    free( longHeader );
}
