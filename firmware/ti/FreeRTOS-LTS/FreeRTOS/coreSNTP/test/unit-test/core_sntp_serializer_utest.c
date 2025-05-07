/*
 * coreSNTP v1.3.1
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

/* Standard includes. */
#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdint.h>

/* POSIX include. */
#include <arpa/inet.h>

/* Unity include. */
#include "unity.h"

/* coreSNTP Serializer API include */
#include "core_sntp_serializer.h"

#define TEST_TIMESTAMP         \
    {                          \
        .seconds = UINT32_MAX, \
        .fractions = 1000      \
    }

#define ZERO_TIMESTAMP \
    {                  \
        .seconds = 0,  \
        .fractions = 0 \
    }

/* Bits 3-5 are used for Version in 1st byte of SNTP packet. */
#define SNTP_PACKET_VERSION_VAL                    ( 4 /* Version */ << 3 /* Bits 3-5 used in byte */ )

/* Values for "Mode" field in an SNTP packet. */
#define SNTP_PACKET_MODE_SERVER                    ( 4 )
#define SNTP_PACKET_MODE_CLIENT                    ( 3 )

/* The least significant bit position of "Leap Indicator" field
 * in the first byte of an SNTP packet. */
#define SNTP_PACKET_LEAP_INDICATOR_LSB             ( 6 )

/* The byte positions of SNTP packet fields in the 48 bytes sized
 * packet format. */
#define SNTP_PACKET_STRATUM_BYTE_POS               ( 1 )
#define SNTP_PACKET_KOD_CODE_FIRST_BYTE_POS        ( 12 )
#define SNTP_PACKET_ORIGIN_TIME_FIRST_BYTE_POS     ( 24 )
#define SNTP_PACKET_RX_TIMESTAMP_FIRST_BYTE_POS    ( 32 )
#define SNTP_PACKET_TX_TIMESTAMP_FIRST_BYTE_POS    ( 40 )

/* Values of "Stratum" field in an SNTP packet. */
#define SNTP_PACKET_STRATUM_KOD                    ( 0 )
#define SNTP_PACKET_STRATUM_SECONDARY_SERVER       ( 15 )

/* ASCII string codes that a server can send in a Kiss-o'-Death response. */
#define KOD_CODE_DENY                              "DENY"
#define KOD_CODE_RSTR                              "RSTR"
#define KOD_CODE_RATE                              "RATE"
#define KOD_CODE_OTHER_EXAMPLE_1                   "AUTH"
#define KOD_CODE_OTHER_EXAMPLE_2                   "CRYP"

#define YEARS_20_IN_SECONDS                        ( ( 20 * 365 + 20 / 4 ) * 24 * 3600 )
#define YEARS_68_IN_SECONDS                        ( ( 68 * 365 + 68 / 4 ) * 24 * 3600 )

/* Macro utility to convert the fixed-size Kiss-o'-Death ASCII code
 * to integer.*/
#define INTEGER_VAL_OF_KOD_CODE( codePtr )                 \
    ( ( uint32_t ) ( ( ( uint32_t ) codePtr[ 0 ] << 24 ) | \
                     ( ( uint32_t ) codePtr[ 1 ] << 16 ) | \
                     ( ( uint32_t ) codePtr[ 2 ] << 8 ) |  \
                     ( ( uint32_t ) codePtr[ 3 ] ) ) )

/* Buffer used for SNTP requests and responses in tests. */
static uint8_t testBuffer[ SNTP_PACKET_BASE_SIZE ];

static SntpResponseData_t parsedData;

static SntpTimestamp_t zeroTimestamp = ZERO_TIMESTAMP;

/* ============================ Helper Functions ============================ */

/* Utility macro to convert seconds to milliseconds. */
static uint64_t TO_MS( uint64_t seconds )
{
    return( seconds * 1000 );
}

static void addTimestampToResponseBuffer( SntpTimestamp_t * pTime,
                                          uint8_t * pResponseBuffer,
                                          size_t startingPos )
{
    /* Convert the request time into network byte order to use to fill in buffer. */
    uint32_t secs = pTime->seconds;
    uint32_t fracs = pTime->fractions;

    pResponseBuffer[ startingPos ] = secs >> 24;      /* seconds, byte 1*/
    pResponseBuffer[ startingPos + 1 ] = secs >> 16;  /* seconds, byte 2 */
    pResponseBuffer[ startingPos + 2 ] = secs >> 8;   /* seconds, byte 3 */
    pResponseBuffer[ startingPos + 3 ] = secs;        /* seconds, byte 4 */
    pResponseBuffer[ startingPos + 4 ] = fracs >> 24; /* fractions, byte 1*/
    pResponseBuffer[ startingPos + 5 ] = fracs >> 16; /* fractions, byte 2 */
    pResponseBuffer[ startingPos + 6 ] = fracs >> 8;  /* fractions, byte 3 */
    pResponseBuffer[ startingPos + 7 ] = fracs;       /* fractions, byte 4 */
}

static void fillValidSntpResponseData( uint8_t * pBuffer,
                                       SntpTimestamp_t * pRequestTime )
{
    /* Clear the buffer. */
    memset( pBuffer, 0, SNTP_PACKET_BASE_SIZE );

    /* Set the "Version" and "Mode" fields in the first byte of SNTP packet. */
    pBuffer[ 0 ] = SNTP_PACKET_VERSION_VAL | SNTP_PACKET_MODE_SERVER;

    /* Set the SNTP response packet to contain the "originate" timestamp
     * correctly, as matching the SNTP request timestamp. */
    addTimestampToResponseBuffer( pRequestTime,
                                  pBuffer,
                                  SNTP_PACKET_ORIGIN_TIME_FIRST_BYTE_POS );

    SntpTimestamp_t testTime = TEST_TIMESTAMP;

    /* Set the SNTP response packet to contain the "receive" timestamp
     * correctly, as matching the SNTP request timestamp. */
    addTimestampToResponseBuffer( &testTime,
                                  pBuffer,
                                  SNTP_PACKET_RX_TIMESTAMP_FIRST_BYTE_POS );

    /* Set the SNTP response packet to contain the "transmit" timestamp
     * correctly, as matching the SNTP request timestamp. */
    addTimestampToResponseBuffer( &testTime,
                                  pBuffer,
                                  SNTP_PACKET_TX_TIMESTAMP_FIRST_BYTE_POS );

    /* Set the "Stratum" byte in the response packet to represent a
     * secondary NTP server. */
    pBuffer[ SNTP_PACKET_STRATUM_BYTE_POS ] = SNTP_PACKET_STRATUM_SECONDARY_SERVER;
}

/* Common test code that fills SNTP response packet with server times and validates
* that @ref Sntp_DeserializeResponse API correctly calculates the clock offset.  */
static void testClockOffsetCalculation( SntpTimestamp_t * clientTxTime,
                                        SntpTimestamp_t * serverRxTime,
                                        SntpTimestamp_t * serverTxTime,
                                        SntpTimestamp_t * clientRxTime,
                                        SntpStatus_t expectedStatus,
                                        int64_t expectedClockOffsetMs )
{
    /* Update the response packet with the server time. */
    addTimestampToResponseBuffer( clientTxTime,
                                  testBuffer,
                                  SNTP_PACKET_ORIGIN_TIME_FIRST_BYTE_POS );
    addTimestampToResponseBuffer( serverRxTime,
                                  testBuffer,
                                  SNTP_PACKET_RX_TIMESTAMP_FIRST_BYTE_POS );
    addTimestampToResponseBuffer( serverTxTime,
                                  testBuffer,
                                  SNTP_PACKET_TX_TIMESTAMP_FIRST_BYTE_POS );

    /* Call the API under test. */
    TEST_ASSERT_EQUAL( expectedStatus, Sntp_DeserializeResponse( clientTxTime,
                                                                 clientRxTime,
                                                                 testBuffer,
                                                                 sizeof( testBuffer ),
                                                                 &parsedData ) );

    /* Make sure that the API has indicated in the output parameter that
     * clock-offset could not be calculated. */
    TEST_ASSERT_EQUAL( expectedClockOffsetMs, parsedData.clockOffsetMs );

    /* Validate other fields in the output parameter. */
    TEST_ASSERT_EQUAL( 0, memcmp( &parsedData.serverTime, serverTxTime, sizeof( SntpTimestamp_t ) ) );
    TEST_ASSERT_EQUAL( NoLeapSecond, parsedData.leapSecondType );
    TEST_ASSERT_EQUAL( SNTP_KISS_OF_DEATH_CODE_NONE, parsedData.rejectedResponseCode );
}

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    memset( &parsedData, 0, sizeof( parsedData ) );
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

/* ========================================================================== */

/**
 * @brief Test @ref Sntp_SerializeRequest with invalid parameters.
 */
void test_SerializeRequest_InvalidParams( void )
{
    SntpTimestamp_t testTime = TEST_TIMESTAMP;

    /* Pass invalid time object. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_SerializeRequest( NULL,
                                              ( rand() % UINT32_MAX ),
                                              testBuffer,
                                              sizeof( testBuffer ) ) );

    /* Pass invalid buffer. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_SerializeRequest( &testTime,
                                              ( rand() % UINT32_MAX ),
                                              NULL,
                                              sizeof( testBuffer ) ) );

    /* Pass zero timestamp for request time. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_SerializeRequest( &zeroTimestamp,
                                              ( rand() % UINT32_MAX ),
                                              testBuffer,
                                              sizeof( testBuffer ) ) );

    /* Pass a buffer size less than 48 bytes of minimum SNTP packet size. */
    TEST_ASSERT_EQUAL( SntpErrorBufferTooSmall,
                       Sntp_SerializeRequest( &testTime,
                                              ( rand() % UINT32_MAX ),
                                              testBuffer,
                                              1 ) );
}

/**
 * @brief Validate the serialization operation of the @ref Sntp_SerializeRequest API.
 */
void test_SerializeRequest_NominalCase( void )
{
    SntpTimestamp_t testTime = TEST_TIMESTAMP;
    const uint32_t randomVal = 0xAABBCCDD;

    /* Expected transmit timestamp in the SNTP request packet. */
    const SntpTimestamp_t expectedTxTime =
    {
        .seconds   = testTime.seconds,
        .fractions = ( testTime.fractions | ( randomVal >> 16 ) )
    };

    /* The expected serialization of the SNTP request packet. */
    uint8_t expectedSerialization[ SNTP_PACKET_BASE_SIZE ] =
    {
        0x00 /* Leap Indicator */ | 0x20 /* Version */ | 0x03, /* Client Mode */
        0x00,                                                  /* stratum */
        0x00,                                                  /* poll interval */
        0x00,                                                  /* precision */
        0x00, 0x00, 0x00, 0x00,                                /* root delay */
        0x00, 0x00, 0x00, 0x00,                                /* root dispersion */
        0x00, 0x00, 0x00, 0x00,                                /* reference ID */
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,        /* reference time */
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,        /* origin timestamp */
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,        /* receive timestamp */
        expectedTxTime.seconds >> 24,                          /* transmit timestamp - seconds, byte 1 */
        expectedTxTime.seconds >> 16,                          /* transmit timestamp - seconds, byte 2 */
        expectedTxTime.seconds >> 8,                           /* transmit timestamp - seconds, byte 3 */
        expectedTxTime.seconds,                                /* transmit timestamp - seconds, byte 4 */
        expectedTxTime.fractions >> 24,                        /* transmit timestamp - fractions, byte 1 */
        expectedTxTime.fractions >> 16,                        /* transmit timestamp - fractions, byte 2 */
        expectedTxTime.fractions >> 8,                         /* transmit timestamp - fractions, byte 3 */
        expectedTxTime.fractions,                              /* transmit timestamp - fractions, byte 4 */
    };

    /* Call the API under test. */
    TEST_ASSERT_EQUAL( SntpSuccess,
                       Sntp_SerializeRequest( &testTime,
                                              randomVal,
                                              testBuffer,
                                              sizeof( testBuffer ) ) );

    /* Validate that serialization operation by the API. */
    TEST_ASSERT_EQUAL_UINT8_ARRAY( expectedSerialization,
                                   testBuffer,
                                   SNTP_PACKET_BASE_SIZE );

    /* Check that the request timestamp object has been updated with the random value. */
    TEST_ASSERT_EQUAL( 0, memcmp( &expectedTxTime,
                                  &testTime,
                                  sizeof( SntpTimestamp_t ) ) );
}

/**
 * @brief Test @ref Sntp_DeserializeResponse with invalid parameters.
 */
void test_DeserializeResponse_InvalidParams( void )
{
    SntpTimestamp_t testTime = TEST_TIMESTAMP;

    /* Pass invalid time objects. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_DeserializeResponse( NULL,
                                                 &testTime,
                                                 testBuffer,
                                                 sizeof( testBuffer ),
                                                 &parsedData ) );
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_DeserializeResponse( &testTime,
                                                 NULL,
                                                 testBuffer,
                                                 sizeof( testBuffer ),
                                                 &parsedData ) );

    /* Pass invalid buffer. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_DeserializeResponse( &testTime,
                                                 &testTime,
                                                 NULL,
                                                 sizeof( testBuffer ),
                                                 &parsedData ) );

    /* Pass a buffer size less than 48 bytes of minimum SNTP packet size. */
    TEST_ASSERT_EQUAL( SntpErrorBufferTooSmall,
                       Sntp_DeserializeResponse( &testTime,
                                                 &testTime,
                                                 testBuffer,
                                                 sizeof( testBuffer ) / 2,
                                                 &parsedData ) );

    /* Pass invalid output parameter. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_DeserializeResponse( &testTime,
                                                 &testTime,
                                                 testBuffer,
                                                 sizeof( testBuffer ),
                                                 NULL ) );

    /* Pass zero timestamp for request time. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_DeserializeResponse( &zeroTimestamp,
                                                 &testTime,
                                                 testBuffer,
                                                 sizeof( testBuffer ),
                                                 &parsedData ) );
}

/**
 * @brief Test that @ref Sntp_DeserializeResponse API can detect invalid
 * SNTP response packets.
 */
void test_DeserializeResponse_Invalid_Responses( void )
{
    SntpTimestamp_t clientTime = TEST_TIMESTAMP;

    /* Fill buffer with general SNTP response data. */
    fillValidSntpResponseData( testBuffer, &clientTime );

    /* ******* Test when SNTP packet does not a non-server value in the "Mode" field. **** */
    testBuffer[ 0 ] = SNTP_PACKET_VERSION_VAL | SNTP_PACKET_MODE_CLIENT;

    /* Call the API under test. */
    TEST_ASSERT_EQUAL( SntpInvalidResponse, Sntp_DeserializeResponse( &clientTime,
                                                                      &clientTime,
                                                                      testBuffer,
                                                                      sizeof( testBuffer ),
                                                                      &parsedData ) );


    /* Set the Mode field to the correct value for Server. */
    testBuffer[ 0 ] = SNTP_PACKET_VERSION_VAL | SNTP_PACKET_MODE_SERVER;

    /************** Test when "originate timestamp" is zero ***************/
    addTimestampToResponseBuffer( &zeroTimestamp,
                                  testBuffer,
                                  SNTP_PACKET_ORIGIN_TIME_FIRST_BYTE_POS );
    /* Call the API under test. */
    TEST_ASSERT_EQUAL( SntpInvalidResponse, Sntp_DeserializeResponse( &clientTime,
                                                                      &clientTime,
                                                                      testBuffer,
                                                                      sizeof( testBuffer ),
                                                                      &parsedData ) );

    /* Set the "originate timestamp" to a non-zero value for the next test. */
    addTimestampToResponseBuffer( &clientTime,
                                  testBuffer,
                                  SNTP_PACKET_ORIGIN_TIME_FIRST_BYTE_POS );


    /************** Test when "receive timestamp" is zero ***************/
    addTimestampToResponseBuffer( &zeroTimestamp,
                                  testBuffer,
                                  SNTP_PACKET_RX_TIMESTAMP_FIRST_BYTE_POS );
    /* Call the API under test. */
    TEST_ASSERT_EQUAL( SntpInvalidResponse, Sntp_DeserializeResponse( &clientTime,
                                                                      &clientTime,
                                                                      testBuffer,
                                                                      sizeof( testBuffer ),
                                                                      &parsedData ) );

    /* Set the "receive timestamp" to a non-zero value for the next test. */
    addTimestampToResponseBuffer( &clientTime,
                                  testBuffer,
                                  SNTP_PACKET_RX_TIMESTAMP_FIRST_BYTE_POS );


    /************** Test when "transmit timestamp" is zero ***************/
    addTimestampToResponseBuffer( &zeroTimestamp,
                                  testBuffer,
                                  SNTP_PACKET_TX_TIMESTAMP_FIRST_BYTE_POS );
    /* Call the API under test. */
    TEST_ASSERT_EQUAL( SntpInvalidResponse, Sntp_DeserializeResponse( &clientTime,
                                                                      &clientTime,
                                                                      testBuffer,
                                                                      sizeof( testBuffer ),
                                                                      &parsedData ) );

    /* Set the "transmit timestamp" to a non-zero value for the next test. */
    addTimestampToResponseBuffer( &clientTime,
                                  testBuffer,
                                  SNTP_PACKET_TX_TIMESTAMP_FIRST_BYTE_POS );


    /******** Test when SNTP response packet does not have "originate" timestamp matching
     * the "transmit" time sent by the client in the SNTP request. ************/
    SntpTimestamp_t originateTime = TEST_TIMESTAMP;


    /* Test when only the seconds part of the "originate" timestamp does not match
     * the client request time .*/
    originateTime.seconds = clientTime.seconds + 1;
    addTimestampToResponseBuffer( &originateTime,
                                  testBuffer,
                                  SNTP_PACKET_ORIGIN_TIME_FIRST_BYTE_POS );

    /* Call the API under test. */
    TEST_ASSERT_EQUAL( SntpInvalidResponse, Sntp_DeserializeResponse( &clientTime,
                                                                      &clientTime,
                                                                      testBuffer,
                                                                      sizeof( testBuffer ),
                                                                      &parsedData ) );

    /* Test when only the fractions part of the "originate" timestamp does not match
     * the client request time .*/
    originateTime.seconds = clientTime.seconds;
    originateTime.fractions = clientTime.fractions + 1;
    addTimestampToResponseBuffer( &originateTime,
                                  testBuffer,
                                  SNTP_PACKET_ORIGIN_TIME_FIRST_BYTE_POS );


    /* Call the API under test. */
    TEST_ASSERT_EQUAL( SntpInvalidResponse, Sntp_DeserializeResponse( &clientTime,
                                                                      &clientTime,
                                                                      testBuffer,
                                                                      sizeof( testBuffer ),
                                                                      &parsedData ) );
}

/**
 * @brief Test @ref Sntp_DeserializeResponse API to de-serialize Kiss-o'-Death
 * responses from SNTP server.
 *
 * The API should return an error code appropriate for the Kiss-o'-Death code
 * and update the member of output parameter to point the ASCII string code
 * in the response packet.
 */
void test_DeserializeResponse_KoD_packets( void )
{
    /* Use same value for request and response times, as API should not process
     * them for Kiss-o'-Death response packets. */
    SntpTimestamp_t testTime = TEST_TIMESTAMP;
    uint32_t KodCodeNetworkOrder = 0;

    /* Populate the buffer with a valid SNTP response before converting it
     * into a Kiss-o'-Death message. */
    fillValidSntpResponseData( testBuffer, &testTime );

    /* Update the "Stratum" field in the buffer to make the packet a Kiss-o'-Death message. */
    testBuffer[ SNTP_PACKET_STRATUM_BYTE_POS ] = SNTP_PACKET_STRATUM_KOD;

/* Common test code for testing de-serialization of Kiss-o'-Death packet containing a specific
 * code with@ref Sntp_DeserializeResponse API. */
#define TEST_API_FOR_KOD_CODE( code, expectedStatus )                                      \
    do {                                                                                   \
        KodCodeNetworkOrder = INTEGER_VAL_OF_KOD_CODE( code );                             \
        testBuffer[ SNTP_PACKET_KOD_CODE_FIRST_BYTE_POS ] = KodCodeNetworkOrder >> 24;     \
        testBuffer[ SNTP_PACKET_KOD_CODE_FIRST_BYTE_POS + 1 ] = KodCodeNetworkOrder >> 16; \
        testBuffer[ SNTP_PACKET_KOD_CODE_FIRST_BYTE_POS + 2 ] = KodCodeNetworkOrder >> 8;  \
        testBuffer[ SNTP_PACKET_KOD_CODE_FIRST_BYTE_POS + 3 ] = KodCodeNetworkOrder;       \
                                                                                           \
        /* Call API under test. */                                                         \
        TEST_ASSERT_EQUAL( expectedStatus,                                                 \
                           Sntp_DeserializeResponse( &testTime,                            \
                                                     &testTime,                            \
                                                     testBuffer,                           \
                                                     sizeof( testBuffer ),                 \
                                                     &parsedData ) );                      \
                                                                                           \
        /* Test that API has populated the output parameter with the parsed \
         * KoD code. */                                       \
        TEST_ASSERT_EQUAL( INTEGER_VAL_OF_KOD_CODE( code ),   \
                           parsedData.rejectedResponseCode ); \
                                                              \
    } while( 0 )

    /* Test Kiss-o'-Death server response with "DENY" code. */
    TEST_API_FOR_KOD_CODE( KOD_CODE_DENY, SntpRejectedResponseChangeServer );

    /* Test Kiss-o'-Death server response with "RSTR" code. */
    TEST_API_FOR_KOD_CODE( KOD_CODE_RSTR, SntpRejectedResponseChangeServer );

    /* Test Kiss-o'-Death server response with "RATE" code. */
    TEST_API_FOR_KOD_CODE( KOD_CODE_RATE, SntpRejectedResponseRetryWithBackoff );

    /* ***** Test de-serialization of Kiss-o'-Death server response with other codes ***** */
    TEST_API_FOR_KOD_CODE( KOD_CODE_OTHER_EXAMPLE_1, SntpRejectedResponseOtherCode );
    TEST_API_FOR_KOD_CODE( KOD_CODE_OTHER_EXAMPLE_2, SntpRejectedResponseOtherCode );
}

/**
 * @brief Test that @ref Sntp_DeserializeResponse API can process an accepted
 * SNTP server response, and compute clock-offset when the server and client times
 * are >= 68 years apart.
 */
void test_DeserializeResponse_AcceptedResponse_ClockOffset_Edge_Cases( void )
{
    SntpTimestamp_t clientTime = TEST_TIMESTAMP;

    /* Fill buffer with general SNTP response data. */
    fillValidSntpResponseData( testBuffer, &clientTime );

    /* Test when the client is 68 years ahead of server time .*/
    SntpTimestamp_t serverTime =
    {
        clientTime.seconds - YEARS_68_IN_SECONDS,
        clientTime.fractions
    };

    testClockOffsetCalculation( &clientTime, &serverTime,
                                &serverTime, &clientTime,
                                SntpSuccess,
                                TO_MS( -YEARS_68_IN_SECONDS ) );

    /* Now test when the client is 68 years ahead of server time .*/
    serverTime.seconds = clientTime.seconds + YEARS_68_IN_SECONDS;
    testClockOffsetCalculation( &clientTime, &serverTime,
                                &serverTime, &clientTime,
                                SntpSuccess,
                                TO_MS( YEARS_68_IN_SECONDS ) );

    /* Now test special cases when the server and client times are (INT32_MAX + 1) =
     * 2^31 apart seconds apart. The library should ALWAYS think that server
     * is ahead of the client in this special case, and thus return the maximum
     * signed 32 bit integer as the clock-offset.
     */
    /* Case when "Server Time - Client Time" results in negative value. */
    serverTime.seconds = clientTime.seconds + INT32_MAX + 1;
    testClockOffsetCalculation( &clientTime, &serverTime,
                                &serverTime, &clientTime,
                                SntpSuccess,
                                TO_MS( ( int64_t ) INT32_MAX + 1 ) );
    /* Test when "Server Time - Client Time" results in positive value. */
    serverTime.seconds = UINT32_MAX;
    clientTime.seconds = serverTime.seconds - INT32_MAX - 1;
    testClockOffsetCalculation( &clientTime, &serverTime,
                                &serverTime, &clientTime,
                                SntpSuccess,
                                TO_MS( ( int64_t ) INT32_MAX + 1 ) );

    /* Reset client time to UINT32_MAX */
    clientTime.seconds = UINT32_MAX;

    /* Now test cases when the server and client times are exactly
     * INT32_MAX seconds apart. */
    serverTime.seconds = clientTime.seconds - INT32_MAX;
    testClockOffsetCalculation( &clientTime, &serverTime,
                                &serverTime, &clientTime,
                                SntpSuccess,
                                TO_MS( -INT32_MAX ) );
    serverTime.seconds = clientTime.seconds + INT32_MAX;
    testClockOffsetCalculation( &clientTime, &serverTime,
                                &serverTime, &clientTime,
                                SntpSuccess,
                                TO_MS( INT32_MAX ) );

    /* Reset client and server times to be 68 years apart. */
    clientTime.seconds = UINT32_MAX;
    serverTime.seconds = UINT32_MAX + YEARS_68_IN_SECONDS;

    /* Now test the contrived case when only the send network path
     * represents timestamps that overflow but the receive network path
     * has timestamps that do not overflow.
     * As only the single network path contains time difference of 68 years,
     * the expected clock-offset, being an average of the network paths, is
     * 34 years of duration. */
    testClockOffsetCalculation( &clientTime, &serverTime,           /* Send Path times are 68 years apart */
                                &serverTime, &serverTime,           /* Receive path times are the same. */
                                SntpSuccess,
                                TO_MS( YEARS_68_IN_SECONDS / 2 ) ); /* Expected offset of 34 years. */

    /* Now test the contrived case when only the receive network path
     * represents timestamps that overflow but the send network path
     * has timestamps that do not overflow.
     * As only the single network path contains time difference of 68 years,
     * the expected clock-offset, being an average of the network paths, is
     * 34 years of duration. */
    testClockOffsetCalculation( &clientTime, &clientTime,           /* Send Path times are the same, i.e. don't overflow */
                                &serverTime, &clientTime,           /* Receive path times are 68 years apart. */
                                SntpSuccess,
                                TO_MS( YEARS_68_IN_SECONDS / 2 ) ); /* Expected offset of 34 years. */
}

void test_Sntp_DeserializeResponse_ClockOffset_Milliseconds_Cases( void )
{
    SntpTimestamp_t clientTime =
    {
        .seconds   = 0,
        /* 500 milliseconds. */
        .fractions = 500 * 1000 * SNTP_FRACTION_VALUE_PER_MICROSECOND
    };

    /* Fill buffer with general SNTP response data. */
    fillValidSntpResponseData( testBuffer, &clientTime );

    SntpTimestamp_t serverTime =
    {
        .seconds   = clientTime.seconds,
        .fractions = clientTime.fractions
    };

    /* Test when server is ahead of client time. */
    serverTime.fractions = 700 * 1000 * SNTP_FRACTION_VALUE_PER_MICROSECOND; /* 700 milliseconds. */
    testClockOffsetCalculation( &clientTime, &serverTime,                    /* Send Path times are 68 years apart */
                                &serverTime, &clientTime,                    /* Receive path times are the same. */
                                SntpSuccess, 200 );

    /* Test when server is behind client time. */
    serverTime.fractions = 100 * 1000 * SNTP_FRACTION_VALUE_PER_MICROSECOND; /* 100 milliseconds. */
    testClockOffsetCalculation( &clientTime, &serverTime,                    /* Send Path times are 68 years apart */
                                &serverTime, &clientTime,                    /* Receive path times are the same. */
                                SntpSuccess, -400 );

    /* Test when complex case of NTP time overflow with client being ahead of server by 3900 milliseconds. */
    serverTime.seconds = UINT32_MAX - 3;                                     /* 4 seconds behind in "seconds" value. */
    serverTime.fractions = 600 * 1000 * SNTP_FRACTION_VALUE_PER_MICROSECOND; /* 100 milliseconds ahead. */
    testClockOffsetCalculation( &clientTime, &serverTime,                    /* Send Path times are 68 years apart */
                                &serverTime, &clientTime,                    /* Receive path times are the same. */
                                SntpSuccess, -3900 );
}

/**
 * @brief Test that @ref Sntp_DeserializeResponse API can process an accepted
 * SNTP server response, and calculate the clock offset for non-overflow cases
 * (i.e. when the client and server times are within 34 years of each other).
 */
void test_DeserializeResponse_AcceptedResponse_Nominal_Case( void )
{
    SntpTimestamp_t clientTxTime = TEST_TIMESTAMP;

    /* Fill buffer with general SNTP response data. */
    fillValidSntpResponseData( testBuffer, &clientTxTime );

    /* Use the the same values for Rx and Tx times for server and client in the first couple
     * of tests for simplicity. */

    /* ==================Test when client and server are in same NTP era.================ */

    /* Test when the client is 20 years ahead of server time to generate a negative offset
     * result.*/
    SntpTimestamp_t serverTxTime =
    {
        clientTxTime.seconds - YEARS_20_IN_SECONDS,
        clientTxTime.fractions
    };
    int32_t expectedOffset = -YEARS_20_IN_SECONDS;

    testClockOffsetCalculation( &clientTxTime, &serverTxTime,
                                &serverTxTime, &clientTxTime,
                                SntpSuccess, TO_MS( expectedOffset ) );

    /* Now test for the client being 20 years behind server time to generate a positive
     * offset result.*/
    serverTxTime.seconds = UINT32_MAX;
    clientTxTime.seconds = UINT32_MAX - YEARS_20_IN_SECONDS;
    expectedOffset = YEARS_20_IN_SECONDS;

    testClockOffsetCalculation( &clientTxTime, &serverTxTime,
                                &serverTxTime, &clientTxTime,
                                SntpSuccess, TO_MS( expectedOffset ) );

    /* ==================Test when client and server are in different NTP eras.================ */

    /* Test when the server is ahead of client to generate a positive clock offset result.*/
    clientTxTime.seconds = UINT32_MAX;                       /* Client is in NTP era 0. */
    serverTxTime.seconds = UINT32_MAX + YEARS_20_IN_SECONDS; /* Server is in NTP era 1. */
    expectedOffset = YEARS_20_IN_SECONDS;

    testClockOffsetCalculation( &clientTxTime, &serverTxTime,
                                &serverTxTime, &clientTxTime,
                                SntpSuccess, TO_MS( expectedOffset ) );

    /* Test when the client is ahead of server to generate a negative clock offset result.*/
    clientTxTime.seconds = UINT32_MAX + YEARS_20_IN_SECONDS; /* Client is in NTP era 1. */
    serverTxTime.seconds = UINT32_MAX;                       /* Server is in NTP era 0. */
    expectedOffset = -YEARS_20_IN_SECONDS;

    testClockOffsetCalculation( &clientTxTime, &serverTxTime,
                                &serverTxTime, &clientTxTime,
                                SntpSuccess, TO_MS( expectedOffset ) );

    /* Now test with different values for T1 (client Tx), T2 (server Rx), T3 (server Tx) and T4 (client Rx)
     * that are used in the clock-offset calculation.
     * The test case uses 2 seconds as network delay on both Client -> Server and Server -> Client path
     * and 2 seconds for server processing time between receiving SNTP request and sending SNTP response */
    clientTxTime.seconds = UINT32_MAX;
    SntpTimestamp_t serverRxTime =
    {
        clientTxTime.seconds + YEARS_20_IN_SECONDS + 2,
        serverTxTime.fractions
    };

    serverTxTime.seconds = serverRxTime.seconds + 2;
    SntpTimestamp_t clientRxTime =
    {
        clientTxTime.seconds + 6, /* 2 seconds each for Client -> Server, Server -> Server,
                                   * Server -> Client */
        clientTxTime.fractions
    };

    expectedOffset = YEARS_20_IN_SECONDS;

    testClockOffsetCalculation( &clientTxTime, &serverRxTime,
                                &serverTxTime, &clientRxTime,
                                SntpSuccess, TO_MS( expectedOffset ) );
}

/**
 * @brief Test that @ref Sntp_DeserializeResponse API can de-serialize leap-second
 * information in an accepted SNTP response packet from a server.
 */
void test_DeserializeResponse_AcceptedResponse_LeapSecond( void )
{
    SntpTimestamp_t clientTime = TEST_TIMESTAMP;
    SntpTimestamp_t serverTime = TEST_TIMESTAMP;

    /* Fill buffer with general SNTP response data. */
    fillValidSntpResponseData( testBuffer, &clientTime );

    /* Update the response packet with the server time. */
    addTimestampToResponseBuffer( &serverTime,
                                  testBuffer,
                                  SNTP_PACKET_RX_TIMESTAMP_FIRST_BYTE_POS );
    addTimestampToResponseBuffer( &serverTime,
                                  testBuffer,
                                  SNTP_PACKET_TX_TIMESTAMP_FIRST_BYTE_POS );

#define TEST_LEAP_SECOND_DESERIALIZATION( expectedLeapSecond )                                            \
    do {                                                                                                  \
        /* Call the API under test. */                                                                    \
        TEST_ASSERT_EQUAL( SntpSuccess, Sntp_DeserializeResponse( &clientTime,                            \
                                                                  &clientTime,                            \
                                                                  testBuffer,                             \
                                                                  sizeof( testBuffer ),                   \
                                                                  &parsedData ) );                        \
                                                                                                          \
        /* As the clock and server times are same, the clock offset, should be zero. */                   \
        TEST_ASSERT_EQUAL( 0, parsedData.clockOffsetMs );                                                 \
                                                                                                          \
        /* Validate other fields in the output parameter. */                                              \
        TEST_ASSERT_EQUAL( 0, memcmp( &parsedData.serverTime, &serverTime, sizeof( SntpTimestamp_t ) ) ); \
        TEST_ASSERT_EQUAL( expectedLeapSecond, parsedData.leapSecondType );                               \
        TEST_ASSERT_EQUAL( SNTP_KISS_OF_DEATH_CODE_NONE, parsedData.rejectedResponseCode );               \
    } while( 0 )

    /* Update SNTP response packet to indicate an upcoming leap second insertion. */
    testBuffer[ 0 ] = ( LastMinuteHas61Seconds << SNTP_PACKET_LEAP_INDICATOR_LSB ) |
                      SNTP_PACKET_VERSION_VAL | SNTP_PACKET_MODE_SERVER;
    TEST_LEAP_SECOND_DESERIALIZATION( LastMinuteHas61Seconds );

    /* Update SNTP response packet to indicate an upcoming leap second deletion. */
    testBuffer[ 0 ] = ( LastMinuteHas59Seconds << SNTP_PACKET_LEAP_INDICATOR_LSB ) |
                      SNTP_PACKET_VERSION_VAL | SNTP_PACKET_MODE_SERVER;
    TEST_LEAP_SECOND_DESERIALIZATION( LastMinuteHas59Seconds );
}

/**
 * @brief Tests the @ref Sntp_CalculatePollInterval utility function returns
 * error for invalid parameters passed to the API.
 */
void test_CalculatePollInterval_InvalidParams( void )
{
    uint32_t pollInterval = 0;

    /* Test with invalid clock frequency. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter, Sntp_CalculatePollInterval( 0,
                                                                          100,
                                                                          &pollInterval ) );
    /* Test with invalid desired accuracy. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter, Sntp_CalculatePollInterval( 100,
                                                                          0,
                                                                          &pollInterval ) );

    /* Test with invalid output parameter. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter, Sntp_CalculatePollInterval( 100,
                                                                          50,
                                                                          NULL ) );

    /* Test with parameters that cause poll interval value of less than 1 second. */
    TEST_ASSERT_EQUAL( SntpZeroPollInterval, Sntp_CalculatePollInterval( 10000 /* High Error Clock. */,
                                                                         1 /* High Accuracy Requirement */,
                                                                         &pollInterval ) );
}

/**
 * @brief Tests the @ref Sntp_CalculatePollInterval utility function calculates
 * the poll interval period as the closes power of 2 value for achieving the
 * desired clock accuracy.
 */
void test_CalculatePollInterval_Nominal( void )
{
    uint32_t pollInterval = 0;
    uint32_t expectedInterval = 0;

    /* Test the SNTPv4 specification example of 200 PPM clock frequency and
     * 1 minute of desired accuracy. */
    expectedInterval = 0x00040000;
    TEST_ASSERT_EQUAL( SntpSuccess, Sntp_CalculatePollInterval( 200 /* Clock Tolerance */,
                                                                1 /* minute */ * 60 * 1000 /* Desired Accuracy */,
                                                                &pollInterval ) );
    TEST_ASSERT_EQUAL( expectedInterval, pollInterval );

    /* Test another case where the exact poll interval for achieving desired frequency
     * is an exponent of 2 value. For 512 seconds (or 2^9) poll interval, the maximum
     * clock drift with 125 PPM is 125 * 512 = 64000 microseconds = 64 milliseconds.  */
    expectedInterval = 0x00000200;
    TEST_ASSERT_EQUAL( SntpSuccess, Sntp_CalculatePollInterval( 125 /* Clock Tolerance (PPM) */,
                                                                64 /* Desired Accuracy (ms)*/,
                                                                &pollInterval ) );

    /* Test for maximum possible value of calculated poll interval when the clock frequency
     * tolerance is minimum (i.e. 1 PPM or high accuracy system clock ) but the desired accuracy
     * is very low (i.e. largest value of 16 bit parameter as 65535 ms OR ~ 1 minute).
     * This test proves that the 32-bit
     * width of poll integer value can hold the largest calculation of poll interval value. */
    expectedInterval = 0x02000000; /* 536,870,912 seconds OR ~ 17 years */
    TEST_ASSERT_EQUAL( SntpSuccess, Sntp_CalculatePollInterval( 1 /* Clock Tolerance (PPM) */,
                                                                UINT16_MAX /* Desired Accuracy (ms)*/,
                                                                &pollInterval ) );
    TEST_ASSERT_EQUAL( expectedInterval, pollInterval );
}


/**
 * @brief Tests the @ref Sntp_ConvertToUnixTime utility function returns
 * expected error when invalid parameters or unsupported timestamps are passed.
 */
void test_ConvertToUnixTime_InvalidParams( void )
{
    SntpTimestamp_t sntpTime;

    /* Use same memory for UNIX seconds and microseconds as we are not
     * testing those values. */
    uint32_t unixTime;

    /* Test with NULL SNTP time. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter, Sntp_ConvertToUnixTime( NULL,
                                                                      &unixTime,
                                                                      &unixTime ) );
    /* Test with NULL output parameters. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter, Sntp_ConvertToUnixTime( &sntpTime,
                                                                      NULL,
                                                                      &unixTime ) );
    TEST_ASSERT_EQUAL( SntpErrorBadParameter, Sntp_ConvertToUnixTime( &sntpTime,
                                                                      &unixTime,
                                                                      NULL ) );

    /* Test with time before UNIX epoch or 1st Jan 1970 .*/
    sntpTime.seconds = SNTP_TIME_AT_UNIX_EPOCH_SECS - 5;
    TEST_ASSERT_EQUAL( SntpErrorTimeNotSupported, Sntp_ConvertToUnixTime( &sntpTime,
                                                                          &unixTime,
                                                                          &unixTime ) );

    /* Test with timestamp that after largest UNIX time for signed 32-bit integer systems
     * (i.e. after 18 Jan 2036 3:14:07) */
    sntpTime.seconds = SNTP_TIME_AT_LARGEST_UNIX_TIME_SECS + 5;
    TEST_ASSERT_EQUAL( SntpErrorTimeNotSupported, Sntp_ConvertToUnixTime( &sntpTime,
                                                                          &unixTime,
                                                                          &unixTime ) );
}

/**
 * @brief Tests the @ref Sntp_ConvertToUnixTime utility function returns
 * expected error when invalid parameters or unsupported timestamps are passed.
 */
void test_ConvertToUnixTime_Nominal( void )
{
    SntpTimestamp_t sntpTime = TEST_TIMESTAMP;
    uint32_t unixTimeSecs;
    uint32_t unixTimeMs;

#define TEST_SNTP_TO_UNIX_CONVERSION( sntpTimeSecs, sntpTimeFracs,               \
                                      expectedUnixTimeSecs, expectedUnixTimeMs ) \
    do {                                                                         \
        /* Set the SNTP timestamps. */                                           \
        sntpTime.seconds = sntpTimeSecs;                                         \
        sntpTime.fractions = sntpTimeFracs;                                      \
                                                                                 \
        /* Call API under test. */                                               \
        TEST_ASSERT_EQUAL( SntpSuccess, Sntp_ConvertToUnixTime( &sntpTime,       \
                                                                &unixTimeSecs,   \
                                                                &unixTimeMs ) ); \
        /* Validate the generated UNIX time. */                                  \
        TEST_ASSERT_EQUAL( expectedUnixTimeSecs, unixTimeSecs );                 \
        TEST_ASSERT_EQUAL( expectedUnixTimeMs, unixTimeMs );                     \
    } while( 0 )

    /* Test with SNTP time at UNIX epoch. .*/
    TEST_SNTP_TO_UNIX_CONVERSION( SNTP_TIME_AT_UNIX_EPOCH_SECS, /* Sntp Seconds. */
                                  0 /* Sntp  Fractions. */,
                                  0 /* Unix Seconds */,
                                  0 /* Unix Microseconds */ );

    /* Test with SNTP time in the range between UNIX epoch and Smallest SNTP time in Era 1 .*/
    TEST_SNTP_TO_UNIX_CONVERSION( SNTP_TIME_AT_UNIX_EPOCH_SECS + 1000 /* Sntp Seconds. */,
                                  500 /* Sntp  Fractions. */,
                                  1000 /* Unix Seconds */,
                                  500 / SNTP_FRACTION_VALUE_PER_MICROSECOND /* Unix Microseconds */ );

    /* Test with SNTP time at largest SNTP time in Era 0 .*/
    TEST_SNTP_TO_UNIX_CONVERSION( UINT32_MAX /* Sntp Seconds. */,
                                  0 /* Sntp Fractions. */,
                                  UINT32_MAX - SNTP_TIME_AT_UNIX_EPOCH_SECS, /* Unix Seconds */
                                  0 /* Unix Microseconds */ );

    /* Test with SNTP time at smallest SNTP time in Era 1 .*/
    TEST_SNTP_TO_UNIX_CONVERSION( UINT32_MAX + 1 /* Sntp Seconds. */,
                                  0 /* Sntp Fractions. */,
                                  UNIX_TIME_SECS_AT_SNTP_ERA_1_SMALLEST_TIME, /* Unix Seconds */
                                  0 /* Unix Microseconds */ );

    /* Test SNTP time in the range [SNTP Era 1 Epoch, 32-bit signed UNIX max time] .*/
    TEST_SNTP_TO_UNIX_CONVERSION( UINT32_MAX + 1000 /* Sntp Seconds. */,
                                  4000 /* Sntp Fractions. */,
                                  UNIX_TIME_SECS_AT_SNTP_ERA_1_SMALLEST_TIME + 999, /* Unix Seconds */
                                  4000 / SNTP_FRACTION_VALUE_PER_MICROSECOND /* Unix Microseconds */ );

    /* Test with SNTP time that represents the 32-bit signed maximum UNIX time
     * (i.e. at 19 Jan 2038 3:14:07 )  .*/
    TEST_SNTP_TO_UNIX_CONVERSION( SNTP_TIME_AT_LARGEST_UNIX_TIME_SECS /* Sntp Seconds. */,
                                  0 /* Sntp Fractions. */,
                                  INT32_MAX, /* Unix Seconds */
                                  0 /* Unix Microseconds */ );
}
