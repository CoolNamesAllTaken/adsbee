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

/* Unity include. */
#include "unity.h"

/*#define SNTP_DO_NOT_USE_CUSTOM_CONFIG    1 */

/* coreSNTP Client API include */
#include "core_sntp_client.h"

/* Include mock header of Serializer API of coreSNTP. */
#include "mock_core_sntp_serializer.h"

/* Test IPv4 address for time server. */
#define TEST_SERVER_ADDR          ( 0xAABBCCDD )

/* Test server response timeout (in ms). */
#define TEST_RESPONSE_TIMEOUT     ( 500 )

/* Test block time for calls to Sntp_ReceiveTimeResponse API. */
#define TEST_RECV_BLOCK_TIME      ( TEST_RESPONSE_TIMEOUT / 2 )

/* Test values for the "last request time" state of the SNTP context. */
#define LAST_REQUEST_TIME_SECS    10
#define LAST_REQUEST_TIME_MS      100

/* Test block time for the Sntp_SendRequestTime API.
 * This serves as the timeout value for send operations. */
#define SEND_TIMEOUT_MS           10

/* Utility to convert milliseconds to fractions value in
 * SNTP timestamp. */
#define CONVERT_MS_TO_FRACTIONS( MS ) \
    ( MS * 1000 * SNTP_FRACTION_VALUE_PER_MICROSECOND )

/* Test definition of NetworkContext_t structure. */
typedef struct NetworkContext
{
    int udpSocket;
} NetworkContext_t;

/* Test definition of SntpAuthContext_t structure. */
typedef struct SntpAuthContext
{
    uint32_t keyId;
} SntpAuthContext_t;

/* Global variables common to test cases. */
static SntpContext_t context;
static uint8_t testBuffer[ 100 ];
static SntpServerInfo_t testServers[] =
{
    {
        "my.ntp.server.1",
        strlen( "my.ntp.server.1" ),
        SNTP_DEFAULT_SERVER_PORT
    },
    {
        "my.ntp.server.2",
        strlen( "my.ntp.server.2" ),
        SNTP_DEFAULT_SERVER_PORT
    }
};
static UdpTransportInterface_t transportIntf;
static NetworkContext_t netContext;
static SntpAuthenticationInterface_t authIntf;
static SntpAuthContext_t authContext;

/* Variables for configuring behavior of interface functions. */
static bool dnsResolveRetCode = true;
static uint32_t dnsResolveAddr = TEST_SERVER_ADDR;
static SntpTimestamp_t currentTimeList[ 4 ];
static uint8_t currentTimeIndex;
static size_t expectedBytesToSend = SNTP_PACKET_BASE_SIZE;
static int32_t udpSendRetCodes[ 2 ];
static uint8_t currentUdpSendCodeIndex;
static int32_t udpRecvRetCodes[ 3 ];
static uint8_t currentUdpRecvCodeIndex;
static size_t expectedBytesToRecv = SNTP_PACKET_BASE_SIZE;
static SntpStatus_t generateClientAuthRetCode = SntpSuccess;
static uint16_t authCodeSize;
static SntpStatus_t validateServerAuthRetCode = SntpSuccess;

/* Output parameter for mock of Sntp_DeserializeResponse API. */
static SntpResponseData_t mockResponseData =
{
    .clockOffsetMs        = 1000,
    .leapSecondType       = NoLeapSecond,
    .rejectedResponseCode = SNTP_KISS_OF_DEATH_CODE_NONE,
    .serverTime           =
    {
        .seconds          = 0xAABBCCDD,
        .fractions        = 0x11223344
    }
};

/* ========================= Helper Functions ============================ */

/* Test definition of the @ref SntpResolveDns_t interface. */
static bool dnsResolve( const SntpServerInfo_t * pServerAddr,
                        uint32_t * pIpV4Addr )
{
    TEST_ASSERT_NOT_NULL( pServerAddr );
    TEST_ASSERT_NOT_NULL( pIpV4Addr );

    *pIpV4Addr = TEST_SERVER_ADDR;

    return dnsResolveRetCode;
}

/* Test definition of the @ref SntpGetTime_t interface. */
static void getTime( SntpTimestamp_t * pCurrentTime )
{
    TEST_ASSERT_NOT_NULL( pCurrentTime );

    /* Set the current time output parameter based on index
     * in the time list. */
    pCurrentTime->seconds = currentTimeList[ currentTimeIndex ].seconds;
    pCurrentTime->fractions = currentTimeList[ currentTimeIndex ].fractions;

    /* Increment the index to point to the next in the list. */
    currentTimeIndex = ( currentTimeIndex + 1 ) %
                       ( sizeof( currentTimeList ) / sizeof( SntpTimestamp_t ) );
}

/* Test definition of the @ref SntpSetTime_t interface. */
static void setTime( const SntpServerInfo_t * pTimeServer,
                     const SntpTimestamp_t * pServerTime,
                     int64_t clockOffsetMs,
                     SntpLeapSecondInfo_t leapSecondInfo )
{
    TEST_ASSERT_NOT_NULL( pTimeServer );
    TEST_ASSERT_NOT_NULL( pServerTime );
    TEST_ASSERT_EQUAL( mockResponseData.clockOffsetMs, clockOffsetMs );
    TEST_ASSERT_EQUAL( mockResponseData.leapSecondType, leapSecondInfo );
    TEST_ASSERT_EQUAL_MEMORY( &mockResponseData.serverTime, pServerTime, sizeof( SntpTimestamp_t ) );
}

/* Test definition of the @ref UdpTransportSendTo_t interface. */
static int32_t UdpSendTo( NetworkContext_t * pNetworkContext,
                          uint32_t serverAddr,
                          uint16_t serverPort,
                          const void * pBuffer,
                          uint16_t bytesToSend )
{
    TEST_ASSERT_EQUAL_PTR( &netContext, pNetworkContext );
    TEST_ASSERT_NOT_NULL( pBuffer );
    TEST_ASSERT_EQUAL( dnsResolveAddr, serverAddr );
    TEST_ASSERT_EQUAL( SNTP_DEFAULT_SERVER_PORT, serverPort );
    TEST_ASSERT_EQUAL( expectedBytesToSend, bytesToSend );

    int32_t retCode = udpSendRetCodes[ currentUdpSendCodeIndex ];

    /* Increment the index in the return code list to the next. */
    currentUdpSendCodeIndex = ( currentUdpSendCodeIndex + 1 ) %
                              ( sizeof( udpSendRetCodes ) / sizeof( int32_t ) );

    return retCode;
}

/* Test definition of the @ref UdpTransportRecvFrom_t interface. */
static int32_t UdpRecvFrom( NetworkContext_t * pNetworkContext,
                            uint32_t serverAddr,
                            uint16_t serverPort,
                            void * pBuffer,
                            uint16_t bytesToRecv )
{
    TEST_ASSERT_EQUAL_PTR( &netContext, pNetworkContext );
    TEST_ASSERT_NOT_NULL( pBuffer );
    TEST_ASSERT_EQUAL( context.currentServerAddr, serverAddr );
    TEST_ASSERT_EQUAL( SNTP_DEFAULT_SERVER_PORT, serverPort );
    TEST_ASSERT_EQUAL( expectedBytesToRecv, bytesToRecv );

    int32_t retCode = udpRecvRetCodes[ currentUdpRecvCodeIndex ];

    /* Increment the index in the return code list to the next. */
    currentUdpRecvCodeIndex = ( currentUdpRecvCodeIndex + 1 ) %
                              ( sizeof( udpRecvRetCodes ) / sizeof( int32_t ) );
    return retCode;
}

/* Test definition for @ref SntpGenerateAuthCode_t interface. */
static SntpStatus_t generateClientAuth( SntpAuthContext_t * pContext,
                                        const SntpServerInfo_t * pTimeServer,
                                        void * pBuffer,
                                        size_t bufferSize,
                                        uint16_t * pAuthCodeSize )
{
    TEST_ASSERT_EQUAL_PTR( &authContext, pContext );
    TEST_ASSERT_NOT_NULL( pTimeServer );
    TEST_ASSERT_EQUAL_PTR( testBuffer, pBuffer );
    TEST_ASSERT_NOT_NULL( pAuthCodeSize );
    TEST_ASSERT_EQUAL( context.bufferSize, bufferSize );
    TEST_ASSERT_GREATER_OR_EQUAL( SNTP_PACKET_BASE_SIZE, bufferSize );

    *pAuthCodeSize = authCodeSize;

    return generateClientAuthRetCode;
}

/* Test definition for @ref SntpValidateServerAuth_t interface. */
static SntpStatus_t validateServerAuth( SntpAuthContext_t * pContext,
                                        const SntpServerInfo_t * pTimeServer,
                                        const void * pResponseData,
                                        uint16_t responseSize )
{
    TEST_ASSERT_EQUAL_PTR( &authContext, pContext );
    TEST_ASSERT_NOT_NULL( pTimeServer );
    TEST_ASSERT_EQUAL_PTR( testBuffer, pResponseData );
    TEST_ASSERT_GREATER_OR_EQUAL( SNTP_PACKET_BASE_SIZE, responseSize );
    TEST_ASSERT_EQUAL( context.sntpPacketSize, responseSize );

    return validateServerAuthRetCode;
}

/* Enumeration for the API functions of the SNTP Client layer. */
enum SntpClientApiType
{
    ApiInvalid,
    ApiSendTimeRequest,
    ApiReceiveTimeResponse
};

/* Common function for testing all scenarios of invalid context. */
static void testApiForInvalidContextCases( enum SntpClientApiType api )
{
#define SELECT_API_AND_TEST_INVALID_CONTEXT( api, context )                                               \
    do {                                                                                                  \
        if( api == ApiSendTimeRequest )                                                                   \
        {                                                                                                 \
            TEST_ASSERT_EQUAL( SntpErrorContextNotInitialized, Sntp_SendTimeRequest( &context,            \
                                                                                     rand() % UINT32_MAX, \
                                                                                     SEND_TIMEOUT_MS ) ); \
        }                                                                                                 \
        else                                                                                              \
        {                                                                                                 \
            TEST_ASSERT_EQUAL( SntpErrorContextNotInitialized, Sntp_ReceiveTimeResponse( &context, 0 ) ); \
        }                                                                                                 \
    } while( 0 )


    /* Start with a non-initialized context. */
    SntpContext_t testContext;
    memset( &testContext, 0, sizeof( SntpContext_t ) );
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );

    /* Now fully initialize context and then test all scenarios with only one member being invalid. */
    TEST_ASSERT_EQUAL( SntpSuccess,
                       Sntp_Init( &testContext,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  &authIntf ) );

    /* Test with invalid servers in the context. */
    testContext.pTimeServers = NULL;
    testContext.numOfServers = 0;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );
    testContext.pTimeServers = testServers;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );

    /* Reset the server list to be valid. */
    testContext.pTimeServers = testServers;
    testContext.numOfServers = sizeof( testServers ) / sizeof( SntpServerInfo_t );

    /* Test with invalid network buffer and/or buffer size in the context. */
    testContext.pNetworkBuffer = NULL;
    testContext.bufferSize = 0;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );
    testContext.pNetworkBuffer = testBuffer;
    testContext.bufferSize = SNTP_PACKET_BASE_SIZE - 1;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );

    /* Reset the network buffer and size to be valid in the context. */
    testContext.pNetworkBuffer = testBuffer;
    testContext.bufferSize = sizeof( testBuffer );

    /* Test with invalid DNS Resolution interface function. */
    testContext.resolveDnsFunc = NULL;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );

    /* Reset the DNS Resolution function pointer to be valid. */
    testContext.resolveDnsFunc = dnsResolve;

    /* Test with invalid SntpGetTime_t interface function. */
    testContext.getTimeFunc = NULL;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );

    /* Reset the SntpGetTime_t function pointer to be valid. */
    testContext.getTimeFunc = getTime;

    /* Test with invalid SntpSetTime_t interface function. */
    testContext.setTimeFunc = NULL;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );

    /* Reset the SntpSetTime_t function pointer to be valid. */
    testContext.setTimeFunc = setTime;

    /* Test with invalid SntpSetTime_t interface function. */
    testContext.networkIntf.recvFrom = NULL;
    testContext.networkIntf.sendTo = NULL;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );
    testContext.networkIntf.sendTo = UdpSendTo;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );
    testContext.networkIntf.sendTo = NULL;
    testContext.networkIntf.recvFrom = UdpRecvFrom;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );

    /* Reset the network interface function pointers to be valid. */
    testContext.networkIntf.sendTo = UdpSendTo;
    testContext.networkIntf.recvFrom = UdpRecvFrom;

    /* Test cases when only one of the authentication interface functions is set,
     * instead of both. */
    testContext.authIntf.generateClientAuth = NULL;
    testContext.authIntf.validateServerAuth = validateServerAuth;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );
    testContext.authIntf.generateClientAuth = generateClientAuth;
    testContext.authIntf.validateServerAuth = NULL;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );

    /* Test with invalid value of the sntpPacketSize member of the context. */
    testContext.sntpPacketSize = SNTP_PACKET_BASE_SIZE - 1;
    SELECT_API_AND_TEST_INVALID_CONTEXT( api, testContext );
}

/* Helper function to set values in the currentTimeList that is used in the
 * test implementation of the SntpGetTime_t interface. */
static void setSystemTimeAtIndex( size_t index,
                                  uint32_t seconds,
                                  uint32_t milliseconds )
{
    currentTimeList[ index ].seconds = seconds;
    currentTimeList[ index ].fractions = CONVERT_MS_TO_FRACTIONS( milliseconds );
}


/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    /* Reset the global variables. */
    dnsResolveRetCode = true;
    dnsResolveAddr = TEST_SERVER_ADDR;
    generateClientAuthRetCode = SntpSuccess;
    validateServerAuthRetCode = SntpSuccess;
    currentTimeIndex = 0;
    authCodeSize = 0;
    expectedBytesToSend = SNTP_PACKET_BASE_SIZE;
    expectedBytesToRecv = SNTP_PACKET_BASE_SIZE;

    /* Reset array of UDP I/O functions return codes. */
    memset( udpSendRetCodes, 0, sizeof( udpSendRetCodes ) );
    currentUdpSendCodeIndex = 0;
    memset( udpRecvRetCodes, 0, sizeof( udpRecvRetCodes ) );
    currentUdpRecvCodeIndex = 0;

    /* Reset the current time list for the SntpGetTime_t
     * interface function. */
    memset( currentTimeList, 0, sizeof( currentTimeList ) );

    /* Set the transport interface object. */
    transportIntf.pUserContext = &netContext;
    transportIntf.sendTo = UdpSendTo;
    transportIntf.recvFrom = UdpRecvFrom;

    /* Set the auth interface object. */
    authIntf.pAuthContext = &authContext;
    authIntf.generateClientAuth = generateClientAuth;
    authIntf.validateServerAuth = validateServerAuth;

    /* Clear the network buffer. */
    memset( &testBuffer, 0, sizeof( testBuffer ) );

    /* Initialize context. */
    TEST_ASSERT_EQUAL( SntpSuccess,
                       Sntp_Init( &context,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  &authIntf ) );

    /* Update the "Last Request Time" state of the context to a non-zero value to
     * check that it gets cleared by the library only AFTER receiving a valid SNTP response. */
    context.lastRequestTime.seconds = LAST_REQUEST_TIME_SECS;
    context.lastRequestTime.fractions = CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS );
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
 * @brief Test @ref Sntp_Init with invalid parameters.
 */
void test_Init_InvalidParams( void )
{
    /* Pass invalid context memory. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( NULL,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  NULL ) );

    /* Pass invalid list of time servers. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( &context,
                                  NULL,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  NULL ) );
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( &context,
                                  testServers,
                                  0,
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  NULL ) );

    /* Pass invalid network buffer. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( &context,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  NULL,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  NULL ) );
    TEST_ASSERT_EQUAL( SntpErrorBufferTooSmall,
                       Sntp_Init( &context,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  SNTP_PACKET_BASE_SIZE / 2,
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  NULL ) );

    /* Pass invalid required interface definitions. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( &context,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  NULL,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  NULL ) );
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( &context,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  NULL,
                                  setTime,
                                  &transportIntf,
                                  NULL ) );
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( &context,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  NULL,
                                  &transportIntf,
                                  NULL ) );
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( &context,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  NULL,
                                  NULL ) );

    /* Pass valid transport interface object but invalid members. */
    transportIntf.recvFrom = NULL;
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( &context,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  NULL ) );
    transportIntf.recvFrom = UdpRecvFrom;
    transportIntf.sendTo = NULL;
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( &context,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  NULL ) );

    /* Set the transport interface object to be valid for next test. */
    transportIntf.sendTo = UdpSendTo;

    /* Pass valid authentication interface object but invalid members. */
    authIntf.generateClientAuth = NULL;
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( &context,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  &authIntf ) );
    authIntf.generateClientAuth = generateClientAuth;
    authIntf.validateServerAuth = NULL;
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_Init( &context,
                                  testServers,
                                  sizeof( testServers ) / sizeof( SntpServerInfo_t ),
                                  TEST_RESPONSE_TIMEOUT,
                                  testBuffer,
                                  sizeof( testBuffer ),
                                  dnsResolve,
                                  getTime,
                                  setTime,
                                  &transportIntf,
                                  &authIntf ) );
}

/**
 * @brief Test @ref Sntp_Init API correctly initializes a context.
 */
void test_Init_Nominal( void )
{
#define TEST_SNTP_INIT_SUCCESS( pAuthIntf )                                                                    \
    do {                                                                                                       \
        /* Call the API under test. */                                                                         \
        TEST_ASSERT_EQUAL( SntpSuccess,                                                                        \
                           Sntp_Init( &context,                                                                \
                                      testServers,                                                             \
                                      sizeof( testServers ) / sizeof( SntpServerInfo_t ),                      \
                                      TEST_RESPONSE_TIMEOUT,                                                   \
                                      testBuffer,                                                              \
                                      sizeof( testBuffer ),                                                    \
                                      dnsResolve,                                                              \
                                      getTime,                                                                 \
                                      setTime,                                                                 \
                                      &transportIntf,                                                          \
                                      pAuthIntf ) );                                                           \
                                                                                                               \
        /* Make sure that the passed parameters have been set in the context. */                               \
        TEST_ASSERT_EQUAL( testServers, context.pTimeServers );                                                \
        TEST_ASSERT_EQUAL( sizeof( testServers ) / sizeof( SntpServerInfo_t ), context.numOfServers );         \
        TEST_ASSERT_EQUAL_PTR( testBuffer, context.pNetworkBuffer );                                           \
        TEST_ASSERT_EQUAL( TEST_RESPONSE_TIMEOUT, context.responseTimeoutMs );                                 \
        TEST_ASSERT_EQUAL( sizeof( testBuffer ), context.bufferSize );                                         \
        TEST_ASSERT_EQUAL_PTR( dnsResolve, context.resolveDnsFunc );                                           \
        TEST_ASSERT_EQUAL_PTR( getTime, context.getTimeFunc );                                                 \
        TEST_ASSERT_EQUAL_PTR( setTime, context.setTimeFunc );                                                 \
        TEST_ASSERT_EQUAL_MEMORY( &transportIntf,                                                              \
                                  &context.networkIntf,                                                        \
                                  sizeof( UdpTransportInterface_t ) );                                         \
        if( pAuthIntf == NULL )                                                                                \
        {                                                                                                      \
            TEST_ASSERT_NULL( context.authIntf.pAuthContext );                                                 \
            TEST_ASSERT_NULL( context.authIntf.generateClientAuth );                                           \
            TEST_ASSERT_NULL( context.authIntf.validateServerAuth );                                           \
        }                                                                                                      \
        else                                                                                                   \
        {                                                                                                      \
            TEST_ASSERT_EQUAL_MEMORY( &authIntf, &context.authIntf, sizeof( SntpAuthenticationInterface_t ) ); \
        }                                                                                                      \
                                                                                                               \
        /* Validate the initialization of the state members of the context. */                                 \
        TEST_ASSERT_EQUAL( 0, context.currentServerIndex );                                                    \
        TEST_ASSERT_EQUAL( 0, context.currentServerAddr );                                                     \
        TEST_ASSERT_EQUAL( 0, context.lastRequestTime.seconds );                                               \
        TEST_ASSERT_EQUAL( 0, context.lastRequestTime.fractions );                                             \
        TEST_ASSERT_EQUAL( SNTP_PACKET_BASE_SIZE, context.sntpPacketSize );                                    \
    } while( 0 )

    /* Test when an authentication interface is not passed. */
    TEST_SNTP_INIT_SUCCESS( NULL );

    /* Reset the context memory. */
    memset( &context, 0, sizeof( SntpContext_t ) );

    /* Test with a valid authentication interface. */
    TEST_SNTP_INIT_SUCCESS( &authIntf );
}

/**
 * @brief Validate the behavior of @ref Sntp_SendTimeRequest for invalid
 * parameters
 */
void test_Sntp_SendTimeRequest_InvalidParams()
{
    /* Test with NULL context parameter. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_SendTimeRequest( NULL, rand() % UINT32_MAX, SEND_TIMEOUT_MS ) );

    /* Test all cases of context with invalid members. */
    testApiForInvalidContextCases( ApiSendTimeRequest );

    /* Reset the context member for current server to a valid value. */
    context.currentServerIndex = 0U;
}

/**
 * @brief Validate the behavior of @ref Sntp_SendTimeRequest when the DNS resolution
 * of time server fails.
 */
void test_Sntp_SendTimeRequest_Dns_Failure()
{
    /* Test case when DNS resolution of server fails. */
    dnsResolveRetCode = false;
    TEST_ASSERT_EQUAL( SntpErrorDnsFailure,
                       Sntp_SendTimeRequest( &context, rand() % UINT32_MAX, SEND_TIMEOUT_MS ) );
}

/**
 * @brief Validate the behavior of @ref Sntp_SendTimeRequest when authentication
 * interface returns error of the request buffer being insufficient in size for
 * adding authentication data.
 */
void test_Sntp_SendTimeRequest_Auth_Failure_BufferTooSmall()
{
    /* Set the behavior of the serializer function dependency to always return
     * success. */
    Sntp_SerializeRequest_IgnoreAndReturn( SntpSuccess );

    /* Test case when authentication interface call for adding client authentication
     * fails. */
    generateClientAuthRetCode = SntpErrorBufferTooSmall;
    TEST_ASSERT_EQUAL( SntpErrorBufferTooSmall,
                       Sntp_SendTimeRequest( &context, rand() % UINT32_MAX, SEND_TIMEOUT_MS ) );
}

/**
 * @brief Validate the behavior of @ref Sntp_SendTimeRequest when failure from
 * the authentication interface function, that generates client authentication,
 * returning failure.
 */
void test_Sntp_SendTimeRequest_Auth_Failure_InternalError()
{
    /* Set the behavior of the serializer function dependency to always return
     * success. */
    Sntp_SerializeRequest_IgnoreAndReturn( SntpSuccess );

    generateClientAuthRetCode = SntpErrorAuthFailure;
    TEST_ASSERT_EQUAL( SntpErrorAuthFailure,
                       Sntp_SendTimeRequest( &context, rand() % UINT32_MAX, SEND_TIMEOUT_MS ) );
}

/**
 * @brief Validate that @ref Sntp_SendTimeRequest returns failure when the authentication
 * data size returned by the @ref SntpGenerateAuthCode_t function of authentication interface
 * is invalid, i.e. the size exceeds the buffer capacity for holding authentication data.
 */
void test_Sntp_SendTimeRequest_Auth_Failure_InvalidOutputParam()
{
    /* Set the behavior of the serializer function dependency to always return
     * success. */
    Sntp_SerializeRequest_IgnoreAndReturn( SntpSuccess );

    /* Test when authentication interface returns an invalid authentication data
     * size.*/
    authCodeSize = sizeof( testBuffer ) - SNTP_PACKET_BASE_SIZE + 1; /* 1 byte more than buffer can
                                                                      * take for holding auth data. */
    TEST_ASSERT_EQUAL( SntpErrorAuthFailure,
                       Sntp_SendTimeRequest( &context, rand() % UINT32_MAX, SEND_TIMEOUT_MS ) );
}

/**
 * @brief Validate the behavior of @ref Sntp_SendTimeRequest when transport send operation
 * fails in the first try.
 */
void test_Sntp_SendTimeRequest_Transport_Send_Failure_ErrorOnFirstTry()
{
    /* Set the behavior of the serializer function dependency to always return
     * success. */
    Sntp_SerializeRequest_IgnoreAndReturn( SntpSuccess );

    /* Test case when transport send fails with negative error code sent in the first
     * call to transport interface send function. */
    udpSendRetCodes[ currentUdpSendCodeIndex ] = -2;
    TEST_ASSERT_EQUAL( SntpErrorNetworkFailure,
                       Sntp_SendTimeRequest( &context, rand() % UINT32_MAX, SEND_TIMEOUT_MS ) );
}

/**
 * @brief Validate the behavior of @ref Sntp_SendTimeRequest when transport send operation
 * fails in a retry attempt.
 */
void test_Sntp_SendTimeRequest_Transport_Send_Failure_ErrorOnRetry()
{
    /* Set the behavior of the serializer function dependency to always return
     * success. */
    Sntp_SerializeRequest_IgnoreAndReturn( SntpSuccess );


    /* Test case when transport send fails with negative error code sent after some
     * calls to transport interface send function. */
    udpSendRetCodes[ 0 ] = 0;  /* 1st call sending 0 bytes.*/
    udpSendRetCodes[ 1 ] = -1; /* 2nd call returning error.*/
    TEST_ASSERT_EQUAL( SntpErrorNetworkFailure,
                       Sntp_SendTimeRequest( &context, rand() % UINT32_MAX, SEND_TIMEOUT_MS ) );

    /* Reset the index in the current time list. */
    currentTimeIndex = 0;
    currentUdpSendCodeIndex = 0;
}

/**
 * @brief Validate the behavior of @ref Sntp_SendTimeRequest when retries time
 * out for transport send operation.
 */
void test_Sntp_SendTimeRequest_Transport_Send_Error_RetryTimeout()
{
    /* Set the behavior of the serializer function dependency to always return
     * success. */
    Sntp_SerializeRequest_IgnoreAndReturn( SntpSuccess );

    /* Test case when transport send operation times out due to no data being
     * sent for #SEND_TIMEOUT_MS duration. */
    udpSendRetCodes[ 0 ] = 0;
    udpSendRetCodes[ 1 ] = 0;
    currentTimeList[ 1 ].fractions = 0;                                                  /* SntpGetTime_t call before the loop in sendSntpPacket. */
    currentTimeList[ 2 ].fractions = CONVERT_MS_TO_FRACTIONS( SEND_TIMEOUT_MS / 2 );     /* SntpGetTime_t call in 1st iteration of loop. */
    currentTimeList[ 3 ].fractions = CONVERT_MS_TO_FRACTIONS( ( SEND_TIMEOUT_MS + 1 ) ); /* SntpGetTime_t call in 2nd iteration of loop. */
    TEST_ASSERT_EQUAL( SntpErrorSendTimeout,
                       Sntp_SendTimeRequest( &context, rand() % UINT32_MAX, SEND_TIMEOUT_MS ) );
}

/**
 * @brief Validate that the @ref Sntp_SendTimeRequest API treats partial data being sent
 * by the UDP transport interface as an error because UDP does not support partial sends.
 */
void test_Sntp_SendTimeRequest_Transport_Send_Error_PartialSend()
{
    /* Set the behavior of the serializer function dependency to always return
     * success. */
    Sntp_SerializeRequest_IgnoreAndReturn( SntpSuccess );

    /* Test case when transport send returns partial number of bytes sent. This is
     * incorrect as UDP protocol does not support partial writes. */
    udpSendRetCodes[ 0 ] = 0;                       /* 1st call sending 0 bytes.*/
    udpSendRetCodes[ 1 ] = expectedBytesToSend / 2; /* 2nd call returning partial bytes.*/
    TEST_ASSERT_EQUAL( SntpErrorNetworkFailure,
                       Sntp_SendTimeRequest( &context, rand() % UINT32_MAX, SEND_TIMEOUT_MS ) );
}

/**
 * @brief Validate behavior of @ref Sntp_SendTimeRequest in success cases.
 */
void test_SendTimeRequest_Nominal( void )
{
    uint32_t randNum = ( rand() % UINT32_MAX );

    /* Set the size of authentication data within the SNTP packet. */
    authCodeSize = sizeof( testBuffer ) - SNTP_PACKET_BASE_SIZE;

#define TEST_SUCCESS_CASE( packetSize, timeBeforeLoop, timeIn1stIteration )                                                     \
    do {                                                                                                                        \
        /* Reset indices to lists controlling behavior of interface functions. */                                               \
        currentTimeIndex = 0;                                                                                                   \
        currentUdpSendCodeIndex = 0;                                                                                            \
                                                                                                                                \
        /* Set the parameter expectations and behavior of call to serializer function .*/                                       \
        Sntp_SerializeRequest_ExpectAndReturn( &context.lastRequestTime, randNum,                                               \
                                               testBuffer, sizeof( testBuffer ), SntpSuccess );                                 \
                                                                                                                                \
        /* Update the global variable of expected number of bytes to send with network send function. */                        \
        expectedBytesToSend = packetSize;                                                                                       \
                                                                                                                                \
        /* Set the behavior of the transport send and get time interface functions. */                                          \
        udpSendRetCodes[ 0 ] = 0;                                      /* 1st return value for no data send. */                 \
        udpSendRetCodes[ 1 ] = expectedBytesToSend;                    /* 2nd return value for the packet send. */              \
        currentTimeList[ 1 ].seconds = timeBeforeLoop.seconds;         /* Time call in before loop  in sendSntpPacket. */       \
        currentTimeList[ 1 ].fractions = timeBeforeLoop.fractions;     /* Time call in before loop in sendSntpPacket loop. */   \
        currentTimeList[ 2 ].seconds = timeIn1stIteration.seconds;     /* Time call in 1st iteration of sendSntpPacket loop. */ \
        currentTimeList[ 2 ].fractions = timeIn1stIteration.fractions; /* Time call in 1st iteration of sendSntpPacket loop. */ \
        TEST_ASSERT_EQUAL( SntpSuccess, Sntp_SendTimeRequest( &context, randNum, SEND_TIMEOUT_MS ) );                           \
    } while( 0 )

    SntpTimestamp_t beforeLoopTime;
    SntpTimestamp_t inLoopTime;
    beforeLoopTime.seconds = 0;
    beforeLoopTime.fractions = 0;
    inLoopTime.seconds = 0;
    inLoopTime.fractions = CONVERT_MS_TO_FRACTIONS( SEND_TIMEOUT_MS / 2 );

    /* Test when no authentication interface is provided. */
    context.authIntf.generateClientAuth = NULL;
    context.authIntf.validateServerAuth = NULL;
    TEST_SUCCESS_CASE( SNTP_PACKET_BASE_SIZE, beforeLoopTime, inLoopTime );

    /* Test when an authentication interface is provided. */
    context.authIntf.generateClientAuth = generateClientAuth;
    context.authIntf.validateServerAuth = validateServerAuth;
    TEST_SUCCESS_CASE( SNTP_PACKET_BASE_SIZE + authCodeSize, beforeLoopTime, inLoopTime );

    /* Test edge case when SNTP time overflows (i.e. at 7 Feb 2036 6h 28m 16s UTC )
     * during the send operation. */
    beforeLoopTime.seconds = UINT32_MAX;
    beforeLoopTime.fractions = UINT32_MAX; /* Last time in SNTP era 0. */
    inLoopTime.seconds = 0;                /* Time in SNTP era 1. */
    inLoopTime.fractions = CONVERT_MS_TO_FRACTIONS( SEND_TIMEOUT_MS / 2 );
    /* Test when an authentication interface is provided. */
    TEST_SUCCESS_CASE( SNTP_PACKET_BASE_SIZE + authCodeSize, beforeLoopTime, inLoopTime );
}

/**
 * @brief Validate the behavior of @ref Sntp_ReceiveTimeResponse API for all error cases.
 */
void test_Sntp_ReceiveTimeResponse_InvalidParams()
{
    /* Test with NULL context parameter. */
    TEST_ASSERT_EQUAL( SntpErrorBadParameter,
                       Sntp_ReceiveTimeResponse( NULL, TEST_RESPONSE_TIMEOUT ) );

    /* Test all cases of context with invalid members. */
    testApiForInvalidContextCases( ApiReceiveTimeResponse );
}

/**
 * @brief Validate the behavior of @ref Sntp_ReceiveTimeResponse API for the case
 * when the transport receive operation returns error in the first read attempt within
 * the receive loop of the API.
 */
void test_ReceiveTimeResponse_Transport_Read_Failures_NoRetry( void )
{
    /* Test case when transport receive fails in the first byte read attempt. */
    udpRecvRetCodes[ 0 ] = -1; /* 1st read call. No data read.*/
    TEST_ASSERT_EQUAL( SntpErrorNetworkFailure,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the "last request time" state of the context was not modified from network error. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );
}

/**
 * @brief Validate the behavior of @ref Sntp_ReceiveTimeResponse API for cases
 * when the transport receive operation returns error in a read retry attempt within
 * the receive loop of the API.
 */
void test_ReceiveTimeResponse_Transport_Read_Failures_AfterRetries( void )
{
    /* Set the times to be returned by SntpGetTime_t function to be within the server response timeout
     * as well as block time windows. */
    setSystemTimeAtIndex( 0, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_MS );
    setSystemTimeAtIndex( 1, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_MS + TEST_RECV_BLOCK_TIME / 2 );
    setSystemTimeAtIndex( 2, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_MS + ( 2 * TEST_RECV_BLOCK_TIME / 3 ) );

    /* Test cases when transport receive fail in the retry attempts. */
    udpRecvRetCodes[ 0 ] = 0;  /* 1st read call. No data read.*/
    udpRecvRetCodes[ 1 ] = -1; /* Encounter error in 2nd call to receive remaining packet.*/
    TEST_ASSERT_EQUAL( SntpErrorNetworkFailure,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the "last request time" state of the context was not modified from network error. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );

    /* Reset the receive code index. */
    currentUdpRecvCodeIndex = 0;
    currentTimeIndex = 0;
    udpRecvRetCodes[ 0 ] = 0;  /* 1st read call. No data read.*/
    udpRecvRetCodes[ 1 ] = 0;  /* 2nd call also reading zero bytes .*/
    udpRecvRetCodes[ 2 ] = -1; /* Encounter error in 3rd call.*/
    TEST_ASSERT_EQUAL( SntpErrorNetworkFailure,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the "last request time" state of the context was not modified from network error. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );
}

/**
 * @brief Validate that the @ref Sntp_ReceiveTimeResponse API returns error when the transport
 * read interface returns code representing partial read, which is not supported by UDP.
 * UDP only supports either a complete packet read or read of no packet.
 */
void test_Sntp_ReceiveTimeResponse_Read_Failure_PartialRead()
{
    /* Test case when transport interface reads partial data. */
    udpRecvRetCodes[ 0 ] = SNTP_PACKET_BASE_SIZE / 2; /* 1st read call returning partial data which is invalid for UDP reads. */

    TEST_ASSERT_EQUAL( SntpErrorNetworkFailure, Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the "last request time" state of the context was not modified from network error. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );
}

/**
 * @brief Validate that the @ref Sntp_ReceiveTimeResponse API returns error when the transport
 * read interface returns code representing more number of bytes read from the network than asked for
 * by the library.
 */
void test_Sntp_ReceiveTimeResponse_Read_Failure_LargerPacketThanExpected()
{
    /* Test cases when transport read returns more than expected number of bytes read. */
    udpRecvRetCodes[ 0 ] = context.sntpPacketSize + 1; /* 1st read call returning partial data which is invalid for UDP reads. */

    TEST_ASSERT_EQUAL( SntpErrorNetworkFailure, Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the "last request time" state of the context was not modified from network error. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );
}

/**
 * @brief Validate the behavior of @ref Sntp_ReceiveTimeResponse API for the case
 * when no server response is received for the entire block time.
 */
void test_Sntp_ReceiveTimeResponse_BlockTime_Timeout( void )
{
    /* Set the times to be returned by SntpGetTime_t function to violate the block time window that
     * will be passed to the library in this test. */
    setSystemTimeAtIndex( 0, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_MS );
    setSystemTimeAtIndex( 1, LAST_REQUEST_TIME_SECS,
                          LAST_REQUEST_TIME_MS + TEST_RECV_BLOCK_TIME / 2 ); /* 1st SntpGetTime_t call in recv retry loop. */
    setSystemTimeAtIndex( 2, LAST_REQUEST_TIME_SECS,
                          LAST_REQUEST_TIME_MS + TEST_RECV_BLOCK_TIME );     /* 2nd SntpGetTime_t call with no data read. */

    /* Test case when transport receive operation times out due to no data being
     * received for the passed block time duration. */
    udpRecvRetCodes[ 0 ] = 0; /* 1st read call. No data read. */
    udpRecvRetCodes[ 1 ] = 0; /* No data in 2nd call as well.*/
    TEST_ASSERT_EQUAL( SntpNoResponseReceived,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the "last request time" state of the context was not modified from network error. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );
}

/**
 * @brief Validate the behavior of @ref Sntp_ReceiveTimeResponse API for the
 * case when the wait for server response times out.
 */
void test_Sntp_ReceiveTimeResponse_Server_Response_Timeout( void )
{
    /* Setup test to receive no data in the first attempt and we encounter server response
     * timeout. */
    udpRecvRetCodes[ 0 ] = 0;                                             /* 1st read call. No data read. */
    setSystemTimeAtIndex( 1, LAST_REQUEST_TIME_SECS,
                          LAST_REQUEST_TIME_MS + TEST_RESPONSE_TIMEOUT ); /* Set the SntpGetTime_t to return timeout value. */
    TEST_ASSERT_EQUAL( SntpErrorResponseTimeout,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the server has been rotated for the response timeout. */
    TEST_ASSERT_EQUAL( 1, context.currentServerIndex );

    /* Ensure that the "last request time" state of the context was not modified from network error. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );

    /* Reset the indices of lists that control behavior of interface functions. */
    currentTimeIndex = 0;
    currentUdpRecvCodeIndex = 0;
    context.currentServerIndex = 0;

    /* Setup test to receive no data in the second read attempt and then encounter server response timeout. */
    udpRecvRetCodes[ 0 ] = 0;                                                /* 1st read call. No data read. */
    setSystemTimeAtIndex( 1, LAST_REQUEST_TIME_SECS,
                          LAST_REQUEST_TIME_MS + TEST_RECV_BLOCK_TIME / 2 ); /* SntpGetTime_t call for the first read attempt. */
    udpRecvRetCodes[ 1 ] = 0;                                                /* 2nd call to check data availability. Receive no data. */
    setSystemTimeAtIndex( 1, LAST_REQUEST_TIME_SECS,
                          LAST_REQUEST_TIME_MS + TEST_RESPONSE_TIMEOUT );    /* SntpGetTime_t call after the second read attempt returning
                                                                              * timeout. */
    TEST_ASSERT_EQUAL( SntpErrorResponseTimeout,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the server has been rotated for the response timeout. */
    TEST_ASSERT_EQUAL( 1, context.currentServerIndex );

    /* Ensure that the "last request time" state of the context was not modified from network error. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );
}

/**
 * @brief Validate the behavior of @ref Sntp_ReceiveTimeResponse API for case of
 * failure in authentication authentication function when validating server response.
 */
void test_ReceiveTimeResponse_ServerAuth_Failure()
{
    /* Update size of SNTP packet to receive from network to include authentication data. */
    authCodeSize = sizeof( testBuffer ) - SNTP_PACKET_BASE_SIZE;
    context.sntpPacketSize = SNTP_PACKET_BASE_SIZE + authCodeSize;
    expectedBytesToRecv = context.sntpPacketSize;

    /* Set up the test to receive all the server response data. */
    udpRecvRetCodes[ 0 ] = expectedBytesToRecv;

    validateServerAuthRetCode = SntpErrorAuthFailure;
    TEST_ASSERT_EQUAL( SntpErrorAuthFailure,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );
    /* Ensure that the "last request time" state of the context was not modified from network error. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );
}

void test_ReceiveTimeResponse_InvalidServerAuth()
{
    /* Update size of SNTP packet to receive from network to include authentication data. */
    authCodeSize = sizeof( testBuffer ) - SNTP_PACKET_BASE_SIZE;
    context.sntpPacketSize = SNTP_PACKET_BASE_SIZE + authCodeSize;
    expectedBytesToRecv = context.sntpPacketSize;

    /* Set up the test to receive all the server response data. */
    udpRecvRetCodes[ 0 ] = expectedBytesToRecv;

    validateServerAuthRetCode = SntpServerNotAuthenticated;
    TEST_ASSERT_EQUAL( SntpServerNotAuthenticated,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the "last request time" state of the context was not modified from network error. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );
}

/**
 * @brief Verifies behavior of Sntp_ReceiveTimeResponse API for the case when server sends a rejected
 * response packet for time request. In such cases of receiving Kiss-o'-Death packet, the API is expected
 * to translate all the rejection codes to #SntpRejectedResponse response code and reset the "last request
 * time" state of the context to protect against replay attacks.
 */
void test_Sntp_ReceiveTimeResponse_Deserialize_Failures()
{
    /* Configure the behavior of the server validating authentication interface to return success. */
    authCodeSize = sizeof( testBuffer ) - SNTP_PACKET_BASE_SIZE;
    validateServerAuthRetCode = SntpSuccess;

#define TEST_SERVER_REJECTION_RESPONSE( status )                                                                                 \
    do {                                                                                                                         \
        /* Reset the indices of lists that control behavior of interface functions. */                                           \
        currentTimeIndex = 0;                                                                                                    \
        currentUdpRecvCodeIndex = 0;                                                                                             \
                                                                                                                                 \
        /* Assign non-zero to "last request time" state of context is cleared on receiving server response. */                   \
        context.lastRequestTime.seconds = LAST_REQUEST_TIME_MS;                                                                  \
        context.lastRequestTime.fractions = CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS );                                     \
                                                                                                                                 \
        udpRecvRetCodes[ 0 ] = SNTP_PACKET_BASE_SIZE;                                                                            \
                                                                                                                                 \
        /* Configure the Sntp_DeserializeResponse mock to return the particular server rejection status code. */                 \
        Sntp_DeserializeResponse_IgnoreAndReturn( status );                                                                      \
                                                                                                                                 \
        /* The API is expected to convert all Kiss-o'-Death rejection codes in server response to #SntpRejectedResponse code. */ \
        TEST_ASSERT_EQUAL( SntpRejectedResponse,                                                                                 \
                           Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );                                         \
                                                                                                                                 \
        /* Ensure that the "Last Request Time" state has been cleared to zero as a valid response packet is received. */         \
        TEST_ASSERT_EQUAL( 0, context.lastRequestTime.seconds );                                                                 \
        TEST_ASSERT_EQUAL( 0, context.lastRequestTime.fractions );                                                               \
    } while( 0 )

    TEST_SERVER_REJECTION_RESPONSE( SntpRejectedResponseRetryWithBackoff );
    TEST_SERVER_REJECTION_RESPONSE( SntpRejectedResponseChangeServer );
    TEST_SERVER_REJECTION_RESPONSE( SntpRejectedResponseOtherCode );
}

/**
 * @brief Verifies behavior of Sntp_ReceiveTimeResponse API for the case of receiving a malformed or incorrect
 * packet from the server.
 */
void test_Sntp_ReceiveTimeResponse_InvalidServerResponse( void )
{
    udpRecvRetCodes[ 0 ] = SNTP_PACKET_BASE_SIZE;

    Sntp_DeserializeResponse_IgnoreAndReturn( SntpInvalidResponse );
    TEST_ASSERT_EQUAL( SntpInvalidResponse,
                       Sntp_ReceiveTimeResponse( &context, TEST_RESPONSE_TIMEOUT ) );

    /* Ensure that the "last request time" state of the context was not modified as valid response
     * packet has not been received. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );
}

/**
 * @brief Validates that the @ref Sntp_ReceiveTimeResponse API does not clear the lastRequestTime
 * state of the context when server authentication functionality is not enable and the received response
 * represents a server rejection and the server. This behavior is expected from the API to prevent
 * attackers to spoof server response packets for launching Denial of Service attacks that is dependent
 * on the state clearing functionality.
 */
void test_ReceiveTimeResponse_DoSAttack_Protection_NoServerAuth( void )
{
    /* Test when server response is received without server validation. */
    context.authIntf.validateServerAuth = NULL;
    context.authIntf.generateClientAuth = NULL;

    udpRecvRetCodes[ 0 ] = context.sntpPacketSize;

#define COMMON_TEST_DOS_PROTECTION( rejectedStatus )                                                             \
    do {                                                                                                         \
                                                                                                                 \
        /* Reset the indices of lists that control behavior of interface functions. */                           \
        currentTimeIndex = 0;                                                                                    \
        currentUdpRecvCodeIndex = 0;                                                                             \
        /* Reset the current server index in the context. */                                                     \
        context.currentServerIndex = 0;                                                                          \
        Sntp_DeserializeResponse_IgnoreAndReturn( rejectedStatus );                                              \
        TEST_ASSERT_EQUAL( SntpRejectedResponse,                                                                 \
                           Sntp_ReceiveTimeResponse( &context, TEST_RESPONSE_TIMEOUT ) );                        \
                                                                                                                 \
        /* Ensure that the "last request time" state of the context was not modified. */                         \
        TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );                            \
        TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions ); \
    } while( 0 )

    COMMON_TEST_DOS_PROTECTION( SntpRejectedResponseChangeServer );
    COMMON_TEST_DOS_PROTECTION( SntpRejectedResponseOtherCode );
    COMMON_TEST_DOS_PROTECTION( SntpRejectedResponseRetryWithBackoff );
}

void test_ReceiveTimeResponse_NoServerResponse()
{
    /* Test when no response is received from the server for the entire block time containing
     *  multiple read attempts. */
    udpRecvRetCodes[ 0 ] = 0;                                                                           /* 1st attempt to check data availability. No data received.*/
    udpRecvRetCodes[ 1 ] = 0;                                                                           /* 2nd attempt to check data availability. No data received. */
    setSystemTimeAtIndex( 0, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_MS );                            /* 1st GetTime_t call. */
    setSystemTimeAtIndex( 1, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_MS + TEST_RECV_BLOCK_TIME / 2 ); /* GetTime_t call in 1st read attempt. */
    setSystemTimeAtIndex( 2, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_MS + TEST_RECV_BLOCK_TIME );     /* GetTime_t call in 2nd read attempt that should cause block time to complete. */

    TEST_ASSERT_EQUAL( SntpNoResponseReceived, Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the "last request time" state of the context was not modified as valid response
     * packet has not been received. */
    TEST_ASSERT_EQUAL( LAST_REQUEST_TIME_SECS, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS ), context.lastRequestTime.fractions );
}

void test_ReceiveTimeResponse_SuccessCase_With_AuthIntf()
{
    /* Configure the behavior of the server validating authentication interface to return success. */
    authCodeSize = sizeof( testBuffer ) - SNTP_PACKET_BASE_SIZE;
    validateServerAuthRetCode = SntpSuccess;

#define COMMON_TEST_SETUP() \
    do {                    \
        /* Set the behavior of the deserializer function dependency to always return \
         * success. */                                                                                                                                 \
        Sntp_DeserializeResponse_ExpectAndReturn( &context.lastRequestTime, NULL, context.pNetworkBuffer, context.sntpPacketSize, NULL, SntpSuccess ); \
        Sntp_DeserializeResponse_ReturnThruPtr_pParsedResponse( &mockResponseData );                                                                   \
        Sntp_DeserializeResponse_IgnoreArg_pResponseRxTime();                                                                                          \
        Sntp_DeserializeResponse_IgnoreArg_pParsedResponse();                                                                                          \
                                                                                                                                                       \
        /* Reset the indices of lists that control behavior of interface functions. */                                                                 \
        currentTimeIndex = 0;                                                                                                                          \
        currentUdpRecvCodeIndex = 0;                                                                                                                   \
        context.currentServerIndex = 0;                                                                                                                \
                                                                                                                                                       \
        /* Set the last request time value to determine that the API function clears it on getting a valid response. */                                \
        context.lastRequestTime.seconds = LAST_REQUEST_TIME_SECS;                                                                                      \
        context.lastRequestTime.fractions = CONVERT_MS_TO_FRACTIONS( LAST_REQUEST_TIME_MS );                                                           \
    } while( 0 )                                                                                                                                       \

    COMMON_TEST_SETUP();

    /* Test when server response is received successfully in 1st read attempt. */
    udpRecvRetCodes[ 0 ] = SNTP_PACKET_BASE_SIZE;                                                       /* 2nd attempt to check data availability. No data received. */
    setSystemTimeAtIndex( 0, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_MS + TEST_RECV_BLOCK_TIME / 2 ); /* 1st GetTime_t call. */
    TEST_ASSERT_EQUAL( SntpSuccess,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the "Last Request Time" state has been cleared to zero as a valid SNTP
     * response packet is received. */
    TEST_ASSERT_EQUAL( 0, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( 0, context.lastRequestTime.fractions );

    COMMON_TEST_SETUP();
    /* Test when server response is received successfully over multiple read attempts. */
    udpRecvRetCodes[ 0 ] = 0;                                                                                   /* 1st read attempt. No data received.*/
    udpRecvRetCodes[ 1 ] = SNTP_PACKET_BASE_SIZE;                                                               /* Complete response packet. */
    setSystemTimeAtIndex( 1, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_MS + TEST_RECV_BLOCK_TIME / 2 );         /* SntpGetTime_t call for first read attempt. */
    setSystemTimeAtIndex( 2, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_MS + ( 2 * TEST_RECV_BLOCK_TIME / 3 ) ); /* SntpGetTime_t call for second read attempt. */
    TEST_ASSERT_EQUAL( SntpSuccess,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the "Last Request Time" state has been cleared to zero as a valid SNTP
     * response packet is received. */
    TEST_ASSERT_EQUAL( 0, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( 0, context.lastRequestTime.fractions );
}

void test_ReceiveTimeResponse_SuccessCase_Without_AuthIntf()
{
    /* Set the behavior of the deserializer function dependency to always return success. */
    Sntp_DeserializeResponse_ExpectAndReturn( &context.lastRequestTime, NULL, context.pNetworkBuffer, context.sntpPacketSize, NULL, SntpSuccess );
    Sntp_DeserializeResponse_ReturnThruPtr_pParsedResponse( &mockResponseData );
    Sntp_DeserializeResponse_IgnoreArg_pResponseRxTime();
    Sntp_DeserializeResponse_IgnoreArg_pParsedResponse();

    /* Test when server response is received without server validation. */
    context.authIntf.validateServerAuth = NULL;   /* Remove the authentication interface from the context. */
    context.authIntf.generateClientAuth = NULL;
    udpRecvRetCodes[ 0 ] = SNTP_PACKET_BASE_SIZE; /* Read server packet in first read attempt. */
    TEST_ASSERT_EQUAL( SntpSuccess,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Ensure that the "Last Request Time" state has been cleared to zero as a valid SNTP
     * response packet is received. */
    TEST_ASSERT_EQUAL( 0, context.lastRequestTime.seconds );
    TEST_ASSERT_EQUAL( 0, context.lastRequestTime.fractions );
}

/**
 * @brief Validate that the server rotation logic in the library wraps around to the starting
 * of the list of servers when all servers have been exhausted. This test validates for the
 * case when the server rotation occurs due to reception of server rejection of time request.
 */
void test_Sntp_ReceiveTimeResponse_ServerRotation_WrapAround_ServerRejection( void )
{
    /* Test server rotation wrap around when a server rejection response is received. */

    /* Configure the behavior of the Sntp_DeserializeResponse API to return server rejection status. */
    Sntp_DeserializeResponse_IgnoreAndReturn( SntpRejectedResponseChangeServer );

    /* Update the context to refer to the last server in the configured list of servers to test that server
     * rotation wraps around to the first server in the list. */
    context.currentServerIndex = 1;

    /* Configure the behavior of test's SntpGetTime_t and transport receive interface functions. */
    udpRecvRetCodes[ 0 ] = SNTP_PACKET_BASE_SIZE;                                                         /* 1st attempt to check data availability. No data received.*/
    setSystemTimeAtIndex( 1, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_SECS + TEST_RECV_BLOCK_TIME / 2 ); /* SntpGetTime_t call for first read attempt. */

    /* Call the API under test. */
    TEST_ASSERT_EQUAL( SntpRejectedResponse,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Validate that the server rotation chose the next server by wrapping around to the
     *  first server in the list. */
    TEST_ASSERT_EQUAL( 0, context.currentServerIndex );
}

/**
 * @brief Validate that the server rotation logic in the library wraps around to the starting
 * of the list of servers when all servers have been exhausted. This test validates for the
 * case when the server rotation occurs due to server response timeout.
 */
void test_Sntp_ReceiveTimeResponse_ServerRotation_WrapAround_ResponseTimeout( void )
{
    /* Update the context to refer to the last server in the configured list of servers to test that server
     * rotation wraps around to the first server in the list. */
    context.currentServerIndex = 1;

    /* Setup test to receive no data in the first attempt and encounter server response timeout. */
    udpRecvRetCodes[ 0 ] = 0;                                                                        /* Read attempt receiving no data. */
    setSystemTimeAtIndex( 1, LAST_REQUEST_TIME_SECS, LAST_REQUEST_TIME_MS + TEST_RESPONSE_TIMEOUT ); /* Return time causing response timeout in the first attempt. */

    TEST_ASSERT_EQUAL( SntpErrorResponseTimeout,
                       Sntp_ReceiveTimeResponse( &context, TEST_RECV_BLOCK_TIME ) );

    /* Validate that the server rotation chose the next server by wrapping around to the
     *  first server in the list. */
    TEST_ASSERT_EQUAL( 0, context.currentServerIndex );
}


/**
 * @brief Validates the @ref Sntp_StatusToStr function.
 */
void test_StatusToStr( void )
{
    TEST_ASSERT_EQUAL_STRING( "SntpSuccess", Sntp_StatusToStr( SntpSuccess ) );
    TEST_ASSERT_EQUAL_STRING( "SntpErrorBadParameter", Sntp_StatusToStr( SntpErrorBadParameter ) );
    TEST_ASSERT_EQUAL_STRING( "SntpRejectedResponse", Sntp_StatusToStr( SntpRejectedResponse ) );
    TEST_ASSERT_EQUAL_STRING( "SntpRejectedResponseChangeServer", Sntp_StatusToStr( SntpRejectedResponseChangeServer ) );
    TEST_ASSERT_EQUAL_STRING( "SntpRejectedResponseRetryWithBackoff", Sntp_StatusToStr( SntpRejectedResponseRetryWithBackoff ) );
    TEST_ASSERT_EQUAL_STRING( "SntpRejectedResponseOtherCode", Sntp_StatusToStr( SntpRejectedResponseOtherCode ) );
    TEST_ASSERT_EQUAL_STRING( "SntpErrorBufferTooSmall", Sntp_StatusToStr( SntpErrorBufferTooSmall ) );
    TEST_ASSERT_EQUAL_STRING( "SntpInvalidResponse", Sntp_StatusToStr( SntpInvalidResponse ) );
    TEST_ASSERT_EQUAL_STRING( "SntpZeroPollInterval", Sntp_StatusToStr( SntpZeroPollInterval ) );
    TEST_ASSERT_EQUAL_STRING( "SntpErrorTimeNotSupported", Sntp_StatusToStr( SntpErrorTimeNotSupported ) );
    TEST_ASSERT_EQUAL_STRING( "SntpErrorDnsFailure", Sntp_StatusToStr( SntpErrorDnsFailure ) );
    TEST_ASSERT_EQUAL_STRING( "SntpErrorNetworkFailure", Sntp_StatusToStr( SntpErrorNetworkFailure ) );
    TEST_ASSERT_EQUAL_STRING( "SntpServerNotAuthenticated", Sntp_StatusToStr( SntpServerNotAuthenticated ) );
    TEST_ASSERT_EQUAL_STRING( "SntpErrorAuthFailure", Sntp_StatusToStr( SntpErrorAuthFailure ) );
    TEST_ASSERT_EQUAL_STRING( "SntpErrorSendTimeout", Sntp_StatusToStr( SntpErrorSendTimeout ) );
    TEST_ASSERT_EQUAL_STRING( "SntpErrorResponseTimeout", Sntp_StatusToStr( SntpErrorResponseTimeout ) );
    TEST_ASSERT_EQUAL_STRING( "SntpNoResponseReceived", Sntp_StatusToStr( SntpNoResponseReceived ) );
    TEST_ASSERT_EQUAL_STRING( "SntpErrorContextNotInitialized", Sntp_StatusToStr( SntpErrorContextNotInitialized ) );

    TEST_ASSERT_EQUAL_STRING( "Invalid status code!", Sntp_StatusToStr( 100 ) );
}
