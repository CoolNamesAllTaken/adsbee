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

/**
 * @file core_sntp_stubs.c
 * @brief Definition of stubs for UDP transport and authentication interfaces of coreSNTP API.
 */

#include <stdint.h>
#include "core_sntp_client.h"
#include "core_sntp_serializer.h"
#include "core_sntp_stubs.h"

#define TEST_TIMESTAMP         \
    {                          \
        .seconds = UINT32_MAX, \
        .fractions = 1000      \
    }

/* An exclusive bound on the times that the NetworkInterfaceSendStub will be
 * invoked before returning a loop terminating value. This is usually defined
 * in the Makefile of the harnessed function. */
#ifndef MAX_NETWORK_SEND_TRIES
    #define MAX_NETWORK_SEND_TRIES    2
#endif

/* An exclusive bound on the times that the NetworkInterfaceReceiveStub will
 * return an unbound value. At this value and beyond, the
 * NetworkInterfaceReceiveStub will return zero on every call. */
#ifndef MAX_NETWORK_RECV_TRIES
    #define MAX_NETWORK_RECV_TRIES    5
#endif

static SntpTimestamp_t testTime = TEST_TIMESTAMP;

int32_t NetworkInterfaceReceiveStub( NetworkContext_t * pNetworkContext,
                                     uint32_t serverAddr,
                                     uint16_t serverPort,
                                     void * pBuffer,
                                     uint16_t bytesToRecv )
{
    __CPROVER_assert( pBuffer != NULL,
                      "NetworkInterfaceReceiveStub pBuffer is NULL." );

    __CPROVER_assert( __CPROVER_w_ok( pBuffer, bytesToRecv ),
                      "NetworkInterfaceReceiveStub pBuffer is not writable up to bytesToRecv." );

    /* The havoc fills the buffer with unconstrained values. */
    __CPROVER_havoc_object( pBuffer );

    int32_t bytesOrError;
    static size_t tries = 0;

    /* It is a bug for the application defined transport receive function to return
     * more than bytesToRecv. */
    __CPROVER_assume( bytesOrError <= ( int32_t ) bytesToRecv );

    if( tries < ( MAX_NETWORK_RECV_TRIES - 1 ) )
    {
        tries++;
    }
    else
    {
        tries = 0;

        bytesOrError = SNTP_PACKET_BASE_SIZE;
    }

    return bytesOrError;
}
int32_t NetworkInterfaceSendStub( NetworkContext_t * pNetworkContext,
                                  uint32_t serverAddr,
                                  uint16_t serverPort,
                                  const void * pBuffer,
                                  uint16_t bytesToSend )
{
    __CPROVER_assert( pBuffer != NULL,
                      "NetworkInterfaceSendStub pBuffer is NULL." );

    __CPROVER_assert( __CPROVER_r_ok( pBuffer, bytesToSend ),
                      "NetworkInterfaceSendStub pBuffer is not readable up to bytesToSend." );

    /* The number of tries to send the message before this invocation. */
    static size_t tries = 0;

    int32_t bytesOrError;

    /* It is a bug for the application defined transport send function to return
     * more than bytesToSend. */
    __CPROVER_assume( bytesOrError <= ( int32_t ) bytesToSend );

    /* If the maximum tries are reached, then return a timeout. In the SNTP library
     * this stub is wrapped in a loop that will not end until the bytesOrError
     * returned is negative. This means we could loop possibly INT32_MAX
     * iterations. Looping for INT32_MAX times adds no value to the proof.
     * What matters is that the SNTP library can handle all the possible values
     * that could be returned. */
    if( tries < ( MAX_NETWORK_SEND_TRIES - 1 ) )
    {
        tries++;
    }
    else
    {
        tries = 0;
        /* This ensures that all the remaining bytes are sent in the last try. */
        bytesOrError = bytesToSend;
    }

    return bytesOrError;
}

SntpStatus_t GenerateClientAuthStub( SntpAuthContext_t * pContext,
                                     const SntpServerInfo_t * pTimeServer,
                                     void * pBuffer,
                                     size_t bufferSize,
                                     uint16_t * pAuthCodeSize )
{
    __CPROVER_assert( pTimeServer != NULL,
                      "GenerateClientAuthStub Time Server is NULL." );

    __CPROVER_assert( pBuffer != NULL,
                      "GenerateClientAuthStub pBuffer is NULL." );

    SntpStatus_t sntpStatus = SntpSuccess;

    if( bufferSize <= SNTP_PACKET_BASE_SIZE )
    {
        sntpStatus = SntpErrorBufferTooSmall;
    }
    else
    {
        *pAuthCodeSize = SNTP_PACKET_BASE_SIZE;
    }

    return sntpStatus;
}

SntpStatus_t ValidateServerAuthStub( SntpAuthContext_t * pContext,
                                     const SntpServerInfo_t * pTimeServer,
                                     const void * pResponseData,
                                     uint16_t responseSize )
{
    return SntpSuccess;
}

bool ResolveDnsFuncStub( const SntpServerInfo_t * pServerAddr,
                         uint32_t * pIpV4Addr )
{
    __CPROVER_assert( pServerAddr != NULL,
                      "ResolveDnsFuncStub pServerAddr is NULL." );

    /* For the proofs, returning a non deterministic boolean value
     * will be good enough. */
    return nondet_bool();
}

void GetTimeFuncStub( SntpTimestamp_t * pCurrentTime )
{
    __CPROVER_assert( pCurrentTime != NULL,
                      "GetTimeFuncStub pCurrentTime is NULL." );

    bool value = nondet_bool();

    if( value )
    {
        testTime.fractions = testTime.fractions + ( uint32_t ) 100000000;
    }
    else
    {
        testTime.fractions = testTime.fractions - ( uint32_t ) 1;
    }

    *pCurrentTime = testTime;
}

void SetTimeFuncStub( const SntpServerInfo_t * pTimeServer,
                      const SntpTimestamp_t * pServerTime,
                      int64_t clockOffsetMs,
                      SntpLeapSecondInfo_t leapSecondInfo )
{
    __CPROVER_assert( pTimeServer != NULL,
                      "SetTimeFuncStub pTimeServer is NULL." );

    __CPROVER_assert( pServerTime != NULL,
                      "SetTimeFuncStub pServerTime is NULL." );
}

SntpStatus_t Sntp_SerializeRequest( SntpTimestamp_t * pRequestTime,
                                    uint32_t randomNumber,
                                    void * pBuffer,
                                    size_t bufferSize )
{
    __CPROVER_assert( pRequestTime != NULL,
                      "Sntp_SerializeRequest pRequestTime is NULL." );

    __CPROVER_assert( pBuffer != NULL,
                      "Sntp_SerializeRequest pBuffer is NULL." );

    return SntpSuccess;
}

SntpStatus_t Sntp_DeserializeResponse( const SntpTimestamp_t * pRequestTime,
                                       const SntpTimestamp_t * pResponseRxTime,
                                       const void * pResponseBuffer,
                                       size_t bufferSize,
                                       SntpResponseData_t * pParsedResponse )
{
    if( nondet_bool() )
    {
        return SntpSuccess;
    }
    else
    {
        return SntpRejectedResponseRetryWithBackoff;
    }
}
