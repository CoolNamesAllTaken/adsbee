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
 * @file core_sntp_client.c
 * @brief Implementation of the client API of the coreSNTP library.
 */

/* Standard includes. */
#include <assert.h>
#include <string.h>

/* SNTP client library API include. */
#include "core_sntp_client.h"

#include "core_sntp_config_defaults.h"

/**
 * @brief Utility to convert fractions part of SNTP timestamp to milliseconds.
 *
 * @param[in] fractions The fractions value in an SNTP timestamp.
 */
#define FRACTIONS_TO_MS( fractions ) \
    ( fractions / ( SNTP_FRACTION_VALUE_PER_MICROSECOND * 1000U ) )

SntpStatus_t Sntp_Init( SntpContext_t * pContext,
                        const SntpServerInfo_t * pTimeServers,
                        size_t numOfServers,
                        uint32_t serverResponseTimeoutMs,
                        uint8_t * pNetworkBuffer,
                        size_t bufferSize,
                        SntpResolveDns_t resolveDnsFunc,
                        SntpGetTime_t getSystemTimeFunc,
                        SntpSetTime_t setSystemTimeFunc,
                        const UdpTransportInterface_t * pTransportIntf,
                        const SntpAuthenticationInterface_t * pAuthIntf )
{
    SntpStatus_t status = SntpSuccess;

    /* Validate pointer parameters are not NULL. */
    if( ( pContext == NULL ) || ( pTimeServers == NULL ) ||
        ( pNetworkBuffer == NULL ) || ( resolveDnsFunc == NULL ) ||
        ( getSystemTimeFunc == NULL ) || ( setSystemTimeFunc == NULL ) ||
        ( pTransportIntf == NULL ) )
    {
        LogError( ( "Invalid parameter: Pointer parameters (except pAuthIntf) cannot be NULL" ) );

        status = SntpErrorBadParameter;
    }
    /* Validate the length of the servers list.*/
    else if( numOfServers == 0U )
    {
        LogError( ( "Invalid parameter: Size of server list cannot be zero" ) );
        status = SntpErrorBadParameter;
    }
    /* Validate that the UDP transport interface functions are valid. */
    else if( ( pTransportIntf->recvFrom == NULL ) || ( pTransportIntf->sendTo == NULL ) )
    {
        LogError( ( "Invalid parameter: Function members of UDP transport interface cannot be NULL" ) );
        status = SntpErrorBadParameter;
    }

    /* If an authentication interface is provided, validate that its function pointer
     * members are valid. */
    else if( ( pAuthIntf != NULL ) &&
             ( ( pAuthIntf->generateClientAuth == NULL ) ||
               ( pAuthIntf->validateServerAuth == NULL ) ) )
    {
        LogError( ( "Invalid parameter: Function members of authentication interface cannot be NULL" ) );
        status = SntpErrorBadParameter;
    }
    else if( bufferSize < SNTP_PACKET_BASE_SIZE )
    {
        LogError( ( "Cannot initialize context: Passed network buffer size is less than %lu bytes: "
                    "bufferSize=%lu",
                    ( unsigned long ) SNTP_PACKET_BASE_SIZE,
                    ( unsigned long ) bufferSize ) );
        status = SntpErrorBufferTooSmall;
    }
    else
    {
        /* Reset the context memory to zero. */
        ( void ) memset( pContext, 0, sizeof( SntpContext_t ) );

        /* Set the members of the context with passed parameters. */
        pContext->pTimeServers = pTimeServers;
        pContext->numOfServers = numOfServers;

        pContext->responseTimeoutMs = serverResponseTimeoutMs;

        pContext->pNetworkBuffer = pNetworkBuffer;
        pContext->bufferSize = bufferSize;

        pContext->resolveDnsFunc = resolveDnsFunc;
        pContext->getTimeFunc = getSystemTimeFunc;
        pContext->setTimeFunc = setSystemTimeFunc;

        /* Copy contents of UDP transport interface to context. */
        ( void ) memcpy( &pContext->networkIntf, pTransportIntf, sizeof( UdpTransportInterface_t ) );

        /* If authentication interface has been passed, copy its contents to the context. */
        if( pAuthIntf != NULL )
        {
            ( void ) memcpy( &pContext->authIntf, pAuthIntf, sizeof( SntpAuthenticationInterface_t ) );
        }

        /* Initialize the packet size member to the standard minimum SNTP packet size.*/
        pContext->sntpPacketSize = SNTP_PACKET_BASE_SIZE;
    }

    return status;
}

/**
 * @brief Utility to calculate the difference in milliseconds between 2
 * SNTP timestamps.
 *
 * @param[in] pCurrentTime The more recent timestamp.
 * @param[in] pOlderTime The older timestamp.
 *
 * @note This functions supports the edge case of SNTP timestamp overflow
 * when @p pCurrentTime represents time in NTP era 1 (i.e. time since 7 Feb 2036)
 * and the @p OlderTime represents time in NTP era 0 (i.e. time since 1st Jan 1900).
 *
 * @return Returns the calculated time duration between the two timestamps.
 *
 * @note This function returns the calculated time difference as unsigned 64 bit
 * to avoid integer overflow when converting time difference between the seconds part
 * of the timestamps, which are 32 bits wide, to milliseconds.
 */
static uint64_t calculateElapsedTimeMs( const SntpTimestamp_t * pCurrentTime,
                                        const SntpTimestamp_t * pOlderTime )
{
    uint64_t timeDiffMs = 0UL;
    uint32_t timeDiffSec = 0U;

    assert( pCurrentTime != NULL );
    assert( pOlderTime != NULL );

    /* Detect if SNTP time has overflown between the 2 timestamps. */
    if( pCurrentTime->seconds < pOlderTime->seconds )
    {
        /* Handle the SNTP time overflow by calculating the actual time
         * duration from pOlderTime, that exists in NTP era 0, to pCurrentTime,
         * that exists in NTP era 1. */
        timeDiffSec = ( UINT32_MAX - pOlderTime->seconds ) + /* Time in NTP era 0. */
                      1U +                                   /* Epoch time in NTP era 1, i.e. 7 Feb 2036 6h:14m:28s. */
                      pCurrentTime->seconds;                 /* Time in NTP era 1. */

        timeDiffMs = ( uint64_t ) timeDiffSec * 1000UL;
    }
    else
    {
        timeDiffSec = ( pCurrentTime->seconds - pOlderTime->seconds );
        timeDiffMs = ( uint64_t ) timeDiffSec * 1000UL;
    }

    if( pCurrentTime->fractions > pOlderTime->fractions )
    {
        timeDiffMs += ( ( uint64_t ) pCurrentTime->fractions - ( uint64_t ) pOlderTime->fractions ) /
                      ( SNTP_FRACTION_VALUE_PER_MICROSECOND * 1000UL );
    }
    else
    {
        timeDiffMs -= ( ( uint64_t ) pOlderTime->fractions - ( uint64_t ) pCurrentTime->fractions ) /
                      ( SNTP_FRACTION_VALUE_PER_MICROSECOND * 1000UL );
    }

    return timeDiffMs;
}

/**
 * @brief Validates the content of the SNTP context passed to the APIs to
 * check whether it represents an initialized context.
 *
 * @param[in] pContext The SNTP context to validate.
 *
 * @return Returns one of the following:
 * - #SntpSuccess if the context is verified to be initialized.
 * - #SntpErrorBadParameter if the context is NULL.
 * - #SntpErrorContextNotInitialized if the context is validated to be initialized.
 */
static SntpStatus_t validateContext( const SntpContext_t * pContext )
{
    SntpStatus_t status = SntpSuccess;

    /* Check if the context parameter is invalid. */
    if( pContext == NULL )
    {
        status = SntpErrorBadParameter;
        LogError( ( "Invalid context parameter: Context is NULL" ) );
    }

    /* Validate pointer parameters are not NULL. */
    else if( ( pContext->pTimeServers == NULL ) || ( pContext->pNetworkBuffer == NULL ) ||
             ( pContext->resolveDnsFunc == NULL ) ||
             ( pContext->getTimeFunc == NULL ) || ( pContext->setTimeFunc == NULL ) )
    {
        status = SntpErrorContextNotInitialized;
    }

    /* Validate the size of the configured servers list, network buffer size and the state
     * variable for the SNTP packet size.*/
    else if( ( pContext->numOfServers == 0U ) || ( pContext->bufferSize < SNTP_PACKET_BASE_SIZE ) ||
             ( pContext->sntpPacketSize < SNTP_PACKET_BASE_SIZE ) )
    {
        status = SntpErrorContextNotInitialized;
    }
    /* Validate that the UDP transport interface functions are valid. */
    else if( ( pContext->networkIntf.recvFrom == NULL ) || ( pContext->networkIntf.sendTo == NULL ) )
    {
        status = SntpErrorContextNotInitialized;
    }

    /* If an authentication interface is provided, validate that both its function pointer
     * members are valid. */
    else if( ( ( pContext->authIntf.generateClientAuth != NULL ) && ( pContext->authIntf.validateServerAuth == NULL ) ) ||
             ( ( pContext->authIntf.generateClientAuth == NULL ) && ( pContext->authIntf.validateServerAuth != NULL ) ) )
    {
        status = SntpErrorContextNotInitialized;
    }
    else
    {
        status = SntpSuccess;
    }

    if( status == SntpErrorContextNotInitialized )
    {
        LogError( ( "Invalid context parameter: Context is not initialized with Sntp_Init" ) );
    }

    return status;
}

/**
 * @brief Sends SNTP request packet to the passed server over the network
 * using transport interface's send function.
 *
 * @note For the case of zero byte transmissions over the network, this function
 * repeatedly retries the send operation by calling the transport interface
 * until either:
 * 1. The requested number of bytes @p packetSize have been sent.
 *                    OR
 * 2. There is an error in sending data over the network.
 *
 * @note This function treats partial data transmissions as error as UDP
 * transport protocol does not support partial sends.
 *
 * @param[in] pNetworkIntf The UDP transport interface to use for
 * sending data over the network.
 * @param[in] timeServer The IPv4 address of the server to send the
 * SNTP request packet to.
 * @param[in] serverPort The port of the @p timeServer to send the
 * request to.
 * @param[in] getTimeFunc The function to query system time for
 * tracking retry time period of no data transmissions.
 * @param[in] pPacket The buffer containing the SNTP packet data
 * to send over the network.
 * @param[in] packetSize The size of data in the SNTP request packet.
 * @param[in] timeoutMs The timeout period for retry attempts of sending
 * SNTP request packet over the network.
 *
 * @return Returns #SntpSuccess on successful transmission of the entire
 * SNTP request packet over the network; #SntpErrorNetworkFailure
 * to indicate failure from transport interface; #SntpErrorSendTimeout if
 * time request could not be sent over the network within the @p timeoutMs
 * duration.
 */
static SntpStatus_t sendSntpPacket( const UdpTransportInterface_t * pNetworkIntf,
                                    uint32_t timeServer,
                                    uint16_t serverPort,
                                    SntpGetTime_t getTimeFunc,
                                    const uint8_t * pPacket,
                                    uint16_t packetSize,
                                    uint32_t timeoutMs )
{
    const uint8_t * pIndex = pPacket;
    int32_t bytesSent = 0;
    SntpTimestamp_t lastSendTime;
    bool shouldRetry = false;
    SntpStatus_t status = SntpErrorSendTimeout;

    assert( pPacket != NULL );
    assert( getTimeFunc != NULL );
    assert( pNetworkIntf != NULL );
    assert( packetSize >= SNTP_PACKET_BASE_SIZE );

    /* Record the starting time of attempting to send data. This begins the retry timeout
     * window. */
    getTimeFunc( &lastSendTime );

    /* Loop until the entire packet is sent. */
    do
    {
        /* Reset flag for retrying send operation for the iteration. If request packet cannot be
         * sent and timeout has not occurred, the flag will be set later for the next iteration. */
        shouldRetry = false;

        bytesSent = pNetworkIntf->sendTo( pNetworkIntf->pUserContext,
                                          timeServer,
                                          serverPort,
                                          pIndex,
                                          packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Unable to send request packet: Transport send failed. "
                        "ErrorCode=%ld.",
                        ( long int ) bytesSent ) );
            status = SntpErrorNetworkFailure;
        }
        else if( bytesSent == 0 )
        {
            /* No bytes were sent over the network. Retry send if we have not timed out. */

            SntpTimestamp_t currentTime;
            uint64_t elapsedTimeMs;

            getTimeFunc( &currentTime );

            /* Calculate time elapsed since last data was sent over network. */
            elapsedTimeMs = calculateElapsedTimeMs( &currentTime, &lastSendTime );

            /* Check for timeout if we have been waiting to send any data over the network. */
            if( elapsedTimeMs >= timeoutMs )
            {
                LogError( ( "Unable to send request packet: Timed out retrying send: "
                            "SendRetryTimeout=%lums",
                            ( unsigned long ) timeoutMs ) );
                status = SntpErrorSendTimeout;
            }
            else
            {
                shouldRetry = true;
            }
        }

        /* Partial sends are not supported by UDP, which only supports sending the entire datagram as a whole.
         * Thus, if the transport send function returns status representing partial send, it will be treated as failure. */
        else if( bytesSent != ( int32_t ) packetSize )
        {
            LogError( ( "Unable to send request packet: Transport send returned unexpected bytes sent. "
                        "ReturnCode=%ld, ExpectedCode=%u",
                        ( long int ) bytesSent,
                        ( unsigned int ) packetSize ) );

            status = SntpErrorNetworkFailure;
        }
        else
        {
            /* The time request packet has been sent over the network. */
            status = SntpSuccess;
        }
    } while( shouldRetry == true );

    return status;
}

/**
 * @brief Adds client authentication data to SNTP request packet by calling the
 * authentication interface.
 *
 * @param[in] pContext The SNTP context.
 *
 * @return Returns one of the following:
 * - #SntpSuccess if the interface function successfully appends client
 * authentication data.
 * - #SntpErrorAuthFailure when the interface returns either an error OR an
 * incorrect size of the client authentication data.
 */
static SntpStatus_t addClientAuthentication( SntpContext_t * pContext )
{
    SntpStatus_t status = SntpSuccess;
    uint16_t authDataSize = 0U;

    assert( pContext != NULL );
    assert( pContext->authIntf.generateClientAuth != NULL );
    assert( pContext->currentServerIndex <= pContext->numOfServers );

    status = pContext->authIntf.generateClientAuth( pContext->authIntf.pAuthContext,
                                                    &pContext->pTimeServers[ pContext->currentServerIndex ],
                                                    pContext->pNetworkBuffer,
                                                    pContext->bufferSize,
                                                    &authDataSize );

    if( status != SntpSuccess )
    {
        LogError( ( "Unable to send time request: Client authentication function failed: "
                    "RetStatus=%s", Sntp_StatusToStr( status ) ) );
    }

    /* Sanity check that the returned authentication data size fits in the remaining space
     * of the request buffer besides the first #SNTP_PACKET_BASE_SIZE bytes. */
    else if( authDataSize > ( pContext->bufferSize - SNTP_PACKET_BASE_SIZE ) )
    {
        LogError( ( "Unable to send time request: Invalid authentication code size: "
                    "AuthCodeSize=%lu, NetworkBufferSize=%lu",
                    ( unsigned long ) authDataSize,
                    ( unsigned long ) pContext->bufferSize ) );
        status = SntpErrorAuthFailure;
    }
    else
    {
        /* With the authentication data added. calculate total SNTP request packet size. The same
         * size would be expected in the SNTP response from server. */
        pContext->sntpPacketSize = SNTP_PACKET_BASE_SIZE + authDataSize;

        LogInfo( ( "Appended client authentication code to SNTP request packet:"
                   " AuthCodeSize=%lu, TotalPacketSize=%lu",
                   ( unsigned long ) authDataSize,
                   ( unsigned long ) pContext->sntpPacketSize ) );
    }

    return status;
}

SntpStatus_t Sntp_SendTimeRequest( SntpContext_t * pContext,
                                   uint32_t randomNumber,
                                   uint32_t blockTimeMs )
{
    SntpStatus_t status = SntpSuccess;

    /* Validate the context parameter. */
    status = validateContext( pContext );

    if( status == SntpSuccess )
    {
        const SntpServerInfo_t * pServer = NULL;

        /* Set local variable for the currently indexed server to use for time
         * query. */
        pServer = &pContext->pTimeServers[ pContext->currentServerIndex ];

        LogDebug( ( "Using server %.*s for time query",
                    ( int ) pServer->serverNameLen, pServer->pServerName ) );

        /* Perform DNS resolution of the currently indexed server in the list
         * of configured servers. */
        if( pContext->resolveDnsFunc( pServer, &pContext->currentServerAddr ) == false )
        {
            LogError( ( "Unable to send time request: DNS resolution failed: Server=%.*s",
                        ( int ) pServer->serverNameLen, pServer->pServerName ) );

            status = SntpErrorDnsFailure;
        }
        else
        {
            LogDebug( ( "Server DNS resolved: Address=0x%08lx",
                        ( unsigned long ) pContext->currentServerAddr ) );
        }

        if( status == SntpSuccess )
        {
            /* Obtain current system time to generate SNTP request packet. */
            pContext->getTimeFunc( &pContext->lastRequestTime );

            LogDebug( ( "Obtained current time for SNTP request packet: Time=%lus %lums",
                        ( unsigned long ) pContext->lastRequestTime.seconds,
                        ( unsigned long ) FRACTIONS_TO_MS( pContext->lastRequestTime.fractions ) ) );

            /* Generate SNTP request packet with the current system time and
             * the passed random number. */
            status = Sntp_SerializeRequest( &pContext->lastRequestTime,
                                            randomNumber,
                                            pContext->pNetworkBuffer,
                                            pContext->bufferSize );

            /* The serialization should be successful as all parameter validation has
             * been done before. */
            assert( status == SntpSuccess );
        }

        /* If an authentication interface has been configured, call the function to append client
         * authentication data to SNTP request buffer. */
        if( ( status == SntpSuccess ) && ( pContext->authIntf.generateClientAuth != NULL ) )
        {
            status = addClientAuthentication( pContext );
        }

        if( status == SntpSuccess )
        {
            LogInfo( ( "Sending serialized SNTP request packet to the server: Addr=%lu, Port=%u",
                       ( unsigned long ) pContext->currentServerAddr,
                       pContext->pTimeServers[ pContext->currentServerIndex ].port ) );

            /* Send the request packet over the network to the time server. */
            status = sendSntpPacket( &pContext->networkIntf,
                                     pContext->currentServerAddr,
                                     pContext->pTimeServers[ pContext->currentServerIndex ].port,
                                     pContext->getTimeFunc,
                                     pContext->pNetworkBuffer,
                                     pContext->sntpPacketSize,
                                     blockTimeMs );
        }
    }

    return status;
}

/**
 * @brief Utility to update the SNTP context to rotate the server of use for subsequent
 * time request(s).
 *
 * @note If there is no next server remaining, after the current server's index, in the list of
 * configured servers, the server rotation algorithm wraps around to the first server in the list.
 * The wrap around is done so that an application using the library for a long-running SNTP client
 * functionality (like a daemon task) does not become dysfunctional after all configured time
 * servers have been used up. Time synchronization can be a critical functionality for a system
 * and the wrap around logic ensures that the SNTP client continues to function in such a case.
 *
 * @note Server rotation is performed ONLY when either of:
 * - The current server responds with a rejection for time request.
 *                         OR
 * - The current server response wait has timed out.
 */
static void rotateServerForNextTimeQuery( SntpContext_t * pContext )
{
    size_t nextServerIndex = ( pContext->currentServerIndex + 1U ) % pContext->numOfServers;

    LogInfo( ( "Rotating server for next time query: PreviousServer=%.*s, NextServer=%.*s",
               ( int ) pContext->pTimeServers[ pContext->currentServerIndex ].serverNameLen,
               pContext->pTimeServers[ pContext->currentServerIndex ].pServerName,
               ( int ) pContext->pTimeServers[ nextServerIndex ].serverNameLen,
               pContext->pTimeServers[ nextServerIndex ].pServerName ) );

    pContext->currentServerIndex = nextServerIndex;
}


/**
 * @brief This function attempts to receive the SNTP response packet from a server.
 *
 * @note This function treats reads of data sizes less than the expected server response packet,
 * as an error as UDP does not support partial reads. Such a scenario can exist either due:
 * - An error in the server sending its response with smaller packet size than the request packet OR
 * - A malicious attacker spoofing or modifying server response OR
 * - An error in the UDP transport interface implementation for read operation.
 *
 * @param[in] pTransportIntf The UDP transport interface to use for receiving data from
 * the network.
 * @param[in] timeServer The server to read the response from the network.
 * @param[in] serverPort The port of the server to read the response from.
 * @param[in, out] pBuffer This will be filled with the server response read from the
 * network.
 * @param[in] responseSize The size of server response to read from the network.
 *
 * @return It returns one of the following:
 * - #SntpSuccess if an SNTP response packet is received from the network.
 * - #SntpNoResponseReceived if a server response is not received from the network.
 * - #SntpErrorNetworkFailure if there is an internal failure in reading from the network
 * in the user-defined transport interface.
 */
static SntpStatus_t receiveSntpResponse( const UdpTransportInterface_t * pTransportIntf,
                                         uint32_t timeServer,
                                         uint16_t serverPort,
                                         uint8_t * pBuffer,
                                         uint16_t responseSize )
{
    SntpStatus_t status = SntpNoResponseReceived;
    int32_t bytesRead = 0;

    assert( pTransportIntf != NULL );
    assert( pTransportIntf->recvFrom != NULL );
    assert( pBuffer != NULL );
    assert( responseSize >= SNTP_PACKET_BASE_SIZE );

    bytesRead = pTransportIntf->recvFrom( pTransportIntf->pUserContext,
                                          timeServer,
                                          serverPort,
                                          pBuffer,
                                          responseSize );

    /* Negative return code indicates error. */
    if( bytesRead < 0 )
    {
        status = SntpErrorNetworkFailure;
        LogError( ( "Unable to receive server response: Transport receive failed: Code=%ld",
                    ( long int ) bytesRead ) );
    }
    /* If the packet was not available on the network, check whether we can retry. */
    else if( bytesRead == 0 )
    {
        status = SntpNoResponseReceived;
    }

    /* Partial reads are not supported by UDP, which only supports receiving the entire datagram as a whole.
     * Thus, if the transport receive function returns reception of partial data, it will be treated as failure. */
    else if( bytesRead != ( int32_t ) responseSize )
    {
        LogError( ( "Failed to receive server response: Transport recv returned less than expected bytes."
                    "ExpectedBytes=%u, ReadBytes=%ld",
                    responseSize,
                    ( long int ) bytesRead ) );
        status = SntpErrorNetworkFailure;
    }
    else
    {
        LogDebug( ( "Received server response: PacketSize=%ld", ( long int ) bytesRead ) );
        status = SntpSuccess;
    }

    return status;
}

/**
 * @brief Processes the response from a server by de-serializing the SNTP packet to
 * validate the server (if an authentication interface has been configured), determine
 * whether server has accepted or rejected the time request, and update the system clock
 * if the server responded positively with time.
 *
 * @param[in] pContext The SNTP context representing the SNTP client.
 * @param[in] pResponseRxTime The time of receiving the server response from the network.
 *
 * @return It returns one of the following:
 * - #SntpSuccess if the server response is successfully de-serialized and system clock
 * updated.
 * - #SntpErrorAuthFailure if there is internal failure in user-defined authentication
 * interface when validating server from the response.
 * - #SntpServerNotAuthenticated if the server failed authenticated check in the user-defined
 * interface.
 * - #SntpRejectedResponse if the server has rejected the time request in its response.
 * - #SntpInvalidResponse if the server response failed sanity checks.
 */
static SntpStatus_t processServerResponse( SntpContext_t * pContext,
                                           const SntpTimestamp_t * pResponseRxTime )
{
    SntpStatus_t status = SntpSuccess;
    const SntpServerInfo_t * pServer = &pContext->pTimeServers[ pContext->currentServerIndex ];

    assert( pContext != NULL );
    assert( pResponseRxTime != NULL );

    if( pContext->authIntf.validateServerAuth != NULL )
    {
        /* Verify the server from the authentication data in the SNTP response packet. */
        status = pContext->authIntf.validateServerAuth( pContext->authIntf.pAuthContext,
                                                        pServer,
                                                        pContext->pNetworkBuffer,
                                                        pContext->sntpPacketSize );
        assert( ( status == SntpSuccess ) || ( status == SntpErrorAuthFailure ) ||
                ( status == SntpServerNotAuthenticated ) );

        if( status != SntpSuccess )
        {
            LogError( ( "Unable to use server response: Server authentication function failed: "
                        "ReturnStatus=%s", Sntp_StatusToStr( status ) ) );
        }
        else
        {
            LogDebug( ( "Server response has been validated: Server=%.*s",
                        ( int ) pServer->serverNameLen, pServer->pServerName ) );
        }
    }

    if( status == SntpSuccess )
    {
        SntpResponseData_t parsedResponse = { 0 };

        /* De-serialize response packet to determine whether the server accepted or rejected
         * the request for time. Also, calculate the system clock offset if the server responded
         * with time. */
        status = Sntp_DeserializeResponse( &pContext->lastRequestTime,
                                           pResponseRxTime,
                                           pContext->pNetworkBuffer,
                                           pContext->sntpPacketSize,
                                           &parsedResponse );

        /* We do not expect the following errors to be returned as the context
         * has been validated in the Sntp_ReceiveTimeResponse API. */
        assert( status != SntpErrorBadParameter );
        assert( status != SntpErrorBufferTooSmall );

        if( ( status == SntpRejectedResponseChangeServer ) ||
            ( status == SntpRejectedResponseRetryWithBackoff ) ||
            ( status == SntpRejectedResponseOtherCode ) )
        {
            /* Server has rejected the time request. Thus, we will rotate to the next time server
             * in the list. */
            rotateServerForNextTimeQuery( pContext );

            LogError( ( "Unable to use server response: Server has rejected request for time: RejectionCode=%.*s",
                        ( int ) SNTP_KISS_OF_DEATH_CODE_LENGTH,
                        ( char * ) &parsedResponse.rejectedResponseCode ) );

            status = SntpRejectedResponse;
        }
        else if( status == SntpInvalidResponse )
        {
            LogError( ( "Unable to use server response: Server response failed sanity checks." ) );
        }
        else
        {
            /* Server has responded successfully with time, and we have calculated the clock offset
             * of system clock relative to the server.*/
            LogDebug( ( "Updating system time: ServerTime=%lu %lums ClockOffset=%lds",
                        ( unsigned long ) parsedResponse.serverTime.seconds,
                        ( unsigned long ) FRACTIONS_TO_MS( parsedResponse.serverTime.fractions ),
                        /* Print out in seconds instead of Ms to account for C90 lack of %lld */
                        ( long ) parsedResponse.clockOffsetMs / 1000 ) );

            /* Update the system clock with the calculated offset. */
            pContext->setTimeFunc( pServer, &parsedResponse.serverTime,
                                   parsedResponse.clockOffsetMs, parsedResponse.leapSecondType );

            status = SntpSuccess;
        }
    }

    /* Reset the last request time state in context to protect against replay attacks.
     * Note: The last request time is not cleared when a rejection response packet is received and the client does
     * has not authenticated server from the response. This is because clearing of the state causes the coreSNTP
     * library to discard any subsequent server response packets (as the "originate timestamp" of those packets will
     * not match the last request time value of the context), and thus, an attacker can cause Denial of Service
     * attacks by spoofing server response before the actual server is able to respond.
     */
    if( ( status == SntpSuccess ) ||
        ( ( pContext->authIntf.validateServerAuth != NULL ) && ( status == SntpRejectedResponse ) ) )
    {
        /* In the attack of SNTP request packet being replayed, the replayed request packet is serviced by
         * SNTP/NTP server with SNTP response (as servers are stateless) and client receives the response
         * containing new values of server timestamps but the stale value of "originate timestamp".
         * To prevent the coreSNTP library from servicing such a server response (associated with the replayed
         * SNTP request packet), the last request timestamp state is cleared in the context after receiving the
         * first valid server response. Therefore, any subsequent server response(s) from replayed client request
         * packets can be invalidated due to the "originate timestamp" not matching the last request time stored
         * in the context.
         * Note: If an attacker spoofs a server response with a zero "originate timestamp" after the coreSNTP
         * library (i.e. the SNTP client) has cleared the internal state to zero, the spoofed packet will be
         * discarded as the coreSNTP serializer does not accept server responses with zero value for timestamps.
         */
        pContext->lastRequestTime.seconds = 0U;
        pContext->lastRequestTime.fractions = 0U;
    }

    return status;
}

/**
 * @brief Determines whether a retry attempt should be made to receive server response packet from the network
 * depending on the timing constraints of server response timeout, @p responseTimeoutMs, and the block time
 * period, @p blockTimeMs, passed. If neither of the time windows have expired, the function determines that the
 * read operation can be re-tried.
 *
 * @param[in] pCurrentTime The current time in the system used for calculating elapsed time windows.
 * @param[in] pReadStartTime The time of the first read attempt in the current set of read tries occurring
 * from the Sntp_ReceiveTimeRequest API call by the application. This time is used for calculating the elapsed
 * time to determine whether the block time has expired.
 * @param[in] pRequestTime The time of sending the SNTP request to the server for which the response is
 * awaited. This time is used for calculating total elapsed elapsed time of waiting for server response to
 * determine if a server response timeout has occurred.
 * @param[in] responseTimeoutMs The server response timeout configuration.
 * @param[in] blockTimeMs The maximum block time of waiting for server response across read tries in the current
 * call made by application to Sntp_ReceiveTimeResponse API.
 * @param[out] pHasResponseTimedOut This will be populated with state to indicate whether the wait for server
 * response has timed out.
 *
 * @return Returns true for retrying read operation of server response; false on either server response timeout
 * OR completion of block time window.
 */
static bool decideAboutReadRetry( const SntpTimestamp_t * pCurrentTime,
                                  const SntpTimestamp_t * pReadStartTime,
                                  const SntpTimestamp_t * pRequestTime,
                                  uint32_t responseTimeoutMs,
                                  uint32_t blockTimeMs,
                                  bool * pHasResponseTimedOut )
{
    uint64_t timeSinceRequestMs = 0UL;
    uint64_t timeElapsedInReadAttempts = 0UL;
    bool shouldRetry = false;

    assert( pCurrentTime != NULL );
    assert( pReadStartTime != NULL );
    assert( pRequestTime != NULL );
    assert( pHasResponseTimedOut != NULL );

    /* Calculate time elapsed since the time request was sent to the server
     * to determine whether the server response has timed out. */
    timeSinceRequestMs = calculateElapsedTimeMs( pCurrentTime, pRequestTime );

    /* Calculate the time elapsed across all the read attempts so far to determine
     * whether the block time window for reading server response has expired. */
    timeElapsedInReadAttempts = calculateElapsedTimeMs( pCurrentTime, pReadStartTime );

    /* Check whether a response timeout has occurred to inform whether we should
     * wait for server response anymore. */
    if( timeSinceRequestMs >= ( uint64_t ) responseTimeoutMs )
    {
        shouldRetry = false;
        *pHasResponseTimedOut = true;

        LogError( ( "Unable to receive response: Server response has timed out: "
                    "RequestTime=%lus %lums, TimeoutDuration=%lums, ElapsedTime=%lus",
                    ( unsigned long ) pRequestTime->seconds,
                    ( unsigned long ) FRACTIONS_TO_MS( pRequestTime->fractions ),
                    ( unsigned long ) responseTimeoutMs,
                    /* Print out in seconds instead of Ms to account for C90 lack of %llu */
                    ( unsigned long ) ( ( timeSinceRequestMs + 500UL ) / 1000UL ) ) );
    }
    /* Check whether the block time window has expired to determine whether read can be retried. */
    else if( timeElapsedInReadAttempts >= ( uint64_t ) blockTimeMs )
    {
        shouldRetry = false;
        LogDebug( ( "Did not receive server response: Read block time has expired: "
                    "BlockTime=%lums, ResponseWaitElapsedTime=%lus",
                    ( unsigned long ) blockTimeMs,
                    /* Print out in seconds instead of Ms to account for C90 lack of %llu */
                    ( unsigned long ) ( ( timeSinceRequestMs + 500UL ) / 1000UL ) ) );
    }
    else
    {
        shouldRetry = true;
        LogDebug( ( "Did not receive server response: Retrying read: "
                    "BlockTime=%lums, ResponseWaitElapsedTime=%lus, ResponseTimeout=%lums",
                    ( unsigned long ) blockTimeMs,
                    /* Print out in seconds instead of Ms to account for C90 lack of %llu */
                    ( unsigned long ) ( ( timeSinceRequestMs + 500UL ) / 1000UL ),
                    ( unsigned long ) responseTimeoutMs ) );
    }

    return shouldRetry;
}

SntpStatus_t Sntp_ReceiveTimeResponse( SntpContext_t * pContext,
                                       uint32_t blockTimeMs )
{
    SntpStatus_t status = SntpNoResponseReceived;
    bool hasResponseTimedOut = false;

    /* Validate the context parameter. */
    status = validateContext( pContext );

    if( status == SntpSuccess )
    {
        SntpTimestamp_t startTime, currentTime;
        const SntpTimestamp_t * pRequestTime = &pContext->lastRequestTime;
        bool shouldRetry = false;

        /* Record time before read attempts so that it can be used as base time for
         * for tracking the block time window across read retries. */
        pContext->getTimeFunc( &startTime );

        do
        {
            /* Reset the retry read operation flag. If the server response is not received in the current iteration's read
             * attempt and the wait has not timed out, the flag will be set to perform a retry. */
            shouldRetry = false;

            /* Make an attempt to read the server response from the network. */
            status = receiveSntpResponse( &pContext->networkIntf,
                                          pContext->currentServerAddr,
                                          pContext->pTimeServers[ pContext->currentServerIndex ].port,
                                          pContext->pNetworkBuffer,
                                          pContext->sntpPacketSize );

            /* If the server response is received, deserialize it, validate the server
             * (if authentication interface is provided), and update system time with
             * the calculated clock offset. */
            if( status == SntpSuccess )
            {
                /* Get current time to de-serialize the receive server response packet. */
                pContext->getTimeFunc( &currentTime );

                status = processServerResponse( pContext, &currentTime );
            }
            else if( status == SntpNoResponseReceived )
            {
                /* Get current time to determine whether another attempt for reading the packet can
                 * be made. */
                pContext->getTimeFunc( &currentTime );

                /* Set the flag to retry read of server response from the network. */
                shouldRetry = decideAboutReadRetry( &currentTime,
                                                    &startTime,
                                                    pRequestTime,
                                                    pContext->responseTimeoutMs,
                                                    blockTimeMs,
                                                    &hasResponseTimedOut );
            }
            else
            {
                /* Empty else marker. */
            }
        } while( shouldRetry == true );

        /* If the wait for server response to the time request has timed out, rotate the server of use in the
         * context for subsequent time request(s). Also, update the return status to indicate response timeout. */
        if( hasResponseTimedOut == true )
        {
            status = SntpErrorResponseTimeout;

            /* Rotate server to the next in the list of configured servers in the context. */
            rotateServerForNextTimeQuery( pContext );
        }
    }

    return status;
}

const char * Sntp_StatusToStr( SntpStatus_t status )
{
    const char * pString = NULL;

    switch( status )
    {
        case SntpSuccess:
            pString = "SntpSuccess";
            break;

        case SntpErrorBadParameter:
            pString = "SntpErrorBadParameter";
            break;

        case SntpRejectedResponse:
            pString = "SntpRejectedResponse";
            break;

        case SntpRejectedResponseChangeServer:
            pString = "SntpRejectedResponseChangeServer";
            break;

        case SntpRejectedResponseRetryWithBackoff:
            pString = "SntpRejectedResponseRetryWithBackoff";
            break;

        case SntpRejectedResponseOtherCode:
            pString = "SntpRejectedResponseOtherCode";
            break;

        case SntpErrorBufferTooSmall:
            pString = "SntpErrorBufferTooSmall";
            break;

        case SntpInvalidResponse:
            pString = "SntpInvalidResponse";
            break;

        case SntpZeroPollInterval:
            pString = "SntpZeroPollInterval";
            break;

        case SntpErrorTimeNotSupported:
            pString = "SntpErrorTimeNotSupported";
            break;

        case SntpErrorDnsFailure:
            pString = "SntpErrorDnsFailure";
            break;

        case SntpErrorNetworkFailure:
            pString = "SntpErrorNetworkFailure";
            break;

        case SntpServerNotAuthenticated:
            pString = "SntpServerNotAuthenticated";
            break;

        case SntpErrorAuthFailure:
            pString = "SntpErrorAuthFailure";
            break;

        case SntpErrorSendTimeout:
            pString = "SntpErrorSendTimeout";
            break;

        case SntpErrorResponseTimeout:
            pString = "SntpErrorResponseTimeout";
            break;

        case SntpNoResponseReceived:
            pString = "SntpNoResponseReceived";
            break;

        case SntpErrorContextNotInitialized:
            pString = "SntpErrorContextNotInitialized";
            break;

        default:
            pString = "Invalid status code!";
            break;
    }

    return pString;
}
