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
 * @file core_sntp_client.h
 * @brief API of an SNTPv4 client library that can send time requests and receive time response to/from
 * SNTP/NTP servers. The library follows the Best Practices suggested in the the SNTPv4 specification,
 * [RFC 4330](https://tools.ietf.org/html/rfc4330).
 * The library can be used to run an SNTP client in a dedicated deamon task to periodically synchronize
 * time from the Internet.
 */

#ifndef CORE_SNTP_CLIENT_H_
#define CORE_SNTP_CLIENT_H_

/* Standard include. */
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

/* Include coreSNTP Serializer header. */
#include "core_sntp_serializer.h"

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 * @ingroup sntp_constants
 * @brief The default UDP port supported by SNTP/NTP servers for client-server
 * communication.
 *
 * @note It is possible for a server to use a different port number than
 * the default port when using the Network Time Security protocol as the security
 * mechanism for SNTP communication. For more information, refer to Section 4.1.8
 * of [RFC 8915](https://tools.ietf.org/html/rfc8915).
 */
#define SNTP_DEFAULT_SERVER_PORT    ( 123U )

/**
 * @ingroup sntp_struct_types
 * @brief Structure representing information for a time server.
 */
typedef struct SntpServerInfo
{
    const char * pServerName; /**<@brief The time server name. */
    size_t serverNameLen;     /**<@brief The length of the server name.*/
    uint16_t port;            /**<@brief The UDP port supported by the server
                               * for SNTP/NTP communication. */
} SntpServerInfo_t;

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to resolve time server domain-name
 * to an IPv4 address.
 * The SNTP client library attempts to resolve the DNS of the time-server being
 * used every time the @ref Sntp_SendTimeRequest API is called.
 *
 * @param[in] pServerAddr The time-server whose IPv4 address is to be resolved.
 * @param[out] pIpV4Addr This should be filled with the resolved IPv4 address.
 * of @p pTimeServer.
 *
 * @return `true` if DNS resolution is successful; otherwise `false` to represent
 * failure.
 */
typedef bool ( * SntpResolveDns_t )( const SntpServerInfo_t * pServerAddr,
                                     uint32_t * pIpV4Addr );

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to obtain the current system time
 * in SNTP timestamp format.
 *
 * @note If your platform follows UNIX representation of time, the
 * #SNTP_TIME_AT_UNIX_EPOCH_SECS and #SNTP_FRACTION_VALUE_PER_MICROSECOND macros
 * can be used to convert UNIX time to SNTP timestamp.
 *
 * @param[out] pCurrentTime This should be filled with the current system time
 * in SNTP timestamp format.
 *
 * @return `true` if obtaining system time is successful; otherwise `false` to
 * represent failure.
 */
typedef void ( * SntpGetTime_t )( SntpTimestamp_t * pCurrentTime );

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to update the system clock time
 * so that it is synchronized the time server used for getting current time.
 *
 * @param[in] pTimeServer The time server used to request time.
 * @param[in] pServerTime The current time returned by the @p pTimeServer.
 * @param[in] clockOffsetMs The calculated clock offset (in milliseconds) of the
 * system relative to the server time.
 * @param[in] leapSecondInfo Information about whether there is about an upcoming
 * leap second adjustment of insertion or deletion in the last minute before midnight
 * on the last day of the current month. For more information on leap seconds, refer
 * to https://www.nist.gov/pml/time-and-frequency-division/leap-seconds-faqs. Depending
 * on the accuracy requirements of the system clock, the user can choose to account
 * for the leap second or ignore it in their system clock update logic.
 *
 * @note If the @p clockOffsetMs is positive, then the system time is BEHIND the server time,
 * and if the @p clockOffsetMs, the system time is AHEAD of the server time. To correct the
 * system time, the user can use either of "step", "slew" OR combination of the two clock
 * discipline methodologies depending on the application needs.
 * If the application requires a smooth time continuum of system time, then the "slew"
 * discipline methodology can be used with the clock offset value, @p clockOffSetMs, to correct
 * the system clock gradually with a "slew rate".
 * If the application can accept sudden jump in time (forward or backward), then
 * the "step" discipline methodology can be used to directly update the system
 * clock with the current server time, @p pServerTime, every time the coreSNTP library
 * calls the interface.
 */
typedef void ( * SntpSetTime_t )( const SntpServerInfo_t * pTimeServer,
                                  const SntpTimestamp_t * pServerTime,
                                  int64_t clockOffsetMs,
                                  SntpLeapSecondInfo_t leapSecondInfo );

/**
 * @ingroup sntp_struct_types
 * @typedef NetworkContext_t
 * @brief A user-defined type for context that is passed to the transport interface functions.
 * It MUST be defined by the user to use the library.
 * It is of incomplete type to allow user to define to the needs of their transport
 * interface implementation.
 */
struct NetworkContext;
typedef struct NetworkContext NetworkContext_t;

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to send time request as a single datagram
 * to server on the network over User Datagram Protocol (UDP).
 *
 * @note It is RECOMMENDED that the send operation is non-blocking, i.e. it
 * SHOULD immediately return when the entire UDP data cannot be sent over the
 * network. In such a case, the coreSNTP library will re-try send operation
 * for a maximum period of blocking time passed to the @ref Sntp_SendTimeRequest API.
 *
 * @note If the size of the SNTP packet exceeds the Maximum Transmission Unit (MTU)
 * supported by the network interface of the device, the user-defined implementation
 * MAY either support fragmentation of UDP packets OR use a size for authentication data
 * that allows the SNTP packet to fit within the MTU required size threshold. (Note that
 * the size of SNTP packet is #SNTP_PACKET_BASE_SIZE + authentication data.)
 *
 * @param[in,out] pNetworkContext The user defined NetworkContext_t which
 * is opaque to the coreSNTP library.
 * @param[in] serverAddr The IPv4 address of the time server to send the data to.
 * @param[in] serverPort The port of the server to send data to.
 * @param[in] pBuffer The buffer containing the data to send over the network.
 * @param[in] bytesToSend The size of data in @p pBuffer to send.
 *
 * @return The function SHOULD return one of the following integer codes:
 * - @p bytesToSend when all requested data is successfully transmitted over the
 * network.
 * - 0 when no data could be sent over the network (due to network buffer being
 * full, for example), and the send operation can be retried.
 * - < 0 when the send operation failed to send any data due to an internal error,
 * and operation cannot be retried.
 */
typedef int32_t ( * UdpTransportSendTo_t )( NetworkContext_t * pNetworkContext,
                                            uint32_t serverAddr,
                                            uint16_t serverPort,
                                            const void * pBuffer,
                                            uint16_t bytesToSend );

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to receive the server response, to a time
 * request (sent through the @ref UdpTransportSendTo_t function), from the network over
 * User Datagram Protocol (UDP).
 *
 * @note It is RECOMMENDED that the read operation is non-blocking, i.e. it
 * SHOULD immediately return when no data is available on the network.
 * In such a case, the coreSNTP library will re-try send operation for a maximum period
 * of blocking time passed through the @ref Sntp_ReceiveTimeResponse API.
 *
 * @note If the size of the SNTP response packet from the server exceeds the
 * Maximum Transmission Unit (MTU) supported by the network interface of the device,
 * the user-defined implementation of the interface MAY either support receiving and
 * assembling fragmented UDP packets OR use an authentication data size that allows
 * SNTP packet to fit within the MTU required packet size threshold. (Note that
 * the size of SNTP packet is #SNTP_PACKET_BASE_SIZE + authentication data.)
 *
 * @param[in,out] pNetworkContext The user defined NetworkContext_t which
 * is opaque to the coreSNTP library.
 * @param[in] serverAddr The IPv4 address of the time server to receive data from.
 * @param[in] serverPort The port of the server to receive data from.
 * @param[out] pBuffer This SHOULD be filled with data received from the network.
 * @param[in] bytesToRecv The expected number of bytes to receive from the
 * server.
 *
 * @return The function SHOULD return one of the following integer codes:
 * - @p bytesToRecv value if all the requested number of bytes are received
 * from the network.
 * - ZERO when no data is available on the network, and the operation can be
 * retried.
 * - < 0 when the read operation failed due to internal error, and operation cannot
 * be retried.
 */
typedef int32_t ( * UdpTransportRecvFrom_t )( NetworkContext_t * pNetworkContext,
                                              uint32_t serverAddr,
                                              uint16_t serverPort,
                                              void * pBuffer,
                                              uint16_t bytesToRecv );

/**
 * @ingroup sntp_struct_types
 * @brief Struct representing the UDP transport interface for user-defined functions
 * that coreSNTP library depends on for performing read/write network operations.
 */
typedef struct UdpTransportIntf
{
    NetworkContext_t * pUserContext; /**<@brief The user-defined context for storing
                                      * network socket information. */
    UdpTransportSendTo_t sendTo;     /**<@brief The user-defined UDP send function. */
    UdpTransportRecvFrom_t recvFrom; /**<@brief The user-defined UDP receive function. */
} UdpTransportInterface_t;

/**
 * @ingroup sntp_struct_types
 * @typedef SntpAuthContext_t
 * @brief A user-defined type for context that is passed to the authentication interface functions.
 * It MUST be defined by the user to use the library.
 * It is of incomplete type to allow user to defined to the the needs of their authentication
 * interface implementation.
 */
struct SntpAuthContext;
typedef struct SntpAuthContext SntpAuthContext_t;

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to generate and append
 * authentication code in an SNTP request buffer for the SNTP client to be
 * authenticated by the time server, if a security mechanism is used.
 *
 * The user can choose to implement with any security mechanism, symmetric
 * key-based (like AES-CMAC) or asymmetric key-based (like Network Time Security),
 * depending on the security mechanism supported by the time server being used
 * to synchronize time with.
 *
 * @note The function SHOULD generate the authentication data for the first
 * #SNTP_PACKET_BASE_SIZE bytes of SNTP request packet present in the passed buffer
 * @p pBuffer, and fill the generated authentication data after #SNTP_PACKET_BASE_SIZE
 * bytes in the buffer.
 *
 * @param[in,out] pContext The user defined NetworkContext_t which
 * is opaque to the coreSNTP library.
 * @param[in] pTimeServer The time server being used to request time from.
 * This parameter is useful to choose the security mechanism when multiple time
 * servers are configured in the library, and they require different security
 * mechanisms or authentication credentials to use.
 * @param[in, out] pBuffer This buffer SHOULD be filled with the authentication
 * code generated from the #SNTP_PACKET_BASE_SIZE bytes of SNTP request data
 * present in it.
 * @param[in] bufferSize The maximum amount of data that can be held by the buffer,
 * @p pBuffer.
 * @param[out] pAuthCodeSize This should be filled with size of the authentication
 * data appended to the SNTP request buffer, @p pBuffer. This value plus
 * #SNTP_PACKET_BASE_SIZE should not exceed the buffer size, @p bufferSize.
 *
 * @return The function SHOULD return one of the following integer codes:
 * - #SntpSuccess when the authentication data is successfully appended to @p pBuffer.
 * - #SntpErrorBufferTooSmall when the user-supplied buffer (to the SntpContext_t through
 * @ref Sntp_Init) is not large enough to hold authentication data.
 * - #SntpErrorAuthFailure for failure to generate authentication data due to internal
 * error.
 */
typedef SntpStatus_t (* SntpGenerateAuthCode_t )( SntpAuthContext_t * pContext,
                                                  const SntpServerInfo_t * pTimeServer,
                                                  void * pBuffer,
                                                  size_t bufferSize,
                                                  uint16_t * pAuthCodeSize );

/**
 * @ingroup sntp_callback_types
 * @brief Interface for user-defined function to authenticate server by validating
 * the authentication code present in its SNTP response to a time request, if
 * a security mechanism is supported by the server.
 *
 * The user can choose to implement with any security mechanism, symmetric
 * key-based (like AES-CMAC) or asymmetric key-based (like Network Time Security),
 * depending on the security mechanism supported by the time server being used
 * to synchronize time with.
 *
 * @note In an SNTP response, the authentication code is present only after the
 * first #SNTP_PACKET_BASE_SIZE bytes. Depending on the security mechanism used,
 * the first #SNTP_PACKET_BASE_SIZE bytes MAY be used in validating the
 * authentication data sent by the server.
 *
 * @param[in,out] pContext The user defined NetworkContext_t which
 * is opaque to the coreSNTP library.
 * @param[in] pTimeServer The time server that has to be authenticated from its
 * SNTP response.
 * This parameter is useful to choose the security mechanism when multiple time
 * servers are configured in the library, and they require different security
 * mechanisms or authentication credentials to use.
 * @param[in] pResponseData The SNTP response from the server that contains the
 * authentication code after the first #SNTP_PACKET_BASE_SIZE bytes.
 * @param[in] responseSize The total size of the response from the server.
 *
 * @return The function SHOULD return one of the following integer codes:
 * - #SntpSuccess when the server is successfully authenticated.
 * - #SntpServerNotAuthenticated when server could not be authenticated.
 * - #SntpErrorAuthFailure for failure to authenticate server due to internal
 * error.
 */
typedef SntpStatus_t (* SntpValidateServerAuth_t )( SntpAuthContext_t * pContext,
                                                    const SntpServerInfo_t * pTimeServer,
                                                    const void * pResponseData,
                                                    uint16_t responseSize );

/**
 * @ingroup sntp_struct_types
 * @brief Struct representing the authentication interface for securely
 * communicating with time servers.
 *
 * @note Using a security mechanism is OPTIONAL for using the coreSNTP
 * library i.e. a user does not need to define the authentication interface
 * if they are not using a security mechanism for SNTP communication.
 */
typedef struct SntpAuthenticationIntf
{
    /**
     *@brief The user-defined context for storing information like
     * key credentials required for cryptographic operations in the
     * security mechanism used for communicating with server.
     */
    SntpAuthContext_t * pAuthContext;

    /**
     * @brief The user-defined function for appending client authentication data.
     * */
    SntpGenerateAuthCode_t generateClientAuth;

    /**
     * @brief The user-defined function for authenticating server from its SNTP
     * response.
     */
    SntpValidateServerAuth_t validateServerAuth;
} SntpAuthenticationInterface_t;

/**
 * @ingroup sntp_struct_types
 * @brief Structure for a context that stores state for managing a long-running
 * SNTP client that periodically polls time and synchronizes system clock.
 */
typedef struct SntpContext
{
    /**
     * @brief List of time servers in decreasing priority order configured
     * for the SNTP client.
     * Only a single server is configured for use at a time across polling
     * attempts until the server rejects a time request or there is a response
     * timeout, after which, the next server in the list is used for subsequent
     * polling requests.
     */
    const SntpServerInfo_t * pTimeServers;

    /**
     * @brief Number of servers configured for use.
     */
    size_t numOfServers;

    /**
     * @brief The index for the currently configured time server for time querying
     * from the list of time servers in @ref pTimeServers.
     */
    size_t currentServerIndex;

    /**
     * @brief The user-supplied buffer for storing network data of both SNTP requests
     * and SNTP response.
     */
    uint8_t * pNetworkBuffer;

    /**
     * @brief The size of the network buffer.
     */
    size_t bufferSize;

    /**
     * @brief The user-supplied function for resolving DNS name of time servers.
     */
    SntpResolveDns_t resolveDnsFunc;

    /**
     * @brief The user-supplied function for obtaining the current system time.
     */
    SntpGetTime_t getTimeFunc;

    /**
     * @brief The user-supplied function for correcting system time after receiving
     * time from a server.
     */
    SntpSetTime_t setTimeFunc;

    /**
     * @brief The user-defined interface for performing User Datagram Protocol (UDP)
     * send and receive network operations.
     */
    UdpTransportInterface_t networkIntf;

    /**
     * @brief The user-defined interface for incorporating security mechanism of
     * adding client authentication in SNTP request as well as authenticating server
     * from SNTP response.
     *
     * @note If the application will not use security mechanism for any of the
     * configured servers, then this interface can be undefined.
     */
    SntpAuthenticationInterface_t authIntf;

    /**
     * @brief Cache of the resolved Ipv4 address of the current server being used for
     * time synchronization.
     * As a Best Practice functionality, the client library attempts to resolve the
     * DNS of the time-server every time the @ref Sntp_SendTimeRequest API is called.
     */
    uint32_t currentServerAddr;

    /**
     * @brief Cache of the timestamp of sending the last time request to a server
     * for replay attack protection by checking that the server response contains
     * the same timestamp in its "originate timestamp" field.
     */
    SntpTimestamp_t lastRequestTime;

    /**
     * @brief State member for storing the size of the SNTP packet that includes
     * both #SNTP_PACKET_BASE_SIZE bytes plus any authentication data, if a security
     * mechanism is used.
     * This value is used for expecting the same size for an SNTP response
     * from the server.
     */
    uint16_t sntpPacketSize;

    /**
     * @brief The timeout duration (in milliseconds) for receiving a response, through
     * @ref Sntp_ReceiveTimeResponse API, from a server after the request for time is
     * sent to it through @ref Sntp_SendTimeRequest API.
     */
    uint32_t responseTimeoutMs;
} SntpContext_t;

/**
 * @brief Initializes a context for SNTP client communication with SNTP/NTP
 * servers.
 *
 * @param[out] pContext The user-supplied memory for the context that will be
 * initialized to represent an SNTP client.
 * @param[in] pTimeServers The list of decreasing order of priority of time
 * servers that should be used by the SNTP client. This list MUST stay in
 * scope for all the time of use of the context.
 * @param[in] numOfServers The number of servers in the list, @p pTimeServers.
 * @param[in] serverResponseTimeoutMs The timeout duration (in milliseconds) for
 * receiving server response for time requests. The same timeout value is used for
 * each server in the @p pTimeServers list.
 * @param[in] pNetworkBuffer The user-supplied memory that will be used for
 * storing network data for SNTP client-server communication. The buffer
 * MUST stay in scope for all the time of use of the context.
 * @param[in] bufferSize The size of the passed buffer @p pNetworkBuffer. The buffer
 * SHOULD be appropriately sized for storing an entire SNTP packet which includes
 * both #SNTP_PACKET_BASE_SIZE bytes of standard SNTP packet size, and space for
 * authentication data, if security mechanism is used to communicate with any of
 * the time servers configured for use.
 * @param[in] resolveDnsFunc The user-defined function for DNS resolution of time
 * server.
 * @param[in] getSystemTimeFunc The user-defined function for querying system
 * time.
 * @param[in] setSystemTimeFunc The user-defined function for correcting system
 * time for every successful time response received from a server.
 * @param[in] pTransportIntf The user-defined function for performing network
 * send/recv operations over UDP.
 * @param[in] pAuthIntf The user-defined interface for generating client authentication
 * in SNTP requests and authenticating servers in SNTP responses, if security mechanism
 * is used in SNTP communication with server(s). If security mechanism is not used in
 * communication with any of the configured servers (in @p pTimeServers), then the
 * @ref SntpAuthenticationInterface_t does not need to be defined and this parameter
 * can be NULL.
 *
 * @return This function returns one of the following:
 * - #SntpSuccess if the context is initialized.
 * - #SntpErrorBadParameter if any of the passed parameters in invalid.
 * - #SntpErrorBufferTooSmall if the buffer does not have the minimum size
 * required for a valid SNTP response packet.
 */
/* @[define_sntp_init] */
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
                        const SntpAuthenticationInterface_t * pAuthIntf );
/* @[define_sntp_init] */


/**
 * @brief Sends a request for time from the currently configured server (in the
 * context).
 * If the user has provided an authentication interface, the client
 * authentication code is appended to the request before sending over the network
 * by calling the @ref SntpGenerateAuthCode_t function of the
 * @ref SntpAuthenticationInterface_t.
 *
 * @note This function will ONLY send a request if there is a server available
 * in the configured list that has not rejected an earlier request for time.
 * This adheres to the Best Practice functionality specified in [Section 10 Point 8
 * of SNTPv4 specification](https://tools.ietf.org/html/rfc4330#section-10).
 *
 * @param[in] pContext The context representing an SNTPv4 client.
 * @param[in] randomNumber A random number serializing the SNTP request packet
 * to protect against spoofing attacks by attackers that are off the network path
 * of the SNTP client-server communication. This mechanism is suggested by SNTPv4
 * specification in [RFC 4330 Section 3](https://tools.ietf.org/html/rfc4330#section-3).
 * @param[in] blockTimeMs The maximum duration of time (in milliseconds) the function will
 * block on attempting to send time request to the server over the network. If a zero
 * block time value is provided, then the function will attempt to send the packet ONLY
 * once.
 *
 * @note It is RECOMMENDED that a True Random Number Generator is used to generate the
 * random number by using a hardware module, like Hardware Security Module (HSM), Secure Element,
 * etc, as the entropy source.
 *
 * @return The API function returns one of the following:
 *  - #SntpSuccess if a time request is successfully sent to the currently configured
 * time server in the context.
 *  - #SntpErrorBadParameter if an invalid context is passed to the function.
 *  - #SntpErrorContextNotInitialized if an uninitialized or invalid context is passed
 * to the function.
 *  - #SntpErrorDnsFailure if there is failure in the user-defined function for
 * DNS resolution of the time server.
 *  - #SntpErrorNetworkFailure if the SNTP request could not be sent over the network
 * through the user-defined transport interface.
 *  - #SntpErrorAuthFailure if there was a failure in generating the client
 * authentication code in the user-defined authentication interface.
 *  - #SntpErrorSendTimeout if the time request packet could not be sent over the
 * network for the entire @p blockTimeMs duration.
 */
/* @[define_sntp_sendtimerequest] */
SntpStatus_t Sntp_SendTimeRequest( SntpContext_t * pContext,
                                   uint32_t randomNumber,
                                   uint32_t blockTimeMs );
/* @[define_sntp_sendtimerequest] */


/**
 * @brief Receives a time response from the server that has been requested for time with
 * the @ref Sntp_SendTimeRequest API function.
 * Once an accepted response containing time from server is received, this function calls
 * the user-defined @ref SntpSetTime_t function to update the system time.
 *
 * @note If the user has provided an authentication interface to the client
 * (through @ref Sntp_Init), the server response is authenticated by calling the
 * @ref SntpValidateServerAuth_t function of the @ref SntpAuthenticationInterface_t interface.
 *
 * @note On receiving a successful server response containing server time,
 * this API calculates the clock offset value of the system clock relative to the
 * server before calling the user-defined @ref SntpSetTime_t function for updating
 * the system time.
 *
 * @note For correct calculation of clock-offset, the server and client times MUST be within
 * ~68 years (or 2^31 seconds) of each other. In the special case when the server and client
 * times are exactly 2^31 seconds apart, the library ASSUMES that the server time is ahead
 * of the client time, and returns the positive clock-offset value of INT32_MAX seconds.
 *
 * @note This API will rotate the server of use in the library for the next time request
 * (through the @ref Sntp_SendTimeRequest) if either of following events occur:
 *  - The server has responded with a rejection for the time request.
 *                         OR
 *  - The server response wait has timed out.
 * If all the servers configured in the context have been used, the API will rotate server for
 * time query back to the first server in the list which will be used in next time request.
 *
 * @param[in] pContext The context representing an SNTPv4 client.
 * @param[in] blockTimeMs The maximum duration of time (in milliseconds) the function will
 * block on receiving a response from the server unless either the response is received
 * OR a response timeout occurs.
 *
 * @note This function can be called multiple times with zero or small blocking times
 * to poll whether server response is received until either the response response is
 * received from the server OR a response timeout has occurred.
 *
 * @return This API functions returns one of the following:
 *  - #SntpSuccess if a successful server response is received.
 *  - #SntpErrorContextNotInitialized if an uninitialized or invalid context is passed
 * to the function.
 *  - #SntpErrorBadParameter if an invalid context is passed to the function.
 *  - #SntpErrorNetworkFailure if there is a failure in the user-defined transport
 *  - #SntpErrorAuthFailure if an internal error occurs in the user-defined
 * authentication interface when validating the server response.
 *  - #SntpServerNotAuthenticated when the server could not be authenticated from
 * its response with the user-defined authentication interface.
 *  - #SntpInvalidResponse if the server response fails sanity checks expected in an
 * SNTP response packet.
 *  - #SntpErrorResponseTimeout if a timeout has occurred in receiving response from
 * the server.
 *  - #SntpRejectedResponse if the server responded with a rejection for the time
 * request.
 */
/* @[define_sntp_receivetimeresponse] */
SntpStatus_t Sntp_ReceiveTimeResponse( SntpContext_t * pContext,
                                       uint32_t blockTimeMs );
/* @[define_sntp_receivetimeresponse] */

/**
 * @brief Converts @ref SntpStatus_t to its equivalent
 * string.
 *
 * @note The returned string MUST NOT be modified.
 *
 * @param[in] status The status to convert to a string.
 *
 * @return The string representation of the status
 * code.
 */
/* @[define_sntp_statustostr] */
const char * Sntp_StatusToStr( SntpStatus_t status );
/* @[define_sntp_statustostr] */

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_SNTP_CLIENT_H_ */
