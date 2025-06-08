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
 * @file core_sntp_stubs_stubs.h
 * @brief Stubs definitions of UDP transport interface and authentication interface of coreSNTP API.
 */
#ifndef CORE_SNTP_CBMC_STUBS_H_
#define CORE_SNTP_CBMC_STUBS_H_

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include "core_sntp_client.h"

/**
 * @brief Application defined network interface send function.
 *
 * @param[in] pNetworkContext Application defined network interface context.
 * @param[in] serverAddr Server address to which application sends data.
 * @param[in] serverPort Server port to which application sends data.
 * @param[out] pBuffer SNTP network send buffer.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return Any value from INT32_MIN to INT32_MAX.
 */
int32_t NetworkInterfaceSendStub( NetworkContext_t * pNetworkContext,
                                  uint32_t serverAddr,
                                  uint16_t serverPort,
                                  const void * pBuffer,
                                  uint16_t bytesToSend );

/**
 * @brief Application defined network interface receive function.
 *
 * @param[in] pNetworkContext Application defined network interface context.
 * @param[in] serverAddr Server address from which application receives data.
 * @param[in] serverPort Server port from which application receives data.
 * @param[out] pBuffer SNTP network receive buffer.
 * @param[in] bytesToRecv SNTP requested bytes.
 *
 * @return Any value from INT32_MIN to INT32_MAX.
 */
int32_t NetworkInterfaceReceiveStub( NetworkContext_t * pNetworkContext,
                                     uint32_t serverAddr,
                                     uint16_t serverPort,
                                     void * pBuffer,
                                     uint16_t bytesToRecv );

/**
 * @brief Application defined function to generate and append
 * authentication code in an SNTP request buffer for the SNTP client to be
 * authenticated by the time server, if a security mechanism is used.
 *
 * @param[in] pContext Application defined authentication interface context.
 * @param[in] pTimeServer The time server being used to request time from.
 * This parameter is useful to choose the security mechanism when multiple time
 * servers are configured in the library, and they require different security
 * mechanisms or authentication credentials to use.
 * @param[in] pBuffer SNTP request buffer.
 * @param[in] bufferSize The maximum amount of data that can be held by the buffer.
 * @param[out] pAuthCodeSize This should be filled with size of the authentication
 * data appended to the SNTP request buffer, @p pBuffer.
 *
 * @return The function SHOULD return one of the following integer codes:
 * - #SntpSuccess when the authentication data is successfully appended to @p pBuffer.
 * - #SntpErrorBufferTooSmall when the user-supplied buffer (to the SntpContext_t through
 * @ref Sntp_Init) is not large enough to hold authentication data.
 */
SntpStatus_t GenerateClientAuthStub( SntpAuthContext_t * pContext,
                                     const SntpServerInfo_t * pTimeServer,
                                     void * pBuffer,
                                     size_t bufferSize,
                                     uint16_t * pAuthCodeSize );

/**
 * @brief Application defined function to authenticate server by validating
 * the authentication code present in its SNTP response to a time request, if
 * a security mechanism is supported by the server.
 *
 * @param[in,out] pContext The application defined NetworkContext_t which
 * is opaque to the coreSNTP library.
 * @param[in] pTimeServer The time server that has to be authenticated from its
 * SNTP response.
 * @param[in] pResponseData The SNTP response from the server that contains the
 * authentication code after the first #SNTP_PACKET_BASE_SIZE bytes.
 * @param[in] responseSize The total size of the response from the server.
 *
 * @return The function ALWAYS returns #SntpSuccess
 */
SntpStatus_t ValidateServerAuthStub( SntpAuthContext_t * pContext,
                                     const SntpServerInfo_t * pTimeServer,
                                     const void * pResponseData,
                                     uint16_t responseSize );

/**
 * @brief Application defined function to resolve time server domain-name
 * to an IPv4 address.
 *
 * @param[in] pTimeServer The time-server whose IPv4 address is to be resolved.
 * @param[out] pIpV4Addr This should be filled with the resolved IPv4 address.
 * of @p pTimeServer.
 *
 * @return `true` if DNS resolution is successful; otherwise `false` to represent
 * failure.
 */
bool ResolveDnsFuncStub( const SntpServerInfo_t * pServerAddr,
                         uint32_t * pIpV4Addr );

/**
 * @brief Application defined function to obtain the current system time
 * in SNTP timestamp format.
 *
 * @param[out] pCurrentTime This should be filled with the current system time
 * in SNTP timestamp format.
 */
void GetTimeFuncStub( SntpTimestamp_t * pCurrentTime );

/**
 * @brief Application defined function to update the system clock time
 * so that it is synchronized the time server used for getting current time.
 *
 * @param[in] pTimeServer The time server used to request time.
 * @param[in] pServerTime The current time returned by the @p pTimeServer.
 * @param[in] clockOffSetMs The calculated clock offset of the system relative
 * to the server time.
 * @param[in] leapSecondInfo Information about whether there is about an upcoming
 * leap second adjustment.
 */
void SetTimeFuncStub( const SntpServerInfo_t * pTimeServer,
                      const SntpTimestamp_t * pServerTime,
                      int64_t clockOffsetMs,
                      SntpLeapSecondInfo_t leapSecondInfo );

#endif /* ifndef CORE_SNTP_CBMC_STUBS_H_ */
