/*
 * coreHTTP v3.1.1
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file core_http_config.h
 * @brief Custom configurations for the coreHTTP library.
 */

#ifndef CORE_HTTP_CONFIG_H
#define CORE_HTTP_CONFIG_H

/**
 * @brief The maximum duration between non-empty network reads while receiving
 * an HTTP response via the #HTTPClient_Send API function.
 *
 * The transport receive function may be called multiple times until the end of
 * the response is detected by the parser. This timeout represents the maximum
 * duration that is allowed without any data reception from the network for the
 * incoming response.
 *
 * If the timeout expires, the #HTTPClient_Send function will return
 * #HTTPNetworkError.
 *
 * This is set to 1 to exit right away after a zero is received in the transport
 * receive stub. There is no added value, in proving memory safety, to repeat
 * the logic that checks if the retry timeout is reached.
 */
#define HTTP_RECV_RETRY_TIMEOUT_MS    ( 1U )

/**
 * @brief The maximum duration between non-empty network transmissions while
 * sending an HTTP request via the #HTTPClient_Send API function.
 *
 * When sending an HTTP request, the transport send function may be called multiple
 * times until all of the required number of bytes are sent.
 * This timeout represents the maximum duration that is allowed for no data
 * transmission over the network through the transport send function.
 *
 * If the timeout expires, the #HTTPClient_Send function returns #HTTPNetworkError.
 *
 * This is set to 1 to exit right away after a zero is received in the transport
 * send stub. There is no added value, in proving memory safety, to repeat
 * the logic that checks if the retry timeout is reached.
 */
#define HTTP_SEND_RETRY_TIMEOUT_MS    ( 1U )


#endif /* ifndef CORE_HTTP_CONFIG_H */
