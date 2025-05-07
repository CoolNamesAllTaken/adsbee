/*
 * SigV4 Library v1.3.0
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
 * @file sigv4_config.h
 * @brief The default values for configuration macros used by the SigV4 Library.
 *
 * @note This file should NOT be modified. If custom values are needed for any
 * configuration macros, a sigv4_config.h file should be provided to the SigV4
 * Library to override the default values defined in this file. To use
 * the custom config file, the preprocessor macro SIGV4_DO_NOT_USE_CUSTOM_CONFIG
 * must NOT be set.
 */

#ifndef SIGV4_CONFIG_H_
#define SIGV4_CONFIG_H_

/**
 * @brief Macro indicating the largest block size of any hashing
 * algorithm used for SigV4 authentication i.e. the maximum of all
 * values specified for the hashBlockLen in #SigV4CryptoInterface_t.
 * For example, using SHA-512 would require this value to be at least 128.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `64`
 */
#define SIGV4_HASH_MAX_BLOCK_LENGTH     ( MAX_HASH_BLOCK_LEN - 1U )

/**
 * @brief Macro defining the maximum digest length of the specified hash function,
 * used to determine the length of the output buffer.
 *
 * This macro should be updated if using a hashing algorithm other than SHA256
 * (32 byte digest length). For example, using SHA512 would require this
 * value to be at least 64.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `32`
 */
#define SIGV4_HASH_MAX_DIGEST_LENGTH    ( MAX_HASH_DIGEST_LEN - 1U )

/**
 * @brief Macro defining the size of the internal buffer used for incremental
 * canonicalization and hashing.
 *
 * A buffer of this size in bytes is declared on the stack. It should be be
 * large enough for the digest output of the specified hash function.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `1024`
 */
#ifndef SIGV4_PROCESSING_BUFFER_LENGTH
    #define SIGV4_PROCESSING_BUFFER_LENGTH    60U
#endif

/**
 * @brief Macro defining the maximum number of headers in the request, used to
 * assist the library in sorting header fields during canonicalization.
 *
 * This macro should be updated if the number of request headers the application
 * wishes to sign is higher or lower than the default value (100).
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `100`
 */
#ifndef SIGV4_MAX_HTTP_HEADER_COUNT
    #define SIGV4_MAX_HTTP_HEADER_COUNT    5U
#endif

/**
 * @brief Macro defining the maximum number of query key/value pairs, used to
 * assist the library in sorting query keys during canonicalization.
 *
 * This macro should be updated if the number of query key/value pairs the
 * application wishes to sign is higher or lower than the default value (100).
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `100`
 */
#ifndef SIGV4_MAX_QUERY_PAIR_COUNT
    #define SIGV4_MAX_QUERY_PAIR_COUNT    5U
#endif

#endif /* ifndef SIGV4_CONFIG_H_ */
