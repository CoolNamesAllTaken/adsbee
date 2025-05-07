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

/**
 * @file sigv4_stubs.h
 * @brief Declarations for the (normally) static functions from sigv4.c.
 * Please see sigv4.c for documentation.
 */

#ifndef SIGV4_STUBS_H_
#define SIGV4_STUBS_H_

#include <stdbool.h>

#include <sigv4.h>
#include <sigv4_internal.h>

void addToDate( const char formatChar,
                int32_t result,
                SigV4DateTime_t * pDateElements );

SigV4Status_t scanValue( const char * pDate,
                         const char formatChar,
                         size_t readLoc,
                         size_t lenToRead,
                         SigV4DateTime_t * pDateElements );

SigV4Status_t writeLineToCanonicalRequest( const char * pLine,
                                           size_t lineLen,
                                           CanonicalContext_t * pCanonicalContext );

SigV4Status_t SigV4_EncodeURI( const char * pUri,
                               size_t uriLen,
                               char * pCanonicalURI,
                               size_t * canonicalURILen,
                               bool encodeSlash,
                               bool doubleEncodeEquals );

SigV4Status_t generateCanonicalQuery( const char * pQuery,
                                      size_t queryLen,
                                      const bool doubleEncodeEqualsInParmsValues,
                                      CanonicalContext_t * pCanonicalContext );

SigV4Status_t generateCanonicalAndSignedHeaders( const char * pHeaders,
                                                 size_t headersLen,
                                                 uint32_t flags,
                                                 CanonicalContext_t * canonicalRequest,
                                                 char ** pSignedHeaders,
                                                 size_t * pSignedHeadersLen );

SigV4Status_t copyHeaderStringToCanonicalBuffer( const char * pData,
                                                 size_t dataLen,
                                                 uint32_t flags,
                                                 char separator,
                                                 CanonicalContext_t * canonicalRequest );

#endif /* ifndef SIGV4_STUBS_H_ */
