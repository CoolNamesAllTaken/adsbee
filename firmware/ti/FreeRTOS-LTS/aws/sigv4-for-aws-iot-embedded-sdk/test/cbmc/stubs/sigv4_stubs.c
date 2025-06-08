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
 * @file sigv4_stubs.c
 * @brief Implements the functions declared in sigv4_stubs.h
 */

#include <sigv4.h>
#include <sigv4_internal.h>
#include <sigv4_stubs.h>

SigV4Status_t scanValue( const char * pDate,
                         const char formatChar,
                         size_t readLoc,
                         size_t lenToRead,
                         SigV4DateTime_t * pDateElements )
{
    SigV4Status_t returnStatus = SigV4InvalidParameter;
    const char * pMonthNames[] = MONTH_NAMES;
    const char * pLoc = pDate + readLoc;
    size_t remainingLenToRead = lenToRead;
    int32_t result = 0;
    static flag = 0;

    assert( pDate != NULL );
    assert( pDateElements != NULL );

    if( formatChar == '*' )
    {
        remainingLenToRead = 0U;
    }

    /* Determine if month value is non-numeric. */
    if( ( formatChar == 'M' ) && ( remainingLenToRead == MONTH_ASCII_LEN ) )
    {
        returnStatus = SigV4Success;

        remainingLenToRead = 0U;
    }

    /* Interpret integer value of numeric representation. */
    while( ( remainingLenToRead > 0U ) && ( *pLoc >= '0' ) && ( *pLoc <= '9' ) )
    {
        result = ( result * 10 ) + ( int32_t ) ( *pLoc - '0' );
        remainingLenToRead--;
        pLoc += 1;
    }

    if( remainingLenToRead != 0U )
    {
        LogError( ( "Parsing Error: Expected numerical string of type '%%%d%c', "
                    "but received '%.*s'.",
                    ( int ) lenToRead,
                    formatChar,
                    ( int ) lenToRead,
                    pLoc ) );
        returnStatus = SigV4ISOFormattingError;
    }

    if( returnStatus != SigV4ISOFormattingError )
    {
        addToDate( formatChar,
                   result,
                   pDateElements );
    }

    return returnStatus;
}

void addToDate( const char formatChar,
                int32_t result,
                SigV4DateTime_t * pDateElements )
{
    assert( pDateElements != NULL );
    assert( result >= 0 );

    switch( formatChar )
    {
        case 'Y':
            pDateElements->year = result;
            break;

        case 'M':
            pDateElements->mon = result;
            break;

        case 'D':
            pDateElements->mday = result;
            break;

        case 'h':
            pDateElements->hour = result;
            break;

        case 'm':
            pDateElements->min = result;
            break;

        case 's':
            pDateElements->sec = result;
            break;

        default:

            /* Do not assign values for skipped characters ('*'), or
             * unrecognized format specifiers. */
            break;
    }
}

SigV4Status_t writeLineToCanonicalRequest( const char * pLine,
                                           size_t lineLen,
                                           CanonicalContext_t * pCanonicalContext )
{
    SigV4Status_t ret = SigV4InsufficientMemory;

    assert( pCanonicalContext != NULL );

    if( pCanonicalContext->bufRemaining >= ( lineLen + 1U ) )
    {
        assert( __CPROVER_w_ok( &( pCanonicalContext->pBufProcessing[ pCanonicalContext->uxCursorIndex ] ), ( lineLen + 1U ) ) );
        ret = SigV4Success;
    }

    return ret;
}

SigV4Status_t SigV4_EncodeURI( const char * pUri,
                               size_t uriLen,
                               char * pCanonicalURI,
                               size_t * canonicalURILen,
                               bool encodeSlash,
                               bool doubleEncodeEquals )
{
    SigV4Status_t returnStatus = SigV4Success;

    assert( pUri != NULL );
    assert( pCanonicalURI != NULL );
    assert( canonicalURILen != NULL );

    if( nondet_bool() )
    {
        returnStatus = SigV4Success;
    }
    else
    {
        returnStatus = SigV4InsufficientMemory;
    }

    return returnStatus;
}

SigV4Status_t generateCanonicalQuery( const char * pQuery,
                                      size_t queryLen,
                                      const bool doubleEncodeEqualsInParmsValues,
                                      CanonicalContext_t * pCanonicalContext )
{
    SigV4Status_t returnStatus = SigV4InsufficientMemory;

    assert( pCanonicalContext != NULL );

    if( nondet_bool() )
    {
        __CPROVER_assume( pCanonicalContext->bufRemaining < SIGV4_PROCESSING_BUFFER_LENGTH );
        returnStatus = SigV4Success;
    }
    else
    {
        returnStatus = SigV4InsufficientMemory;
    }

    return returnStatus;
}

SigV4Status_t generateCanonicalAndSignedHeaders( const char * pHeaders,
                                                 size_t headersLen,
                                                 uint32_t flags,
                                                 CanonicalContext_t * pCanonicalContext,
                                                 char ** pSignedHeaders,
                                                 size_t * pSignedHeadersLen )
{
    SigV4Status_t returnStatus = SigV4InsufficientMemory;

    assert( pHeaders != NULL );
    assert( pCanonicalContext != NULL );
    assert( pSignedHeaders != NULL );
    assert( pSignedHeadersLen != NULL );

    if( nondet_bool() )
    {
        /* The signed headers are assumed to start at a location within the processing
         * buffer and should not end past the length of the processing buffer. */
        size_t headersLen, headerOffset, bytesConsumed;
        char * pHeaders = NULL;
        __CPROVER_assume( pCanonicalContext->bufRemaining < SIGV4_PROCESSING_BUFFER_LENGTH );
        bytesConsumed = SIGV4_PROCESSING_BUFFER_LENGTH - pCanonicalContext->bufRemaining;
        __CPROVER_assume( headerOffset < bytesConsumed );
        __CPROVER_assume( headersLen > 0U && headersLen <= bytesConsumed - headerOffset );
        pHeaders = ( char * ) pCanonicalContext->pBufProcessing + headerOffset;

        *pSignedHeadersLen = headersLen;
        *pSignedHeaders = pHeaders;
        returnStatus = SigV4Success;
    }
    else
    {
        returnStatus = SigV4InsufficientMemory;
    }

    return returnStatus;
}

SigV4Status_t copyHeaderStringToCanonicalBuffer( const char * pData,
                                                 size_t dataLen,
                                                 uint32_t flags,
                                                 char separator,
                                                 CanonicalContext_t * canonicalRequest )
{
    SigV4Status_t returnStatus = SigV4Success;
    size_t buffRemaining;

    __CPROVER_assume( pData != NULL );
    __CPROVER_assume( dataLen > 0 );
    __CPROVER_assume( dataLen < CBMC_MAX_OBJECT_SIZE );

    assert( ( pData != NULL ) && ( dataLen > 0 ) );
    assert( canonicalRequest != NULL );

    buffRemaining = canonicalRequest->bufRemaining;

    if( buffRemaining < dataLen )
    {
        returnStatus = SigV4InsufficientMemory;
    }

    return returnStatus;
}
