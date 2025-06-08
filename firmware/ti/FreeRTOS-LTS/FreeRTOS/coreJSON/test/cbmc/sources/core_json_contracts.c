/*
 * coreJSON v3.3.0
 * Copyright (C) 2023 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifndef CORE_JSON_CONTRACTS_C_
#define CORE_JSON_CONTRACTS_C_

#include "core_json_contracts.h"

/**
 * When to use `&` vs `&&`:
 * Prefer `cond1 & cond2` when `cond2` can be evaluated without errors without knowing that `cond1` holds: e.g.  `( 0 < i ) & ( i < j )`.
 *
 * Use `cond1 && cond2` when `cond1` must be established first to ensure that `cond2` can be evaluated without error: e.g.
 * `( allocated( p, size ) & ( 0 < i & i < size ) ) && p[i] > 0`.
 */

/* Valid allocated buffer up to size max. */
bool isValidBuffer( const char * buf,
                    size_t max )
{
    return ( 0U < max )
           & ( allocated( buf, max ) );
}

/* Valid allocated buffer up to size max and allocated start index. */
bool isValidBufferWithStartIndex( const char * buf,
                                  size_t max,
                                  size_t * start )
{
    return isValidBuffer( buf, max )
           & ( allocated( start, sizeof( *start ) ) );
}

/* Invariant for index in the buffer. */
bool isValidStart( size_t start,
                   size_t old_start,
                   size_t max )
{
    return ( start >= old_start ) &&
           ( ( old_start < max ) ? ( start <= max ) : ( start == old_start ) );
}

bool JSON_SearchConstPreconditions( const char * buf,
                                    size_t max,
                                    const char * query,
                                    size_t queryLength,
                                    const char ** outValue,
                                    size_t * outValueLength,
                                    JSONTypes_t * outType )
{
    return ( buf == NULL || allocated( buf, max ) )
           & ( query == NULL || allocated( query, queryLength ) )
           & ( outValue == NULL || allocated( outValue, sizeof( *outValue ) ) )
           & ( outValueLength == NULL || allocated( outValueLength, sizeof( *outValueLength ) ) )
           & ( outType == NULL || allocated( outType, sizeof( *outType ) ) );
}

bool JSON_SearchConstPostconditions( JSONStatus_t result,
                                     const char * buf,
                                     const char ** outValue,
                                     size_t * outValueLength,
                                     size_t max )
{
    bool validity = isJSONSearchEnum( result );

    if( validity && ( result == JSONSuccess ) )
    {
        char * endOfValue = *outValue + *outValueLength;
        char * endOfBuf = buf + max;
        validity = pointer_in_range( buf, endOfValue, endOfBuf );
    }

    return validity;
}

bool JSON_IteratePreconditions( const char * buf,
                                size_t max,
                                size_t * start,
                                size_t * next,
                                JSONPair_t * outPair )
{
    return ( 0 < max )
           & ( buf == NULL || allocated( buf, max ) )
           & ( start == NULL || allocated( start, sizeof( *start ) ) )
           & ( next == NULL || allocated( next, sizeof( *next ) ) )
           & ( outPair == NULL || allocated( outPair, sizeof( *outPair ) ) )
           & IMPLIES( outPair != NULL, ( ( outPair->keyLength == 0 && outPair->key == NULL ) || allocated( outPair->key, outPair->keyLength ) ) )
           & IMPLIES( outPair != NULL, ( ( outPair->valueLength == 0 && outPair->value == NULL ) || allocated( outPair->value, outPair->valueLength ) ) );
}

bool JSON_IteratePostconditions( JSONStatus_t result,
                                 const char * buf,
                                 size_t max,
                                 JSONPair_t * outPair )
{
    bool validity = isJSONIterateEnum( result );

    if( validity && ( result == JSONSuccess ) )
    {
        validity = IMPLIES( ( outPair->key != NULL ), ( ( outPair->key > buf ) && ( ( outPair->key + outPair->keyLength ) < ( buf + max ) ) ) )
                   & IMPLIES( ( outPair->key != NULL ), ( ( outPair->key + outPair->keyLength ) < outPair->value ) )
                   & ( ( outPair->value > buf ) && ( ( outPair->value + outPair->valueLength ) <= ( buf + max ) ) )
                   & ( isJSONTypesEnum( outPair->jsonType ) );
    }

    return validity;
}

JSONStatus_t JSON_ValidatePreconditions( const char * buf,
                                         size_t max )
{
    return( buf == NULL || allocated( buf, max ) );
}

bool arraySearchPreconditions( const char * buf,
                               size_t max,
                               size_t * outValue,
                               size_t * outValueLength )
{
    return ( isValidBuffer( buf, max ) )
           & ( allocated( outValue, sizeof( *outValue ) ) )
           & ( allocated( outValueLength, sizeof( *outValueLength ) ) )
           & ( *outValueLength <= max );
}

bool arraySearchPostconditions( bool result,
                                const char * buf,
                                size_t max,
                                size_t * outValue,
                                size_t * outValueLength,
                                size_t old_outValue,
                                size_t old_outValueLength )
{
    bool validity = true;

    if( result )
    {
        validity = ( *outValue < max ) &&
                   ( 0 < *outValueLength && *outValueLength <= max - *outValue ) &&
                   IMPLIES( buf[ *outValue ] == '"', ( 2 <= *outValueLength && *outValueLength <= max - *outValue ) );
    }
    else
    {
        validity = ( *outValue == old_outValue ) &&
                   ( *outValueLength == old_outValueLength );
    }

    return validity;
}

bool objectSearchPreconditions( const char * buf,
                                size_t max,
                                const char * query,
                                size_t queryLength,
                                size_t * outValue,
                                size_t * outValueLength )
{
    return arraySearchPreconditions( buf, max, outValue, outValueLength )
           & ( allocated( query, queryLength ) );
}

bool multiSearchPreconditions( const char * buf,
                               size_t max,
                               const char * query,
                               size_t queryLength,
                               size_t * outValue,
                               size_t * outValueLength )
{
    return ( isValidBuffer( buf, max ) )
           & ( 0U < queryLength )
           & ( allocated( query, queryLength ) )
           & ( allocated( outValue, sizeof( *outValue ) ) )
           & ( allocated( outValueLength, sizeof( *outValueLength ) ) );
}

bool multiSearchPostconditions( JSONStatus_t result,
                                const char * buf,
                                size_t max,
                                size_t * outValue,
                                size_t * outValueLength,
                                size_t old_outValue,
                                size_t old_outValueLength )
{
    bool validity = isJSONSearchEnum( result ) &&
                    arraySearchPostconditions( result == JSONSuccess, buf, max, outValue, outValueLength, old_outValue, old_outValueLength );

    return validity;
}

bool skipPostconditions( bool result,
                         const char * buf,
                         size_t * start,
                         size_t old_start,
                         size_t max,
                         size_t gap )
{
    bool validity = isValidStart( *start, old_start, max ) &&
                    IMPLIES( result, ( old_start < max ) && ( *start > old_start + gap ) );

    return validity;
}

bool skipCollectionPostconditions( JSONStatus_t result,
                                   const char * buf,
                                   size_t * start,
                                   size_t old_start,
                                   size_t max )
{
    bool validity = isSkipCollectionEnum( result ) &&
                    skipPostconditions( ( result == JSONSuccess ), buf, start, old_start, max, 1 );

    return validity;
}

bool skipScalarsPreconditions( const char * buf,
                               size_t * start,
                               size_t max,
                               char mode )
{
    return ( ( mode == '{' ) || ( mode == '[' ) )
           & isValidBufferWithStartIndex( buf, max, start );
}

bool skipAnyScalarPostconditions( bool result,
                                  const char * buf,
                                  size_t * start,
                                  size_t old_start,
                                  size_t max )
{
    bool validity = skipPostconditions( result, buf, start, old_start, max, 0 ) &&
                    IMPLIES( ( result && ( buf[ old_start ] == '"' ) ), *start >= old_start + 2 );

    return validity;
}

bool skipDigitsPreconditions( const char * buf,
                              size_t * start,
                              size_t max,
                              int32_t * outValue )
{
    return ( outValue == NULL || allocated( outValue, sizeof( *outValue ) ) )
           & isValidBufferWithStartIndex( buf, max, start );
}

bool skipDigitsPostconditions( bool result,
                               const char * buf,
                               size_t * start,
                               size_t old_start,
                               size_t max,
                               size_t gap )
{
    bool validity = skipPostconditions( result, buf, start, old_start, max, 0 ) &&
                    IMPLIES( result, ( ( ( buf[ old_start ] ) >= '0' ) && ( ( buf[ old_start ] ) <= '9' ) ) );

    return validity;
}

#endif /* ifndef CORE_JSON_CONTRACTS_C_ */
