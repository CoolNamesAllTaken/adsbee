/*
 * coreJSON v3.3.0
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

#ifndef CORE_JSON_CONTRACTS_H_
#define CORE_JSON_CONTRACTS_H_

#include <stdint.h>

#include "core_json.h"

#define isBool( x )             ( ( x == true ) || ( x == false ) )

/* Parameter check fail values for JSON API functions. */
#define isParameterEnum( x )    ( ( x == JSONNullParameter ) || ( x == JSONBadParameter ) )

/* These 3 enums represent all the ways skipCollection() can fail. */
#define isSkipCollectionFailEnum( x ) \
    ( ( x == JSONPartial ) || ( x == JSONIllegalDocument ) || ( x == JSONMaxDepthExceeded ) )

/* All possible return values for skipCollection(). */
#define isSkipCollectionEnum( x )    ( isSkipCollectionFailEnum( x ) || ( x == JSONSuccess ) )

/* All possible return values for JSON_Validate(). */
#define isJSONValidateEnum( x )      ( isSkipCollectionEnum( x ) || isParameterEnum( x ) )

/* All possible return values for JSON_Search(). */
#define isJSONSearchEnum( x )        ( isJSONValidateEnum( x ) || ( x == JSONNotFound ) )

/* All possible return values for JSON_Iterate(). */
#define isJSONIterateEnum( x )                                \
    ( isParameterEnum( x ) || ( x == JSONIllegalDocument ) || \
      ( x == JSONNotFound ) || ( x == JSONSuccess ) )

/* All possible type values output from JSON_SearchT(). */
#define isJSONTypesEnum( x ) \
    ( ( x == JSONString ) || \
      ( x == JSONNumber ) || \
      ( x == JSONTrue ) ||   \
      ( x == JSONFalse ) ||  \
      ( x == JSONNull ) ||   \
      ( x == JSONObject ) || \
      ( x == JSONArray ) )

#define IMPLIES( a, b )    ( a ? b : true )

/**
 * Renaming all contract clauses from CBMC for readability.
 * For more information about contracts in CBMC, see
 * https://diffblue.github.io/cbmc/contracts-user.html.
 */
#define requires            __CPROVER_requires
#define ensures             __CPROVER_ensures
#define assigns             __CPROVER_assigns

/**
 * Renaming all standard predicates from CBMC for readability.
 * For more information about contracts in CBMC, see
 * https://diffblue.github.io/cbmc/contracts-user.html.
 */
#define allocated           __CPROVER_is_fresh
#define old                 __CPROVER_old
#define result              __CPROVER_return_value
#define pointer_in_range    __CPROVER_pointer_in_range_dfcc

/**
 * These are declarations for all predicates used in coreJSON function contracts.
 */

bool isValidBuffer( const char * buf,
                    size_t max );
bool isValidBufferWithStartIndex( const char * buf,
                                  size_t max,
                                  size_t * start );
bool isValidStart( size_t start,
                   size_t old_start,
                   size_t max );
bool JSON_SearchConstPreconditions( const char * buf,
                                    size_t max,
                                    const char * query,
                                    size_t queryLength,
                                    const char ** outValue,
                                    size_t * outValueLength,
                                    JSONTypes_t * outType );
bool JSON_SearchConstPostconditions( JSONStatus_t result,
                                     const char * buf,
                                     const char ** outValue,
                                     size_t * outValueLength,
                                     size_t max );
bool JSON_IteratePreconditions( const char * buf,
                                size_t max,
                                size_t * start,
                                size_t * next,
                                JSONPair_t * outPair );
bool JSON_IteratePostconditions( JSONStatus_t result,
                                 const char * buf,
                                 size_t max,
                                 JSONPair_t * outPair );
JSONStatus_t JSON_ValidatePreconditions( const char * buf,
                                         size_t max );
bool arraySearchPreconditions( const char * buf,
                               size_t max,
                               size_t * outValue,
                               size_t * outValueLength );
bool arraySearchPostconditions( bool result,
                                const char * buf,
                                size_t max,
                                size_t * outValue,
                                size_t * outValueLength,
                                size_t old_outValue,
                                size_t old_outValueLength );
bool objectSearchPreconditions( const char * buf,
                                size_t max,
                                const char * query,
                                size_t queryLength,
                                size_t * outValue,
                                size_t * outValueLength );
bool multiSearchPreconditions( const char * buf,
                               size_t max,
                               const char * query,
                               size_t queryLength,
                               size_t * outValue,
                               size_t * outValueLength );
bool multiSearchPostconditions( JSONStatus_t result,
                                const char * buf,
                                size_t max,
                                size_t * outValue,
                                size_t * outValueLength,
                                size_t old_outValue,
                                size_t old_outValueLength );
bool skipPostconditions( bool result,
                         const char * buf,
                         size_t * start,
                         size_t old_start,
                         size_t max,
                         size_t gap );
bool skipCollectionPostconditions( JSONStatus_t result,
                                   const char * buf,
                                   size_t * start,
                                   size_t old_start,
                                   size_t max );
bool skipScalarsPreconditions( const char * buf,
                               size_t * start,
                               size_t max,
                               char mode );
bool skipAnyScalarPostconditions( bool result,
                                  const char * buf,
                                  size_t * start,
                                  size_t old_start,
                                  size_t max );
bool skipDigitsPreconditions( const char * buf,
                              size_t * start,
                              size_t max,
                              int32_t * outValue );
bool skipDigitsPostconditions( bool result,
                               const char * buf,
                               size_t * start,
                               size_t old_start,
                               size_t max,
                               size_t gap );

/**
 * These are declarations for the user-facing functions in core_json.h
 * with their respective function contracts.
 *
 * Please see core_json.h for documentation.
 */

JSONStatus_t JSON_SearchConst( const char * buf,
                               size_t max,
                               const char * query,
                               size_t queryLength,
                               const char ** outValue,
                               size_t * outValueLength,
                               JSONTypes_t * outType )
requires( JSON_SearchConstPreconditions( buf, max, query, queryLength, outValue, outValueLength, outType ) )
assigns( *outValue, *outValueLength, *outType )
ensures( JSON_SearchConstPostconditions( result, buf, outValue, outValueLength, max ) )
;

JSONStatus_t JSON_Iterate( const char * buf,
                           size_t max,
                           size_t * start,
                           size_t * next,
                           JSONPair_t * outPair )
requires( JSON_IteratePreconditions( buf, max, start, next, outPair ) )
assigns( *start, *next, *outPair )
ensures( JSON_IteratePostconditions( result, buf, max, outPair ) )
;

JSONStatus_t JSON_Validate( const char * buf,
                            size_t max )
requires( JSON_ValidatePreconditions( buf, max ) )
ensures( isJSONValidateEnum( result ) )
;

/**
 * These are declarations for the (normally) static functions from core_json.c
 * with their respective function contracts.
 *
 * Please see core_json.c for documentation.
 */

bool arraySearch( const char * buf,
                  size_t max,
                  uint32_t queryIndex,
                  size_t * outValue,
                  size_t * outValueLength )
requires( arraySearchPreconditions( buf, max, outValue, outValueLength ) )
assigns( *outValue, *outValueLength )
ensures( arraySearchPostconditions( result, buf, max, outValue, outValueLength, old( *outValue ), old( *outValueLength ) ) )
;

bool objectSearch( const char * buf,
                   size_t max,
                   const char * query,
                   size_t queryLength,
                   size_t * outValue,
                   size_t * outValueLength )
requires( objectSearchPreconditions( buf, max, query, queryLength, outValue, outValueLength ) )
assigns( *outValue, *outValueLength )
ensures( arraySearchPostconditions( result, buf, max, outValue, outValueLength, old( *outValue ), old( *outValueLength ) ) )
;

JSONStatus_t multiSearch( const char * buf,
                          size_t max,
                          const char * query,
                          size_t queryLength,
                          size_t * outValue,
                          size_t * outValueLength )
requires( multiSearchPreconditions( buf, max, query, queryLength, outValue, outValueLength ) )
assigns( *outValue, *outValueLength )
ensures( multiSearchPostconditions( result, buf, max, outValue, outValueLength, old( *outValue ), old( *outValueLength ) ) )
;

JSONStatus_t skipCollection( const char * buf,
                             size_t * start,
                             size_t max )
requires( isValidBufferWithStartIndex( buf, max, start ) )
assigns( *start )
ensures( skipCollectionPostconditions( result, buf, start, old( *start ), max ) )
;

void skipScalars( const char * buf,
                  size_t * start,
                  size_t max,
                  char mode )
requires( skipScalarsPreconditions( buf, start, max, mode ) )
assigns( *start )
ensures( isValidStart( *start, old( *start ), max ) )
;

void skipObjectScalars( const char * buf,
                        size_t * start,
                        size_t max )
requires( isValidBufferWithStartIndex( buf, max, start ) )
assigns( *start )
ensures( isValidStart( *start, old( *start ), max ) )
;

bool skipAnyScalar( const char * buf,
                    size_t * start,
                    size_t max )
requires( isValidBufferWithStartIndex( buf, max, start ) )
assigns( *start )
ensures( skipAnyScalarPostconditions( result, buf, start, old( *start ), max ) )
;

void skipSpace( const char * buf,
                size_t * start,
                size_t max )
requires( isValidBufferWithStartIndex( buf, max, start ) )
assigns( *start )
ensures( isValidStart( *start, old( *start ), max ) )
;

bool skipString( const char * buf,
                 size_t * start,
                 size_t max )
requires( isValidBufferWithStartIndex( buf, max, start ) )
assigns( *start )
ensures( skipPostconditions( result, buf, start, old( *start ), max, 1 ) )
;

bool skipEscape( const char * buf,
                 size_t * start,
                 size_t max )
requires( isValidBufferWithStartIndex( buf, max, start ) )
assigns( *start )
ensures( skipPostconditions( result, buf, start, old( *start ), max, 1 ) )
;

bool skipUTF8( const char * buf,
               size_t * start,
               size_t max )
requires( isValidBufferWithStartIndex( buf, max, start ) )
assigns( *start )
ensures( skipPostconditions( result, buf, start, old( *start ), max, 0 ) )
;

bool skipDigits( const char * buf,
                 size_t * start,
                 size_t max,
                 int32_t * outValue )
requires( skipDigitsPreconditions( buf, start, max, outValue ) )
assigns( *start;
         outValue != NULL: *outValue )
ensures( skipDigitsPostconditions( result, buf, start, old( *start ), max, 0 ) )
;

#endif /* ifndef CORE_JSON_CONTRACTS_H_ */
