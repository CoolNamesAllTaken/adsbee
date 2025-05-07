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

/**
 * @file core_json.h
 * @brief Include this header file to use coreJSON in your application.
 */

#ifndef CORE_JSON_H_
#define CORE_JSON_H_

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 *  @brief By default, has the stand behavior of assert() for
 *  parameter checking. To swap out the assert(), define this
 *  macro with the desired behavior.  */
#ifndef coreJSON_ASSERT
    #define coreJSON_ASSERT( expr )    assert( expr )
#endif


/**
 * @ingroup json_enum_types
 * @brief Return codes from coreJSON library functions.
 */
typedef enum
{
    JSONPartial = 0,      /**< @brief JSON document is valid so far but incomplete. */
    JSONSuccess,          /**< @brief JSON document is valid and complete. */
    JSONIllegalDocument,  /**< @brief JSON document is invalid or malformed. */
    JSONMaxDepthExceeded, /**< @brief JSON document has nesting that exceeds JSON_MAX_DEPTH. */
    JSONNotFound,         /**< @brief Query key could not be found in the JSON document. */
    JSONNullParameter,    /**< @brief Pointer parameter passed to a function is NULL. */
    JSONBadParameter      /**< @brief Query key is empty, or any subpart is empty, or max is 0. */
} JSONStatus_t;

/**
 * @brief Parse a buffer to determine if it contains a valid JSON document.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in] max  The size of the buffer.
 *
 * @note The maximum nesting depth may be specified by defining the macro
 * JSON_MAX_DEPTH.  The default is 32 of sizeof(char).
 *
 * @note By default, a valid JSON document may contain a single element
 * (e.g., string, boolean, number).  To require that a valid document
 * contain an object or array, define JSON_VALIDATE_COLLECTIONS_ONLY.
 *
 * @return #JSONSuccess if the buffer contents are valid JSON;
 * #JSONNullParameter if buf is NULL;
 * #JSONBadParameter if max is 0;
 * #JSONIllegalDocument if the buffer contents are NOT valid JSON;
 * #JSONMaxDepthExceeded if object and array nesting exceeds a threshold;
 * #JSONPartial if the buffer contents are potentially valid but incomplete.
 *
 * <b>Example</b>
 * @code{c}
 *     // Variables used in this example.
 *     JSONStatus_t result;
 *     char buffer[] = "{\"foo\":\"abc\",\"bar\":{\"foo\":\"xyz\"}}";
 *     size_t bufferLength = sizeof( buffer ) - 1;
 *
 *     result = JSON_Validate( buffer, bufferLength );
 *
 *     // JSON document is valid.
 *     assert( result == JSONSuccess );
 * @endcode
 */
/* @[declare_json_validate] */
JSONStatus_t JSON_Validate( const char * buf,
                            size_t max );
/* @[declare_json_validate] */

/**
 * @brief Find a key or array index in a JSON document and output the
 * pointer @p outValue to its value.
 *
 * Any value may also be an object or an array to a maximum depth.  A search
 * may descend through nested objects or arrays when the query contains matching
 * key strings or array indexes joined by a separator.
 *
 * For example, if the provided buffer contains <code>{"foo":"abc","bar":{"foo":"xyz"}}</code>,
 * then a search for 'foo' would output <code>abc</code>, 'bar' would output
 * <code>{"foo":"xyz"}</code>, and a search for 'bar.foo' would output
 * <code>xyz</code>.
 *
 * If the provided buffer contains <code>[123,456,{"foo":"abc","bar":[88,99]}]</code>,
 * then a search for '[1]' would output <code>456</code>, '[2].foo' would output
 * <code>abc</code>, and '[2].bar[0]' would output <code>88</code>.
 *
 * On success, the pointer @p outValue points to a location in buf.  No null
 * termination is done for the value.  For valid JSON it is safe to place
 * a null character at the end of the value, so long as the character
 * replaced is put back before running another search.
 *
 * @param[in] buf  The buffer to search.
 * @param[in] max  size of the buffer.
 * @param[in] query  The object keys and array indexes to search for.
 * @param[in] queryLength  Length of the key.
 * @param[out] outValue  A pointer to receive the address of the value found.
 * @param[out] outValueLength  A pointer to receive the length of the value found.
 *
 * @note The maximum nesting depth may be specified by defining the macro
 * JSON_MAX_DEPTH.  The default is 32 of sizeof(char).
 *
 * @note JSON_Search() performs validation, but stops upon finding a matching
 * key and its value. To validate the entire JSON document, use JSON_Validate().
 *
 * @return #JSONSuccess if the query is matched and the value output;
 * #JSONNullParameter if any pointer parameters are NULL;
 * #JSONBadParameter if the query is empty, or the portion after a separator is empty,
 * or max is 0, or an index is too large to convert to a signed 32-bit integer;
 * #JSONNotFound if the query has no match.
 *
 * <b>Example</b>
 * @code{c}
 *     // Variables used in this example.
 *     JSONStatus_t result;
 *     char buffer[] = "{\"foo\":\"abc\",\"bar\":{\"foo\":\"xyz\"}}";
 *     size_t bufferLength = sizeof( buffer ) - 1;
 *     char query[] = "bar.foo";
 *     size_t queryLength = sizeof( query ) - 1;
 *     char * value;
 *     size_t valueLength;
 *
 *     // Calling JSON_Validate() is not necessary if the document is guaranteed to be valid.
 *     result = JSON_Validate( buffer, bufferLength );
 *
 *     if( result == JSONSuccess )
 *     {
 *         result = JSON_Search( buffer, bufferLength, query, queryLength,
 *                               &value, &valueLength );
 *     }
 *
 *     if( result == JSONSuccess )
 *     {
 *         // The pointer "value" will point to a location in the "buffer".
 *         char save = value[ valueLength ];
 *         // After saving the character, set it to a null byte for printing.
 *         value[ valueLength ] = '\0';
 *         // "Found: bar.foo -> xyz" will be printed.
 *         printf( "Found: %s -> %s\n", query, value );
 *         // Restore the original character.
 *         value[ valueLength ] = save;
 *     }
 * @endcode
 *
 * @note The maximum index value is ~2 billion ( 2^31 - 9 ).
 */
/* @[declare_json_search] */
#define JSON_Search( buf, max, query, queryLength, outValue, outValueLength ) \
    JSON_SearchT( buf, max, query, queryLength, outValue, outValueLength, NULL )
/* @[declare_json_search] */

/**
 * @brief The largest value usable as an array index in a query
 * for JSON_Search(), ~2 billion.
 */
#define MAX_INDEX_VALUE    ( 0x7FFFFFF7 )   /* 2^31 - 9 */

/**
 * @ingroup json_enum_types
 * @brief Value types from the JSON standard.
 */
typedef enum
{
    JSONInvalid = 0, /**< @brief Not a valid JSON type. */
    JSONString,      /**< @brief A quote delimited sequence of Unicode characters. */
    JSONNumber,      /**< @brief A rational number. */
    JSONTrue,        /**< @brief The literal value true. */
    JSONFalse,       /**< @brief The literal value false. */
    JSONNull,        /**< @brief The literal value null. */
    JSONObject,      /**< @brief A collection of zero or more key-value pairs. */
    JSONArray        /**< @brief A collection of zero or more values. */
} JSONTypes_t;

/**
 * @brief Same as JSON_Search(), but also outputs a type for the value found
 *
 * See @ref JSON_Search for documentation of common behavior.
 *
 * @param[in] buf  The buffer to search.
 * @param[in] max  size of the buffer.
 * @param[in] query  The object keys and array indexes to search for.
 * @param[in] queryLength  Length of the key.
 * @param[out] outValue  A pointer to receive the address of the value found.
 * @param[out] outValueLength  A pointer to receive the length of the value found.
 * @param[out] outType  An enum indicating the JSON-specific type of the value.
 */
/* @[declare_json_searcht] */
JSONStatus_t JSON_SearchT( char * buf,
                           size_t max,
                           const char * query,
                           size_t queryLength,
                           char ** outValue,
                           size_t * outValueLength,
                           JSONTypes_t * outType );
/* @[declare_json_searcht] */

/**
 * @brief Same as JSON_SearchT(), but with const qualified buf and outValue arguments.
 *
 * See @ref JSON_Search for documentation of common behavior.
 *
 * @param[in] buf  The buffer to search.
 * @param[in] max  size of the buffer.
 * @param[in] query  The object keys and array indexes to search for.
 * @param[in] queryLength  Length of the key.
 * @param[out] outValue  A pointer to receive the address of the value found.
 * @param[out] outValueLength  A pointer to receive the length of the value found.
 * @param[out] outType  An enum indicating the JSON-specific type of the value.
 */
/* @[declare_json_searchconst] */
JSONStatus_t JSON_SearchConst( const char * buf,
                               size_t max,
                               const char * query,
                               size_t queryLength,
                               const char ** outValue,
                               size_t * outValueLength,
                               JSONTypes_t * outType );
/* @[declare_json_searchconst] */

/**
 * @ingroup json_struct_types
 * @brief Structure to represent a key-value pair.
 */
typedef struct
{
    const char * key;     /**< @brief Pointer to the code point sequence for key. */
    size_t keyLength;     /**< @brief Length of the code point sequence for key. */
    const char * value;   /**< @brief Pointer to the code point sequence for value. */
    size_t valueLength;   /**< @brief Length of the code point sequence for value. */
    JSONTypes_t jsonType; /**< @brief JSON-specific type of the value. */
} JSONPair_t;

/**
 * @brief Output the next key-value pair or value from a collection.
 *
 * This function may be used in a loop to output each key-value pair from an object,
 * or each value from an array.  For the first invocation, the integers pointed to by
 * start and next should be initialized to 0.  These will be updated by the function.
 * If another key-value pair or value is present, the output structure is populated
 * and #JSONSuccess is returned; otherwise the structure is unchanged and #JSONNotFound
 * is returned.
 *
 * @param[in] buf  The buffer to search.
 * @param[in] max  size of the buffer.
 * @param[in,out] start  The index at which the collection begins.
 * @param[in,out] next  The index at which to seek the next value.
 * @param[out] outPair  A pointer to receive the next key-value pair.
 *
 * @note This function expects a valid JSON document; run JSON_Validate() first.
 *
 * @note For an object, the outPair structure will reference a key and its value.
 * For an array, only the value will be referenced (i.e., outPair.key will be NULL).
 *
 * @return #JSONSuccess if a value is output;
 * #JSONIllegalDocument if the buffer does not contain a collection;
 * #JSONNotFound if there are no further values in the collection.
 *
 * <b>Example</b>
 * @code{c}
 *     // Variables used in this example.
 *     static char * json_types[] =
 *     {
 *         "invalid",
 *         "string",
 *         "number",
 *         "true",
 *         "false",
 *         "null",
 *         "object",
 *         "array"
 *     };
 *
 *     void show( const char * json,
 *                size_t length )
 *     {
 *         size_t start = 0, next = 0;
 *         JSONPair_t pair = { 0 };
 *         JSONStatus_t result;
 *
 *         result = JSON_Validate( json, length );
 *         if( result == JSONSuccess )
 *         {
 *             result = JSON_Iterate( json, length, &start, &next, &pair );
 *         }
 *
 *         while( result == JSONSuccess )
 *         {
 *             if( pair.key != NULL )
 *             {
 *                 printf( "key: %.*s\t", ( int ) pair.keyLength, pair.key );
 *             }
 *
 *             printf( "value: (%s) %.*s\n", json_types[ pair.jsonType ],
 *                     ( int ) pair.valueLength, pair.value );
 *
 *             result = JSON_Iterate( json, length, &start, &next, &pair );
 *         }
 *     }
 * @endcode
 */
/* @[declare_json_iterate] */
JSONStatus_t JSON_Iterate( const char * buf,
                           size_t max,
                           size_t * start,
                           size_t * next,
                           JSONPair_t * outPair );
/* @[declare_json_iterate] */

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_JSON_H_ */
