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
 * @file HTTPClient_ReadHeader_llhttp_execute.c
 * @brief A stub function for llhttp_execute for coverage of
 * #HTTPClient_ReadHeader.
 */

#include <stdbool.h>
#include <stdint.h>

#include "core_http_client.h"
#include "core_http_client_private.h"
#include "llhttp.h"

/**
 * @brief Attains coverage when a variable needs to possibly contain two values.
 */
bool nondet_bool();

llhttp_errno_t llhttp_execute( llhttp_t * parser,
                               const char * data,
                               size_t len )
{
    char * pValue;
    size_t fieldLength, fieldOffset, valueLength, valueOffset;
    int http_errno;
    findHeaderContext_t * pParsingContext;

    __CPROVER_assert( parser != NULL,
                      "llhttp_execute parser is NULL" );
    __CPROVER_assert( data != NULL,
                      "llhttp_execute data is NULL" );
    __CPROVER_assert( len < CBMC_MAX_OBJECT_SIZE,
                      "llhttp_execute len >= CBMC_MAX_OBJECT_SIZE" );

    parser->error = http_errno;

    __CPROVER_assume( fieldLength <= len );
    __CPROVER_assume( fieldOffset < fieldLength );
    __CPROVER_assume( valueLength <= len );
    __CPROVER_assume( valueOffset < valueLength );

    pParsingContext = ( findHeaderContext_t * ) ( parser->data );
    pParsingContext->pField = data + fieldOffset;
    pParsingContext->fieldLen = fieldLength;
    pParsingContext->pValueLoc = NULL;
    pParsingContext->pValueLen = 0;
    pParsingContext->fieldFound = nondet_bool() ? 0 : 1;

    if( pParsingContext->fieldFound )
    {
        pParsingContext->valueFound = nondet_bool() ? 0 : 1;
    }
    else
    {
        pParsingContext->valueFound = 0;
    }

    if( pParsingContext->valueFound )
    {
        pValue = data + valueOffset;
        pParsingContext->pValueLen = &valueLength;
        pParsingContext->pValueLoc = &pValue;
    }

    return parser->error;
}
