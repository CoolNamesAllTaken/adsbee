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
 * @file HTTPClient_Send_llhttp_execute.c
 * @brief A stub function for llhttp_execute for coverage of
 * #HTTPClient_Send.
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
    size_t fieldLength, valueLength;
    HTTPParsingContext_t * pParsingContext;
    int http_errno;

    __CPROVER_assert( parser != NULL,
                      "llhttp_execute parser is NULL" );
    __CPROVER_assert( data != NULL,
                      "llhttp_execute data is NULL" );
    __CPROVER_assert( len < CBMC_MAX_OBJECT_SIZE,
                      "llhttp_execute len >= CBMC_MAX_OBJECT_SIZE" );

    __CPROVER_assume( fieldLength <= len );
    __CPROVER_assume( valueLength <= len );

    parser->error = http_errno;

    pParsingContext = ( HTTPParsingContext_t * ) ( parser->data );
    /* Choose whether the parser found the header */
    pParsingContext->pLastHeaderField = malloc( fieldLength );
    __CPROVER_assume( pParsingContext->pLastHeaderField != NULL );
    pParsingContext->state = HTTP_PARSING_COMPLETE;

    if( pParsingContext->pLastHeaderField )
    {
        pParsingContext->lastHeaderFieldLen = fieldLength;
        pParsingContext->pLastHeaderValue = malloc( valueLength );
        __CPROVER_assume( pParsingContext->pLastHeaderValue != NULL );
        pParsingContext->lastHeaderValueLen = valueLength;
    }
    else
    {
        pParsingContext->lastHeaderFieldLen = 0U;
        pParsingContext->pLastHeaderValue = NULL;
        pParsingContext->lastHeaderValueLen = 0U;
    }

    /* The body pointer is set by the httpParserOnBodyCallback. But since we are
     * removing that from CBMC proof execution, the body has to be set here. */
    size_t bodyOffset;

    if( pParsingContext->pResponse->bufferLen == 0U )
    {
        bodyOffset = 0U;
    }
    else
    {
        /* Body offset can be anything as long as it doesn't exceed the buffer length
         * and the length of the current data packet. */
        __CPROVER_assume( bodyOffset < pParsingContext->pResponse->bufferLen );
        __CPROVER_assume( bodyOffset < len );
    }

    pParsingContext->pResponse->pBody = pParsingContext->pBufferCur + bodyOffset;

    if( parser->error == HPE_PAUSED )
    {
        /* When the parser is paused ensure that the error_pos member points to
         * a valid location in the response buffer. */
        size_t errorPosOffset;

        __CPROVER_assume( errorPosOffset < pParsingContext->pResponse->bufferLen );
        __CPROVER_assume( errorPosOffset < len );

        parser->error_pos = pParsingContext->pResponse->pBuffer + errorPosOffset;
    }

    return parser->error;
}
