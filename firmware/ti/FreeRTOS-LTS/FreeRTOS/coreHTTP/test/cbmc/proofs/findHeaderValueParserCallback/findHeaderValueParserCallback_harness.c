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
 * @file findHeaderValueParserCallback_harness.c
 * @brief Implements the proof harness for findHeaderValueParserCallback function.
 */

#include "http_cbmc_state.h"
#include "llhttp.h"
#include "core_http_client.h"

int __CPROVER_file_local_core_http_client_c_findHeaderValueParserCallback( llhttp_t * pHttpParser,
                                                                           const char * pValueLoc,
                                                                           size_t valueLen );

void findHeaderValueParserCallback_harness()
{
    llhttp_t * pHttpParser;
    HTTPResponse_t * pResponse;
    findHeaderContext_t * pFindHeaderContext;
    size_t fieldLen, fieldOffset, valueLen, valueOffset;
    char * pValueLoc;

    pHttpParser = allocateHttpReadHeaderParser( NULL );
    pResponse = allocateHttpResponse( NULL );
    pFindHeaderContext = allocateFindHeaderContext( NULL );
    __CPROVER_assume( isValidHttpResponse( pResponse ) &&
                      pResponse != NULL &&
                      pResponse->pBuffer != NULL &&
                      pResponse->bufferLen > 0 );

    __CPROVER_assume( valueOffset <= pResponse->bufferLen );
    __CPROVER_assume( valueLen <= pResponse->bufferLen - valueOffset );
    pValueLoc = pResponse->pBuffer + valueOffset;

    __CPROVER_assume( fieldOffset <= pResponse->bufferLen );
    __CPROVER_assume( fieldLen > 0 );
    __CPROVER_assume( fieldLen <= pResponse->bufferLen - fieldOffset );
    pFindHeaderContext->pField = pResponse->pBuffer + fieldOffset;
    pFindHeaderContext->fieldLen = fieldLen;
    pFindHeaderContext->pValueLen = &valueLen;
    pFindHeaderContext->pValueLoc = &pValueLoc;
    pFindHeaderContext->fieldFound = nondet_bool() ? 0 : 1;
    pFindHeaderContext->valueFound = 0;
    pHttpParser->data = ( void * ) pFindHeaderContext;

    __CPROVER_file_local_core_http_client_c_findHeaderValueParserCallback( pHttpParser, pValueLoc, valueLen );
}
