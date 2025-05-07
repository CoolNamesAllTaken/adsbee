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
 * @file SigV4_GenerateHTTPAuthorization_harness.c
 * @brief Implements the proof harness for the SigV4_GenerateHTTPAuthorization function.
 */

/* Include paths for public enums, structures, and macros. */
#include "stdlib.h"
#include "sigv4.h"
#include "sigv4_internal.h"
#include "hash_stubs.h"

void harness()
{
    SigV4Parameters_t * pSigV4Params;
    SigV4HttpParameters_t * pHttpParams;
    SigV4CryptoInterface_t * pCryptoInterface;
    SigV4Credentials_t * pCredentials;
    char * pAuthBuf;
    size_t * authBufLen;
    char * pSignature;
    size_t signatureLen;
    SigV4Status_t status;

    pHttpParams = malloc( sizeof( SigV4HttpParameters_t ) );
    pSigV4Params = malloc( sizeof( SigV4Parameters_t ) );
    pCryptoInterface = malloc( sizeof( SigV4CryptoInterface_t ) );
    pCredentials = malloc( sizeof( SigV4Credentials_t ) );

    /* This property applies to all hash functions. */
    if( pCryptoInterface != NULL )
    {
        __CPROVER_assume( SIGV4_HMAC_SIGNING_KEY_PREFIX_LEN < pCryptoInterface->hashBlockLen && pCryptoInterface->hashBlockLen <= MAX_HASH_BLOCK_LEN );
        __CPROVER_assume( 0U < pCryptoInterface->hashDigestLen && pCryptoInterface->hashDigestLen <= MAX_HASH_DIGEST_LEN );
        __CPROVER_assume( pCryptoInterface->hashDigestLen <= pCryptoInterface->hashBlockLen );
        pCryptoInterface->hashInit = nondet_bool() ? NULL : HashInitStub;
        pCryptoInterface->hashUpdate = nondet_bool() ? NULL : HashUpdateStub;
        pCryptoInterface->hashFinal = nondet_bool() ? NULL : HashFinalStub;
    }

    if( pCredentials != NULL )
    {
        /* Make size assumptions for string-like types. */
        __CPROVER_assume( pCredentials->accessKeyIdLen <= MAX_ACCESS_KEY_ID_LEN );
        __CPROVER_assume( pCredentials->secretAccessKeyLen < CBMC_MAX_OBJECT_SIZE );
        pCredentials->pAccessKeyId = malloc( pCredentials->accessKeyIdLen );
        pCredentials->pSecretAccessKey = malloc( pCredentials->secretAccessKeyLen );
    }

    if( pHttpParams != NULL )
    {
        /* Make size assumptions for string-like types. */
        __CPROVER_assume( pHttpParams->payloadLen < CBMC_MAX_OBJECT_SIZE );
        __CPROVER_assume( pHttpParams->httpMethodLen < CBMC_MAX_OBJECT_SIZE );
        __CPROVER_assume( pHttpParams->pathLen < MAX_URI_LEN );
        __CPROVER_assume( pHttpParams->queryLen < MAX_QUERY_LEN );
        __CPROVER_assume( pHttpParams->headersLen < MAX_HEADERS_LEN );
        pHttpParams->pPayload = malloc( pHttpParams->payloadLen );
        pHttpParams->pHttpMethod = malloc( pHttpParams->httpMethodLen );
        pHttpParams->pPath = malloc( pHttpParams->pathLen );
        pHttpParams->pQuery = malloc( pHttpParams->queryLen );
        pHttpParams->pHeaders = malloc( pHttpParams->headersLen );
    }

    if( pSigV4Params != NULL )
    {
        /* Make size assumptions for string-like types. */
        __CPROVER_assume( pSigV4Params->regionLen < MAX_REGION_LEN );
        __CPROVER_assume( pSigV4Params->serviceLen < MAX_SERVICE_LEN );
        __CPROVER_assume( pSigV4Params->algorithmLen < MAX_ALGORITHM_LEN );
        pSigV4Params->pRegion = malloc( pSigV4Params->regionLen );
        pSigV4Params->pService = malloc( pSigV4Params->serviceLen );
        pSigV4Params->pAlgorithm = malloc( pSigV4Params->algorithmLen );

        /* The ISO date has a fixed length. */
        pSigV4Params->pDateIso8601 = malloc( SIGV4_ISO_STRING_LEN );

        /* Set other structs within SigV4Parameters_t. */
        pSigV4Params->pCredentials = pCredentials;
        pSigV4Params->pCryptoInterface = pCryptoInterface;
        pSigV4Params->pHttpParameters = pHttpParams;
    }

    authBufLen = malloc( sizeof( size_t ) );

    if( authBufLen != NULL )
    {
        __CPROVER_assume( *authBufLen < CBMC_MAX_OBJECT_SIZE );
        pAuthBuf = malloc( *authBufLen );
    }

    status = SigV4_GenerateHTTPAuthorization( pSigV4Params,
                                              pAuthBuf,
                                              authBufLen,
                                              nondet_bool() ? NULL : &pSignature,
                                              nondet_bool() ? NULL : &signatureLen );
    __CPROVER_assert( status == SigV4InvalidParameter || status == SigV4Success || status == SigV4HashError || status == SigV4InsufficientMemory || status == SigV4MaxHeaderPairCountExceeded || status == SigV4MaxQueryPairCountExceeded, "This is not a valid SigV4 return status" );

    if( status == SigV4Success )
    {
        /* The signature must start at a location within pAuthBuf and
         * should not end past the length of pAuthBuf. */
        __CPROVER_assert( pAuthBuf <= pSignature,
                          "Signature does not start at a location within pAuthBuf." );
        __CPROVER_assert( pSignature + signatureLen <= pAuthBuf + *authBufLen,
                          "Signature ends past the length of pAuthBuf." );
    }
}
