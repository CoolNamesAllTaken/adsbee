/*
 * corePKCS11 v3.6.1
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
 * @file mbedtls_utils.h
 * @brief Helper functions originating from mbedTLS.
 */

#ifndef _MBEDTLS_UTILS_H_
#define _MBEDTLS_UTILS_H_

/* Standard includes. */
#include <string.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/*-----------------------------------------------------------*/

/**
 * @brief Converts PEM documents into DER formatted byte arrays.
 * This is a helper function from MbedTLS util pem2der.c
 * (https://github.com/ARMmbed/mbedtls/blob/development/programs/util/pem2der.c#L75)
 *
 * @param pucInput[in]    Pointer to PEM object
 * @param xLen[in]        Length of PEM object
 * @param pucOutput[out]  Pointer to buffer where DER object will be placed
 * @param pxOlen[in/out]  Pointer to length of DER buffer.  This value is updated
 *                        to contain the actual length of the converted DER object.
 *
 * @return 0 if successful. Negative if conversion failed. If buffer is not
 * large enough to hold converted object, pxOlen is still updated but -1 is
 * returned.
 */
int convert_pem_to_der( const unsigned char * pucInput,
                        size_t xLen,
                        unsigned char * pucOutput,
                        size_t * pxOlen );

/*-----------------------------------------------------------*/



/**
 * @brief This function is a modified version of the static function
 * rsa_rsassa_pkcs1_v15_encode() inside of rsa.c in MbedTLS.  It has been
 * extracted so that corePKCS11 libraries and testing may use it.
 *
 * Formats cryptographically hashed data for RSA signing in accordance
 * with PKCS #1 version 1.5.
 *
 * Currently assumes SHA-256.
 *
 * @param hash[in]     Buffer containing the hashed message or the raw data.
 * @param dst_len[in]  Length of the encoded message.
 * @param dst[out]     Buffer to hold the encoded message.
 */
int PKI_RSA_RSASSA_PKCS1_v15_Encode( const unsigned char * hash,
                                     size_t dst_len,
                                     unsigned char * dst );

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef _MBEDTLS_UTILS_H_ */
