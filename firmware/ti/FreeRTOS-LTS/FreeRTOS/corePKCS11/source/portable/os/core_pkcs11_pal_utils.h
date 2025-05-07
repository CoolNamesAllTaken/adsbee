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
 * @file core_pkcs11_pal_utils.h
 * @brief Utility functions that are common for the software based PKCS #11
 * implementation provided by corePKCS11 for both PAL layers of POSIX and
 * Windows Simulator based FreeRTOS environments.
 * These utils contain information of the on-flash storage files used for
 * storing all PKCS #11 labels supported by the corePKCS11 library.
 */
/*-----------------------------------------------------------*/

/* PKCS 11 includes. */
#include "core_pkcs11_config.h"
#include "core_pkcs11_config_defaults.h"
#include "core_pkcs11.h"

/**
 * @ingroup pkcs11_enums
 * @brief Enums for managing PKCS #11 object types.
 *
 */
enum eObjectHandles
{
    eInvalidHandle = 0,       /**< According to PKCS #11 spec, 0 is never a valid object handle. */
    eAwsDevicePrivateKey = 1, /**< Private Key. */
    eAwsDevicePublicKey,      /**< Public Key. */
    eAwsDeviceCertificate,    /**< Certificate. */
    eAwsCodeSigningKey,       /**< Code Signing Key. */
    eAwsHMACSecretKey,        /**< HMAC Secret Key. */
    eAwsCMACSecretKey,        /**< CMAC Secret Key. */
    eAwsClaimPrivateKey,      /**< Provisioning Claim Private Key. */
    eAwsClaimCertificate      /**< Provisioning Claim Certificate. */
};


/**
 * @brief Checks to see if a file exists
 *
 * @param[in] pcLabel            The PKCS #11 label to convert to a file name
 * @param[out] pcFileName        The name of the file to check for existence.
 * @param[out] pHandle           The type of the PKCS #11 object.
 *
 */
void PAL_UTILS_LabelToFilenameHandle( const char * pcLabel,
                                      const char ** pcFileName,
                                      CK_OBJECT_HANDLE_PTR pHandle );

/**
 * @brief Maps object handle to file name.
 *
 * @param[in] pcLabel The PKCS #11 label to convert to a file name
 * @param[out] pcFileName This will be populated with the file name that the
 * @p pcLabel maps to.
 * @param[out] pIsPrivateKey This will be set to true if the object handle
 * represents a secret credential like asymmetric private key or a symmetric
 * key.
 */
CK_RV PAL_UTILS_HandleToFilename( CK_OBJECT_HANDLE xHandle,
                                  const char ** pcFileName,
                                  CK_BBOOL * pIsPrivateKey );
