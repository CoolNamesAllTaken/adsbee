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
 * @file core_pkcs11_pal_utils.c
 * @brief Utility functions that are common for the software based PKCS #11
 * implementation provided by corePKCS11 for both PAL layers of POSIX and
 * Windows Simulator based FreeRTOS environments.
 * These utils contain information of the on-flash storage files used for
 * storing all PKCS #11 labels supported by the corePKCS11 library.
 */
/*-----------------------------------------------------------*/

/* C standard includes. */
#include <string.h>
#include <stdint.h>

/* corePKCS11 header include. */
#include "core_pkcs11_pal_utils.h"

/**
 * @ingroup pkcs11_macros
 * @brief Macros for managing PKCS #11 objects in flash.
 *
 */
#define pkcs11palFILE_NAME_CLIENT_CERTIFICATE    "corePKCS11_Certificate.dat"       /**< The file name of the Certificate object. */
#define pkcs11palFILE_NAME_KEY                   "corePKCS11_Key.dat"               /**< The file name of the Key object. */
#define pkcs11palFILE_NAME_PUBLIC_KEY            "corePKCS11_PubKey.dat"            /**< The file name of the Public Key object. */
#define pkcs11palFILE_CODE_SIGN_PUBLIC_KEY       "corePKCS11_CodeSignKey.dat"       /**< The file name of the Code Sign Key object. */
#define pkcs11palFILE_HMAC_SECRET_KEY            "corePKCS11_HMACKey.dat"           /**< The file name of the HMAC Secret Key object. */
#define pkcs11palFILE_CMAC_SECRET_KEY            "corePKCS11_CMACKey.dat"           /**< The file name of the CMAC Secret Key object. */
#define pkcs11palFILE_NAME_CLAIM_CERTIFICATE     "corePKCS11_Claim_Certificate.dat" /**< The file name of the Provisioning Claim Certificate object. */
#define pkcs11palFILE_NAME_CLAIM_KEY             "corePKCS11_Claim_Key.dat"         /**< The file name of the Provisioning Claim Key object. */


void PAL_UTILS_LabelToFilenameHandle( const char * pcLabel,
                                      const char ** pcFileName,
                                      CK_OBJECT_HANDLE_PTR pHandle )
{
    if( ( pcLabel != NULL ) && ( pHandle != NULL ) && ( pcFileName != NULL ) )
    {
        if( 0 == strncmp( pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS,
                          pcLabel,
                          sizeof( pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS ) ) )
        {
            *pcFileName = pkcs11palFILE_NAME_CLIENT_CERTIFICATE;
            *pHandle = ( CK_OBJECT_HANDLE ) eAwsDeviceCertificate;
        }
        else if( 0 == strncmp( pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS,
                               pcLabel,
                               sizeof( pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS ) ) )
        {
            *pcFileName = pkcs11palFILE_NAME_KEY;
            *pHandle = ( CK_OBJECT_HANDLE ) eAwsDevicePrivateKey;
        }
        else if( 0 == strncmp( pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS,
                               pcLabel,
                               sizeof( pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS ) ) )
        {
            *pcFileName = pkcs11palFILE_NAME_PUBLIC_KEY;
            *pHandle = ( CK_OBJECT_HANDLE ) eAwsDevicePublicKey;
        }
        else if( 0 == strncmp( pkcs11configLABEL_CODE_VERIFICATION_KEY,
                               pcLabel,
                               sizeof( pkcs11configLABEL_CODE_VERIFICATION_KEY ) ) )
        {
            *pcFileName = pkcs11palFILE_CODE_SIGN_PUBLIC_KEY;
            *pHandle = ( CK_OBJECT_HANDLE ) eAwsCodeSigningKey;
        }
        else if( 0 == strncmp( pkcs11configLABEL_HMAC_KEY,
                               pcLabel,
                               sizeof( pkcs11configLABEL_HMAC_KEY ) ) )
        {
            *pcFileName = pkcs11palFILE_HMAC_SECRET_KEY;
            *pHandle = ( CK_OBJECT_HANDLE ) eAwsHMACSecretKey;
        }
        else if( 0 == strncmp( pkcs11configLABEL_CMAC_KEY,
                               pcLabel,
                               sizeof( pkcs11configLABEL_CMAC_KEY ) ) )
        {
            *pcFileName = pkcs11palFILE_CMAC_SECRET_KEY;
            *pHandle = ( CK_OBJECT_HANDLE ) eAwsCMACSecretKey;
        }
        else if( 0 == strncmp( pkcs11configLABEL_CLAIM_CERTIFICATE,
                               pcLabel,
                               sizeof( pkcs11configLABEL_CLAIM_CERTIFICATE ) ) )
        {
            *pcFileName = pkcs11palFILE_NAME_CLAIM_CERTIFICATE;
            *pHandle = ( CK_OBJECT_HANDLE ) eAwsClaimCertificate;
        }
        else if( 0 == strncmp( pkcs11configLABEL_CLAIM_PRIVATE_KEY,
                               pcLabel,
                               sizeof( pkcs11configLABEL_CLAIM_PRIVATE_KEY ) ) )
        {
            *pcFileName = pkcs11palFILE_NAME_CLAIM_KEY;
            *pHandle = ( CK_OBJECT_HANDLE ) eAwsClaimPrivateKey;
        }
        else
        {
            *pcFileName = NULL;
            *pHandle = ( CK_OBJECT_HANDLE ) eInvalidHandle;
        }

        LogDebug( ( "Converted %s to %s", pcLabel, *pcFileName ) );
    }
    else
    {
        LogError( ( "Could not convert label to filename. Received a NULL parameter." ) );
    }
}

CK_RV PAL_UTILS_HandleToFilename( CK_OBJECT_HANDLE xHandle,
                                  const char ** pcFileName,
                                  CK_BBOOL * pIsPrivate )
{
    CK_RV xReturn = CKR_OK;

    if( pcFileName != NULL )
    {
        switch( ( CK_OBJECT_HANDLE ) xHandle )
        {
            case eAwsDeviceCertificate:
                *pcFileName = pkcs11palFILE_NAME_CLIENT_CERTIFICATE;
                /* MISRA Ref 10.5.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/corePKCS11/blob/main/MISRA.md#rule-105 */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                *pIsPrivate = ( CK_BBOOL ) CK_FALSE;
                break;

            case eAwsDevicePrivateKey:
                *pcFileName = pkcs11palFILE_NAME_KEY;
                /* MISRA Ref 10.5.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/corePKCS11/blob/main/MISRA.md#rule-105 */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                *pIsPrivate = ( CK_BBOOL ) CK_TRUE;
                break;

            case eAwsDevicePublicKey:
                *pcFileName = pkcs11palFILE_NAME_PUBLIC_KEY;
                /* MISRA Ref 10.5.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/corePKCS11/blob/main/MISRA.md#rule-105 */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                *pIsPrivate = ( CK_BBOOL ) CK_FALSE;
                break;

            case eAwsCodeSigningKey:
                *pcFileName = pkcs11palFILE_CODE_SIGN_PUBLIC_KEY;
                /* MISRA Ref 10.5.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/corePKCS11/blob/main/MISRA.md#rule-105 */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                *pIsPrivate = ( CK_BBOOL ) CK_FALSE;
                break;

            case eAwsHMACSecretKey:
                *pcFileName = pkcs11palFILE_HMAC_SECRET_KEY;
                /* MISRA Ref 10.5.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/corePKCS11/blob/main/MISRA.md#rule-105 */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                *pIsPrivate = ( CK_BBOOL ) CK_TRUE;
                break;

            case eAwsCMACSecretKey:
                *pcFileName = pkcs11palFILE_CMAC_SECRET_KEY;
                /* MISRA Ref 10.5.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/corePKCS11/blob/main/MISRA.md#rule-105 */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                *pIsPrivate = ( CK_BBOOL ) CK_TRUE;
                break;

            case eAwsClaimCertificate:
                *pcFileName = pkcs11palFILE_NAME_CLAIM_CERTIFICATE;
                /* MISRA Ref 10.5.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/corePKCS11/blob/main/MISRA.md#rule-105 */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                *pIsPrivate = ( CK_BBOOL ) CK_FALSE;
                break;

            case eAwsClaimPrivateKey:
                *pcFileName = pkcs11palFILE_NAME_CLAIM_KEY;
                /* MISRA Ref 10.5.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/corePKCS11/blob/main/MISRA.md#rule-105 */
                /* coverity[misra_c_2012_rule_10_5_violation] */
                *pIsPrivate = ( CK_BBOOL ) CK_TRUE;
                break;

            default:
                xReturn = CKR_KEY_HANDLE_INVALID;
                break;
        }
    }
    else
    {
        LogError( ( "Could not convert label to filename. Received a NULL parameter." ) );
    }

    return xReturn;
}
