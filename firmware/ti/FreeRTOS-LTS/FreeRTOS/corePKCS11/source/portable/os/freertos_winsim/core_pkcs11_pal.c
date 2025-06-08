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
 * @file core_pkcs11_pal.c
 * @brief Windows Simulator file save and read implementation
 * for PKCS#11 based on mbedTLS with for software keys. This
 * file deviates from the FreeRTOS style standard for some function names and
 * data types in order to maintain compliance with the PKCS#11 standard.
 */

/*-----------------------------------------------------------*/

/* System Includes */
#include <stdio.h>
#include <string.h>

#ifdef WIN32
    #ifdef WIN32_LEAN_AND_MEAN
        #include <winsock2.h>
    #else
        #include <winsock.h>
    #endif /* WIN32_LEAN_AND_MEAN */
#endif /* WIN32 */

/* FreeRTOS Includes */
#include "FreeRTOS.h"

/* corePKCS11 Includes */
#include "core_pkcs11.h"
#include "core_pkcs11_config.h"
#include "core_pkcs11_config_defaults.h"
#include "core_pkcs11_pal_utils.h"

/*-----------------------------------------------------------*/

/**
 * @brief Checks to see if a file exists
 *
 * @param[in] pcFileName         The name of the file to check for existence.
 *
 * @returns pdTRUE if the file exists, pdFALSE if not.
 */
BaseType_t prvFileExists( const char * pcFileName )
{
    DWORD xReturn;

    xReturn = GetFileAttributesA( pcFileName );

    if( INVALID_FILE_ATTRIBUTES == xReturn )
    {
        return pdFALSE;
    }
    else
    {
        return pdTRUE;
    }
}

/*-----------------------------------------------------------*/

CK_RV PKCS11_PAL_Initialize( void )
{
    return CKR_OK;
}

CK_OBJECT_HANDLE PKCS11_PAL_SaveObject( CK_ATTRIBUTE_PTR pxLabel,
                                        CK_BYTE_PTR pucData,
                                        CK_ULONG ulDataSize )
{
    uint32_t ulStatus = 0;
    HANDLE hFile = INVALID_HANDLE_VALUE;
    DWORD lpNumberOfBytesWritten;
    char * pcFileName = NULL;
    CK_OBJECT_HANDLE xHandle = eInvalidHandle;

    /* Converts a label to its respective filename and handle. */
    PAL_UTILS_LabelToFilenameHandle( pxLabel->pValue,
                                     &pcFileName,
                                     &xHandle );

    /* If your project requires additional PKCS#11 objects, add them here. */

    if( pcFileName != NULL )
    {
        /* Create the file. */
        hFile = CreateFileA( pcFileName,
                             GENERIC_WRITE,
                             0,
                             NULL,
                             CREATE_ALWAYS,
                             FILE_ATTRIBUTE_NORMAL,
                             NULL );

        if( INVALID_HANDLE_VALUE == hFile )
        {
            ulStatus = GetLastError();
            LogError( ( "Unable to create file %d \r\n", ulStatus ) );
            xHandle = eInvalidHandle;
        }

        /* Write the object data. */
        if( ERROR_SUCCESS == ulStatus )
        {
            if( FALSE == WriteFile( hFile, pucData, ulDataSize, &lpNumberOfBytesWritten, NULL ) )
            {
                ulStatus = GetLastError();
                xHandle = eInvalidHandle;
            }
        }

        /* Clean up. */
        if( INVALID_HANDLE_VALUE != hFile )
        {
            CloseHandle( hFile );
        }
    }

    return xHandle;
}

/*-----------------------------------------------------------*/


CK_OBJECT_HANDLE PKCS11_PAL_FindObject( CK_BYTE_PTR pxLabel,
                                        CK_ULONG usLength )
{
    /* Avoid compiler warnings about unused variables. */
    ( void ) usLength;

    CK_OBJECT_HANDLE xHandle = eInvalidHandle;
    char * pcFileName = NULL;

    /* Converts a label to its respective filename and handle. */
    PAL_UTILS_LabelToFilenameHandle( pxLabel,
                                     &pcFileName,
                                     &xHandle );

    /* Check if object exists/has been created before returning. */
    if( pdTRUE != prvFileExists( pcFileName ) )
    {
        xHandle = eInvalidHandle;
    }

    return xHandle;
}
/*-----------------------------------------------------------*/

CK_RV PKCS11_PAL_GetObjectValue( CK_OBJECT_HANDLE xHandle,
                                 CK_BYTE_PTR * ppucData,
                                 CK_ULONG_PTR pulDataSize,
                                 CK_BBOOL * pIsPrivate )
{
    CK_RV ulReturn = CKR_KEY_HANDLE_INVALID;
    uint32_t ulDriverReturn = 0;
    HANDLE hFile = INVALID_HANDLE_VALUE;
    uint32_t ulSize = 0;
    char * pcFileName = NULL;


    ulReturn = PAL_UTILS_HandleToFilename( xHandle,
                                           &pcFileName,
                                           pIsPrivate );

    if( ( pcFileName != NULL ) && ( pdTRUE == prvFileExists( pcFileName ) ) )
    {
        /* Open the file. */
        hFile = CreateFileA( pcFileName,
                             GENERIC_READ,
                             FILE_SHARE_READ,
                             NULL,
                             OPEN_EXISTING,
                             FILE_ATTRIBUTE_NORMAL,
                             NULL );

        if( INVALID_HANDLE_VALUE == hFile )
        {
            ulDriverReturn = GetLastError();
            LogError( ( "Unable to open file %d \r\n", ulDriverReturn ) );
            ulReturn = CKR_FUNCTION_FAILED;
        }

        if( 0 == ulReturn )
        {
            /* Get the file size. */
            *pulDataSize = GetFileSize( hFile, ( LPDWORD ) ( &ulSize ) );

            /* Create a buffer. */
            *ppucData = pvPortMalloc( *pulDataSize );

            if( NULL == *ppucData )
            {
                ulReturn = CKR_HOST_MEMORY;
            }
        }

        /* Read the file. */
        if( 0 == ulReturn )
        {
            if( FALSE == ReadFile( hFile,
                                   *ppucData,
                                   *pulDataSize,
                                   ( LPDWORD ) ( &ulSize ),
                                   NULL ) )
            {
                LogError( ( "Unable to read file \r\n" ) );
                ulReturn = CKR_FUNCTION_FAILED;
            }
        }

        /* Confirm the amount of data read. */
        if( 0 == ulReturn )
        {
            ulReturn = CKR_OK;

            if( ulSize != *pulDataSize )
            {
                ulReturn = CKR_FUNCTION_FAILED;
            }
        }

        /* Clean up. */
        if( INVALID_HANDLE_VALUE != hFile )
        {
            CloseHandle( hFile );
        }
    }

    return ulReturn;
}

/*-----------------------------------------------------------*/

void PKCS11_PAL_GetObjectValueCleanup( CK_BYTE_PTR pucData,
                                       CK_ULONG ulDataSize )
{
    /* Unused parameters. */
    ( void ) ulDataSize;

    if( NULL != pucData )
    {
        vPortFree( pucData );
    }
}

/*-----------------------------------------------------------*/

CK_RV PKCS11_PAL_DestroyObject( CK_OBJECT_HANDLE xHandle )
{
    const char * pcFileName = NULL;
    CK_BBOOL xIsPrivate = CK_TRUE;
    CK_RV xResult = CKR_OBJECT_HANDLE_INVALID;
    BOOL ret = 0;

    xResult = PAL_UTILS_HandleToFilename( xHandle,
                                          &pcFileName,
                                          &xIsPrivate );

    if( xResult == CKR_OK )
    {
        if( pdTRUE == prvFileExists( pcFileName ) )
        {
            ret = DeleteFileA( pcFileName );

            if( ret == 0 )
            {
                xResult = CKR_FUNCTION_FAILED;
            }
            else
            {
                xResult = CKR_OK;
            }
        }
    }

    return xResult;
}

/*-----------------------------------------------------------*/
