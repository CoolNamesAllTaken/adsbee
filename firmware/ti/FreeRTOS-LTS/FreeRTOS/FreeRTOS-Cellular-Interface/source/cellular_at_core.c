/*
 * FreeRTOS-Cellular-Interface v1.4.0
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
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 */

/**
 * @brief FreeRTOS Cellular Library common AT command parsing functions.
 */

#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#ifndef CELLULAR_DO_NOT_USE_CUSTOM_CONFIG
    /* Include custom config file before other headers. */
    #include "cellular_config.h"
#endif

#include "cellular_config_defaults.h"

#include "cellular_at_core.h"
#include "cellular_internal.h"

/*-----------------------------------------------------------*/

/**
 * @brief String validation results.
 */
typedef enum CellularATStringValidationResult
{
    CELLULAR_AT_STRING_VALID,     /**< String is valid. */
    CELLULAR_AT_STRING_EMPTY,     /**< String is empty. */
    CELLULAR_AT_STRING_TOO_LARGE, /**< String is too large. */
    CELLULAR_AT_STRING_UNKNOWN    /**< Unknown String validation state. */
} CellularATStringValidationResult_t;

/*-----------------------------------------------------------*/

static void validateString( const char * pString,
                            CellularATStringValidationResult_t * pStringValidationResult );
static uint8_t _charToNibble( char c );

/*-----------------------------------------------------------*/

static void validateString( const char * pString,
                            CellularATStringValidationResult_t * pStringValidationResult )
{
    const char * pNullCharacterLocation = NULL;

    /* Validate the string length. If the string length is longer than expected, return
     * error to stop further processing.
     *
     * CELLULAR_AT_MAX_STRING_SIZE defines the valid string length excluding NULL terminating
     * character. The longest valid string has '\0' at ( CELLULAR_AT_MAX_STRING_SIZE + 1U )
     */
    pNullCharacterLocation = memchr( pString, ( int32_t ) '\0', ( CELLULAR_AT_MAX_STRING_SIZE + 1U ) );

    if( pNullCharacterLocation == pString )
    {
        *pStringValidationResult = CELLULAR_AT_STRING_EMPTY;
    }
    else if( pNullCharacterLocation == NULL )
    {
        *pStringValidationResult = CELLULAR_AT_STRING_TOO_LARGE;
    }
    else
    {
        *pStringValidationResult = CELLULAR_AT_STRING_VALID;
    }
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATIsPrefixPresent( const char * pString,
                                              bool * pResult )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;
    char * ptrPrefixChar = NULL;
    char * ptrChar = NULL;

    if( ( pResult == NULL ) || ( pString == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( pString, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    /* Find location of first ':'. */
    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        *pResult = true;

        ptrPrefixChar = strchr( pString, ( int32_t ) ':' );

        if( ptrPrefixChar == NULL )
        {
            *pResult = false;
        }
        else if( !CELLULAR_CHECK_IS_PREFIX_LEADING_CHAR( *pString ) )
        {
            *pResult = false;
        }
        else
        {
            /* There should be only '+', '_', characters or digit before seperator. */
            for( ptrChar = ( char * ) pString; ptrChar < ptrPrefixChar; ptrChar++ )
            {
                /* It's caused by stanard api isalpha and isdigit. */
                /* MISRA Ref 4.6.1  [Basic numerical type] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#directive-46 */
                /* MISRA Ref 10.4.1 [Same essential type] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-104 */
                /* MISRA Ref 10.8.1 [Essential type casting] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-108 */
                /* coverity[misra_c_2012_directive_4_6_violation] */
                /* coverity[misra_c_2012_rule_10_4_violation] */
                /* coverity[misra_c_2012_rule_10_8_violation] */
                if( CELLULAR_CHECK_IS_PREFIX_CHAR( ( char ) ( *ptrChar ) ) )
                {
                    *pResult = false;
                    break;
                }
            }
        }
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATStrStartWith( const char * pString,
                                           const char * pPrefix,
                                           bool * pResult )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;
    const char * pTempString = pString;
    const char * pTempPrefix = pPrefix;

    if( ( pResult == NULL ) || ( pString == NULL ) || ( pPrefix == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( pTempString, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( pTempPrefix, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        *pResult = true;

        while( *pTempPrefix != '\0' )
        {
            if( *pTempPrefix != *pTempString )
            {
                *pResult = false;
                break;
            }

            pTempPrefix++;
            pTempString++;
        }
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATRemovePrefix( char ** ppString )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;

    if( ( ppString == NULL ) || ( *ppString == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( *ppString, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        /* The strchr() function returns a pointer to the first occurrence of
         * the character in the string or NULL if the character is not found.
         *
         * In case of AT response, prefix is always followed by a colon (':'). */
        *ppString = strchr( *ppString, ( int32_t ) ':' );

        if( *ppString == NULL )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
        else
        {
            /* Note that we remove both the prefix and the colon. */
            ( *ppString )++;
        }
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATRemoveLeadingWhiteSpaces( char ** ppString )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;

    if( ( ppString == NULL ) || ( *ppString == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( *ppString, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        /* isspace is a standard library function and we cannot control it. */
        /* MISRA Ref 4.6.1  [Basic numerical type] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#directive-46 */
        /* MISRA Ref 21.13.1  [Character representation] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-2113 */
        /* coverity[misra_c_2012_rule_21_13_violation] */
        /* coverity[misra_c_2012_directive_4_6_violation] */
        while( ( **ppString != '\0' ) && ( isspace( ( ( int ) ( **ppString ) ) ) != 0U ) )
        {
            ( *ppString )++;
        }
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATRemoveTrailingWhiteSpaces( char * pString )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    char * p = NULL;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;
    uint32_t stringLen = 0;

    if( pString == NULL )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( pString, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        stringLen = ( uint32_t ) strlen( pString );

        /* This API intend to remove the trailing space, and this should be functional
         * when the string length is greater than 2. */
        if( stringLen > 2U )
        {
            p = &( pString[ stringLen ] );

            do
            {
                --p;
                /* isspace is a standard library function and we cannot control it. */
                /* MISRA Ref 4.6.1  [Basic numerical type] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#directive-46 */
                /* MISRA Ref 21.13.1  [Character representation] */
                /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-2113 */
                /* coverity[misra_c_2012_directive_4_6_violation] */
                /* coverity[misra_c_2012_rule_21_13_violation] */
            } while( ( p > pString ) && ( isspace( ( int ) ( *p ) ) != 0U ) );

            p[ 1 ] = '\0';
        }
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATRemoveAllWhiteSpaces( char * pString )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;
    char * p = NULL;
    uint16_t ind = 0;
    char * pTempString = pString;

    if( pString == NULL )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( pTempString, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        p = pTempString;

        while( ( *pTempString ) != '\0' )
        {
            /* isspace is a standard library function and we cannot control it. */
            /* MISRA Ref 4.6.1  [Basic numerical type] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#directive-46 */
            /* MISRA Ref 21.13.1  [Character representation] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-2113 */
            /* coverity[misra_c_2012_rule_21_13_violation] */
            /* coverity[misra_c_2012_directive_4_6_violation] */
            if( isspace( ( ( int ) ( *pTempString ) ) ) == 0U )
            {
                p[ ind ] = *pTempString;
                ind++;
            }

            pTempString++;
        }

        p[ ind ] = '\0';
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATRemoveOutermostDoubleQuote( char ** ppString )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;
    char * p = NULL;
    uint32_t stringLen = 0;

    if( ( ppString == NULL ) || ( *ppString == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( *ppString, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        stringLen = ( uint32_t ) strlen( *ppString );

        if( stringLen > 2U )
        {
            if( **ppString == '\"' )
            {
                ( *ppString )++;
            }

            p = *ppString;

            while( *p != '\0' )
            {
                p++;
            }

            if( *--p == '\"' )
            {
                *p = '\0';
            }
        }
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATRemoveAllDoubleQuote( char * pString )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;
    char * p = NULL;
    uint16_t ind = 0;
    char * pTempString = pString;

    if( pString == NULL )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( pTempString, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        p = pTempString;

        while( ( *pTempString ) != '\0' )
        {
            if( *pTempString != '\"' )
            {
                p[ ind ] = *pTempString;
                ind++;
            }

            pTempString++;
        }

        p[ ind ] = '\0';
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATGetNextTok( char ** ppString,
                                         char ** ppTokOutput )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    const char * pDelimiter = ",";

    if( ( ppString == NULL ) || ( ppTokOutput == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        atStatus = Cellular_ATGetSpecificNextTok( ppString, pDelimiter, ppTokOutput );
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATGetSpecificNextTok( char ** ppString,
                                                 const char * pDelimiter,
                                                 char ** ppTokOutput )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;
    uint16_t tokStrLen = 0, dataStrlen = 0;
    char * tok = NULL;

    if( ( ppString == NULL ) || ( pDelimiter == NULL ) ||
        ( ppTokOutput == NULL ) || ( *ppString == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( *ppString, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        dataStrlen = ( uint16_t ) strlen( *ppString );

        if( ( **ppString ) == ( *pDelimiter ) )
        {
            **ppString = '\0';
            tok = *ppString;
        }
        else
        {
            tok = strtok( *ppString, pDelimiter );
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        tokStrLen = ( uint16_t ) strlen( tok );

        if( ( tokStrLen < dataStrlen ) && ( ( *ppString )[ tokStrLen + 1U ] != '\0' ) )
        {
            *ppString = &( tok[ strlen( tok ) + 1U ] );
        }
        else
        {
            *ppString = &( tok[ strlen( tok ) ] );
        }

        *ppTokOutput = tok;
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

static uint8_t _charToNibble( char c )
{
    uint8_t ret = 0xFF;

    if( ( c >= '0' ) && ( c <= '9' ) )
    {
        ret = ( uint8_t ) ( ( uint32_t ) c - ( uint32_t ) '0' );
    }
    else if( ( c >= 'a' ) && ( c <= 'f' ) )
    {
        ret = ( uint8_t ) ( ( uint32_t ) c - ( uint32_t ) 'a' + ( uint32_t ) 10 );
    }
    else
    {
        if( ( c >= 'A' ) && ( c <= 'F' ) )
        {
            ret = ( uint8_t ) ( ( uint32_t ) c - ( uint32_t ) 'A' + ( uint32_t ) 10 );
        }
    }

    return ret;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATHexStrToHex( const char * pString,
                                          uint8_t * pHexData,
                                          uint16_t hexDataLen )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;
    uint16_t strHexLen = 0, i = 0;
    const char * p;
    uint8_t firstNibble = 0, secondNibble = 0;

    if( ( pString == NULL ) || ( pHexData == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( pString, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        strHexLen = ( uint16_t ) ( strlen( pString ) / 2U );

        if( strHexLen >= hexDataLen )
        {
            atStatus = CELLULAR_AT_NO_MEMORY;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        p = pString;

        for( i = 0; i < strHexLen; i++ )
        {
            firstNibble = _charToNibble( *p );
            secondNibble = _charToNibble( p[ 1 ] );

            if( firstNibble == 0xFFU )
            {
                ( pHexData )[ i ] = firstNibble;
            }
            else
            {
                firstNibble = ( uint8_t ) ( firstNibble << 4 );
                ( pHexData )[ i ] = firstNibble | secondNibble;
            }

            p = &( p[ 2 ] );
        }
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATIsStrDigit( const char * pString,
                                         bool * pResult )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;
    const char * pTempString = pString;

    if( ( pResult == NULL ) || ( pString == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( pTempString, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        *pResult = true;

        while( ( *pTempString != '\0' ) )
        {
            /* isdigit is a standard library function and we cannot control it. */
            /* MISRA Ref 4.6.1  [Basic numerical type] */
            /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#directive-46 */
            /* coverity[misra_c_2012_directive_4_6_violation] */
            if( isdigit( ( ( int ) ( *pTempString ) ) ) == 0U )
            {
                *pResult = false;
            }

            pTempString++;
        }
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATcheckErrorCode( const char * pInputBuf,
                                             const char * const * const ppKeyList,
                                             size_t keyListLen,
                                             bool * pResult )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    uint8_t i = 0;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;
    bool tmpResult;

    if( ( pInputBuf == NULL ) || ( ppKeyList == NULL ) || ( pResult == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( pInputBuf, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        *pResult = false;

        for( i = 0; i < keyListLen; i++ )
        {
            if( ( Cellular_ATStrStartWith( pInputBuf, ppKeyList[ i ], &tmpResult ) == CELLULAR_AT_SUCCESS ) && tmpResult )
            {
                *pResult = true;
                break;
            }
        }
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATStrDup( char ** ppDst,
                                     const char * pSrc )
{
    char * p = NULL;
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    const char * pTempSrc = pSrc;
    CellularATStringValidationResult_t stringValidationResult = CELLULAR_AT_STRING_UNKNOWN;

    if( ( ppDst == NULL ) || ( pTempSrc == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        validateString( pTempSrc, &stringValidationResult );

        if( stringValidationResult != CELLULAR_AT_STRING_VALID )
        {
            atStatus = CELLULAR_AT_BAD_PARAMETER;
        }
    }

    if( atStatus == CELLULAR_AT_SUCCESS )
    {
        *ppDst = ( char * ) Platform_Malloc( sizeof( char ) * ( strlen( pTempSrc ) + 1U ) );

        if( *ppDst != NULL )
        {
            p = *ppDst;

            while( *pTempSrc != '\0' )
            {
                *p = *pTempSrc;
                p++;
                pTempSrc++;
            }

            *p = '\0';
        }
        else
        {
            atStatus = CELLULAR_AT_NO_MEMORY;
        }
    }

    return atStatus;
}

/*-----------------------------------------------------------*/

CellularATError_t Cellular_ATStrtoi( const char * pStr,
                                     int32_t base,
                                     int32_t * pResult )
{
    CellularATError_t atStatus = CELLULAR_AT_SUCCESS;
    int32_t retStrtol = 0;
    char * pEndStr = NULL;

    if( ( pStr == NULL ) || ( pResult == NULL ) )
    {
        atStatus = CELLULAR_AT_BAD_PARAMETER;
    }
    else
    {
        /* MISRA Ref 22.8.1 [Initialize errno] */
        /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-228 */
        /* coverity[misra_c_2012_rule_22_8_violation] */
        retStrtol = ( int32_t ) strtol( pStr, &pEndStr, base );

        /* The return value zero may stand for the failure of strtol. So if the return value
         * is zero, need to check the address of pEndStr, if it's greater than the pStr, that
         * means there is an real parsed zero before pEndStr.
         */
        if( pEndStr == pStr )
        {
            atStatus = CELLULAR_AT_ERROR;
        }
        else
        {
            *pResult = retStrtol;
        }
    }

    /* MISRA Ref 4.7.1 [Testing errno] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#directive-47 */
    /* MISRA Ref 22.9.1 [Testing errno] */
    /* More details at: https://github.com/FreeRTOS/FreeRTOS-Cellular-Interface/blob/main/MISRA.md#rule-229 */
    /* coverity[need_errno_test] */
    /* coverity[return_without_test] */
    return atStatus;
}

/*-----------------------------------------------------------*/
