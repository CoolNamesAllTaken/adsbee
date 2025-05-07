/*
 * AWS IoT Jobs v1.5.1
 * Copyright (C) 2023 Amazon.com, Inc. and its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License. See the LICENSE accompanying this file
 * for the specific language governing permissions and limitations under
 * the License.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "core_json.h"
#include "job_parser.h"

/**
 * @brief Populates common job document fields in result
 *
 * @param jobDoc FreeRTOS OTA job document
 * @param jobDocLength OTA job document length
 * @param fileIndex The index of the file to use
 * @param result Job document structure to populate
 * @return JSONStatus_t JSON parsing status
 */
static JSONStatus_t populateCommonFields( const char * jobDoc,
                                          const size_t jobDocLength,
                                          int32_t fileIndex,
                                          AfrOtaJobDocumentFields_t * result );

/**
 * @brief Populates MQTT job document fields in result
 *
 * @param jobDoc FreeRTOS OTA job document
 * @param jobDocLength OTA job document length
 * @param result Job document structure to populate
 * @return JSONStatus_t JSON parsing status
 */
static JSONStatus_t populateMqttStreamingFields( const char * jobDoc,
                                                 const size_t jobDocLength,
                                                 AfrOtaJobDocumentFields_t * result );

/**
 * @brief Populates HTTP job document fields in result
 *
 * @param jobDoc FreeRTOS OTA job document
 * @param jobDocLength OTA job document length
 * @param fileIndex The index of the file to use
 * @param result Job document structure to populate
 * @return JSONStatus_t JSON parsing status
 */
static JSONStatus_t populateHttpStreamingFields( const char * jobDoc,
                                                 const size_t jobDocLength,
                                                 int32_t fileIndex,
                                                 AfrOtaJobDocumentFields_t * result );

/**
 * @brief Assembles an indexed OTA file query
 *
 * @param fileIndex The file index
 * @param queryString The JSON element inside of the File JSON structure to
 * search for
 * @param queryStringLength The length of the query
 * @param result The resulting value of the query key
 * @param resultLength The length of the value
 */
static void buildIndexedFileQueryString( int32_t fileIndex,
                                         const char * queryString,
                                         size_t queryStringLength,
                                         char * result,
                                         size_t * resultLength );

/**
 * @brief Searches the JSON document for the uint32_t value
 *
 * @param jobDoc FreeRTOS OTA job document
 * @param jobDocLength OTA job document length
 * @param query The JSON path to query
 * @param queryLength The length of the JSON path
 * @param value Pointer to set uint32_t value
 * @return JSONStatus_t JSON parsing status
 */
static JSONStatus_t searchUintValue( const char * jobDoc,
                                     const size_t jobDocLength,
                                     const char * query,
                                     const size_t queryLength,
                                     uint32_t * value );

/**
 * @brief Convert a non-null terminated string to a unsigned 32-bit integer
 *
 * @param string String representation of 32-bit unsigned integer
 * @param length Length of the integer when represented as a string
 * @param value Unsigned 32-bit integer representation of the value
 * @return true Successfully converted to uint32
 * @return false Unsuccessfully converted to uint32
 */
static bool uintFromString( const char * string,
                            const uint32_t length,
                            uint32_t * value );

/**
 * @brief Check if a character is a digit
 *
 * @param c Character to validate
 * @return true Character is a 0-9 digit
 * @return false Character is not a digit
 */
static bool charIsDigit( const char c );

/**
 * @brief Check for multiplication overflow between two uint32 values
 *
 * @param a First uint32 value
 * @param b Second uint32 value
 * @return true If overflow will occur
 * @return false If overflow will not occur
 */
static bool multOverflowUnit32( const uint32_t a,
                                const uint32_t b );

/**
 * @brief Check for addition overflow between two uint32 values
 *
 * @param a First uint32 value
 * @param b Second uint32 value
 * @return true If overflow will occur
 * @return false If overflow will not occur
 */
static bool addOverflowUint32( const uint32_t a,
                               const uint32_t b );

bool populateJobDocFields( const char * jobDoc,
                           const size_t jobDocLength,
                           int32_t fileIndex,
                           AfrOtaJobDocumentFields_t * result )
{
    bool populatedJobDocFields = false;
    JSONStatus_t jsonResult = JSONNotFound;
    const char * protocol = NULL;
    size_t protocolLength = 0U;

    /* TODO - Add assertions for NULL job docs or 0 length documents*/
    jsonResult = populateCommonFields( jobDoc, jobDocLength, fileIndex, result );

    if( jsonResult == JSONSuccess )
    {
        jsonResult = JSON_SearchConst( jobDoc,
                                       jobDocLength,
                                       "afr_ota.protocols[0]",
                                       20U,
                                       &protocol,
                                       &protocolLength,
                                       NULL );
    }

    /* Determine if the supported protocol is MQTT or HTTP */
    if( ( jsonResult == JSONSuccess ) && ( protocolLength == 4U ) )
    {
        if( strncmp( "MQTT", protocol, protocolLength ) == 0 )
        {
            jsonResult = populateMqttStreamingFields( jobDoc,
                                                      jobDocLength,
                                                      result );
        }
        else
        {
            jsonResult = populateHttpStreamingFields( jobDoc,
                                                      jobDocLength,
                                                      fileIndex,
                                                      result );
        }
    }

    populatedJobDocFields = ( jsonResult == JSONSuccess );

    /* Should this nullify the fields which have been populated before
     * returning? */
    return populatedJobDocFields;
}

static JSONStatus_t populateCommonFields( const char * jobDoc,
                                          const size_t jobDocLength,
                                          int32_t fileIndex,
                                          AfrOtaJobDocumentFields_t * result )
{
    JSONStatus_t jsonResult = JSONNotFound;
    const char * jsonValue = NULL;
    size_t jsonValueLength = 0U;
    char queryString[ 33 ];
    size_t queryStringLength;

    if( fileIndex <= 9 )
    {
        buildIndexedFileQueryString( fileIndex,
                                     "filesize",
                                     8U,
                                     queryString,
                                     &queryStringLength );
        jsonResult = searchUintValue( jobDoc,
                                      jobDocLength,
                                      queryString,
                                      queryStringLength,
                                      &( result->fileSize ) );
    }
    else
    {
        jsonResult = JSONIllegalDocument;
    }

    if( jsonResult == JSONSuccess )
    {
        buildIndexedFileQueryString( fileIndex,
                                     "fileid",
                                     6U,
                                     queryString,
                                     &queryStringLength );
        jsonResult = searchUintValue( jobDoc,
                                      jobDocLength,
                                      queryString,
                                      queryStringLength,
                                      &( result->fileId ) );
    }

    if( jsonResult == JSONSuccess )
    {
        buildIndexedFileQueryString( fileIndex,
                                     "filepath",
                                     8U,
                                     queryString,
                                     &queryStringLength );
        jsonResult = JSON_SearchConst( jobDoc,
                                       jobDocLength,
                                       queryString,
                                       queryStringLength,
                                       &jsonValue,
                                       &jsonValueLength,
                                       NULL );
        result->filepath = jsonValue;
        result->filepathLen = ( uint32_t ) jsonValueLength;
    }

    if( jsonResult == JSONSuccess )
    {
        buildIndexedFileQueryString( fileIndex,
                                     "certfile",
                                     8U,
                                     queryString,
                                     &queryStringLength );
        jsonResult = JSON_SearchConst( jobDoc,
                                       jobDocLength,
                                       queryString,
                                       queryStringLength,
                                       &jsonValue,
                                       &jsonValueLength,
                                       NULL );
        result->certfile = jsonValue;
        result->certfileLen = ( uint32_t ) jsonValueLength;
    }

    if( jsonResult == JSONSuccess )
    {
        buildIndexedFileQueryString( fileIndex,
                                     "sig-sha256-ecdsa",
                                     16U,
                                     queryString,
                                     &queryStringLength );
        jsonResult = JSON_SearchConst( jobDoc,
                                       jobDocLength,
                                       queryString,
                                       queryStringLength,
                                       &jsonValue,
                                       &jsonValueLength,
                                       NULL );
        result->signature = jsonValue;
        result->signatureLen = ( uint32_t ) jsonValueLength;
    }

    return jsonResult;
}

static JSONStatus_t populateMqttStreamingFields( const char * jobDoc,
                                                 const size_t jobDocLength,
                                                 AfrOtaJobDocumentFields_t * result )
{
    JSONStatus_t jsonResult = JSONNotFound;
    const char * jsonValue = NULL;
    size_t jsonValueLength = 0U;

    jsonResult = JSON_SearchConst( jobDoc,
                                   jobDocLength,
                                   "afr_ota.streamname",
                                   18U,
                                   &jsonValue,
                                   &jsonValueLength,
                                   NULL );
    result->imageRef = jsonValue;
    result->imageRefLen = ( uint32_t ) jsonValueLength;

    /* If the stream name is empty, consider this an error */
    if( jsonValueLength == 0U )
    {
        jsonResult = JSONNotFound;
    }

    return jsonResult;
}

static JSONStatus_t populateHttpStreamingFields( const char * jobDoc,
                                                 const size_t jobDocLength,
                                                 int32_t fileIndex,
                                                 AfrOtaJobDocumentFields_t * result )
{
    JSONStatus_t jsonResult = JSONNotFound;
    const char * jsonValue = NULL;
    size_t jsonValueLength = 0U;
    char queryString[ 33 ];
    size_t queryStringLength;

    buildIndexedFileQueryString( fileIndex,
                                 "fileType",
                                 8U,
                                 queryString,
                                 &queryStringLength );
    jsonResult = searchUintValue( jobDoc,
                                  jobDocLength,
                                  queryString,
                                  queryStringLength,
                                  &( result->fileType ) );

    if( jsonResult == JSONSuccess )
    {
        buildIndexedFileQueryString( fileIndex,
                                     "auth_scheme",
                                     11U,
                                     queryString,
                                     &queryStringLength );
        jsonResult = JSON_SearchConst( jobDoc,
                                       jobDocLength,
                                       queryString,
                                       queryStringLength,
                                       &jsonValue,
                                       &jsonValueLength,
                                       NULL );
        result->authScheme = jsonValue;
        result->authSchemeLen = ( uint32_t ) jsonValueLength;
    }

    if( jsonResult == JSONSuccess )
    {
        buildIndexedFileQueryString( fileIndex,
                                     "update_data_url",
                                     15U,
                                     queryString,
                                     &queryStringLength );
        jsonResult = JSON_SearchConst( jobDoc,
                                       jobDocLength,
                                       queryString,
                                       queryStringLength,
                                       &jsonValue,
                                       &jsonValueLength,
                                       NULL );
        result->imageRef = jsonValue;
        result->imageRefLen = ( uint32_t ) jsonValueLength;

        /* If the url is empty, consider this an error */
        if( jsonValueLength == 0U )
        {
            jsonResult = JSONNotFound;
        }
    }

    return jsonResult;
}

static void buildIndexedFileQueryString( int32_t fileIndex,
                                         const char * queryString,
                                         size_t queryStringLength,
                                         char * result,
                                         size_t * resultLength )
{
    /*TODO: Should there be a check on the length of the result buffer? */
    ( void ) strncpy( result, ( const char * ) "afr_ota.files[", 15U );
    int32_t index = ( fileIndex + ( int32_t ) '0' );
    result[ 14 ] = ( char ) index;
    ( void ) strncpy( &result[ 15 ], ( const char * ) "].", 3U );
    ( void ) memcpy( &result[ 17 ], queryString, queryStringLength );

    *resultLength = 17U + queryStringLength;
}

static JSONStatus_t searchUintValue( const char * jobDoc,
                                     const size_t jobDocLength,
                                     const char * query,
                                     const size_t queryLength,
                                     uint32_t * value )
{
    bool numConversionSuccess = true;
    JSONStatus_t jsonResult = JSONNotFound;
    const char * jsonValue = NULL;
    size_t jsonValueLength = 0U;

    jsonResult = JSON_SearchConst( jobDoc,
                                   jobDocLength,
                                   query,
                                   queryLength,
                                   &jsonValue,
                                   &jsonValueLength,
                                   NULL );

    if( jsonResult == JSONSuccess )
    {
        numConversionSuccess = uintFromString( jsonValue,
                                               ( const uint32_t )
                                               jsonValueLength,
                                               value );
    }

    return ( numConversionSuccess ) ? jsonResult : JSONBadParameter;
}

static bool uintFromString( const char * string,
                            const uint32_t length,
                            uint32_t * value )
{
    bool ret = false;
    bool overflow = false;
    uint32_t retVal = 0U;
    size_t i;

    if( ( string != NULL ) && ( value != NULL ) )
    {
        for( i = 0U; ( i < length ) && !overflow; i++ )
        {
            char c = string[ i ];

            if( !charIsDigit( c ) )
            {
                break;
            }
            else
            {
                if( !multOverflowUnit32( retVal, 10U ) )
                {
                    retVal *= 10U;

                    if( !addOverflowUint32( retVal, ( ( uint32_t ) c - ( uint32_t ) '0' ) ) )
                    {
                        retVal += ( ( uint32_t ) c - ( uint32_t ) '0' );
                    }
                    else
                    {
                        overflow = true;
                    }
                }
                else
                {
                    overflow = true;
                }
            }
        }

        if( ( length > 0U ) && ( i == length ) )
        {
            *value = retVal;
            ret = true;
        }
    }

    return ret;
}

static bool charIsDigit( const char c )
{
    return ( c >= '0' ) && ( c <= '9' );
}

static bool multOverflowUnit32( const uint32_t a,
                                const uint32_t b )
{
    return ( b > 0U ) && ( a > ( UINT32_MAX / b ) );
}

static bool addOverflowUint32( const uint32_t a,
                               const uint32_t b )
{
    return a > ( UINT32_MAX - b );
}
