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
#include <stdlib.h>
#include <string.h>

#include "core_json.h"

#include "job_parser.h"
#include "ota_job_processor.h"

static bool isFreeRTOSOtaJob( const char * jobDoc,
                              const size_t jobDocLength );
static bool isJobFileIndexValid( const char * jobDoc,
                                 const size_t jobDocLength,
                                 const uint8_t fileIndex );

/**
 * @brief Signals if the job document provided is a FreeRTOS OTA update document
 *
 * @param jobDoc The job document contained in the AWS IoT Job
 * @param jobDocLength The length of the job document
 * @param fields A pointer to an job document fields structure populated by call
 * @return int8_t The next file index in the job. Returns 0 if no additional files are available. Returns -1 if error.
 */
int8_t otaParser_parseJobDocFile( const char * jobDoc,
                                  const size_t jobDocLength,
                                  const uint8_t fileIndex,
                                  AfrOtaJobDocumentFields_t * fields )
{
    bool fieldsPopulated = false;
    int8_t nextFileIndex = -1;

    if( ( jobDoc != NULL ) && ( jobDocLength > 0U ) )
    {
        if( isFreeRTOSOtaJob( jobDoc, jobDocLength ) && isJobFileIndexValid( jobDoc, jobDocLength, fileIndex ) )
        {
            fieldsPopulated = populateJobDocFields( jobDoc,
                                                    jobDocLength,
                                                    ( int32_t ) fileIndex,
                                                    fields );
        }

        if( fieldsPopulated )
        {
            nextFileIndex = ( isJobFileIndexValid( jobDoc, jobDocLength, fileIndex + 1U ) ) ? ( int8_t ) ( ( int8_t ) fileIndex + 1 ) : ( int8_t ) 0;
        }
    }

    return nextFileIndex;
}

static bool isFreeRTOSOtaJob( const char * jobDoc,
                              const size_t jobDocLength )
{
    JSONStatus_t isFreeRTOSOta = JSONIllegalDocument;
    const char * afrOtaDocHeader;
    size_t afrOtaDocHeaderLength = 0U;

    /* FreeRTOS OTA updates have a top level "afr_ota" job document key.
    * Check for this to ensure the document is an FreeRTOS OTA update */
    isFreeRTOSOta = JSON_SearchConst( jobDoc,
                                      jobDocLength,
                                      "afr_ota",
                                      7U,
                                      &afrOtaDocHeader,
                                      &afrOtaDocHeaderLength,
                                      NULL );

    return( JSONSuccess == isFreeRTOSOta );
}

static bool isJobFileIndexValid( const char * jobDoc,
                                 const size_t jobDocLength,
                                 const uint8_t fileIndex )
{
    JSONStatus_t isFreeRTOSOta = JSONIllegalDocument;
    const char * fileValue;
    size_t fileValueLength = 0U;
    char file[ 17U ] = "afr_ota.files[i]";

    if( fileIndex <= 9U )
    {
        int32_t index = ( ( int32_t ) '0' + ( int32_t ) fileIndex );
        file[ 14U ] = ( char ) index;

        isFreeRTOSOta = JSON_SearchConst( jobDoc,
                                          jobDocLength,
                                          file,
                                          16U,
                                          &fileValue,
                                          &fileValueLength,
                                          NULL );
    }

    return( JSONSuccess == isFreeRTOSOta );
}
