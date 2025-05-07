/*
 * AWS IoT Jobs v1.5.1
 * Copyright (C) 2023 Amazon.com, Inc. and its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License. See the LICENSE accompanying this file
 * for the specific language governing permissions and limitations under
 * the License.
 */

#include <string.h>

#include "unity.h"

#include "mock_job_parser.h"
#include "ota_job_processor.h"

#define JOB_DOC_ID                 "jobDocId"
#define JOB_DOC_ID_LEN             8U
#define AFR_OTA_DOCUMENT           "{\"afr_ota\":{\"files\":[{\"filesize\":123456789}]}}"
#define AFR_OTA_DOCUMENT_LENGTH    ( sizeof( AFR_OTA_DOCUMENT ) - 1U )
#define MULTI_FILE_OTA_DOCUMENT                                    \
    "{\"afr_ota\":{\"files\":[{\"filesize\":1},{\"filesize\":2},{" \
    "\"filesize\":3}]}}"
#define MULTI_FILE_OTA_DOCUMENT_LENGTH \
    ( sizeof( MULTI_FILE_OTA_DOCUMENT ) - 1U )
#define TOO_MANY_FILES_OTA_DOCUMENT                                        \
    "{\"afr_ota\":{\"files\":[{\"filesize\":1},{\"filesize\":2},{"         \
    "\"filesize\":3},{\"filesize\":4},{\"filesize\":5},{\"filesize\":6},{" \
    "\"filesize\":7},{\"filesize\":8},{\"filesize\":9},{\"filesize\":10}]}}"
#define TOO_MANY_FILES_OTA_DOCUMENT_LENGTH \
    ( sizeof( TOO_MANY_FILES_OTA_DOCUMENT ) - 1U )
#define CUSTOM_DOCUMENT           "{\"custom_job\":\"test\"}"
#define CUSTOM_DOCUMENT_LENGTH    ( sizeof( CUSTOM_DOCUMENT ) - 1U )

AfrOtaJobDocumentFields_t parsedFields;

/* ===========================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    parsedFields.signature = "expectedSignature";
    parsedFields.signatureLen = strlen( "expectedSignature" );
    parsedFields.filepath = "expectedFilepath";
    parsedFields.filepathLen = strlen( "expectedFilepath" );
    parsedFields.certfile = "expectedCertfile";
    parsedFields.certfileLen = strlen( "expectedCertfile" );
    parsedFields.authScheme = "expectedAuthScheme";
    parsedFields.authSchemeLen = strlen( "expectedAuthScheme" );
    parsedFields.imageRef = "expectedImageRef";
    parsedFields.imageRefLen = strlen( "expectedImageRef" );
    parsedFields.fileId = UINT32_MAX;
    parsedFields.fileSize = UINT32_MAX;
    parsedFields.fileType = UINT32_MAX;
}

/* Called after each test method. */
void tearDown()
{
}

/* Called at the beginning of the whole suite. */
void suiteSetUp()
{
}

/* Called at the end of the whole suite. */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

/*
 * NOTE: In production, the string fields would not be null-terminated strings,
 * however since we're mocking the return we can force them to be
 * null-terminated for easier validation.
 */
void verifyCallbackValues( AfrOtaJobDocumentFields_t * params )
{
    TEST_ASSERT_EQUAL_STRING( "expectedSignature", params->signature );
    TEST_ASSERT_EQUAL( strlen( "expectedSignature" ), params->signatureLen );
    TEST_ASSERT_EQUAL_STRING( "expectedFilepath", params->filepath );
    TEST_ASSERT_EQUAL( strlen( "expectedFilepath" ), params->filepathLen );
    TEST_ASSERT_EQUAL_STRING( "expectedCertfile", params->certfile );
    TEST_ASSERT_EQUAL( strlen( "expectedCertfile" ), params->certfileLen );
    TEST_ASSERT_EQUAL_STRING( "expectedAuthScheme", params->authScheme );
    TEST_ASSERT_EQUAL( strlen( "expectedAuthScheme" ), params->authSchemeLen );
    TEST_ASSERT_EQUAL_STRING( "expectedImageRef", params->imageRef );
    TEST_ASSERT_EQUAL( strlen( "expectedImageRef" ), params->imageRefLen );
    TEST_ASSERT_EQUAL( UINT32_MAX, params->fileId );
    TEST_ASSERT_EQUAL( UINT32_MAX, params->fileSize );
    TEST_ASSERT_EQUAL( UINT32_MAX, params->fileType );
}

static void expectPopulateJobDocWithFileIndex( const char * document,
                                               size_t docLength,
                                               int index )
{
    populateJobDocFields_ExpectAndReturn( document,
                                          docLength,
                                          index,
                                          NULL,
                                          true );
    populateJobDocFields_IgnoreArg_result();
    populateJobDocFields_ReturnThruPtr_result( &parsedFields );
}

/* ===============================   TESTS   =============================== */

void test_parseJobDocFile_returnsZero_whenSingleFileJob( void )
{
    expectPopulateJobDocWithFileIndex( AFR_OTA_DOCUMENT,
                                       AFR_OTA_DOCUMENT_LENGTH,
                                       0 );

    int8_t result = otaParser_parseJobDocFile( AFR_OTA_DOCUMENT,
                                               AFR_OTA_DOCUMENT_LENGTH,
                                               0U,
                                               &parsedFields );

    TEST_ASSERT_EQUAL( 0, result );
}

void test_parseJobDocFile_returnsNextIndex_whenMultiFileIOTOtaJob( void )
{
    expectPopulateJobDocWithFileIndex( MULTI_FILE_OTA_DOCUMENT,
                                       MULTI_FILE_OTA_DOCUMENT_LENGTH,
                                       0 );
    expectPopulateJobDocWithFileIndex( MULTI_FILE_OTA_DOCUMENT,
                                       MULTI_FILE_OTA_DOCUMENT_LENGTH,
                                       1 );

    int8_t result = otaParser_parseJobDocFile( MULTI_FILE_OTA_DOCUMENT,
                                               MULTI_FILE_OTA_DOCUMENT_LENGTH,
                                               0U,
                                               &parsedFields );

    TEST_ASSERT_EQUAL( 1, result );

    result = otaParser_parseJobDocFile( MULTI_FILE_OTA_DOCUMENT,
                                        MULTI_FILE_OTA_DOCUMENT_LENGTH,
                                        1U,
                                        &parsedFields );

    TEST_ASSERT_EQUAL( 2, result );
}

void test_parseJobDocFile_returnsZero_whenLastFileIndex( void )
{
    expectPopulateJobDocWithFileIndex( MULTI_FILE_OTA_DOCUMENT,
                                       MULTI_FILE_OTA_DOCUMENT_LENGTH,
                                       2 );

    int8_t result = otaParser_parseJobDocFile( MULTI_FILE_OTA_DOCUMENT,
                                               MULTI_FILE_OTA_DOCUMENT_LENGTH,
                                               2U,
                                               &parsedFields );

    TEST_ASSERT_EQUAL( 0, result );
}

void test_parseJobDocFile_returnsNegativeOne_whenIndexOutOfRange( void )
{
    int8_t result = otaParser_parseJobDocFile( AFR_OTA_DOCUMENT,
                                               AFR_OTA_DOCUMENT_LENGTH,
                                               1U,
                                               &parsedFields );

    TEST_ASSERT_EQUAL( -1, result );
}

void test_parseJobDocFile_returnsNegativeOne_whenParsingFails( void )
{
    populateJobDocFields_ExpectAndReturn( AFR_OTA_DOCUMENT,
                                          AFR_OTA_DOCUMENT_LENGTH,
                                          0,
                                          NULL,
                                          false );
    populateJobDocFields_IgnoreArg_result();

    int8_t result = otaParser_parseJobDocFile( AFR_OTA_DOCUMENT,
                                               AFR_OTA_DOCUMENT_LENGTH,
                                               0U,
                                               &parsedFields );

    TEST_ASSERT_EQUAL( -1, result );
}

void test_parseJobDocFile_returnsNegativeOne_whenMultiFileParsingFails( void )
{
    populateJobDocFields_ExpectAndReturn( MULTI_FILE_OTA_DOCUMENT,
                                          MULTI_FILE_OTA_DOCUMENT_LENGTH,
                                          0,
                                          NULL,
                                          false );
    populateJobDocFields_IgnoreArg_result();

    int8_t result = otaParser_parseJobDocFile( MULTI_FILE_OTA_DOCUMENT,
                                               MULTI_FILE_OTA_DOCUMENT_LENGTH,
                                               0,
                                               &parsedFields );

    TEST_ASSERT_EQUAL( -1, result );
}

void test_parseJobDocFile_returnsNegativeOne_whenCustomJob( void )
{
    int8_t result = otaParser_parseJobDocFile( CUSTOM_DOCUMENT,
                                               CUSTOM_DOCUMENT_LENGTH,
                                               0U,
                                               &parsedFields );

    TEST_ASSERT_EQUAL( -1, result );
}

void test_parseJobDocFile_returnsFalse_givenNullJobDocument( void )
{
    int8_t result = otaParser_parseJobDocFile( NULL,
                                               CUSTOM_DOCUMENT_LENGTH,
                                               0U,
                                               &parsedFields );

    TEST_ASSERT_EQUAL( -1, result );
}

void test_parseJobDocFile_returnsFalse_givenZeroDocumentLength( void )
{
    int8_t result = otaParser_parseJobDocFile( AFR_OTA_DOCUMENT,
                                               0U,
                                               0U,
                                               &parsedFields );

    TEST_ASSERT_EQUAL( -1, result );
}
