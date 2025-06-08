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
#include <string.h>

#include "unity.h"

#include "job_parser.h"
#include "ota_job_processor.h"

static bool result;
static uint32_t convertedUint;
static AfrOtaJobDocumentFields_t documentFields;

static void resetDocumentFields( void );

/* ===========================   UNITY FIXTURES ============================ */

static void resetDocumentFields( void )
{
    documentFields.signature = NULL;
    documentFields.signatureLen = UINT32_MAX;
    documentFields.filepath = NULL;
    documentFields.filepathLen = UINT32_MAX;
    documentFields.certfile = NULL;
    documentFields.certfileLen = UINT32_MAX;
    documentFields.authScheme = NULL;
    documentFields.authSchemeLen = UINT32_MAX;
    documentFields.imageRef = NULL;
    documentFields.imageRefLen = UINT32_MAX;
    documentFields.fileId = UINT32_MAX;
    documentFields.fileSize = UINT32_MAX;
    documentFields.fileType = UINT32_MAX;
}

/* Called before each test method. */
void setUp()
{
    resetDocumentFields();
    result = true;
    convertedUint = 0U;
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

/* ===============================   TESTS   =============================== */

void test_populateJobDocFields_returnsTrue_givenValidMqttDocument( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],"
                            "\"streamname\":\"AFR_OTA-streamname\",\"files\":[{"
                            "\"filepath\":\"/device\",\"filesize\": "
                            "123456789,\"fileid\":0,\"certfile\":\"certfile."
                            "cert\",\"sig-sha256-ecdsa\":\"signature_hash_"
                            "239871\"}]}}";

    result = false;
    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_TRUE( result );
    TEST_ASSERT_EQUAL( 123456789U, documentFields.fileSize );
    TEST_ASSERT_EQUAL( 0U, documentFields.fileId );
    TEST_ASSERT_EQUAL_STRING_LEN( "certfile.cert",
                                  documentFields.certfile,
                                  strlen( "certfile.cert" ) );
    TEST_ASSERT_EQUAL( strlen( "certfile.cert" ), documentFields.certfileLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "signature_hash_239871",
                                  documentFields.signature,
                                  strlen( "signature_hash_239871" ) );
    TEST_ASSERT_EQUAL( strlen( "signature_hash_239871" ),
                       documentFields.signatureLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "/device",
                                  documentFields.filepath,
                                  strlen( "/device" ) );
    TEST_ASSERT_EQUAL( strlen( "/device" ), documentFields.filepathLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "AFR_OTA-streamname",
                                  documentFields.imageRef,
                                  strlen( "AFR_OTA-streamname" ) );
    TEST_ASSERT_EQUAL( strlen( "AFR_OTA-streamname" ),
                       documentFields.imageRefLen );
    TEST_ASSERT_EQUAL( UINT32_MAX, documentFields.fileType );
    TEST_ASSERT_NULL( documentFields.authScheme );
    TEST_ASSERT_EQUAL( UINT32_MAX, documentFields.authSchemeLen );
}

void test_populateJobDocFields_returnsTrue_givenValidMultiFileMqttDocument( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],"
                            "\"streamname\":\"AFR_OTA-streamname\",\"files\":[{"
                            "\"filepath\":\"/path1\",\"filesize\": "
                            "123456789,\"fileid\":0,\"certfile\":\"certfile."
                            "cert\",\"sig-sha256-ecdsa\":\"signature_hash_"
                            "239871\"},{\"filepath\":\"/path2\",\"filesize\": "
                            "101010,\"fileid\":13,\"certfile\":\"certfile2."
                            "cert\",\"sig-sha256-ecdsa\":\"signature_hash_"
                            "101010\"}]}}";

    result = false;
    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_TRUE( result );
    TEST_ASSERT_EQUAL( 123456789U, documentFields.fileSize );
    TEST_ASSERT_EQUAL( 0U, documentFields.fileId );
    TEST_ASSERT_EQUAL_STRING_LEN( "certfile.cert",
                                  documentFields.certfile,
                                  strlen( "certfile.cert" ) );
    TEST_ASSERT_EQUAL( strlen( "certfile.cert" ), documentFields.certfileLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "signature_hash_239871",
                                  documentFields.signature,
                                  strlen( "signature_hash_239871" ) );
    TEST_ASSERT_EQUAL( strlen( "signature_hash_239871" ),
                       documentFields.signatureLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "/path1",
                                  documentFields.filepath,
                                  strlen( "/path1" ) );
    TEST_ASSERT_EQUAL( strlen( "/path1" ), documentFields.filepathLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "AFR_OTA-streamname",
                                  documentFields.imageRef,
                                  strlen( "AFR_OTA-streamname" ) );
    TEST_ASSERT_EQUAL( strlen( "AFR_OTA-streamname" ),
                       documentFields.imageRefLen );
    TEST_ASSERT_EQUAL( UINT32_MAX, documentFields.fileType );
    TEST_ASSERT_NULL( documentFields.authScheme );
    TEST_ASSERT_EQUAL( UINT32_MAX, documentFields.authSchemeLen );

    result = false;
    result = populateJobDocFields( document,
                                   strlen( document ),
                                   1,
                                   &documentFields );

    TEST_ASSERT_TRUE( result );
    TEST_ASSERT_EQUAL( 101010, documentFields.fileSize );
    TEST_ASSERT_EQUAL( 13U, documentFields.fileId );
    TEST_ASSERT_EQUAL_STRING_LEN( "certfile2.cert",
                                  documentFields.certfile,
                                  strlen( "certfile2.cert" ) );
    TEST_ASSERT_EQUAL( strlen( "certfile2.cert" ), documentFields.certfileLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "signature_hash_101010",
                                  documentFields.signature,
                                  strlen( "signature_hash_101010" ) );
    TEST_ASSERT_EQUAL( strlen( "signature_hash_101010" ),
                       documentFields.signatureLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "/path2",
                                  documentFields.filepath,
                                  strlen( "/path2" ) );
    TEST_ASSERT_EQUAL( strlen( "/path2" ), documentFields.filepathLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "AFR_OTA-streamname",
                                  documentFields.imageRef,
                                  strlen( "AFR_OTA-streamname" ) );
    TEST_ASSERT_EQUAL( strlen( "AFR_OTA-streamname" ),
                       documentFields.imageRefLen );
    TEST_ASSERT_EQUAL( UINT32_MAX, documentFields.fileType );
    TEST_ASSERT_NULL( documentFields.authScheme );
    TEST_ASSERT_EQUAL( UINT32_MAX, documentFields.authSchemeLen );
}

void test_populateJobDocFields_returnsTrue_givenValidHttpDocument( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"HTTP\"],\"files\":["
                            "{\"filepath\":\"/"
                            "device\",\"filesize\":343135,\"fileid\":0,"
                            "\"certfile\":\"/strangepath/"
                            "certificate.cert\",\"fileType\": "
                            "2,\"update_data_url\":\"presignedS3Url.s3.amazon."
                            "com\",\"auth_scheme\":\"aws.s3.presigned\",\"sig-"
                            "sha256-ecdsa\":\"SIGNATUREHASH+ASDFLKJ123===\"}]}"
                            "}";

    result = false;
    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_TRUE( result );
    TEST_ASSERT_EQUAL( 343135U, documentFields.fileSize );
    TEST_ASSERT_EQUAL( 0U, documentFields.fileId );
    TEST_ASSERT_EQUAL( 2U, documentFields.fileType );
    TEST_ASSERT_EQUAL_STRING_LEN( "/strangepath/certificate.cert",
                                  documentFields.certfile,
                                  strlen( "/strangepath/certificate.cert" ) );
    TEST_ASSERT_EQUAL( strlen( "/strangepath/certificate.cert" ),
                       documentFields.certfileLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "SIGNATUREHASH+ASDFLKJ123===",
                                  documentFields.signature,
                                  strlen( "SIGNATUREHASH+ASDFLKJ123===" ) );
    TEST_ASSERT_EQUAL( strlen( "SIGNATUREHASH+ASDFLKJ123===" ),
                       documentFields.signatureLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "/device",
                                  documentFields.filepath,
                                  strlen( "/device" ) );
    TEST_ASSERT_EQUAL( strlen( "/device" ), documentFields.filepathLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "presignedS3Url.s3.amazon.com",
                                  documentFields.imageRef,
                                  strlen( "presignedS3Url.s3.amazon.com" ) );
    TEST_ASSERT_EQUAL( strlen( "presignedS3Url.s3.amazon.com" ),
                       documentFields.imageRefLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "aws.s3.presigned",
                                  documentFields.authScheme,
                                  strlen( "aws.s3.presigned" ) );
    TEST_ASSERT_EQUAL( strlen( "aws.s3.presigned" ),
                       documentFields.authSchemeLen );
}

void test_populateJobDocFields_returnsTrue_givenValidMultiFileHttpDocument( void )
{
    const char *
        document = "{\"afr_ota\":{\"protocols\":[\"HTTP\"],\"files\":[{"
                   "\"filepath\":\"/"
                   "device\",\"filesize\":343135,\"fileid\":0,\"certfile\":\"/"
                   "strangepath/certificate.cert\",\"fileType\": "
                   "2,\"update_data_url\":\"presignedS3Url.s3.amazon.com\","
                   "\"auth_scheme\":\"aws.s3.presigned\",\"sig-sha256-ecdsa\":"
                   "\"SIGNATUREHASH+ASDFLKJ123===\"},{\"filepath\":\"/"
                   "path2\",\"filesize\":43210,\"fileid\":99,\"certfile\":\"/"
                   "strangepath/file.cert\",\"fileType\": "
                   "333,\"update_data_url\":\"presignedS3Url.s3.amazon.com\","
                   "\"auth_scheme\":\"aws.s3.presigned\",\"sig-sha256-ecdsa\":"
                   "\"SIGNATUREHASH+ASDFLKJ123===\"}]}}";

    result = false;
    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_TRUE( result );
    TEST_ASSERT_EQUAL( 343135U, documentFields.fileSize );
    TEST_ASSERT_EQUAL( 0U, documentFields.fileId );
    TEST_ASSERT_EQUAL( 2U, documentFields.fileType );
    TEST_ASSERT_EQUAL_STRING_LEN( "/strangepath/certificate.cert",
                                  documentFields.certfile,
                                  strlen( "/strangepath/certificate.cert" ) );
    TEST_ASSERT_EQUAL( strlen( "/strangepath/certificate.cert" ),
                       documentFields.certfileLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "SIGNATUREHASH+ASDFLKJ123===",
                                  documentFields.signature,
                                  strlen( "SIGNATUREHASH+ASDFLKJ123===" ) );
    TEST_ASSERT_EQUAL( strlen( "SIGNATUREHASH+ASDFLKJ123===" ),
                       documentFields.signatureLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "/device",
                                  documentFields.filepath,
                                  strlen( "/device" ) );
    TEST_ASSERT_EQUAL( strlen( "/device" ), documentFields.filepathLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "presignedS3Url.s3.amazon.com",
                                  documentFields.imageRef,
                                  strlen( "presignedS3Url.s3.amazon.com" ) );
    TEST_ASSERT_EQUAL( strlen( "presignedS3Url.s3.amazon.com" ),
                       documentFields.imageRefLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "aws.s3.presigned",
                                  documentFields.authScheme,
                                  strlen( "aws.s3.presigned" ) );
    TEST_ASSERT_EQUAL( strlen( "aws.s3.presigned" ),
                       documentFields.authSchemeLen );

    result = false;
    result = populateJobDocFields( document,
                                   strlen( document ),
                                   1,
                                   &documentFields );

    TEST_ASSERT_TRUE( result );
    TEST_ASSERT_EQUAL( 43210U, documentFields.fileSize );
    TEST_ASSERT_EQUAL( 99U, documentFields.fileId );
    TEST_ASSERT_EQUAL( 333U, documentFields.fileType );
    TEST_ASSERT_EQUAL_STRING_LEN( "/strangepath/file.cert",
                                  documentFields.certfile,
                                  strlen( "/strangepath/file.cert" ) );
    TEST_ASSERT_EQUAL( strlen( "/strangepath/file.cert" ),
                       documentFields.certfileLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "SIGNATUREHASH+ASDFLKJ123===",
                                  documentFields.signature,
                                  strlen( "SIGNATUREHASH+ASDFLKJ123===" ) );
    TEST_ASSERT_EQUAL( strlen( "SIGNATUREHASH+ASDFLKJ123===" ),
                       documentFields.signatureLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "/path2",
                                  documentFields.filepath,
                                  strlen( "/path2" ) );
    TEST_ASSERT_EQUAL( strlen( "/path2" ), documentFields.filepathLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "presignedS3Url.s3.amazon.com",
                                  documentFields.imageRef,
                                  strlen( "presignedS3Url.s3.amazon.com" ) );
    TEST_ASSERT_EQUAL( strlen( "presignedS3Url.s3.amazon.com" ),
                       documentFields.imageRefLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "aws.s3.presigned",
                                  documentFields.authScheme,
                                  strlen( "aws.s3.presigned" ) );
    TEST_ASSERT_EQUAL( strlen( "aws.s3.presigned" ),
                       documentFields.authSchemeLen );
}

void test_populateJobDocFields_returnsTrue_givenValidMultiProtocolDocument( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"MQTT\",\"HTTP\"],"
                            "\"streamname\":\"AFR_OTA-streamname\",\"files\":[{"
                            "\"filepath\":\"/device\",\"filesize\": "
                            "123456789,\"fileid\":0,\"certfile\":\"certfile."
                            "cert\",\"fileType\": "
                            "66,\"update_data_url\":\"unusedurl.s3.amazon."
                            "com\",\"auth_scheme\":\"aws.s3.presigned\",\"sig-"
                            "sha256-ecdsa\":\"signature_hash_239871\"}]}}";

    result = false;
    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_TRUE( result );
    TEST_ASSERT_EQUAL( 123456789U, documentFields.fileSize );
    TEST_ASSERT_EQUAL( 0U, documentFields.fileId );
    TEST_ASSERT_EQUAL_STRING_LEN( "certfile.cert",
                                  documentFields.certfile,
                                  strlen( "certfile.cert" ) );
    TEST_ASSERT_EQUAL( strlen( "certfile.cert" ), documentFields.certfileLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "signature_hash_239871",
                                  documentFields.signature,
                                  strlen( "signature_hash_239871" ) );
    TEST_ASSERT_EQUAL( strlen( "signature_hash_239871" ),
                       documentFields.signatureLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "/device",
                                  documentFields.filepath,
                                  strlen( "/device" ) );
    TEST_ASSERT_EQUAL( strlen( "/device" ), documentFields.filepathLen );
    TEST_ASSERT_EQUAL_STRING_LEN( "AFR_OTA-streamname",
                                  documentFields.imageRef,
                                  strlen( "AFR_OTA-streamname" ) );
    TEST_ASSERT_EQUAL( strlen( "AFR_OTA-streamname" ),
                       documentFields.imageRefLen );
    TEST_ASSERT_EQUAL( UINT32_MAX, documentFields.fileType );
    TEST_ASSERT_NULL( documentFields.authScheme );
    TEST_ASSERT_EQUAL( UINT32_MAX, documentFields.authSchemeLen );
}

void test_populateJobDocFields_returnsFalse_whenEmptyProtocol( void )
{
    const char *
        document = "{\"afr_ota\":{\"protocols\":[],\"streamname\":\"AFR_OTA-"
                   "d66ffc3b-4325-4496-9358-509f8f3504d1\",\"files\":[{"
                   "\"filepath\": \"/device\",\"filesize\": 20417,\"fileid\": "
                   "0,\"certfile\": "
                   "\"/strangepath/certificate.cert\",\"sig-sha256-ecdsa\": "
                   "\"MEYCIQCVWi3ki1d9fqa1vrRS3dyDE7qJv4Dl1guB9qBzvTz7AgIhAIdTm"
                   "0MeZa2aHpHZnKQERLFpI69ii3GUhycQBOVqqP3N\"}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenMissingProtocol( void )
{
    const char * document = "{\"afr_ota\":{\"streamname\":\"AFR_OTA-d66ffc3b-"
                            "4325-4496-9358-509f8f3504d1\",\"files\":[{"
                            "\"filepath\": \"/device\",\"filesize\": "
                            "20417,\"fileid\": 0,\"certfile\": "
                            "\"/strangepath/"
                            "certificate.cert\",\"sig-sha256-ecdsa\": "
                            "\"MEYCIQCVWi3ki1d9fqa1vrRS3dyDE7qJv4Dl1guB9qBzvTz7"
                            "AgIhAIdTm0MeZa2aHpHZnKQERLFpI69ii3GUhycQBOVqqP3N\""
                            "}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenMissingFilesize( void )
{
    const char *
        document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":"
                   "\"AFR_OTA-d66ffc3b-4325-4496-9358-509f8f3504d1\",\"files\":"
                   "[{\"filepath\": \"/device\",\"fileid\": 0,\"certfile\": "
                   "\"/strangepath/certificate.cert\",\"sig-sha256-ecdsa\": "
                   "\"MEYCIQCVWi3ki1d9fqa1vrRS3dyDE7qJv4Dl1guB9qBzvTz7AgIhAIdTm"
                   "0MeZa2aHpHZnKQERLFpI69ii3GUhycQBOVqqP3N\"}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenMissingFileId( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],"
                            "\"streamname\":\"AFR_OTA-d66ffc3b-4325-4496-9358-"
                            "509f8f3504d1\",\"files\":[{\"filepath\": "
                            "\"/device\",\"filesize\": 20417,\"certfile\": "
                            "\"/strangepath/"
                            "certificate.cert\",\"sig-sha256-ecdsa\": "
                            "\"MEYCIQCVWi3ki1d9fqa1vrRS3dyDE7qJv4Dl1guB9qBzvTz7"
                            "AgIhAIdTm0MeZa2aHpHZnKQERLFpI69ii3GUhycQBOVqqP3N\""
                            "}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenMissingFilePath( void )
{
    const char *
        document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":"
                   "\"AFR_OTA-d66ffc3b-4325-4496-9358-509f8f3504d1\",\"files\":"
                   "[{\"filesize\": 20417,\"fileid\": 0,\"certfile\": "
                   "\"/strangepath/certificate.cert\",\"sig-sha256-ecdsa\": "
                   "\"MEYCIQCVWi3ki1d9fqa1vrRS3dyDE7qJv4Dl1guB9qBzvTz7AgIhAIdTm"
                   "0MeZa2aHpHZnKQERLFpI69ii3GUhycQBOVqqP3N\"}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenMissingCertfile( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],"
                            "\"streamname\":\"AFR_OTA-d66ffc3b-4325-4496-9358-"
                            "509f8f3504d1\",\"files\":[{\"filepath\": "
                            "\"/device\",\"filesize\": 20417,\"fileid\": "
                            "0,\"sig-sha256-ecdsa\": "
                            "\"MEYCIQCVWi3ki1d9fqa1vrRS3dyDE7qJv4Dl1guB9qBzvTz7"
                            "AgIhAIdTm0MeZa2aHpHZnKQERLFpI69ii3GUhycQBOVqqP3N\""
                            "}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenMissingSignature( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],"
                            "\"streamname\":\"AFR_OTA-d66ffc3b-4325-4496-9358-"
                            "509f8f3504d1\",\"files\":[{\"filepath\": "
                            "\"/device\",\"filesize\": 20417,\"fileid\": "
                            "0,\"certfile\": "
                            "\"/strangepath/certificate.cert\"}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenMqttDocEmptyStreamName( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],"
                            "\"streamname\":\"\",\"files\":[{\"filepath\":\"/"
                            "device\",\"filesize\": "
                            "123456789,\"fileid\":0,\"certfile\":\"certfile."
                            "cert\",\"sig-sha256-ecdsa\":\"signature_hash_"
                            "239871\"}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenMqttDocMissingStreamName( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"files\":["
                            "{\"filepath\": \"/device\",\"filesize\": "
                            "20417,\"fileid\": 0,\"certfile\": "
                            "\"/strangepath/"
                            "certificate.cert\",\"sig-sha256-ecdsa\": "
                            "\"MEYCIQCVWi3ki1d9fqa1vrRS3dyDE7qJv4Dl1guB9qBzvTz7"
                            "AgIhAIdTm0MeZa2aHpHZnKQERLFpI69ii3GUhycQBOVqqP3N\""
                            "}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenHttpDocMissingFileType( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"HTTP\"],\"files\":["
                            "{\"filepath\":\"/"
                            "device\",\"filesize\":343135,\"fileid\":0,"
                            "\"certfile\":\"/strangepath/"
                            "certificate.cert\",\"update_data_url\":\"${aws:"
                            "iot:s3-presigned-url:https://"
                            "s3.region.amazonaws.com/joe-ota/SignedImages/"
                            "ffdac2a7-0f70-4f47-8940-886ad260445c}\",\"auth_"
                            "scheme\":\"aws.s3.presigned\",\"sig-sha256-"
                            "ecdsa\":\"MEQCIGOTD5owb5s3R3+"
                            "OlxH5UZcy52Vuz6QrJhg83F8t8tBfAiBTNiX0e8RR5JOzHfSqW"
                            "Kq4WJC/xUwMrcdHEWgSAKfGQA==\"}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenHttpDocEmptyUrl( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"HTTP\"],\"files\":["
                            "{\"filepath\":\"/"
                            "device\",\"filesize\":343135,\"fileid\":0,"
                            "\"certfile\":\"/strangepath/"
                            "certificate.cert\",\"fileType\": "
                            "2,\"update_data_url\":\"\",\"auth_scheme\":\"aws."
                            "s3.presigned\",\"sig-sha256-ecdsa\":"
                            "\"SIGNATUREHASH+ASDFLKJ123===\"}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenHttpDocMissingUrl( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"HTTP\"],\"files\":["
                            "{\"filepath\":\"/"
                            "device\",\"filesize\":343135,\"fileid\":0,"
                            "\"certfile\":\"/strangepath/"
                            "certificate.cert\",\"fileType\": "
                            "2,\"auth_scheme\":\"aws.s3.presigned\",\"sig-"
                            "sha256-ecdsa\":\"MEQCIGOTD5owb5s3R3+"
                            "OlxH5UZcy52Vuz6QrJhg83F8t8tBfAiBTNiX0e8RR5JOzHfSqW"
                            "Kq4WJC/xUwMrcdHEWgSAKfGQA==\"}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenHttpDocMissingAuthScheme( void )
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"HTTP\"],\"files\":["
                            "{\"filepath\":\"/"
                            "device\",\"filesize\":343135,\"fileid\":0,"
                            "\"certfile\":\"/strangepath/"
                            "certificate.cert\",\"fileType\": "
                            "2,\"update_data_url\":\"${aws:iot:s3-presigned-"
                            "url:https://s3.region.amazonaws.com/joe-ota/"
                            "SignedImages/"
                            "ffdac2a7-0f70-4f47-8940-886ad260445c}\",\"sig-"
                            "sha256-ecdsa\":\"MEQCIGOTD5owb5s3R3+"
                            "OlxH5UZcy52Vuz6QrJhg83F8t8tBfAiBTNiX0e8RR5JOzHfSqW"
                            "Kq4WJC/xUwMrcdHEWgSAKfGQA==\"}]}}";

    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenFileSizeIsNegativeInteger()
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],"
                            "\"streamname\":\"AFR_OTA-streamname\",\"files\":[{"
                            "\"filepath\":\"/device\",\"filesize\": "
                            "-123456789,\"fileid\":0,\"certfile\":\"certfile."
                            "cert\",\"sig-sha256-ecdsa\":\"signature_hash_"
                            "239871\"}]}}";

    result = true;
    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenFileSizeZeroLength()
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],"
                            "\"streamname\":\"AFR_OTA-streamname\",\"files\":[{"
                            "\"filepath\":\"/device\",\"filesize\": "
                            "\"\",\"fileid\":0,\"certfile\":\"certfile.cert\","
                            "\"sig-sha256-ecdsa\":\"signature_hash_239871\"}]}"
                            "}";

    result = true;
    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}

void test_populateJobDocFields_returnsFalse_whenFileSizeTooLarge()
{
    const char * document = "{\"afr_ota\":{\"protocols\":[\"MQTT\"],"
                            "\"streamname\":\"AFR_OTA-streamname\",\"files\":[{"
                            "\"filepath\":\"/device\",\"filesize\": "
                            "99999999999999,\"fileid\":0,\"certfile\":"
                            "\"certfile.cert\",\"sig-sha256-ecdsa\":"
                            "\"signature_hash_239871\"}]}}";

    result = true;
    result = populateJobDocFields( document,
                                   strlen( document ),
                                   0,
                                   &documentFields );

    TEST_ASSERT_FALSE( result );
}
