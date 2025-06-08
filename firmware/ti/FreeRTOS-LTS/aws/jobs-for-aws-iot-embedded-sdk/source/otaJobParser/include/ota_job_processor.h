/*
 * AWS IoT Jobs v1.5.1
 * Copyright (C) 2023 Amazon.com, Inc. and its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License. See the LICENSE accompanying this file
 * for the specific language governing permissions and limitations under
 * the License.
 */

#ifndef OTA_JOB_PROCESSOR_H
#define OTA_JOB_PROCESSOR_H

#include <stdint.h>

#include <stddef.h>
#include <stdint.h>

#include "job_parser.h"

/**
 * @brief Signals if the job document provided is an AWS IoT Core OTA update document
 *
 * @param jobDoc The job document contained in the AWS IoT Job
 * @param jobDocLength The length of the job document
 * @param fields A pointer to an job document fields structure populated by call
 * @return int8_t The next file index in the job. Returns 0 if no additional files are available. Returns -1 if error.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows how to use the otaParser_parseJobDocFile API
 * // to parse out the fields of a received Job Document and populate the fields
 * // of the AfrOtaJobDocumentFields_t stucture.
 *
 * const char * jobDoc;                    // Populated by call to Jobs_GetJobDocument
 * size_t jobDocLength;                    // Return value of Jobs_GetJobDocument
 * int8_t fileIndex = 0;
 * AfrOtaJobDocumentFields_t fields = {0}; // populated by API
 *
 * do
 * {
 *     fileIndex = otaParser_parseJobDocFile(jobDoc,
 *                                           jobDocLength,
 *                                           fileIndex,
 *                                           &fields);
 * } while(fileIndex > 0)
 * // File index will be -1 if an error occurred, and 0 if all files were
 * // processed
 * @endcode
 */
/* @[declare_otaparser_parsejobdocfile] */
int8_t otaParser_parseJobDocFile( const char * jobDoc,
                                  const size_t jobDocLength,
                                  const uint8_t fileIndex,
                                  AfrOtaJobDocumentFields_t * fields );
/* @[declare_otaparser_parsejobdocfile] */

#endif /*OTA_JOB_PROCESSOR_H*/
