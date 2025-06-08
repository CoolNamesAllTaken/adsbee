/*
 * AWS IoT Core MQTT File Streams Embedded C v1.1.0
 * Copyright (C) 2023 Amazon.com, Inc. and its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License. See the LICENSE accompanying this file
 * for the specific language governing permissions and limitations under
 * the License.
 */

/**
 * @file MQTTFileDownloader_base64.h
 * @brief Function declarations and error codes for MQTTFileDownloader_base64.c.
 */

#ifndef MQTT_FILE_DOWNLOADER_BASE64_H
#define MQTT_FILE_DOWNLOADER_BASE64_H

/* *INDENT-OFF* */
#ifdef __cplusplus
extern "C" {
#endif
/* *INDENT-ON* */

/* Standard includes. */
#include <stdint.h>
#include <stdlib.h>

/**
 * ota_enum_types
 * @brief The Base64 functionality return status.
 */
typedef enum
{
    /**
     * @brief Base64 function success.
     */
    Base64Success,

    /**
     * @brief Invalid symbol in the encoded data.
     */
    Base64InvalidSymbol,

    /**
     * @brief A Base64 symbol is in an invalid location within the encoded data.
     */
    Base64InvalidSymbolOrdering,

    /**
     * @brief Length of the encoded data is impossible to have been created with
     *        valid Base64 encoding.
     */
    Base64InvalidInputSize,

    /**
     * @brief Input parameter for pointer is null.
     */
    Base64NullPointerInput,

    /**
     * @brief Provided buffer is too small.
     */
    Base64InvalidBufferSize,

    /**
     * @brief Padding bits inside of the encoded data are invalid because they
     * are not zero.
     */
    Base64NonZeroPadding,

    /**
     * @brief Invalid number of padding symbols.
     */
    Base64InvalidPaddingSymbol
} Base64Status_t;

/**
 * @brief Decode Base64 encoded data.
 *
 * @param[out] dest Pointer to a buffer for storing the decoded result.
 * @param[in]  destLen Length of the dest buffer.
 * @param[out] resultLen Pointer to the length of the decoded result.
 * @param[in]  encodedData Pointer to a buffer containing the Base64 encoded
 *             data that is intended to be decoded.
 * @param[in]  encodedLen Length of the encodedData buffer.
 *
 * @return     One of the following:
 *             - #Base64Success if the Base64 encoded data was valid
 *               and successfully decoded.
 *             - An error code defined in ota_base64_private.h if the
 *               encoded data or input parameters are invalid.
 */
Base64Status_t base64_Decode( uint8_t * dest,
                              const size_t destLen,
                              size_t * resultLen,
                              const uint8_t * encodedData,
                              const size_t encodedLen );

/* *INDENT-OFF* */
#ifdef __cplusplus
}
#endif
/* *INDENT-ON* */

#endif /* ifndef MQTT_FILE_DOWNLOADER_BASE64_H */
