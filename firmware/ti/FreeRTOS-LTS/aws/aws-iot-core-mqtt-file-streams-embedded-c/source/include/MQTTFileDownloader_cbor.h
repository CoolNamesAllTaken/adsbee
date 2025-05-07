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
 * @file MQTTFileDownloader_cbor.h
 * @brief Function declarations and field declarations for
 * MQTTFileDownloader_cbor.c.
 */

#ifndef MQTT_FILE_DOWNLOADER_CBOR_H
#define MQTT_FILE_DOWNLOADER_CBOR_H

/* *INDENT-OFF* */
#ifdef __cplusplus
extern "C" {
#endif
/* *INDENT-ON* */

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

/**
 * Message field definitions, per the server specification. These are
 * not part of the library interface but are included here for testability.
 */

#define OTA_CBOR_CLIENTTOKEN_KEY          "c" /*!< Key for client id. */
#define OTA_CBOR_FILEID_KEY               "f" /*!< Key for file id. */
#define OTA_CBOR_BLOCKSIZE_KEY            "l" /*!< Key for file block size. */
#define OTA_CBOR_BLOCKOFFSET_KEY          "o" /*!< Key for file block offset. */
#define OTA_CBOR_BLOCKBITMAP_KEY          "b" /*!< Key for bitmap. */
#define OTA_CBOR_STREAMDESCRIPTION_KEY    "d" /*!< Key for stream name. */
#define OTA_CBOR_STREAMFILES_KEY          "r" /*!< Key for file attributes. */
#define OTA_CBOR_FILESIZE_KEY             "z" /*!< Key for file size. */
#define OTA_CBOR_BLOCKID_KEY              "i" /*!< Key for block id. */
#define OTA_CBOR_BLOCKPAYLOAD_KEY         "p" /*!< Key for payload of a block. */
#define OTA_CBOR_NUMBEROFBLOCKS_KEY       "n" /*!< Key for number of blocks. */

/**
 * @brief Decode a Get Stream response message from AWS IoT OTA.
 */
bool CBOR_Decode_GetStreamResponseMessage( const uint8_t * messageBuffer,
                                           size_t messageSize,
                                           int32_t * fileId,
                                           int32_t * blockId,
                                           int32_t * blockSize,
                                           uint8_t * const * payload,
                                           size_t * payloadSize );

/**
 * @brief Create an encoded Get Stream Request message for the AWS IoT OTA
 * service. The service allows block count or block bitmap to be requested,
 * but not both.
 */
bool CBOR_Encode_GetStreamRequestMessage( uint8_t * messageBuffer,
                                          size_t messageBufferSize,
                                          size_t * encodedMessageSize,
                                          const char * clientToken,
                                          uint32_t fileId,
                                          uint32_t blockSize,
                                          uint32_t blockOffset,
                                          const uint8_t * blockBitmap,
                                          size_t blockBitmapSize,
                                          uint32_t numOfBlocksRequested );

/* *INDENT-OFF* */
#ifdef __cplusplus
}
#endif
/* *INDENT-ON* */

#endif /* ifndef MQTT_FILE_DOWNLOADER_CBOR_H */
