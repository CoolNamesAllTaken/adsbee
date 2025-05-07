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
 * @file MQTTFileDownloader.h
 * @brief MQTT file streaming APIs declaration.
 */

#ifndef MQTT_FILE_DOWNLOADER_H
#define MQTT_FILE_DOWNLOADER_H

#include <stdbool.h>
#include <stdint.h>

/**
 *  @brief Topic strings used by the MQTT downloader.
 *
 * These first few are topic extensions to the dynamic base topic that includes
 * the Thing name.
 */
#define MQTT_API_THINGS                   "$aws/things/"       /*!< Topic prefix for thing APIs. */
#define MQTT_API_STREAMS                  "/streams/"          /*!< Stream API identifier. */
#define MQTT_API_DATA_CBOR                "/data/cbor"         /*!< Stream API suffix. */
#define MQTT_API_GET_CBOR                 "/get/cbor"          /*!< Stream API suffix. */
#define MQTT_API_DATA_JSON                "/data/json"         /*!< JSON DATA Stream API suffix. */
#define MQTT_API_GET_JSON                 "/get/json"          /*!< JSON GET Stream API suffix. */

/**
 * @ingroup mqtt_file_downloader_const_types
 * Maximum stream name length.
 */
#define STREAM_NAME_MAX_LEN               44U

/**
 * @ingroup mqtt_file_downloader_const_types
 * Length of NULL character. Used in calculating lengths of MQTT topics.
 */
#define NULL_CHAR_LEN                     1U

/**
 * @ingroup mqtt_file_downloader_const_types
 * Maximum thing name length.
 */
#define MAX_THINGNAME_LEN                 128U

/**
 * @ingroup mqtt_file_downloader_const_types
 * Stream Request Buffer Size
 */
#define GET_STREAM_REQUEST_BUFFER_SIZE    256U

/**
 * @brief Macro to calculate string length.
 */
#define CONST_STRLEN( s )    ( ( ( uint32_t ) sizeof( s ) ) - 1UL )

/**
 * @brief Length of common parts MQTT topic.
 */
#define TOPIC_COMMON_PARTS_LEN                              \
    ( CONST_STRLEN( MQTT_API_THINGS ) + MAX_THINGNAME_LEN + \
      CONST_STRLEN( MQTT_API_STREAMS ) + STREAM_NAME_MAX_LEN + NULL_CHAR_LEN )

/**
 * @brief Length stream data buffer.
 */
#define TOPIC_STREAM_DATA_BUFFER_SIZE \
    ( TOPIC_COMMON_PARTS_LEN + CONST_STRLEN( MQTT_API_DATA_CBOR ) )

/**
 * @brief Length of get stream buffer.
 */
#define TOPIC_GET_STREAM_BUFFER_SIZE \
    ( TOPIC_COMMON_PARTS_LEN + CONST_STRLEN( MQTT_API_GET_CBOR ) )

/**
 * @ingroup mqtt_file_downloader_enum_types
 * @brief  MQTT File Downloader return codes.
 */
typedef enum
{
    MQTTFileDownloaderFailure,           /**< Failure. */
    MQTTFileDownloaderSuccess,           /**< Success. */
    MQTTFileDownloaderBadParameter,      /**< Bad Parameter. */
    MQTTFileDownloaderNotInitialized,    /**< Downloader not initalized. */
    MQTTFileDownloaderInitFailed,        /**< Downloader init failed. */
    MQTTFileDownloaderSubscribeFailed,   /**< MQTT subscribe failed. */
    MQTTFileDownloaderPublishFailed,     /**< MQTT publish failed. */
    MQTTFileDownloaderDataDecodingFailed /**< MQTT data decoding failed. */
} MQTTFileDownloaderStatus_t;

/**
 * @ingroup mqtt_file_downloader_enum_types
 * @brief contains all the data types supported.
 */
typedef enum
{
    DATA_TYPE_JSON, /**< JSON data type. */
    DATA_TYPE_CBOR  /**< CBOR data type. */
} DataType_t;

/**
 * @ingroup mqtt_file_downloader_struct_types
 * @brief Strucure to mqtt file downloader context.
 */
typedef struct
{
    char topicStreamData[ TOPIC_STREAM_DATA_BUFFER_SIZE ]; /**< Stream data MQTT topic. */
    size_t topicStreamDataLength;                          /**< Stream data MQTT topic length. */
    char topicGetStream[ TOPIC_GET_STREAM_BUFFER_SIZE ];   /**< Get Stream MQTT topic. */
    size_t topicGetStreamLength;                           /**< Get Stream MQTT topic length. */
    uint8_t dataType;                                      /**< Encoding type to be used to download the file. */
} MqttFileDownloaderContext_t;

/**
 * @brief Initializes the MQTT file downloader. Creates the topic name the DATA and Get Stream Data topics
 *
 * @param[in] context MQTT file downloader context pointer.
 * @param[in] streamName Stream name to download the file.
 * @param[in] streamNameLength Length of the Stream name to download the file.
 * @param[in] thingName Thing name of the Device.
 * @param[in] thingNameLength Length of the Thing name of the Device.
 * @param[in] dataType Either JSON or CBOR data type.
 *
 * @return MQTTFileDownloaderStatus_t returns appropriate MQTT File Downloader Status.
 */
/* @[declare_mqttDownloader_init] */
MQTTFileDownloaderStatus_t mqttDownloader_init( MqttFileDownloaderContext_t * context,
                                                const char * streamName,
                                                size_t streamNameLength,
                                                const char * thingName,
                                                size_t thingNameLength,
                                                DataType_t dataType );
/* @[declare_mqttDownloader_init] */

/**
 * @brief Creates the get request for Data blocks from MQTT Streams.
 *
 * @param[in] dataType Either JSON or CBOR data type.
 * @param[in] fileId File Id of the file to be downloaded from MQTT Streams.
 * @param[in] blockSize Requested size of block.
 * @param[in] blockOffset Block Offset.
 * @param[in] numberOfBlocksRequested Number of Blocks requested per request.
 * @param[out] getStreamRequest Buffer to store the get stream request.
 * @param[in] getStreamRequestLength Length of getStreamRequest buffer.
 *
 * @return size_t returns Length of the get stream request.
 */
/* @[declare_mqttDownloader_createGetDataBlockRequest] */
size_t mqttDownloader_createGetDataBlockRequest( DataType_t dataType,
                                                 uint16_t fileId,
                                                 uint32_t blockSize,
                                                 uint16_t blockOffset,
                                                 uint32_t numberOfBlocksRequested,
                                                 char * getStreamRequest,
                                                 size_t getStreamRequestLength );
/* @[declare_mqttDownloader_createGetDataBlockRequest] */

/**
 * @brief Checks if the incoming Publish message contains MQTT Data block.
 *
 * @param[in] context MQTT file downloader context pointer.
 * @param[in] topic incoming Publish message MQTT topic.
 * @param[in] topicLength incoming Publish message MQTT topic length.
 *
 * @return returns True if the message contains Data block else False.
 */
/* @[declare_mqttDownloader_isDataBlockReceived] */
MQTTFileDownloaderStatus_t mqttDownloader_isDataBlockReceived( const MqttFileDownloaderContext_t * context,
                                                               const char * topic,
                                                               size_t topicLength );
/* @[declare_mqttDownloader_isDataBlockReceived] */

/**
 * @brief Retrieve the data block from incoming MQTT message and decode it.
 *
 * @param[in] context MQTT file downloader context pointer.
 * @param[in] message Incoming MQTT message containing data block.
 * @param[in] messageLength Incoming MQTT message length.
 * @param[out] fileId ID of the file to which the data block belongs.
 * @param[out] blockId ID of the received block.
 * @param[out] blockSize Size of the receive block in bytes.
 * @param[out] data Decoded data block.
 * @param[in] dataLength Decoded data block length.
 *
 * @return returns True if the message is handled else False.
 */
/* @[declare_mqttDownloader_processReceivedDataBlock] */
MQTTFileDownloaderStatus_t mqttDownloader_processReceivedDataBlock( const MqttFileDownloaderContext_t * context,
                                                                    uint8_t * message,
                                                                    size_t messageLength,
                                                                    int32_t * fileId,
                                                                    int32_t * blockId,
                                                                    int32_t * blockSize,
                                                                    uint8_t * data,
                                                                    size_t * dataLength );
/* @[declare_mqttDownloader_processReceivedDataBlock] */
#endif /* #ifndef MQTT_FILE_DOWNLOADER_H */
