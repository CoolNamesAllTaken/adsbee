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
 * @file MQTTFileDownloader_defaults.h
 * @brief Default values for various MQTT stream macros.
 */

#ifndef MQTT_FILE_DOWNLOADER_DEFAULT_H
#define MQTT_FILE_DOWNLOADER_DEFAULT_H

#include <stdint.h>

/* MQTT_STREAMS_DO_NOT_USE_CUSTOM_CONFIG allows building the MQTT
 * streams library without a custom config. If a custom config is
 * provided, the MQTT_STREAMS_DO_NOT_USE_CUSTOM_CONFIG macro should not
 * be defined. */
#ifndef MQTT_STREAMS_DO_NOT_USE_CUSTOM_CONFIG
    /* Include custom config file before other, non-standard headers. */
    #include "MQTTFileDownloader_config.h"
#endif

/**
 * @ingroup mqtt_file_downloader_const_types
 * @brief Configure the Maximum size of the data payload. The
 * smallest value is 256 bytes, maximum is 128KB. For more see
 * https://docs.aws.amazon.com/general/latest/gr/iot-core.html
 */
#ifndef mqttFileDownloader_CONFIG_BLOCK_SIZE
    #define mqttFileDownloader_CONFIG_BLOCK_SIZE    4096U
#endif

#endif /* #ifndef MQTT_FILE_DOWNLOADER_DEFAULT_H */
