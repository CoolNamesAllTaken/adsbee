/*
 * AWS IoT Device Defender Client v1.4.0
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
 */

/**
 * @file defender.h
 * @brief Interface for the AWS IoT Device Defender Client Library.
 */

#ifndef DEFENDER_H_
#define DEFENDER_H_

/* Standard includes. */
#include <stdint.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* DEFENDER_DO_NOT_USE_CUSTOM_CONFIG allows building the Device Defender library
 * without a config file. If a config file is provided, DEFENDER_DO_NOT_USE_CUSTOM_CONFIG
 * macro must not be defined.
 */
#ifndef DEFENDER_DO_NOT_USE_CUSTOM_CONFIG
    #include "defender_config.h"
#endif

/* Default config values. */
#include "defender_config_defaults.h"

/**
 * @ingroup defender_enum_types
 * @brief Return codes from defender APIs.
 */
typedef enum
{
    DefenderError = 0,     /**< Generic Error. */
    DefenderSuccess,       /**< Success. */
    DefenderNoMatch,       /**< The provided topic does not match any defender topic. */
    DefenderBadParameter,  /**< Invalid parameters were passed. */
    DefenderBufferTooSmall /**< The output buffer is too small. */
} DefenderStatus_t;

/**
 * @ingroup defender_enum_types
 * @brief Topic values for subscription requests.
 */
typedef enum
{
    DefenderInvalidTopic = -1,  /**< Invalid topic. */
    DefenderJsonReportPublish,  /**< Topic for publishing a JSON report. */
    DefenderJsonReportAccepted, /**< Topic for getting a JSON report accepted response. */
    DefenderJsonReportRejected, /**< Topic for getting a JSON report rejected response. */
    DefenderCborReportPublish,  /**< Topic for publishing a CBOR report. */
    DefenderCborReportAccepted, /**< Topic for getting a CBOR report accepted response. */
    DefenderCborReportRejected, /**< Topic for getting a CBOR report rejected response. */
    DefenderMaxTopic
} DefenderTopic_t;

/*-----------------------------------------------------------*/

/**
 * @brief Helper macro to calculate the length of a string literal.
 */
#define STRING_LITERAL_LENGTH( literal )    ( ( uint16_t ) ( sizeof( literal ) - 1U ) )

/*-----------------------------------------------------------*/

/**
 * @ingroup defender_constants
 * @brief Maximum length of a thing's name as permitted by AWS IoT Core.
 */
#define DEFENDER_THINGNAME_MAX_LENGTH         128U

/**
 * @ingroup defender_constants
 * @brief Minimum period between 2 consecutive defender reports sent by the
 * device.
 *
 * This is as per AWS IoT Device Defender Service reference.
 */
#define DEFENDER_REPORT_MIN_PERIOD_SECONDS    300

/*-----------------------------------------------------------*/

/*
 * A Defender topic has the following format:
 *
 * <Prefix><Thing Name><Bridge><Report Format><Suffix>
 *
 * Where:
 * <Prefix> = $aws/things/
 * <Thing Name> = Name of the thing.
 * <Bridge> = /defender/metrics/
 * <Report Format> = json or cbor
 * <Suffix> = /accepted or /rejected or empty
 *
 * Examples:
 * $aws/things/THING_NAME/defender/metrics/json
 * $aws/things/THING_NAME/defender/metrics/json/accepted
 * $aws/things/THING_NAME/defender/metrics/json/rejected
 * $aws/things/THING_NAME/defender/metrics/cbor
 * $aws/things/THING_NAME/defender/metrics/cbor/accepted
 * $aws/things/THING_NAME/defender/metrics/json/rejected
 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore these macros as they are private.
 */

#define DEFENDER_API_PREFIX                    "$aws/things/"
#define DEFENDER_API_LENGTH_PREFIX             STRING_LITERAL_LENGTH( DEFENDER_API_PREFIX )

#define DEFENDER_API_BRIDGE                    "/defender/metrics/"
#define DEFENDER_API_LENGTH_BRIDGE             STRING_LITERAL_LENGTH( DEFENDER_API_BRIDGE )

#define DEFENDER_API_JSON_FORMAT               "json"
#define DEFENDER_API_LENGTH_JSON_FORMAT        STRING_LITERAL_LENGTH( DEFENDER_API_JSON_FORMAT )

#define DEFENDER_API_CBOR_FORMAT               "cbor"
#define DEFENDER_API_LENGTH_CBOR_FORMAT        STRING_LITERAL_LENGTH( DEFENDER_API_CBOR_FORMAT )

#define DEFENDER_API_ACCEPTED_SUFFIX           "/accepted"
#define DEFENDER_API_LENGTH_ACCEPTED_SUFFIX    STRING_LITERAL_LENGTH( DEFENDER_API_ACCEPTED_SUFFIX )

#define DEFENDER_API_REJECTED_SUFFIX           "/rejected"
#define DEFENDER_API_LENGTH_REJECTED_SUFFIX    STRING_LITERAL_LENGTH( DEFENDER_API_REJECTED_SUFFIX )

#define DEFENDER_API_NULL_SUFFIX               ""
#define DEFENDER_API_LENGTH_NULL_SUFFIX        ( 0U )

/** @endcond */

/*-----------------------------------------------------------*/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this macro as it is private.
 */

/* Defender API topic lengths. */
#define DEFENDER_API_COMMON_LENGTH( thingNameLength, reportFormatLength, suffixLength ) \
    ( DEFENDER_API_LENGTH_PREFIX +                                                      \
      ( thingNameLength ) +                                                             \
      DEFENDER_API_LENGTH_BRIDGE +                                                      \
      ( reportFormatLength ) +                                                          \
      ( suffixLength ) )

/** @endcond */

/**
 * @brief Length of the topic string for publishing a JSON report.
 *
 * @param[in] thingNameLength Length of the thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_LENGTH_JSON_PUBLISH( thingNameLength )      \
    DEFENDER_API_COMMON_LENGTH( thingNameLength,                 \
                                DEFENDER_API_LENGTH_JSON_FORMAT, \
                                DEFENDER_API_LENGTH_NULL_SUFFIX )

/**
 * @brief Length of the topic string for getting a JSON report accepted response.
 *
 * @param[in] thingNameLength Length of the thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_LENGTH_JSON_ACCEPTED( thingNameLength )     \
    DEFENDER_API_COMMON_LENGTH( thingNameLength,                 \
                                DEFENDER_API_LENGTH_JSON_FORMAT, \
                                DEFENDER_API_LENGTH_ACCEPTED_SUFFIX )

/**
 * @brief Length of the topic string for getting a JSON report rejected response.
 *
 * @param[in] thingNameLength Length of the thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_LENGTH_JSON_REJECTED( thingNameLength )     \
    DEFENDER_API_COMMON_LENGTH( thingNameLength,                 \
                                DEFENDER_API_LENGTH_JSON_FORMAT, \
                                DEFENDER_API_LENGTH_REJECTED_SUFFIX )

/**
 * @brief Length of the topic string for publishing a CBOR report.
 *
 * @param[in] thingNameLength Length of the thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_LENGTH_CBOR_PUBLISH( thingNameLength )      \
    DEFENDER_API_COMMON_LENGTH( thingNameLength,                 \
                                DEFENDER_API_LENGTH_CBOR_FORMAT, \
                                DEFENDER_API_LENGTH_NULL_SUFFIX )

/**
 * @brief  Length of the topic string for getting a CBOR report accepted response.
 *
 * @param[in] thingNameLength Length of the thing name. as registered with AWS IoT Core.
 */
#define DEFENDER_API_LENGTH_CBOR_ACCEPTED( thingNameLength )     \
    DEFENDER_API_COMMON_LENGTH( thingNameLength,                 \
                                DEFENDER_API_LENGTH_CBOR_FORMAT, \
                                DEFENDER_API_LENGTH_ACCEPTED_SUFFIX )

/**
 * @brief  Length of the topic string for getting a CBOR report rejected response.
 *
 * @param[in] thingNameLength Length of the thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_LENGTH_CBOR_REJECTED( thingNameLength )     \
    DEFENDER_API_COMMON_LENGTH( thingNameLength,                 \
                                DEFENDER_API_LENGTH_CBOR_FORMAT, \
                                DEFENDER_API_LENGTH_REJECTED_SUFFIX )

/**
 * @brief Maximum length of the topic string for any defender operation.
 *
 * @param[in] thingNameLength Length of the thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_MAX_LENGTH( thingNameLength ) \
    DEFENDER_API_LENGTH_CBOR_ACCEPTED( thingNameLength )

/*-----------------------------------------------------------*/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this macro as it is private.
 */

/* Defender API topics. */
#define DEFENDER_API_COMMON( thingName, reportFormat, suffix ) \
    ( DEFENDER_API_PREFIX                                      \
      thingName                                                \
      DEFENDER_API_BRIDGE                                      \
      reportFormat                                             \
      suffix )

/** @endcond */

/**
 * @brief Topic string for publishing a JSON report.
 *
 * This macro should be used when the thing name is known at the compile time.
 * If the thing name is not known at compile time, the #Defender_GetTopic API
 * should be used instead.
 *
 * @param thingName The thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_JSON_PUBLISH( thingName )     \
    DEFENDER_API_COMMON( thingName,                \
                         DEFENDER_API_JSON_FORMAT, \
                         DEFENDER_API_NULL_SUFFIX )

/**
 * @brief Topic string for getting a JSON report accepted response.
 *
 * This macro should be used when the thing name is known at the compile time.
 * If the thing name is not known at compile time, the #Defender_GetTopic API
 * should be used instead.
 *
 * @param thingName The thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_JSON_ACCEPTED( thingName )    \
    DEFENDER_API_COMMON( thingName,                \
                         DEFENDER_API_JSON_FORMAT, \
                         DEFENDER_API_ACCEPTED_SUFFIX )

/**
 * @brief Topic string for getting a JSON report rejected response.
 *
 * This macro should be used when the thing name is known at the compile time.
 * If the thing name is not known at compile time, the #Defender_GetTopic API
 * should be used instead.
 *
 * @param thingName The thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_JSON_REJECTED( thingName )    \
    DEFENDER_API_COMMON( thingName,                \
                         DEFENDER_API_JSON_FORMAT, \
                         DEFENDER_API_REJECTED_SUFFIX )

/**
 * @brief Topic string for publishing a CBOR report.
 *
 * This macro should be used when the thing name is known at the compile time.
 * If the thing name is not known at compile time, the #Defender_GetTopic API
 * should be used instead.
 *
 * @param thingName The thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_CBOR_PUBLISH( thingName )     \
    DEFENDER_API_COMMON( thingName,                \
                         DEFENDER_API_CBOR_FORMAT, \
                         DEFENDER_API_NULL_SUFFIX )

/**
 * @brief Topic string for getting a CBOR report accepted response.
 *
 * This macro should be used when the thing name is known at the compile time.
 * If the thing name is not known at compile time, the #Defender_GetTopic API
 * should be used instead.
 *
 * @param thingName The thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_CBOR_ACCEPTED( thingName )    \
    DEFENDER_API_COMMON( thingName,                \
                         DEFENDER_API_CBOR_FORMAT, \
                         DEFENDER_API_ACCEPTED_SUFFIX )

/**
 * @brief Topic string for getting a CBOR report rejected response.
 *
 * This macro should be used when the thing name is known at the compile time.
 * If the thing name is not known at compile time, the #Defender_GetTopic API
 * should be used instead.
 *
 * @param thingName The thing name as registered with AWS IoT Core.
 */
#define DEFENDER_API_CBOR_REJECTED( thingName )    \
    DEFENDER_API_COMMON( thingName,                \
                         DEFENDER_API_CBOR_FORMAT, \
                         DEFENDER_API_REJECTED_SUFFIX )

/*-----------------------------------------------------------*/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this macro as it is private.
 */

/* Keys used in defender report. */
#if ( defined( DEFENDER_USE_LONG_KEYS ) && ( DEFENDER_USE_LONG_KEYS == 1 ) )
    #define DEFENDER_REPORT_SELECT_KEY( longKey, shortKey )    longKey
#else
    #define DEFENDER_REPORT_SELECT_KEY( longKey, shortKey )    shortKey
#endif

/** @endcond */

/**
 * @ingroup defender_constants
 * @brief "header" key in the defender report.
 */
#define DEFENDER_REPORT_HEADER_KEY                            DEFENDER_REPORT_SELECT_KEY( "header", "hed" )

/**
 * @ingroup defender_constants
 * @brief Length of the "header" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_HEADER_KEY                     STRING_LITERAL_LENGTH( DEFENDER_REPORT_HEADER_KEY )

/**
 * @ingroup defender_constants
 * @brief "metrics" key in the defender report.
 */
#define DEFENDER_REPORT_METRICS_KEY                           DEFENDER_REPORT_SELECT_KEY( "metrics", "met" )

/**
 * @ingroup defender_constants
 * @brief Length of the "metrics" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_METRICS_KEY                    STRING_LITERAL_LENGTH( DEFENDER_REPORT_METRICS_KEY )

/**
 * @ingroup defender_constants
 * @brief "report_id" key in the defender report.
 */
#define DEFENDER_REPORT_ID_KEY                                DEFENDER_REPORT_SELECT_KEY( "report_id", "rid" )

/**
 * @ingroup defender_constants
 * @brief Length of the "report_id" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_ID_KEY                         STRING_LITERAL_LENGTH( DEFENDER_REPORT_ID_KEY )

/**
 * @ingroup defender_constants
 * @brief "version" key in the defender report.
 */
#define DEFENDER_REPORT_VERSION_KEY                           DEFENDER_REPORT_SELECT_KEY( "version", "v" )

/**
 * @ingroup defender_constants
 * @brief Length of the "version" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_VERSION_KEY                    STRING_LITERAL_LENGTH( DEFENDER_REPORT_VERSION_KEY )

/**
 * @ingroup defender_constants
 * @brief "tcp_connections" key in the defender report.
 */
#define DEFENDER_REPORT_TCP_CONNECTIONS_KEY                   DEFENDER_REPORT_SELECT_KEY( "tcp_connections", "tc" )

/**
 * @ingroup defender_constants
 * @brief Length of the "tcp_connections" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_TCP_CONNECTIONS_KEY            STRING_LITERAL_LENGTH( DEFENDER_REPORT_TCP_CONNECTIONS_KEY )

/**
 * @ingroup defender_constants
 * @brief "established_connections" key in the defender report.
 */
#define DEFENDER_REPORT_ESTABLISHED_CONNECTIONS_KEY           DEFENDER_REPORT_SELECT_KEY( "established_connections", "ec" )

/**
 * @ingroup defender_constants
 * @brief Length of the "established_connections" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_ESTABLISHED_CONNECTIONS_KEY    STRING_LITERAL_LENGTH( DEFENDER_REPORT_ESTABLISHED_CONNECTIONS_KEY )

/**
 * @ingroup defender_constants
 * @brief "connections" key in the defender report.
 */
#define DEFENDER_REPORT_CONNECTIONS_KEY                       DEFENDER_REPORT_SELECT_KEY( "connections", "cs" )

/**
 * @ingroup defender_constants
 * @brief Length of the "connections" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_CONNECTIONS_KEY                STRING_LITERAL_LENGTH( DEFENDER_REPORT_CONNECTIONS_KEY )

/**
 * @ingroup defender_constants
 * @brief "remote_addr" key in the defender report.
 */
#define DEFENDER_REPORT_REMOTE_ADDR_KEY                       DEFENDER_REPORT_SELECT_KEY( "remote_addr", "rad" )

/**
 * @ingroup defender_constants
 * @brief Length of the "remote_addr" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_REMOTE_ADDR_KEY                STRING_LITERAL_LENGTH( DEFENDER_REPORT_REMOTE_ADDR_KEY )

/**
 * @ingroup defender_constants
 * @brief "local_port" key in the defender report.
 */
#define DEFENDER_REPORT_LOCAL_PORT_KEY                        DEFENDER_REPORT_SELECT_KEY( "local_port", "lp" )

/**
 * @ingroup defender_constants
 * @brief Length of the "local_port" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_LOCAL_PORT_KEY                 STRING_LITERAL_LENGTH( DEFENDER_REPORT_LOCAL_PORT_KEY )

/**
 * @ingroup defender_constants
 * @brief "local_interface" key in the defender report.
 */
#define DEFENDER_REPORT_LOCAL_INTERFACE_KEY                   DEFENDER_REPORT_SELECT_KEY( "local_interface", "li" )

/**
 * @ingroup defender_constants
 * @brief Length of the "local_interface" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_LOCAL_INTERFACE_KEY            STRING_LITERAL_LENGTH( DEFENDER_REPORT_LOCAL_INTERFACE_KEY )

/**
 * @ingroup defender_constants
 * @brief "total" key in the defender report.
 */
#define DEFENDER_REPORT_TOTAL_KEY                             DEFENDER_REPORT_SELECT_KEY( "total", "t" )

/**
 * @ingroup defender_constants
 * @brief Length of the "total" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_TOTAL_KEY                      STRING_LITERAL_LENGTH( DEFENDER_REPORT_TOTAL_KEY )

/**
 * @ingroup defender_constants
 * @brief "listening_tcp_ports" key in the defender report.
 */
#define DEFENDER_REPORT_TCP_LISTENING_PORTS_KEY               DEFENDER_REPORT_SELECT_KEY( "listening_tcp_ports", "tp" )

/**
 * @ingroup defender_constants
 * @brief Length of the "listening_tcp_ports" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_TCP_LISTENING_PORTS_KEY        STRING_LITERAL_LENGTH( DEFENDER_REPORT_TCP_LISTENING_PORTS_KEY )

/**
 * @ingroup defender_constants
 * @brief "ports" key in the defender report.
 */
#define DEFENDER_REPORT_PORTS_KEY                             DEFENDER_REPORT_SELECT_KEY( "ports", "pts" )

/**
 * @ingroup defender_constants
 * @brief Length of the "ports" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_PORTS_KEY                      STRING_LITERAL_LENGTH( DEFENDER_REPORT_PORTS_KEY )

/**
 * @ingroup defender_constants
 * @brief "port" key in the defender report.
 */
#define DEFENDER_REPORT_PORT_KEY                              DEFENDER_REPORT_SELECT_KEY( "port", "pt" )

/**
 * @ingroup defender_constants
 * @brief Length of the "port" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_PORT_KEY                       STRING_LITERAL_LENGTH( DEFENDER_REPORT_PORT_KEY )

/**
 * @ingroup defender_constants
 * @brief "interface" key in the defender report.
 */
#define DEFENDER_REPORT_INTERFACE_KEY                         DEFENDER_REPORT_SELECT_KEY( "interface", "if" )

/**
 * @ingroup defender_constants
 * @brief Length of the "interface" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_INTERFACE_KEY                  STRING_LITERAL_LENGTH( DEFENDER_REPORT_INTERFACE_KEY )

/**
 * @ingroup defender_constants
 * @brief "listening_udp_ports" key in the defender report.
 */
#define DEFENDER_REPORT_UDP_LISTENING_PORTS_KEY               DEFENDER_REPORT_SELECT_KEY( "listening_udp_ports", "up" )

/**
 * @ingroup defender_constants
 * @brief Length of the "listening_udp_ports" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_UDP_LISTENING_PORTS_KEY        STRING_LITERAL_LENGTH( DEFENDER_REPORT_UDP_LISTENING_PORTS_KEY )

/**
 * @ingroup defender_constants
 * @brief "network_stats" key in the defender report.
 */
#define DEFENDER_REPORT_NETWORK_STATS_KEY                     DEFENDER_REPORT_SELECT_KEY( "network_stats", "ns" )

/**
 * @ingroup defender_constants
 * @brief Length of the "network_stats" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_NETWORK_STATS_KEY              STRING_LITERAL_LENGTH( DEFENDER_REPORT_NETWORK_STATS_KEY )

/**
 * @ingroup defender_constants
 * @brief "bytes_in" key in the defender report.
 */
#define DEFENDER_REPORT_BYTES_IN_KEY                          DEFENDER_REPORT_SELECT_KEY( "bytes_in", "bi" )

/**
 * @ingroup defender_constants
 * @brief Length of the "bytes_in" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_BYTES_IN_KEY                   STRING_LITERAL_LENGTH( DEFENDER_REPORT_BYTES_IN_KEY )

/**
 * @ingroup defender_constants
 * @brief "bytes_out" key in the defender report.
 */
#define DEFENDER_REPORT_BYTES_OUT_KEY                         DEFENDER_REPORT_SELECT_KEY( "bytes_out", "bo" )

/**
 * @ingroup defender_constants
 * @brief Length of the "bytes_out" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_BYTES_OUT_KEY                  STRING_LITERAL_LENGTH( DEFENDER_REPORT_BYTES_OUT_KEY )

/**
 * @ingroup defender_constants
 * @brief "packets_in" key in the defender report.
 */
#define DEFENDER_REPORT_PKTS_IN_KEY                           DEFENDER_REPORT_SELECT_KEY( "packets_in", "pi" )

/**
 * @ingroup defender_constants
 * @brief Length of the "packets_in" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_PKTS_IN_KEY                    STRING_LITERAL_LENGTH( DEFENDER_REPORT_PKTS_IN_KEY )

/**
 * @ingroup defender_constants
 * @brief "packets_out" key in the defender report.
 */
#define DEFENDER_REPORT_PKTS_OUT_KEY                          DEFENDER_REPORT_SELECT_KEY( "packets_out", "po" )

/**
 * @ingroup defender_constants
 * @brief Length of the "packets_out" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_PKS_OUT_KEY                    STRING_LITERAL_LENGTH( DEFENDER_REPORT_LENGTH_PKS_OUT_KEY )

/**
 * @ingroup defender_constants
 * @brief "custom_metrics" key in the defender report.
 */
#define DEFENDER_REPORT_CUSTOM_METRICS_KEY                    DEFENDER_REPORT_SELECT_KEY( "custom_metrics", "cmet" )

/**
 * @ingroup defender_constants
 * @brief Length of the "custom_metrics" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_CUSTOM_METRICS_KEY             STRING_LITERAL_LENGTH( DEFENDER_REPORT_LENGTH_CUSTOM_METRICS_KEY )

/**
 * @ingroup defender_constants
 * @brief "number" key in the defender report.
 */
#define DEFENDER_REPORT_NUMBER_KEY                            "number"

/**
 * @ingroup defender_constants
 * @brief Length of the "number" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_NUMBER_KEY                     STRING_LITERAL_LENGTH( DEFENDER_REPORT_LENGTH_NUMBER_KEY )

/**
 * @ingroup defender_constants
 * @brief "number_list" key in the defender report.
 */
#define DEFENDER_REPORT_NUMBER_LIST_KEY                       "number_list"

/**
 * @ingroup defender_constants
 * @brief Length of the "number_list" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_NUMBER_LIST_KEY                STRING_LITERAL_LENGTH( DEFENDER_REPORT_LENGTH_NUMBER_LIST_KEY )

/**
 * @ingroup defender_constants
 * @brief "string_list" key in the defender report.
 */
#define DEFENDER_REPORT_STRING_LIST_KEY                       "string_list"

/**
 * @ingroup defender_constants
 * @brief Length of the "string_list" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_STRING_LIST_KEY                STRING_LITERAL_LENGTH( DEFENDER_REPORT_LENGTH_STRING_LIST_KEY )

/**
 * @ingroup defender_constants
 * @brief "ip_list" key in the defender report.
 */
#define DEFENDER_REPORT_IP_LIST_KEY                           "ip_list"

/**
 * @ingroup defender_constants
 * @brief Length of the "ip_list" key in the defender report.
 */
#define DEFENDER_REPORT_LENGTH_IP_LIST_KEY                    STRING_LITERAL_LENGTH( DEFENDER_REPORT_LENGTH_IP_LIST_KEY )

/*-----------------------------------------------------------*/

/**
 * @brief Populate the topic string for a Device Defender operation.
 *
 * @param[in] pBuffer The buffer to write the topic string into.
 * @param[in] bufferLength The length of the buffer.
 * @param[in] pThingName The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength The length of the thing name.
 * @param[in] api The desired Device Defender API.
 * @param[out] pOutLength The length of the topic string written to the buffer.
 *
 * @return #DefenderSuccess if the topic string is written to the buffer;
 * #DefenderBadParameter if invalid parameters are passed;
 * #DefenderBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows how to use the Defender_GetTopic API to
 * // generate a topic string for getting a JSON report accepted response.
 *
 * #define TOPIC_BUFFER_LENGTH      ( 256U )
 *
 * // Every device should have a unique thing name registered with AWS IoT Core.
 * // This example assumes that the device has a unique serial number which is
 * // registered as the thing name with AWS IoT Core.
 * const char * pThingName = GetDeviceSerialNumber();
 * uint16_t thingNameLength = ( uint16_t )strlen( pThingname );
 * char topicBuffer[ TOPIC_BUFFER_LENGTH ] = { 0 };
 * uint16_t topicLength = 0;
 * DefenderStatus_t status = DefenderSuccess;
 *
 * status = Defender_GetTopic( &( topicBuffer[ 0 ] ),
 *                             TOPIC_BUFFER_LENGTH,
 *                             pThingName,
 *                             thingNameLength,
 *                             DefenderJsonReportAccepted,
 *                             &( topicLength ) );
 *
 * if( status == DefenderSuccess )
 * {
 *      // The buffer topicBuffer contains the topic string of length
 *      // topicLength for getting a JSON report accepted response. Subscribe
 *      // to this topic using an MQTT client of your choice.
 * }
 * @endcode
 */
/* @[declare_defender_gettopic] */
DefenderStatus_t Defender_GetTopic( char * pBuffer,
                                    uint16_t bufferLength,
                                    const char * pThingName,
                                    uint16_t thingNameLength,
                                    DefenderTopic_t api,
                                    uint16_t * pOutLength );
/* @[declare_defender_gettopic] */

/*-----------------------------------------------------------*/

/**
 * @brief Check if the given topic is one of the Device Defender topics.
 *
 * The function outputs which API the topic is for. It also optionally outputs
 * the starting location and length of the thing name in the given topic.
 *
 * @param[in] pTopic The topic string to check.
 * @param[in] topicLength The length of the topic string.
 * @param[out] pOutApi The defender topic API value.
 * @param[out] ppOutThingName Optional parameter to output the beginning of the
 *             thing name in the topic string. Pass NULL if not needed.
 * @param[out] pOutThingNameLength Optional parameter to output the length of
 *             the thing name in the topic string. Pass NULL if not needed.
 *
 * @return #DefenderSuccess if the topic is one of the defender topics;
 * #DefenderBadParameter if invalid parameters are passed;
 * #DefenderNoMatch if the topic is NOT one of the defender topics (parameter
 * pOutApi gets #DefenderInvalidTopic).
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows how to use the Defender_MatchTopic API to
 * // check if an incoming MQTT publish message is a Device Defender message.
 *
 * DefenderTopic_t api;
 * DefenderStatus_t status = DefenderSuccess;
 *
 * // pTopic and topicLength are the topic string and length of the topic on
 * // which the publish message is received. These are usually provided by the
 * // MQTT client used. We pass the last two argument as NULL as we are not
 * // interested in the thing name in the topic string.
 * status = Defender_MatchTopic( pTopic,
 *                               topicLength,
 *                               &( api ),
 *                               NULL,
 *                               NULL );
 *
 * if( status == DefenderSuccess )
 * {
 *      if( api == DefenderJsonReportAccepted )
 *      {
 *          // The published JSON report was accepted by the AWS IoT Device
 *          // Defender service. You can parse the response using your choice
 *          // of JSON parser and ensure that the report Id is same as was sent
 *          // in the defender report.
 *      }
 *      else if( api == DefenderJsonReportRejected )
 *      {
 *          // The published JSON report was rejected by the AWS IoT Device
 *          // Defender service.
 *      }
 *      else
 *      {
 *          // Unexpected response.
 *      }
 * }
 * @endcode
 */
/* @[declare_defender_matchtopic] */
DefenderStatus_t Defender_MatchTopic( const char * pTopic,
                                      uint16_t topicLength,
                                      DefenderTopic_t * pOutApi,
                                      const char ** ppOutThingName,
                                      uint16_t * pOutThingNameLength );
/* @[declare_defender_matchtopic] */

/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* DEFENDER_H_ */
