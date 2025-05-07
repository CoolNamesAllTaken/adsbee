/*
 * FreeRTOS-Cellular-Interface v1.4.0
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
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 */

/**
 * @file cellular_config_defaults.h
 * @brief This represents the default values for the configuration macros
 * for the Cellular library.
 *
 * @note This file SHOULD NOT be modified. If custom values are needed for
 * any configuration macro, a cellular_config.h file should be provided to
 * the Cellular library to override the default values defined in this file.
 * To use the custom config file, the CELLULAR_DO_NOT_USE_CUSTOM_CONFIG preprocessor
 * macro SHOULD NOT be set.
 */

#ifndef __CELLULAR_CONFIG_DEFAULTS_H__
#define __CELLULAR_CONFIG_DEFAULTS_H__

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* The macro definition for CELLULAR_DO_NOT_USE_CUSTOM_CONFIG is for Doxygen
 * documentation only. */

/**
 * @brief Define this macro to build the Cellular library without the custom config
 * file cellular_config.h.
 *
 * Without the custom config, the Cellular library builds with
 * default values of config macros defined in cellular_config_defaults.h file.
 *
 * If a custom config is provided, then CELLULAR_DO_NOT_USE_CUSTOM_CONFIG should not
 * be defined.
 */
#ifdef DOXYGEN
    #define CELLULAR_DO_NOT_USE_CUSTOM_CONFIG
#endif

/**
 * @brief Mobile country code max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 3
 */
#ifndef CELLULAR_MCC_MAX_SIZE
    #define CELLULAR_MCC_MAX_SIZE    ( 3U )
#endif

/**
 * @brief Mobile network code max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 3
 */
#ifndef CELLULAR_MNC_MAX_SIZE
    #define CELLULAR_MNC_MAX_SIZE    ( 3U )
#endif

/**
 * @brief Integrate circuit card identity max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 20
 */
#ifndef CELLULAR_ICCID_MAX_SIZE
    #define CELLULAR_ICCID_MAX_SIZE    ( 20U )
#endif

/**
 * @brief International Mobile Subscriber Identity max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 15
 */
#ifndef CELLULAR_IMSI_MAX_SIZE
    #define CELLULAR_IMSI_MAX_SIZE    ( 15U )
#endif

/**
 * @brief Cellular module firmware version max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 32
 */
#ifndef CELLULAR_FW_VERSION_MAX_SIZE
    #define CELLULAR_FW_VERSION_MAX_SIZE    ( 32U )
#endif

/**
 * @brief Cellular module hardware version max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 12
 */
#ifndef CELLULAR_HW_VERSION_MAX_SIZE
    #define CELLULAR_HW_VERSION_MAX_SIZE    ( 12U )
#endif

/**
 * @brief Cellular module serial number max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 12
 */
#ifndef CELLULAR_SERIAL_NUM_MAX_SIZE
    #define CELLULAR_SERIAL_NUM_MAX_SIZE    ( 12U )
#endif

/**
 * @brief International Mobile Equipment Identity number max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 15
 */
#ifndef CELLULAR_IMEI_MAX_SIZE
    #define CELLULAR_IMEI_MAX_SIZE    ( 15U )
#endif

/**
 * @brief Registered network operator name max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 32
 */
#ifndef CELLULAR_NETWORK_NAME_MAX_SIZE
    #define CELLULAR_NETWORK_NAME_MAX_SIZE    ( 32U )
#endif

/**
 * @brief Access point name max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 32
 */
#ifndef CELLULAR_APN_MAX_SIZE
    #define CELLULAR_APN_MAX_SIZE    ( 64U )
#endif

/**
 * @brief Packet data network username max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 32
 */
#ifndef CELLULAR_PDN_USERNAME_MAX_SIZE
    #define CELLULAR_PDN_USERNAME_MAX_SIZE    ( 32U )
#endif

/**
 * @brief Packet data network password max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 32
 */
#ifndef CELLULAR_PDN_PASSWORD_MAX_SIZE
    #define CELLULAR_PDN_PASSWORD_MAX_SIZE    ( 32u )
#endif

/**
 * @brief Cellular data network IP address max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 40
 */
#ifndef CELLULAR_IP_ADDRESS_MAX_SIZE
    #define CELLULAR_IP_ADDRESS_MAX_SIZE    ( 40U )
#endif

/**
 * @brief Cellular AT command max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 200
 */
#ifndef CELLULAR_AT_CMD_MAX_SIZE
    #define CELLULAR_AT_CMD_MAX_SIZE    ( 200U )
#endif

/**
 * @brief Cellular module number of socket max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 12
 */
#ifndef CELLULAR_NUM_SOCKET_MAX
    #define CELLULAR_NUM_SOCKET_MAX    ( 12U )
#endif

/**
 * @brief Cellular module manufacture ID max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 20
 */
#ifndef CELLULAR_MANUFACTURE_ID_MAX_SIZE
    #define CELLULAR_MANUFACTURE_ID_MAX_SIZE    ( 20U )
#endif

/**
 * @brief Cellular module ID max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 10
 */
#ifndef CELLULAR_MODEL_ID_MAX_SIZE
    #define CELLULAR_MODEL_ID_MAX_SIZE    ( 10U )
#endif

/**
 * @brief Cellular EDRX list max size.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 4
 */
#ifndef CELLULAR_EDRX_LIST_MAX_SIZE
    #define CELLULAR_EDRX_LIST_MAX_SIZE    ( 4U )
#endif

/**
 * @brief Cellular PDN context ID min value.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 1
 */
#ifndef CELLULAR_PDN_CONTEXT_ID_MIN
    #define CELLULAR_PDN_CONTEXT_ID_MIN    ( 1U )
#endif

/**
 * @brief Cellular PDN context ID max value.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 1
 */
#ifndef CELLULAR_PDN_CONTEXT_ID_MAX
    #define CELLULAR_PDN_CONTEXT_ID_MAX    ( 16U )
#endif

/**
 * @brief Cellular RAT ( radio access technology ) priority count.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 1
 */
#ifndef CELLULAR_MAX_RAT_PRIORITY_COUNT
    #define CELLULAR_MAX_RAT_PRIORITY_COUNT    ( 3U )
#endif

/**
 * @brief Cellular socket max send data length.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 1460
 */
#ifndef CELLULAR_MAX_SEND_DATA_LEN
    #define CELLULAR_MAX_SEND_DATA_LEN    ( 1460U )
#endif

/**
 * @brief Cellular socket max receive data length.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 1500
 */
#ifndef CELLULAR_MAX_RECV_DATA_LEN
    #define CELLULAR_MAX_RECV_DATA_LEN    ( 1500U )
#endif

/**
 * @brief Cellular module support getHostByName.<br>
 *
 * <b>Possible values:</b>`0 or 1`<br>
 * <b>Default value (if undefined):</b> 1
 */
#ifndef CELLULAR_SUPPORT_GETHOSTBYNAME
    #define CELLULAR_SUPPORT_GETHOSTBYNAME    ( 1U )
#endif

/**
 * @brief Cellular comm interface send timeout in MS.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 1000
 */
#ifndef CELLULAR_COMM_IF_SEND_TIMEOUT_MS
    #define CELLULAR_COMM_IF_SEND_TIMEOUT_MS    ( 1000U )
#endif

/**
 * @brief Cellular comm interface receive timeout in MS.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 1000
 */
#ifndef CELLULAR_COMM_IF_RECV_TIMEOUT_MS
    #define CELLULAR_COMM_IF_RECV_TIMEOUT_MS    ( 1000U )
#endif

/**
 * @brief FreeRTOS Cellular Library use static context.<br>
 *
 * <b>Possible values:</b>`0 or 1`<br>
 * <b>Default value (if undefined):</b> 0
 */
#ifndef CELLULAR_CONFIG_STATIC_ALLOCATION_CONTEXT
    #define CELLULAR_CONFIG_STATIC_ALLOCATION_CONTEXT    ( 0U )
#endif

/**
 * @brief Cellular comm interface use static context.<br>
 *
 * <b>Possible values:</b>`0 or 1`<br>
 * <b>Default value (if undefined):</b> 0
 */
#ifndef CELLULAR_CONFIG_STATIC_COMM_CONTEXT_ALLOCATION
    #define CELLULAR_CONFIG_STATIC_COMM_CONTEXT_ALLOCATION    ( 0U )
#endif

/**
 * @brief Default radio access technology.<br>
 *
 * <b>Possible values:</b>`Any value before CELLULAR_RAT_MAX` ( Reference : @ref CellularRat_t )<br>
 * <b>Default value (if undefined):</b> CELLULAR_RAT_CATM1
 */
#ifndef CELLULAR_CONFIG_DEFAULT_RAT
    #define CELLULAR_CONFIG_DEFAULT_RAT    ( 8 )   /* Set default RAT to CELLULAR_RAT_CATM1 @ref CellularRat_t. */
#endif

/**
 * @brief Cellular comm interface use static socket context.<br>
 *
 * <b>Possible values:</b>`0 or 1`<br>
 * <b>Default value (if undefined):</b> 0
 */
#ifndef CELLULAR_CONFIG_STATIC_SOCKET_CONTEXT_ALLOCATION
    #define CELLULAR_CONFIG_STATIC_SOCKET_CONTEXT_ALLOCATION    ( 0 )
#endif

/**
 * @brief Cellular common AT command timeout.<br>
 *
 * The timeout value for Cellular_Common prefix APIs. The timeout value should be
 * set according to spec. It should be long enough for AT command used in cellular
 * common APIs.
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 5000
 */
#ifndef CELLULAR_COMMON_AT_COMMAND_TIMEOUT_MS
    #define CELLULAR_COMMON_AT_COMMAND_TIMEOUT_MS    ( 5000U )
#endif

/**
 * @brief Cellular AT command raw timeout.<br>
 *
 * The timeout value for Cellular_ATCommandRaw API.
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 5000
 */
#ifndef CELLULAR_AT_COMMAND_RAW_TIMEOUT_MS
    #define CELLULAR_AT_COMMAND_RAW_TIMEOUT_MS    ( 5000U )
#endif

/**
 * @brief Cellular AT command response prefix string length.<br>
 *
 * The maximum length of AT command response prefix string.
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 32
 */
#ifndef CELLULAR_CONFIG_MAX_PREFIX_STRING_LENGTH
    #define CELLULAR_CONFIG_MAX_PREFIX_STRING_LENGTH    ( 32U )
#endif

/**
 * @brief Macro to check prefix leading char.<br>
 *
 * Cellular interface requires prefix string starts with "+". Some cellular modem
 * uses different leading char. This macro can be defined in cellular_config.h to
 * support different leading char.<br>
 *
 * <b>Default value (if undefined):</b> '+'
 *
 * For example:
 * > ^SMSO:(list of supported<fso>s)<br>
 * The prefix string contains <b>"^"</b> which is not default leading char for prefix
 * string. User can define this config to support this prefix string.
 */
#ifndef CELLULAR_CHECK_IS_PREFIX_LEADING_CHAR
    #define CELLULAR_CHECK_IS_PREFIX_LEADING_CHAR( x )    ( ( x ) == '+' )
#endif

/**
 * @brief Macro to check prefix chars.<br>
 *
 * The macro to check prefix string contains valid char. Modem with different prefix
 * strings can be supported with this config.<br>
 *
 * <b>Default value (if undefined):</b> alphabet, digit, '+' and '_'
 *
 * For example:
 * > +APP PDP: 0,ACTIVE<br>
 * The prefix string contains space which is not default valid char. User can define
 * this config to support this prefix string.
 */
#ifndef CELLULAR_CHECK_IS_PREFIX_CHAR
    #define CELLULAR_CHECK_IS_PREFIX_CHAR( inputChar )                    \
    ( ( ( ( int32_t ) isalpha( ( ( int8_t ) ( inputChar ) ) ) ) == 0 ) && \
      ( ( ( int32_t ) isdigit( ( ( int8_t ) ( inputChar ) ) ) ) == 0 ) && \
      ( ( inputChar ) != '_' ) &&                                         \
      ( !( CELLULAR_CHECK_IS_PREFIX_LEADING_CHAR( inputChar ) ) ) )
#endif

/**
 * @brief Cellular AT string length.<br>
 *
 * The maximum length of an AT string.<br>
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 256
 */
#ifndef CELLULAR_AT_MAX_STRING_SIZE
    #define CELLULAR_AT_MAX_STRING_SIZE    ( 256U )
#endif

/**
 * @brief Use AT+CCID command for Integrated Circuit Card ID( ICCID ) information.<br>
 *
 * Acquire ICCID with non-standard 3GPP command AT+CCID in Cellular_CommonGetSimCardInfo.<br>
 *
 * <b>Possible values:</b>`0 or 1`<br>
 * <b>Default value (if undefined):</b> 1
 */
#ifndef CELLULAR_CONFIG_USE_CCID_COMMAND
    #define CELLULAR_CONFIG_USE_CCID_COMMAND    1
#endif

/**
 * @brief Assert function for cellular interface.
 *
 * <b>Possible values:</b>`any assert function`<br>
 * <b>Default value (if undefined):</b> configASSERT
 */
#ifndef CELLULAR_CONFIG_ASSERT
    #define CELLULAR_CONFIG_ASSERT( X )    configASSERT( X )
#endif

/**
 * @brief Use FreeRTOS platform function for backward compatibility.<br>
 *
 * Define FreeRTOS platform function for cellular interface backward compatibility with version earlier
 * than v1.4.0.
 *
 * <b>Possible values:</b>`0 or 1`<br>
 * <b>Default value (if undefined):</b> 1
 */
#ifndef CELLULAR_CONFIG_PLATFORM_FREERTOS
    #define CELLULAR_CONFIG_PLATFORM_FREERTOS    1
#endif

#if CELLULAR_CONFIG_PLATFORM_FREERTOS
    #define PlatformQueueHandle_t    QueueHandle_t
    #define PlatformEventBits_t      EventBits_t
    #define PlatformBaseType_t       BaseType_t
    #define PlatformTickType_t       TickType_t
    #define platformTRUE             pdTRUE
    #define platformFALSE            pdFALSE
    #define platformPASS             pdPASS
    #define platformFAIL             pdFAIL
    #define platformMAX_DELAY        portMAX_DELAY
    #define PlatformQueue_Create     xQueueCreate
    #define PlatformQueue_Send       xQueueSend
    #define PlatformQueue_Receive    xQueueReceive
    #define PlatformQueue_Delete     vQueueDelete
#endif /* if CELLULAR_CONFIG_PLATFORM_FREERTOS */

/**
 * @brief Pktio read buffer size.
 *
 * The pktio read buffer size should be configured to greater than the maximum AT command
 * response size, which is typically the TCP socket receive command response packet size.
 *
 * <b>Possible values:</b>`Any positive integer`<br>
 * <b>Default value (if undefined):</b> 1600
 */
#ifndef CELLULAR_CONFIG_PKTIO_READ_BUFFER_SIZE
    #define CELLULAR_CONFIG_PKTIO_READ_BUFFER_SIZE    1600U
#endif

/**
 * @brief Macro that is called in the cellular library for logging "Error" level
 * messages.
 *
 * To enable error level logging in the cellular library, this macro should be mapped to the
 * application-specific logging implementation that supports error logging.
 *
 * @note This logging macro is called in the cellular library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to cellular_config.h files.
 *
 * <b>Default value</b>: Error logging is turned off, and no code is generated for calls
 * to the macro in the cellular library on compilation.
 */
#ifndef LogError
    #define LogError( message )
#endif

/**
 * @brief Macro that is called in the cellular library for logging "Warning" level
 * messages.
 *
 * To enable warning level logging in the cellular library, this macro should be mapped to the
 * application-specific logging implementation that supports warning logging.
 *
 * @note This logging macro is called in the cellular library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to cellular_config.h files.
 *
 * <b>Default value</b>: Warning logs are turned off, and no code is generated for calls
 * to the macro in the cellular library on compilation.
 */
#ifndef LogWarn
    #define LogWarn( message )
#endif

/**
 * @brief Macro that is called in the cellular library for logging "Info" level
 * messages.
 *
 * To enable info level logging in the cellular library, this macro should be mapped to the
 * application-specific logging implementation that supports info logging.
 *
 * @note This logging macro is called in the cellular library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to cellular_config.h files.
 *
 * <b>Default value</b>: Info logging is turned off, and no code is generated for calls
 * to the macro in the cellular library on compilation.
 */
#ifndef LogInfo
    #define LogInfo( message )
#endif

/**
 * @brief Macro that is called in the cellular library for logging "Debug" level
 * messages.
 *
 * To enable debug level logging from cellular library, this macro should be mapped to the
 * application-specific logging implementation that supports debug logging.
 *
 * @note This logging macro is called in the cellular library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to cellular_config.h files.
 *
 * <b>Default value</b>: Debug logging is turned off, and no code is generated for calls
 * to the macro in the cellular library on compilation.
 */
#ifndef LogDebug
    #define LogDebug( message )
#endif

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* __CELLULAR_CONFIG_DEFAULTS_H__ */
