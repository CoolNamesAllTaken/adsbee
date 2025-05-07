/*
 * AWS IoT Fleet Provisioning v1.2.1
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file fleet_provisioning.h
 * @brief Interface for the AWS IoT Fleet Provisioning Library.
 */

#ifndef FLEET_PROVISIONING_H_
#define FLEET_PROVISIONING_H_

/* Standard includes. */
#include <stdint.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* FLEET_PROVISIONING_DO_NOT_USE_CUSTOM_CONFIG allows building the Fleet
 * Provisioning library without a config file. If a config file is provided,
 * FLEET_PROVISIONING_DO_NOT_USE_CUSTOM_CONFIG macro must not be defined.
 */
#ifndef FLEET_PROVISIONING_DO_NOT_USE_CUSTOM_CONFIG
    #include "fleet_provisioning_config.h"
#endif

/* Default config values. */
#include "fleet_provisioning_config_defaults.h"

/**
 * @ingroup fleet_provisioning_enum_types
 * @brief Return codes for Fleet Provisioning APIs.
 */
typedef enum
{
    FleetProvisioningError = 0,
    FleetProvisioningSuccess,
    FleetProvisioningNoMatch,
    FleetProvisioningBadParameter,
    FleetProvisioningBufferTooSmall
} FleetProvisioningStatus_t;

/**
 * @ingroup fleet_provisioning_enum_types
 * @brief Fleet Provisioning topic values.
 */
typedef enum
{
    FleetProvisioningInvalidTopic = 0,
    FleetProvJsonCreateCertFromCsrPublish,
    FleetProvJsonCreateCertFromCsrAccepted,
    FleetProvJsonCreateCertFromCsrRejected,
    FleetProvJsonCreateKeysAndCertPublish,
    FleetProvJsonCreateKeysAndCertAccepted,
    FleetProvJsonCreateKeysAndCertRejected,
    FleetProvJsonRegisterThingPublish,
    FleetProvJsonRegisterThingAccepted,
    FleetProvJsonRegisterThingRejected,
    FleetProvCborCreateCertFromCsrPublish,
    FleetProvCborCreateCertFromCsrAccepted,
    FleetProvCborCreateCertFromCsrRejected,
    FleetProvCborCreateKeysAndCertPublish,
    FleetProvCborCreateKeysAndCertAccepted,
    FleetProvCborCreateKeysAndCertRejected,
    FleetProvCborRegisterThingPublish,
    FleetProvCborRegisterThingAccepted,
    FleetProvCborRegisterThingRejected
} FleetProvisioningTopic_t;

/**
 * @ingroup fleet_provisioning_enum_types
 * @brief Topics for each Fleet Provisioning APIs.
 */
typedef enum
{
    FleetProvisioningPublish,
    FleetProvisioningAccepted,
    FleetProvisioningRejected
} FleetProvisioningApiTopics_t;

/**
 * @ingroup fleet_provisioning_enum_types
 * @brief Message format for Fleet Provisioning APIs.
 */
typedef enum
{
    FleetProvisioningJson,
    FleetProvisioningCbor
} FleetProvisioningFormat_t;

/*-----------------------------------------------------------*/

/**
 * @ingroup fleet_provisioning_constants
 * @brief Maximum length of a thing's name as permitted by AWS IoT Core.
 */
#define FP_TEMPLATENAME_MAX_LENGTH    36U

/*-----------------------------------------------------------*/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore these macros as they are private.
 */

#define FP_CREATE_CERT_API_PREFIX           "$aws/certificates/create-from-csr/"
#define FP_CREATE_CERT_API_LENGTH_PREFIX    ( ( uint16_t ) ( sizeof( FP_CREATE_CERT_API_PREFIX ) - 1U ) )

#define FP_CREATE_KEYS_API_PREFIX           "$aws/certificates/create/"
#define FP_CREATE_KEYS_API_LENGTH_PREFIX    ( ( uint16_t ) ( sizeof( FP_CREATE_KEYS_API_PREFIX ) - 1U ) )

#define FP_REGISTER_API_PREFIX              "$aws/provisioning-templates/"
#define FP_REGISTER_API_LENGTH_PREFIX       ( ( uint16_t ) ( sizeof( FP_REGISTER_API_PREFIX ) - 1U ) )

#define FP_REGISTER_API_BRIDGE              "/provision/"
#define FP_REGISTER_API_LENGTH_BRIDGE       ( ( uint16_t ) ( sizeof( FP_REGISTER_API_BRIDGE ) - 1U ) )

#define FP_API_JSON_FORMAT                  "json"
#define FP_API_LENGTH_JSON_FORMAT           ( ( uint16_t ) ( sizeof( FP_API_JSON_FORMAT ) - 1U ) )

#define FP_API_CBOR_FORMAT                  "cbor"
#define FP_API_LENGTH_CBOR_FORMAT           ( ( uint16_t ) ( sizeof( FP_API_CBOR_FORMAT ) - 1U ) )

#define FP_API_ACCEPTED_SUFFIX              "/accepted"
#define FP_API_LENGTH_ACCEPTED_SUFFIX       ( ( uint16_t ) ( sizeof( FP_API_ACCEPTED_SUFFIX ) - 1U ) )

#define FP_API_REJECTED_SUFFIX              "/rejected"
#define FP_API_LENGTH_REJECTED_SUFFIX       ( ( uint16_t ) ( sizeof( FP_API_REJECTED_SUFFIX ) - 1U ) )

/** @endcond */

/*-----------------------------------------------------------*/

/* Fleet Provisioning CreateCertificateFromCSR macros */

/**
 * @brief Topic string for publishing a JSON CreateCertificateFromCSR request.
 */
#define FP_JSON_CREATE_CERT_PUBLISH_TOPIC \
    ( FP_CREATE_CERT_API_PREFIX           \
      FP_API_JSON_FORMAT )

/**
 * @brief Topic string for getting a JSON CreateCertificateFromCSR accepted response.
 */
#define FP_JSON_CREATE_CERT_ACCEPTED_TOPIC \
    ( FP_CREATE_CERT_API_PREFIX            \
      FP_API_JSON_FORMAT                   \
      FP_API_ACCEPTED_SUFFIX )

/**
 * @brief Topic string for getting a JSON CreateCertificateFromCSR error response.
 */
#define FP_JSON_CREATE_CERT_REJECTED_TOPIC \
    ( FP_CREATE_CERT_API_PREFIX            \
      FP_API_JSON_FORMAT                   \
      FP_API_REJECTED_SUFFIX )

/**
 * @brief Topic string for publishing a CBOR CreateCertificateFromCSR request.
 */
#define FP_CBOR_CREATE_CERT_PUBLISH_TOPIC \
    ( FP_CREATE_CERT_API_PREFIX           \
      FP_API_CBOR_FORMAT )

/**
 * @brief Topic string for getting a CBOR CreateCertificateFromCSR accepted response.
 */
#define FP_CBOR_CREATE_CERT_ACCEPTED_TOPIC \
    ( FP_CREATE_CERT_API_PREFIX            \
      FP_API_CBOR_FORMAT                   \
      FP_API_ACCEPTED_SUFFIX )

/**
 * @brief Topic string for getting a CBOR CreateCertificateFromCSR error response.
 */
#define FP_CBOR_CREATE_CERT_REJECTED_TOPIC \
    ( FP_CREATE_CERT_API_PREFIX            \
      FP_API_CBOR_FORMAT                   \
      FP_API_REJECTED_SUFFIX )

/**
 * @brief Length of topic string for publishing a JSON CreateCertificateFromCSR request.
 */
#define FP_JSON_CREATE_CERT_PUBLISH_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_JSON_CREATE_CERT_PUBLISH_TOPIC ) - 1U ) )

/**
 * @brief Length of topic string for getting a JSON CreateCertificateFromCSR accepted response.
 */
#define FP_JSON_CREATE_CERT_ACCEPTED_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_JSON_CREATE_CERT_ACCEPTED_TOPIC ) - 1U ) )

/**
 * @brief Length of topic string for getting a JSON CreateCertificateFromCSR error response.
 */
#define FP_JSON_CREATE_CERT_REJECTED_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_JSON_CREATE_CERT_REJECTED_TOPIC ) - 1U ) )

/**
 * @brief Length of topic string for publishing a CBOR CreateCertificateFromCSR request.
 */
#define FP_CBOR_CREATE_CERT_PUBLISH_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_CBOR_CREATE_CERT_PUBLISH_TOPIC ) - 1U ) )

/**
 * @brief Length of topic string for getting a CBOR CreateCertificateFromCSR accepted response.
 */
#define FP_CBOR_CREATE_CERT_ACCEPTED_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_CBOR_CREATE_CERT_ACCEPTED_TOPIC ) - 1U ) )

/**
 * @brief Length of topic string for getting a CBOR CreateCertificateFromCSR error response.
 */
#define FP_CBOR_CREATE_CERT_REJECTED_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_CBOR_CREATE_CERT_REJECTED_TOPIC ) - 1U ) )

/*-----------------------------------------------------------*/

/* Fleet Provisioning CreateKeysAndCertificate macros */

/**
 * @brief Topic string for publishing a JSON CreateKeysAndCertificate request.
 */
#define FP_JSON_CREATE_KEYS_PUBLISH_TOPIC \
    ( FP_CREATE_KEYS_API_PREFIX           \
      FP_API_JSON_FORMAT )

/**
 * @brief Topic string for getting a JSON CreateKeysAndCertificate accepted response.
 */
#define FP_JSON_CREATE_KEYS_ACCEPTED_TOPIC \
    ( FP_CREATE_KEYS_API_PREFIX            \
      FP_API_JSON_FORMAT                   \
      FP_API_ACCEPTED_SUFFIX )

/**
 * @brief Topic string for getting a JSON CreateKeysAndCertificate error
 * response.
 */
#define FP_JSON_CREATE_KEYS_REJECTED_TOPIC \
    ( FP_CREATE_KEYS_API_PREFIX            \
      FP_API_JSON_FORMAT                   \
      FP_API_REJECTED_SUFFIX )

/**
 * @brief Topic string for publishing a CBOR CreateKeysAndCertificate request.
 */
#define FP_CBOR_CREATE_KEYS_PUBLISH_TOPIC \
    ( FP_CREATE_KEYS_API_PREFIX           \
      FP_API_CBOR_FORMAT )

/**
 * @brief Topic string for getting a CBOR CreateKeysAndCertificate accepted response.
 */
#define FP_CBOR_CREATE_KEYS_ACCEPTED_TOPIC \
    ( FP_CREATE_KEYS_API_PREFIX            \
      FP_API_CBOR_FORMAT                   \
      FP_API_ACCEPTED_SUFFIX )

/**
 * @brief Topic string for getting a CBOR CreateKeysAndCertificate error
 * response.
 */
#define FP_CBOR_CREATE_KEYS_REJECTED_TOPIC \
    ( FP_CREATE_KEYS_API_PREFIX            \
      FP_API_CBOR_FORMAT                   \
      FP_API_REJECTED_SUFFIX )

/**
 * @brief Length of topic string for publishing a JSON CreateKeysAndCertificate request.
 */
#define FP_JSON_CREATE_KEYS_PUBLISH_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_JSON_CREATE_KEYS_PUBLISH_TOPIC ) - 1U ) )

/**
 * @brief Length of topic string for getting a JSON CreateKeysAndCertificate accepted response.
 */
#define FP_JSON_CREATE_KEYS_ACCEPTED_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_JSON_CREATE_KEYS_ACCEPTED_TOPIC ) - 1U ) )

/**
 * @brief Length of topic string for getting a JSON CreateKeysAndCertificate error response.
 */
#define FP_JSON_CREATE_KEYS_REJECTED_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_JSON_CREATE_KEYS_REJECTED_TOPIC ) - 1U ) )

/**
 * @brief Length of topic string for publishing a CBOR CreateKeysAndCertificate request.
 */
#define FP_CBOR_CREATE_KEYS_PUBLISH_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_CBOR_CREATE_KEYS_PUBLISH_TOPIC ) - 1U ) )

/**
 * @brief Length of topic string for getting a CBOR CreateKeysAndCertificate accepted response.
 */
#define FP_CBOR_CREATE_KEYS_ACCEPTED_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_CBOR_CREATE_KEYS_ACCEPTED_TOPIC ) - 1U ) )

/**
 * @brief Length of topic string for getting a CBOR CreateKeysAndCertificate error response.
 */
#define FP_CBOR_CREATE_KEYS_REJECTED_LENGTH \
    ( ( uint16_t ) ( sizeof( FP_CBOR_CREATE_KEYS_REJECTED_TOPIC ) - 1U ) )

/*-----------------------------------------------------------*/

/* Fleet Provisioning RegisterThing macros */


/**
 * @brief Topic string for publishing a JSON RegisterThing request.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateName The name of the provisioning template to use.
 */
#define FP_JSON_REGISTER_PUBLISH_TOPIC( templateName ) \
    ( FP_REGISTER_API_PREFIX                           \
      templateName                                     \
      FP_REGISTER_API_BRIDGE                           \
      FP_API_JSON_FORMAT )

/**
 * @brief Topic string for getting a JSON RegisterThing accepted response.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateName The name of the provisioning template to use.
 */
#define FP_JSON_REGISTER_ACCEPTED_TOPIC( templateName ) \
    ( FP_REGISTER_API_PREFIX                            \
      templateName                                      \
      FP_REGISTER_API_BRIDGE                            \
      FP_API_JSON_FORMAT                                \
      FP_API_ACCEPTED_SUFFIX )

/**
 * @brief Topic string for getting a JSON RegisterThing error response.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateName The name of the provisioning template to use.
 */
#define FP_JSON_REGISTER_REJECTED_TOPIC( templateName ) \
    ( FP_REGISTER_API_PREFIX                            \
      templateName                                      \
      FP_REGISTER_API_BRIDGE                            \
      FP_API_JSON_FORMAT                                \
      FP_API_REJECTED_SUFFIX )

/**
 * @brief Topic string for publishing a CBOR RegisterThing request.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateName The name of the provisioning template to use.
 */
#define FP_CBOR_REGISTER_PUBLISH_TOPIC( templateName ) \
    ( FP_REGISTER_API_PREFIX                           \
      templateName                                     \
      FP_REGISTER_API_BRIDGE                           \
      FP_API_CBOR_FORMAT )

/**
 * @brief Topic string for getting a CBOR RegisterThing accepted response.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateName The name of the provisioning template to use.
 */
#define FP_CBOR_REGISTER_ACCEPTED_TOPIC( templateName ) \
    ( FP_REGISTER_API_PREFIX                            \
      templateName                                      \
      FP_REGISTER_API_BRIDGE                            \
      FP_API_CBOR_FORMAT                                \
      FP_API_ACCEPTED_SUFFIX )

/**
 * @brief Topic string for getting a CBOR RegisterThing error response.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateName The name of the provisioning template to use.
 */
#define FP_CBOR_REGISTER_REJECTED_TOPIC( templateName ) \
    ( FP_REGISTER_API_PREFIX                            \
      templateName                                      \
      FP_REGISTER_API_BRIDGE                            \
      FP_API_CBOR_FORMAT                                \
      FP_API_REJECTED_SUFFIX )

/**
 * @brief Length of topic string for publishing a JSON RegisterThing request.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateNameLength The length of the provisioning template name.
 */
#define FP_JSON_REGISTER_PUBLISH_LENGTH( templateNameLength ) \
    ( FP_REGISTER_API_LENGTH_PREFIX +                         \
      ( templateNameLength ) +                                \
      FP_REGISTER_API_LENGTH_BRIDGE +                         \
      FP_API_LENGTH_JSON_FORMAT )

/**
 * @brief Length of topic string for getting a JSON RegisterThing accepted response.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateNameLength The length of the provisioning template name.
 */
#define FP_JSON_REGISTER_ACCEPTED_LENGTH( templateNameLength ) \
    ( FP_REGISTER_API_LENGTH_PREFIX +                          \
      ( templateNameLength ) +                                 \
      FP_REGISTER_API_LENGTH_BRIDGE +                          \
      FP_API_LENGTH_JSON_FORMAT +                              \
      FP_API_LENGTH_ACCEPTED_SUFFIX )

/**
 * @brief Length of topic string for getting a JSON RegisterThing error response.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateNameLength The length of the provisioning template name.
 */
#define FP_JSON_REGISTER_REJECTED_LENGTH( templateNameLength ) \
    ( FP_REGISTER_API_LENGTH_PREFIX +                          \
      ( templateNameLength ) +                                 \
      FP_REGISTER_API_LENGTH_BRIDGE +                          \
      FP_API_LENGTH_JSON_FORMAT +                              \
      FP_API_LENGTH_REJECTED_SUFFIX )

/**
 * @brief Length of topic string for publishing a CBOR RegisterThing request.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateNameLength The length of the provisioning template name.
 */
#define FP_CBOR_REGISTER_PUBLISH_LENGTH( templateNameLength ) \
    ( FP_REGISTER_API_LENGTH_PREFIX +                         \
      ( templateNameLength ) +                                \
      FP_REGISTER_API_LENGTH_BRIDGE +                         \
      FP_API_LENGTH_CBOR_FORMAT )

/**
 * @brief Length of topic string for getting a CBOR RegisterThing accepted response.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateNameLength The length of the provisioning template name.
 */
#define FP_CBOR_REGISTER_ACCEPTED_LENGTH( templateNameLength ) \
    ( FP_REGISTER_API_LENGTH_PREFIX +                          \
      ( templateNameLength ) +                                 \
      FP_REGISTER_API_LENGTH_BRIDGE +                          \
      FP_API_LENGTH_CBOR_FORMAT +                              \
      FP_API_LENGTH_ACCEPTED_SUFFIX )

/**
 * @brief Length of topic string for getting a CBOR RegisterThing error response.
 *
 * This macro should be used when the provisioning template name is known at
 * compile time. If the provisioning template name is not known at compile time,
 * the #FleetProvisioning_GetRegisterThingTopic API should be used instead.
 *
 * @param templateNameLength The length of the provisioning template name.
 */
#define FP_CBOR_REGISTER_REJECTED_LENGTH( templateNameLength ) \
    ( FP_REGISTER_API_LENGTH_PREFIX +                          \
      ( templateNameLength ) +                                 \
      FP_REGISTER_API_LENGTH_BRIDGE +                          \
      FP_API_LENGTH_CBOR_FORMAT +                              \
      FP_API_LENGTH_REJECTED_SUFFIX )

/*-----------------------------------------------------------*/

/* Key names for Fleet Provisioning MQTT API JSON/CBOR payloads. */

/**
 * @brief Key for the PEM-encoded certificate signing request in the
 * CreateCertificateFromCSR request payload.
 */
#define FP_API_CSR_KEY                "certificateSigningRequest"

/**
 * @brief Key for the certificate ownership token in the
 * CreateCertificateFromCSR and CreateKeysAndCertificate response payloads, and
 * the RegisterThing request payload.
 */
#define FP_API_OWNERSHIP_TOKEN_KEY    "certificateOwnershipToken"

/**
 * @brief Key for the certificate ID in the CreateCertificateFromCSR and
 * CreateKeysAndCertificate response payloads.
 */
#define FP_API_CERTIFICATE_ID_KEY     "certificateId"

/**
 * @brief Key for the PEM-encoded certificate in the CreateCertificateFromCSR
 * and CreateKeysAndCertificate response payloads.
 */
#define FP_API_CERTIFICATE_PEM_KEY    "certificatePem"

/**
 * @brief Key for the private key in the CreateKeysAndCertificate response
 * payload.
 */
#define FP_API_PRIVATE_KEY_KEY        "privateKey"

/**
 * @brief Key for the optional parameters in the RegisterThing request payload.
 */
#define FP_API_PARAMETERS_KEY         "parameters"

/**
 * @brief Key for the template-defined device configuration in the
 * RegisterThing response payload.
 */
#define FP_API_DEVICE_CONFIG_KEY      "deviceConfiguration"

/**
 * @brief Key for the name of the created AWS IoT Thing in the RegisterThing
 * response payload.
 */
#define FP_API_THING_NAME_KEY         "thingName"

/**
 * @brief Key for the status code in Fleet Provisioning error response
 * payloads.
 */
#define FP_API_STATUS_CODE_KEY        "statusCode"

/**
 * @brief Key for the error code in Fleet Provisioning error response payloads.
 */
#define FP_API_ERROR_CODE_KEY         "errorCode"

/**
 * @brief Key for the error message in Fleet Provisioning error response
 * payloads.
 */
#define FP_API_ERROR_MESSAGE_KEY      "errorMessage"

/*-----------------------------------------------------------*/

/**
 * @brief Populate the topic string for a Fleet Provisioning RegisterThing topic.
 *
 * @param[out] pTopicBuffer The buffer to write the topic string into.
 * @param[in] bufferLength The length of @p pTopicBuffer.
 * @param[in] format The desired RegisterThing format.
 * @param[in] topic The desired RegisterThing topic.
 * @param[in] pTemplateName The name of the provisioning template configured
 *     with AWS IoT.
 * @param[in] templateNameLength The length of the provisioning template name.
 * @param[out] pOutLength The length of the topic string written to the buffer.
 *
 * @return FleetProvisioningSuccess if the topic string is written to the buffer;
 * FleetProvisioningBadParameter if invalid parameters, such as non-RegisterThing topics, are passed;
 * FleetProvisioningBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * <b>example</b>
 * @code{c}
 *
 * // The following example shows how to use the FleetProvisioning_GetRegisterThingTopic
 * // function to generate a topic string for getting an accepted response for
 * // a JSON RegisterThing request.
 *
 * #define TOPIC_BUFFER_LENGTH      ( 256u )
 *
 * // In order to use the AWS IoT Fleet Provisioning service, there must be a
 * // provisioning template registered with AWS IoT Core.
 * // This example assumes that the template is named "template_name".
 * #define TEMPLATE_NAME "template_name"
 * #define TEMPLATE_NAME_LENGTH ( ( uint16_t ) ( sizeof( TEMPLATE_NAME ) - 1U )
 * char pTopicbuffer[ TOPIC_BUFFER_LENGTH ] = { 0 };
 * uint16_t topicLength = 0;
 * FleetProvisioningStatus_t status = FleetProvisioningError;
 *
 * status = FleetProvisioning_GetRegisterThingTopic( pTopicBuffer,
 *                                                   TOPIC_BUFFER_LENGTH,
 *                                                   FleetProvisioningJson,
 *                                                   FleetProvisioningAccepted,
 *                                                   TEMPLATE_NAME,
 *                                                   TEMPLATE_NAME_LENGTH,
 *                                                   &( topiclength ) );
 *
 * if( status == FleetProvisioningSuccess )
 * {
 *      // The buffer pTopicBuffer contains the topic string of length
 *      // topicLength for getting a response for an accepted JSON RegisterThing
 *      // request. Subscribe to this topic using an MQTT library of your choice.
 * }
 * @endcode
 */
/* @[declare_fleet_provisioning_getregisterthingtopic] */
FleetProvisioningStatus_t FleetProvisioning_GetRegisterThingTopic( char * pTopicBuffer,
                                                                   uint16_t bufferLength,
                                                                   FleetProvisioningFormat_t format,
                                                                   FleetProvisioningApiTopics_t topic,
                                                                   const char * pTemplateName,
                                                                   uint16_t templateNameLength,
                                                                   uint16_t * pOutLength );
/* @[declare_fleet_provisioning_getregisterthingtopic] */

/*-----------------------------------------------------------*/

/**
 * @brief Check if the given topic is one of the Fleet Provisioning topics.
 *
 * The function outputs which API the topic is for.
 *
 * @param[in] pTopic The topic string to check.
 * @param[in] topicLength The length of the topic string.
 * @param[out] pOutApi The Fleet Provisioning topic API value.
 *
 * @return FleetProvisioningSuccess if the topic is one of the Fleet Provisioning topics;
 * FleetProvisioningBadParameter if invalid parameters are passed;
 * FleetProvisioningNoMatch if the topic is NOT one of the Fleet Provisioning topics (parameter
 * pOutApi gets FleetProvisioningInvalidTopic).
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows how to use the FleetProvisioning_MatchTopic
 * // function to check if an incoming MQTT publish message is a Fleet
 * // Provisioning message.
 *
 * FleetProvisioningTopic_t api;
 * FleetProvisioningStatus_t status = FleetProvisioningError;
 *
 * // pTopic and topicLength are the topic string and length of the topic on
 * // which the publish message is received. These are usually provided by the
 * // MQTT library used.
 * status = FleetProvisioning_MatchTopic( pTopic
 *                                        topicLength,
 *                                        &( api ) );
 *
 * if( status == FleetProvisioningSuccess )
 * {
 *      if( api == FleetProvJsonCreateCertFromCsrAccepted )
 *      {
 *          // The published JSON request was accepted and completed by the AWS
 *          // IoT Fleet Provisioning service. You can parse the response using
 *          // your choice of JSON parser get the certificate, ID, and ownership
 *          // token.
 *      }
 *      else if( api == FleetProvJsonCreateCertFromCsrRejected )
 *      {
 *          // The published JSON request was rejected by the AWS IoT Fleet
 *          // Provisioning service.
 *      }
 *      else
 *      {
 *          // Unexpected response.
 *      }
 * }
 * @endcode
 */
/* @[declare_fleet_provisioning_matchtopic] */
FleetProvisioningStatus_t FleetProvisioning_MatchTopic( const char * pTopic,
                                                        uint16_t topicLength,
                                                        FleetProvisioningTopic_t * pOutApi );
/* @[declare_fleet_provisioning_matchtopic] */

/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* FLEET_PROVISIONING_H_ */
