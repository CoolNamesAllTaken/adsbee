/*
 * AWS IoT Device Shadow v1.4.1
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
 * @file shadow.c
 * @brief Implements the user-facing functions of the Shadow library.
 */

/* Standard includes. */
#include <string.h>

/* Shadow includes. */
#include "shadow.h"


/**
 * @brief Maximum shadow name length.
 * Refer to https://docs.aws.amazon.com/general/latest/gr/iot-core.html#device-shadow-limits
 * for more details about the Device Shadow limits.
 */
#define SHADOW_NAME_MAX_LENGTH               ( 64U )

/**
 * @brief Maximum thing name length.
 * Refer to https://docs.aws.amazon.com/general/latest/gr/iot-core.html#device-shadow-limits
 * for more details about the Device Shadow limits.
 */
#define SHADOW_THINGNAME_MAX_LENGTH          ( 128U )

/**
 * @brief The string representing "/shadow/update/accepted".
 */
#define SHADOW_OP_UPDATE_ACCEPTED            SHADOW_OP_UPDATE SHADOW_SUFFIX_ACCEPTED

/**
 * @brief The string representing "/shadow/update/rejected".
 */
#define SHADOW_OP_UPDATE_REJECTED            SHADOW_OP_UPDATE SHADOW_SUFFIX_REJECTED

/**
 * @brief The string representing "/shadow/update/delta".
 */
#define SHADOW_OP_UPDATE_DELTA               SHADOW_OP_UPDATE SHADOW_SUFFIX_DELTA

/**
 * @brief The string representing "/shadow/update/document".
 */
#define SHADOW_OP_UPDATE_DOCUMENTS           SHADOW_OP_UPDATE SHADOW_SUFFIX_DOCUMENTS

/**
 * @brief The string representing "/shadow/delete/accepted".
 */
#define SHADOW_OP_DELETE_ACCEPTED            SHADOW_OP_DELETE SHADOW_SUFFIX_ACCEPTED

/**
 * @brief The string representing "/shadow/delete/accepted".
 */
#define SHADOW_OP_DELETE_REJECTED            SHADOW_OP_DELETE SHADOW_SUFFIX_REJECTED

/**
 * @brief The string representing "/shadow/get/accepted".
 */
#define SHADOW_OP_GET_ACCEPTED               SHADOW_OP_GET SHADOW_SUFFIX_ACCEPTED

/**
 * @brief The string representing "/shadow/get/accepted".
 */
#define SHADOW_OP_GET_REJECTED               SHADOW_OP_GET SHADOW_SUFFIX_REJECTED

/**
 * @brief The length of "/shadow/update/accepted".
 */
#define SHADOW_OP_UPDATE_ACCEPTED_LENGTH     ( SHADOW_OP_UPDATE_LENGTH + SHADOW_SUFFIX_ACCEPTED_LENGTH )

/**
 * @brief The length of "/shadow/update/rejected".
 */
#define SHADOW_OP_UPDATE_REJECTED_LENGTH     ( SHADOW_OP_UPDATE_LENGTH + SHADOW_SUFFIX_REJECTED_LENGTH )

/**
 * @brief The length of "/shadow/update/document".
 */
#define SHADOW_OP_UPDATE_DOCUMENTS_LENGTH    ( SHADOW_OP_UPDATE_LENGTH + SHADOW_SUFFIX_DOCUMENTS_LENGTH )

/**
 * @brief The length of "/shadow/update/rejected".
 */
#define SHADOW_OP_UPDATE_DELTA_LENGTH        ( SHADOW_OP_UPDATE_LENGTH + SHADOW_SUFFIX_DELTA_LENGTH )

/**
 * @brief The length of "/shadow/get/accepted".
 */
#define SHADOW_OP_GET_ACCEPTED_LENGTH        ( SHADOW_OP_GET_LENGTH + SHADOW_SUFFIX_ACCEPTED_LENGTH )

/**
 * @brief The length of "/shadow/get/rejected".
 */
#define SHADOW_OP_GET_REJECTED_LENGTH        ( SHADOW_OP_GET_LENGTH + SHADOW_SUFFIX_REJECTED_LENGTH )

/**
 * @brief The length of "/shadow/get/accepted".
 */
#define SHADOW_OP_DELETE_ACCEPTED_LENGTH     ( SHADOW_OP_DELETE_LENGTH + SHADOW_SUFFIX_ACCEPTED_LENGTH )

/**
 * @brief The length of "/shadow/delete/rejected".
 */
#define SHADOW_OP_DELETE_REJECTED_LENGTH     ( SHADOW_OP_DELETE_LENGTH + SHADOW_SUFFIX_REJECTED_LENGTH )

/**
 * @brief Check if Shadow_MatchTopicString has valid parameters.
 *
 * @param[in] pTopic Pointer to the topic string.
 * @param[in] topicLength Length of pTopic.
 * @param[in] pMessageType Pointer to caller-supplied memory for returning the type of the shadow message.
 *
 * @return Return SHADOW_SUCCESS if the parameters are valid;
 *         return SHADOW_BAD_PARAMETER if not.
 */
static ShadowStatus_t validateMatchTopicParameters( const char * pTopic,
                                                    uint16_t topicLength,
                                                    const ShadowMessageType_t * pMessageType );

/**
 * @brief Check if Shadow_AssembleTopicString has valid parameters.
 *
 * @param[in]  topicType Shadow topic type.
 * @param[in]  pThingName Thing Name string.
 * @param[in]  thingNameLength Length of Thing Name string pointed to by pThingName.
 * @param[in]  pShadowName Shadow Name string.
 * @param[in]  shadowNameLength Length of Shadow Name string pointed to by pShadowName.
 * @param[in]  pTopicBuffer Pointer to the topic buffer.
 * @param[in]  pOutLength Pointer to the length of the topic created.
 *
 * @return Return SHADOW_SUCCESS if the parameters are valid;
 *         return SHADOW_BAD_PARAMETER if not.
 */
static ShadowStatus_t validateAssembleTopicParameters( ShadowTopicStringType_t topicType,
                                                       const char * pThingName,
                                                       uint8_t thingNameLength,
                                                       const char * pShadowName,
                                                       uint8_t shadowNameLength,
                                                       const char * pTopicBuffer,
                                                       const uint16_t * pOutLength );

/**
 * @brief Determine if the string contains the substring.
 *
 * @param[in] pString Pointer to the string.
 * @param[in] stringLength Length of pString.
 * @param[in] pSubString Pointer to the substring.
 * @param[in] subStringLength Length of pSubString.
 *
 * @return Return SHADOW_SUCCESS if it contains;
 *         return SHADOW_FAIL if not.
 */
static ShadowStatus_t containsSubString( const char * pString,
                                         uint16_t stringLength,
                                         const char * pSubString,
                                         uint16_t subStringLength );

/**
 * @brief Check if the Thing or Shadow Name is valid.
 *
 * @param[in] pString Pointer to the starting of a name.
 * @param[in] stringLength Length of pString.
 * @param[in] maxAllowedLength Maximum allowed length of the Thing or Shadow name.
 * @param[out] pNameLength Pointer to caller-supplied memory for returning the length of the Thing or Shadow Name.
 *
 * @return Return SHADOW_SUCCESS if it is valid;
 *         return SHADOW_FAIL if it is not.
 */
static ShadowStatus_t validateName( const char * pString,
                                    uint16_t stringLength,
                                    uint8_t maxAllowedLength,
                                    uint8_t * pNameLength );

/**
 * @brief Extract the Shadow message type from a string.
 *
 * @param[in] pString Pointer to the string.
 * @param[in] stringLength Length of pString.
 * @param[out] pMessageType Pointer to caller-supplied memory for returning the type of the shadow message.
 *
 * @return Return SHADOW_SUCCESS if successfully extracted;
 *         return SHADOW_MESSAGE_TYPE_PARSE_FAILED if failed.
 */
static ShadowStatus_t extractShadowMessageType( const char * pString,
                                                uint16_t stringLength,
                                                ShadowMessageType_t * pMessageType );

/**
 * @brief Extract the Thing name from a topic string.
 *
 * @param[in] pTopic Pointer to the topic string.
 * @param[in] topicLength Length of pTopic.
 * @param[in,out] pConsumedTopicLength Pointer to caller-supplied memory for returning the consumed topic length.
 * @param[out] pThingNameLength Pointer to caller-supplied memory for returning the Thing name length.
 *
 * @return Return SHADOW_SUCCESS if successfully extracted;
 *         return SHADOW_THINGNAME_PARSE_FAILED if Thing name parsing fails.
 */
static ShadowStatus_t extractThingName( const char * pTopic,
                                        uint16_t topicLength,
                                        uint16_t * pConsumedTopicLength,
                                        uint8_t * pThingNameLength );

/**
 * @brief Extract the classic shadow root OR the named shadow root and shadow name from a topic string.
 *
 * @param[in] pTopic Pointer to the topic string.
 * @param[in] topicLength Length of pTopic.
 * @param[in,out] pConsumedTopicLength Pointer to caller-supplied memory for returning the consumed topic length.
 * @param[out] pShadowNameLength Pointer to caller-supplied memory for returning the shadow name length.
 *
 * @return Return SHADOW_SUCCESS if successfully extracted;
 *         return SHADOW_ROOT_PARSE_FAILED shadow root parsing fails.
 *         return SHADOW_SHADOWNAME_PARSE_FAILED shadow name parsing fails.
 */
static ShadowStatus_t extractShadowRootAndName( const char * pTopic,
                                                uint16_t topicLength,
                                                uint16_t * pConsumedTopicLength,
                                                uint8_t * pShadowNameLength );

/**
 * @brief Get the shadow operation string for a given shadow topic type.
 *
 * @param[in] topicType The given shadow topic type.
 *
 * @return The shadow operation string for the given shadow type.
 */
static const char * getShadowOperationString( ShadowTopicStringType_t topicType );

/**
 * @brief Get the shadow operation string length for a given shadow topic type.
 *
 * @param[in] topicType The given shadow topic type.
 *
 * @return The shadow operation string length for the given shadow type.
 */
static uint16_t getShadowOperationLength( ShadowTopicStringType_t topicType );

/**
 * @brief Creates a shadow topic string
 *
 * @param[in] topicType The type of shadow topic to be constructed.
 * @param[in] pThingName Pointer to the Thing name.
 * @param[in] thingNameLength The length of the Thing name.
 * @param[in] pShadowName Pointer to the Shadow name.
 * @param[in] shadowNameLength The length of the Shadow name.
 * @param[out] pTopicBuffer Pointer to caller-supplied memory for returning the constructed shadow topic string.
 */
static void createShadowTopicString( ShadowTopicStringType_t topicType,
                                     const char * pThingName,
                                     uint8_t thingNameLength,
                                     const char * pShadowName,
                                     uint8_t shadowNameLength,
                                     char * pTopicBuffer );

/*-----------------------------------------------------------*/

static ShadowStatus_t validateMatchTopicParameters( const char * pTopic,
                                                    uint16_t topicLength,
                                                    const ShadowMessageType_t * pMessageType )
{
    ShadowStatus_t shadowStatus = SHADOW_SUCCESS;

    if( ( pTopic == NULL ) ||
        ( topicLength == 0U ) ||
        ( pMessageType == NULL ) )
    {
        shadowStatus = SHADOW_BAD_PARAMETER;
        LogError( ( "Invalid input parameters pTopic: %p, topicLength: %u, pMessageType: %p.",
                    ( const void * ) pTopic,
                    ( unsigned int ) topicLength,
                    ( const void * ) pMessageType ) );
    }

    return shadowStatus;
}

/*-----------------------------------------------------------*/

static ShadowStatus_t validateAssembleTopicParameters( ShadowTopicStringType_t topicType,
                                                       const char * pThingName,
                                                       uint8_t thingNameLength,
                                                       const char * pShadowName,
                                                       uint8_t shadowNameLength,
                                                       const char * pTopicBuffer,
                                                       const uint16_t * pOutLength )
{
    ShadowStatus_t shadowStatus = SHADOW_BAD_PARAMETER;

    if( ( pTopicBuffer == NULL ) ||
        ( pThingName == NULL ) ||
        ( thingNameLength == 0U ) ||
        ( ( pShadowName == NULL ) && ( shadowNameLength > 0U ) ) ||
        ( topicType >= ShadowTopicStringTypeMaxNum ) ||
        ( pOutLength == NULL ) )
    {
        LogError( ( "Invalid input parameters pTopicBuffer: %p, pThingName: %p, thingNameLength: %u,\
                    pShadowName: %p, shadowNameLength: %u, topicType: %d, pOutLength: %p.",
                    ( const void * ) pTopicBuffer,
                    ( const void * ) pThingName,
                    ( unsigned int ) thingNameLength,
                    ( const void * ) pShadowName,
                    ( unsigned int ) shadowNameLength,
                    ( int ) topicType,
                    ( const void * ) pOutLength ) );
    }
    else if( thingNameLength > SHADOW_THINGNAME_MAX_LENGTH )
    {
        LogError( ( "Invalid thingNamelength. Thing name length of %u exceeds maximum allowed length %u.",
                    ( unsigned int ) thingNameLength,
                    ( unsigned int ) SHADOW_THINGNAME_MAX_LENGTH ) );
    }
    else if( shadowNameLength > SHADOW_NAME_MAX_LENGTH )
    {
        LogError( ( "Invalid shadowNameLength. Shadow name length of %u exceeds maximum allowed length %u.",
                    ( unsigned int ) shadowNameLength,
                    ( unsigned int ) SHADOW_NAME_MAX_LENGTH ) );
    }
    else
    {
        /* Validations passed .*/
        shadowStatus = SHADOW_SUCCESS;
    }

    return shadowStatus;
}

/*-----------------------------------------------------------*/

static ShadowStatus_t containsSubString( const char * pString,
                                         uint16_t stringLength,
                                         const char * pSubString,
                                         uint16_t subStringLength )
{
    ShadowStatus_t returnStatus = SHADOW_FAIL;

    /* The string must be at least as long as the substring to contain it
     * completely. */
    if( stringLength >= subStringLength )
    {
        /* We are only checking up to subStringLength characters in the original
        * string. The string may be longer and contain additional characters. */
        if( strncmp( pString, pSubString, ( size_t ) subStringLength ) == 0 )
        {
            returnStatus = SHADOW_SUCCESS;
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static ShadowStatus_t validateName( const char * pString,
                                    uint16_t stringLength,
                                    uint8_t maxAllowedLength,
                                    uint8_t * pNameLength )
{
    uint16_t index = 0U;
    ShadowStatus_t returnStatus = SHADOW_FAIL;
    uint8_t parsedName = 0U;

    for( ; index < stringLength; index++ )
    {
        /* The name should always be terminated by a forward slash */
        if( pString[ index ] == ( char ) '/' )
        {
            parsedName = 1U;
            break;
        }
    }

    if( parsedName == 1U )
    {
        if( index == 0U )
        {
            LogDebug( ( "Not a Shadow topic. Unable to find a %s name in the topic.",
                        ( maxAllowedLength == SHADOW_THINGNAME_MAX_LENGTH ) ? "Thing" : "Shadow" ) );
        }
        else if( index > maxAllowedLength )
        {
            LogDebug( ( "Not a Shadow topic. Extracted %s name length of %u exceeds maximum allowed length %u.",
                        ( maxAllowedLength == SHADOW_THINGNAME_MAX_LENGTH ) ? "Thing" : "Shadow",
                        ( unsigned int ) index,
                        ( unsigned int ) maxAllowedLength ) );
        }
        else
        {
            /* Only accept names of greater than zero length.
             * The variable `index` will not exceed the 8 bit integer width here
             * since it will be lesser than the 8 bit integer `maxAllowedLength`. */
            *pNameLength = ( uint8_t ) index;
            returnStatus = SHADOW_SUCCESS;
        }
    }
    else
    {
        LogDebug( ( "Not a Shadow topic. Unable to find a %s name in the topic.",
                    ( maxAllowedLength == SHADOW_THINGNAME_MAX_LENGTH ) ? "Thing" : "Shadow" ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static ShadowStatus_t extractThingName( const char * pTopic,
                                        uint16_t topicLength,
                                        uint16_t * pConsumedTopicLength,
                                        uint8_t * pThingNameLength )
{
    /* Extract thing name. */
    ShadowStatus_t shadowStatus = validateName( &( pTopic[ *pConsumedTopicLength ] ),
                                                topicLength - *pConsumedTopicLength,
                                                SHADOW_THINGNAME_MAX_LENGTH,
                                                pThingNameLength );

    if( shadowStatus != SHADOW_SUCCESS )
    {
        shadowStatus = SHADOW_THINGNAME_PARSE_FAILED;
    }
    else
    {
        *pConsumedTopicLength += *pThingNameLength;
    }

    return shadowStatus;
}

/*-----------------------------------------------------------*/

static ShadowStatus_t extractShadowRootAndName( const char * pTopic,
                                                uint16_t topicLength,
                                                uint16_t * pConsumedTopicLength,
                                                uint8_t * pShadowNameLength )
{
    /* Look for the named shadow root */
    ShadowStatus_t shadowStatus = containsSubString( &( pTopic[ *pConsumedTopicLength ] ),
                                                     topicLength - *pConsumedTopicLength,
                                                     SHADOW_NAMED_ROOT,
                                                     SHADOW_NAMED_ROOT_LENGTH );

    if( shadowStatus == SHADOW_SUCCESS )
    {
        /* Topic is a named shadow */
        *pConsumedTopicLength += SHADOW_NAMED_ROOT_LENGTH;

        /* Extract shadow name. */
        shadowStatus = validateName( &( pTopic[ *pConsumedTopicLength ] ),
                                     topicLength - *pConsumedTopicLength,
                                     SHADOW_NAME_MAX_LENGTH,
                                     pShadowNameLength );

        if( shadowStatus != SHADOW_SUCCESS )
        {
            shadowStatus = SHADOW_SHADOWNAME_PARSE_FAILED;
        }
        else
        {
            *pConsumedTopicLength += *pShadowNameLength;
        }
    }
    else
    {
        /* Not a named shadow. Try to match the classic shadow root. */
        shadowStatus = containsSubString( &( pTopic[ *pConsumedTopicLength ] ),
                                          topicLength - *pConsumedTopicLength,
                                          SHADOW_CLASSIC_ROOT,
                                          SHADOW_CLASSIC_ROOT_LENGTH );

        if( shadowStatus == SHADOW_SUCCESS )
        {
            *pConsumedTopicLength += SHADOW_CLASSIC_ROOT_LENGTH;
        }
        else
        {
            shadowStatus = SHADOW_ROOT_PARSE_FAILED;
            LogDebug( ( "Not a Shadow topic. Failed to parse shadow root in pTopic %.*s", topicLength, pTopic ) );
        }
    }

    return shadowStatus;
}

/*-----------------------------------------------------------*/

static ShadowStatus_t extractShadowMessageType( const char * pString,
                                                uint16_t stringLength,
                                                ShadowMessageType_t * pMessageType )
{
    uint32_t index = 0U;
    ShadowStatus_t returnStatus = SHADOW_FAIL;

    /* Lookup table for Shadow message string. */
    static const char * const pMessageStrings[ ShadowMessageTypeMaxNum ] =
    {
        SHADOW_OP_GET_ACCEPTED,
        SHADOW_OP_GET_REJECTED,
        SHADOW_OP_DELETE_ACCEPTED,
        SHADOW_OP_DELETE_REJECTED,
        SHADOW_OP_UPDATE_ACCEPTED,
        SHADOW_OP_UPDATE_REJECTED,
        SHADOW_OP_UPDATE_DOCUMENTS,
        SHADOW_OP_UPDATE_DELTA
    };

    /* Lookup table for Shadow message string length. */
    static const uint16_t pMessageStringsLength[ ShadowMessageTypeMaxNum ] =
    {
        SHADOW_OP_GET_ACCEPTED_LENGTH,
        SHADOW_OP_GET_REJECTED_LENGTH,
        SHADOW_OP_DELETE_ACCEPTED_LENGTH,
        SHADOW_OP_DELETE_REJECTED_LENGTH,
        SHADOW_OP_UPDATE_ACCEPTED_LENGTH,
        SHADOW_OP_UPDATE_REJECTED_LENGTH,
        SHADOW_OP_UPDATE_DOCUMENTS_LENGTH,
        SHADOW_OP_UPDATE_DELTA_LENGTH
    };

    /* Lookup table for Shadow message types. */
    static const ShadowMessageType_t pMessageTypes[ ShadowMessageTypeMaxNum ] =
    {
        ShadowMessageTypeGetAccepted,
        ShadowMessageTypeGetRejected,
        ShadowMessageTypeDeleteAccepted,
        ShadowMessageTypeDeleteRejected,
        ShadowMessageTypeUpdateAccepted,
        ShadowMessageTypeUpdateRejected,
        ShadowMessageTypeUpdateDocuments,
        ShadowMessageTypeUpdateDelta
    };

    for( ; index < ( uint32_t ) ( sizeof( pMessageStrings ) / sizeof( pMessageStrings[ 0 ] ) ); index++ )
    {
        returnStatus = containsSubString( pString,
                                          stringLength,
                                          pMessageStrings[ index ],
                                          pMessageStringsLength[ index ] );

        /* If the operation string matches, there must not be any other extra
         * character remaining in the string. */
        if( returnStatus == SHADOW_SUCCESS )
        {
            if( stringLength != pMessageStringsLength[ index ] )
            {
                returnStatus = SHADOW_FAIL;
            }
            else
            {
                *pMessageType = pMessageTypes[ index ];
                break;
            }
        }
    }

    if( returnStatus != SHADOW_SUCCESS )
    {
        LogDebug( ( "Not a Shadow topic. Failed to match shadow message type in pString %.*s", stringLength, pString ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static const char * getShadowOperationString( ShadowTopicStringType_t topicType )
{
    const char * shadowOperationString = NULL;

    switch( topicType )
    {
        case ShadowTopicStringTypeGet:
            shadowOperationString = SHADOW_OP_GET;
            break;

        case ShadowTopicStringTypeGetAccepted:
            shadowOperationString = SHADOW_OP_GET_ACCEPTED;
            break;

        case ShadowTopicStringTypeGetRejected:
            shadowOperationString = SHADOW_OP_GET_REJECTED;
            break;

        case ShadowTopicStringTypeDelete:
            shadowOperationString = SHADOW_OP_DELETE;
            break;

        case ShadowTopicStringTypeDeleteAccepted:
            shadowOperationString = SHADOW_OP_DELETE_ACCEPTED;
            break;

        case ShadowTopicStringTypeDeleteRejected:
            shadowOperationString = SHADOW_OP_DELETE_REJECTED;
            break;

        case ShadowTopicStringTypeUpdate:
            shadowOperationString = SHADOW_OP_UPDATE;
            break;

        case ShadowTopicStringTypeUpdateAccepted:
            shadowOperationString = SHADOW_OP_UPDATE_ACCEPTED;
            break;

        case ShadowTopicStringTypeUpdateRejected:
            shadowOperationString = SHADOW_OP_UPDATE_REJECTED;
            break;

        case ShadowTopicStringTypeUpdateDocuments:
            shadowOperationString = SHADOW_OP_UPDATE_DOCUMENTS;
            break;

        case ShadowTopicStringTypeUpdateDelta:
        /* topicType >= ShadowTopicStringTypeMaxNum check is covered at entry of Shadow_AssembleTopicString. */
        default:
            shadowOperationString = SHADOW_OP_UPDATE_DELTA;
            break;
    }

    return shadowOperationString;
}

/*-----------------------------------------------------------*/

static uint16_t getShadowOperationLength( ShadowTopicStringType_t topicType )
{
    uint16_t shadowOperationLength = 0U;

    switch( topicType )
    {
        case ShadowTopicStringTypeGet:
            shadowOperationLength = SHADOW_OP_GET_LENGTH;
            break;

        case ShadowTopicStringTypeGetAccepted:
            shadowOperationLength = SHADOW_OP_GET_ACCEPTED_LENGTH;
            break;

        case ShadowTopicStringTypeGetRejected:
            shadowOperationLength = SHADOW_OP_GET_REJECTED_LENGTH;
            break;

        case ShadowTopicStringTypeDelete:
            shadowOperationLength = SHADOW_OP_DELETE_LENGTH;
            break;

        case ShadowTopicStringTypeDeleteAccepted:
            shadowOperationLength = SHADOW_OP_DELETE_ACCEPTED_LENGTH;
            break;

        case ShadowTopicStringTypeDeleteRejected:
            shadowOperationLength = SHADOW_OP_DELETE_REJECTED_LENGTH;
            break;

        case ShadowTopicStringTypeUpdate:
            shadowOperationLength = SHADOW_OP_UPDATE_LENGTH;
            break;

        case ShadowTopicStringTypeUpdateAccepted:
            shadowOperationLength = SHADOW_OP_UPDATE_ACCEPTED_LENGTH;
            break;

        case ShadowTopicStringTypeUpdateRejected:
            shadowOperationLength = SHADOW_OP_UPDATE_REJECTED_LENGTH;
            break;

        case ShadowTopicStringTypeUpdateDocuments:
            shadowOperationLength = SHADOW_OP_UPDATE_DOCUMENTS_LENGTH;
            break;

        case ShadowTopicStringTypeUpdateDelta:
        /* topicType >= ShadowTopicStringTypeMaxNum check is covered at entry of Shadow_AssembleTopicString. */
        default:
            shadowOperationLength = SHADOW_OP_UPDATE_DELTA_LENGTH;
            break;
    }

    return shadowOperationLength;
}

/*-----------------------------------------------------------*/

static void createShadowTopicString( ShadowTopicStringType_t topicType,
                                     const char * pThingName,
                                     uint8_t thingNameLength,
                                     const char * pShadowName,
                                     uint8_t shadowNameLength,
                                     char * pTopicBuffer )
{
    uint16_t offset = 0U, operationStringLength = 0U;
    const char * pShadowPrefix = SHADOW_PREFIX;
    const char * pOperationString = NULL;
    const char * pClassicShadowRoot = SHADOW_CLASSIC_ROOT;
    const char * pNamedShadowRoot = SHADOW_NAMED_ROOT;

    /* Copy the Shadow topic prefix into the topic buffer. */
    ( void ) memcpy( ( void * ) pTopicBuffer,
                     ( const void * ) pShadowPrefix,
                     ( size_t ) SHADOW_PREFIX_LENGTH );
    offset = ( uint16_t ) ( offset + SHADOW_PREFIX_LENGTH );

    /* Copy the Thing Name into the topic buffer. */
    ( void ) memcpy( ( void * ) &( pTopicBuffer[ offset ] ),
                     ( const void * ) pThingName,
                     ( size_t ) thingNameLength );
    offset = ( uint16_t ) ( offset + thingNameLength );

    /* Are we assembling a named shadow? */
    if( shadowNameLength > 0U )
    {
        /* Copy the named Shadow topic root into the topic buffer. */
        ( void ) memcpy( ( void * ) &( pTopicBuffer[ offset ] ),
                         ( const void * ) pNamedShadowRoot,
                         ( size_t ) SHADOW_NAMED_ROOT_LENGTH );
        offset = ( uint16_t ) ( offset + SHADOW_NAMED_ROOT_LENGTH );

        /* Copy the Shadow Name into the topic buffer. */
        ( void ) memcpy( ( void * ) &( pTopicBuffer[ offset ] ),
                         ( const void * ) pShadowName,
                         ( size_t ) shadowNameLength );
        offset = ( uint16_t ) ( offset + shadowNameLength );
    }
    else
    {
        /* Copy the Classic Shadow topic root into the topic buffer. */
        ( void ) memcpy( ( void * ) &( pTopicBuffer[ offset ] ),
                         ( const void * ) pClassicShadowRoot,
                         ( size_t ) SHADOW_CLASSIC_ROOT_LENGTH );
        offset = ( uint16_t ) ( offset + SHADOW_CLASSIC_ROOT_LENGTH );
    }

    pOperationString = getShadowOperationString( topicType );
    operationStringLength = getShadowOperationLength( topicType );
    /* Copy the Shadow operation string into the topic buffer. */
    ( void ) memcpy( ( void * ) &( pTopicBuffer[ offset ] ),
                     ( const void * ) pOperationString,
                     ( size_t ) operationStringLength );
}

/*-----------------------------------------------------------*/

ShadowStatus_t Shadow_MatchTopicString( const char * pTopic,
                                        uint16_t topicLength,
                                        ShadowMessageType_t * pMessageType,
                                        const char ** pThingName,
                                        uint8_t * pThingNameLength,
                                        const char ** pShadowName,
                                        uint8_t * pShadowNameLength )
{
    uint16_t consumedTopicLength = 0U;
    ShadowStatus_t shadowStatus = SHADOW_SUCCESS;
    uint8_t thingNameLength = 0;
    uint8_t shadowNameLength = 0;

    shadowStatus = validateMatchTopicParameters( pTopic, topicLength, pMessageType );

    /* A shadow topic string takes one of the two forms.
     * Classic shadow:
     *   $aws/things/<thingName>/shadow/<operation>
     *   $aws/things/<thingName>/shadow/<operation>/<suffix>
     * Named shadow:
     *   $aws/things/<thingName>/shadow/name/<shadowName>/<operation>
     *   $aws/things/<thingName>/shadow/name/<shadowName>/<operation>/<suffix>
     *
     * We need to match the following things:
     * 1. Prefix ($aws/things).
     * 2. Thing Name.
     * 3. Classic shadow root (/shadow) OR Named shadow root (/shadow/name) and shadow name
     * 4. Shadow operation and suffix.
     */
    if( shadowStatus == SHADOW_SUCCESS )
    {
        /* First match the prefix. */
        shadowStatus = containsSubString( &( pTopic[ consumedTopicLength ] ),
                                          topicLength - consumedTopicLength,
                                          SHADOW_PREFIX,
                                          SHADOW_PREFIX_LENGTH );

        if( shadowStatus == SHADOW_SUCCESS )
        {
            consumedTopicLength += SHADOW_PREFIX_LENGTH;
        }
        else
        {
            LogDebug( ( "Not a Shadow topic. Failed to parse shadow topic prefix in pTopic %.*s", topicLength, pTopic ) );
        }
    }

    if( shadowStatus == SHADOW_SUCCESS )
    {
        /* Extract thing name. */
        shadowStatus = extractThingName( pTopic,
                                         topicLength,
                                         &consumedTopicLength,
                                         &thingNameLength );
    }

    if( shadowStatus == SHADOW_SUCCESS )
    {
        shadowStatus = extractShadowRootAndName( pTopic,
                                                 topicLength,
                                                 &consumedTopicLength,
                                                 &shadowNameLength );
    }

    if( shadowStatus == SHADOW_SUCCESS )
    {
        /* Extract shadow message type. */
        shadowStatus = extractShadowMessageType( &( pTopic[ consumedTopicLength ] ),
                                                 topicLength - consumedTopicLength,
                                                 pMessageType );

        if( shadowStatus != SHADOW_SUCCESS )
        {
            shadowStatus = SHADOW_MESSAGE_TYPE_PARSE_FAILED;
            LogDebug( ( "Not a Shadow topic. Shadow message type is not in pTopic %.*s, failed to parse shadow message type.", topicLength, pTopic ) );
        }
    }

    if( shadowStatus == SHADOW_SUCCESS )
    {
        /* Update the out parameters if we successfully matched the topic. */
        if( pThingName != NULL )
        {
            /* Thing name comes after shadow prefix. */
            *pThingName = &( pTopic[ SHADOW_PREFIX_LENGTH ] );
        }

        if( pThingNameLength != NULL )
        {
            *pThingNameLength = thingNameLength;
        }

        if( pShadowName != NULL )
        {
            *pShadowName = &( pTopic[ SHADOW_PREFIX_LENGTH + thingNameLength +
                                      SHADOW_NAMED_ROOT_LENGTH ] );
        }

        if( pShadowNameLength != NULL )
        {
            *pShadowNameLength = shadowNameLength;
        }
    }

    return shadowStatus;
}

/*-----------------------------------------------------------*/

ShadowStatus_t Shadow_AssembleTopicString( ShadowTopicStringType_t topicType,
                                           const char * pThingName,
                                           uint8_t thingNameLength,
                                           const char * pShadowName,
                                           uint8_t shadowNameLength,
                                           char * pTopicBuffer,
                                           uint16_t bufferSize,
                                           uint16_t * pOutLength )
{
    uint16_t generatedTopicStringLength = 0U;

    ShadowStatus_t shadowStatus = validateAssembleTopicParameters( topicType,
                                                                   pThingName,
                                                                   thingNameLength,
                                                                   pShadowName,
                                                                   shadowNameLength,
                                                                   pTopicBuffer,
                                                                   pOutLength );

    if( shadowStatus == SHADOW_SUCCESS )
    {
        generatedTopicStringLength = SHADOW_PREFIX_LENGTH +        /* Prefix ("$aws/things/"). */
                                     thingNameLength +             /* Thing name. */
                                     ( ( shadowNameLength > 0U ) ? /* Handle named or classic shadow */
                                       ( SHADOW_NAMED_ROOT_LENGTH + shadowNameLength ) :
                                       SHADOW_CLASSIC_ROOT_LENGTH ) +
                                     getShadowOperationLength( topicType ); /* Shadow operation. */

        if( bufferSize < generatedTopicStringLength )
        {
            shadowStatus = SHADOW_BUFFER_TOO_SMALL;
            LogError( ( "Input bufferSize too small, bufferSize %u, required %u.",
                        ( unsigned int ) bufferSize,
                        ( unsigned int ) generatedTopicStringLength ) );
        }
    }

    if( shadowStatus == SHADOW_SUCCESS )
    {
        /* With everything validated, now create the topic string */
        createShadowTopicString( topicType,
                                 pThingName,
                                 thingNameLength,
                                 pShadowName,
                                 shadowNameLength,
                                 pTopicBuffer );

        /* Return the generated topic string length to the caller. */
        *pOutLength = generatedTopicStringLength;
    }

    return shadowStatus;
}
/*-----------------------------------------------------------*/

ShadowStatus_t Shadow_MatchTopic( const char * pTopic,
                                  uint16_t topicLength,
                                  ShadowMessageType_t * pMessageType,
                                  const char ** pThingName,
                                  uint16_t * pThingNameLength )
{
    /* Shadow_MatchTopicString takes a pointer to a 8 bit unsigned integer for
     * output parameter Thing name length, whereas Shadow_MatchTopic takes a
     * pointer to a 16 bit integer. The maximum possible Thing name length is
     * 128 bytes and hence unsigned 8 bit integer is large enough to hold the
     * Thing name length. Refer to #SHADOW_THINGNAME_MAX_LENGTH for more details.
     * Passing a pointer to 16 bit integer directly to Shadow_MatchTopicString
     * may create data inconsistencies depending on the byte ordering in the
     * device platform. Hence, a local variable of 8 bit integer width is used for
     * the call to Shadow_MatchTopicString, and its value is copied to the 16 bit
     * integer pointer passed to Shadow_MatchTopic. */
    uint8_t thingNameLength = 0U;
    ShadowStatus_t shadowStatus = Shadow_MatchTopicString( pTopic,
                                                           topicLength,
                                                           pMessageType,
                                                           pThingName,
                                                           &thingNameLength,
                                                           NULL,
                                                           NULL );

    /* Update the output parameter for Thing name length. */
    if( pThingNameLength != NULL )
    {
        *pThingNameLength = thingNameLength;
    }

    return shadowStatus;
}
