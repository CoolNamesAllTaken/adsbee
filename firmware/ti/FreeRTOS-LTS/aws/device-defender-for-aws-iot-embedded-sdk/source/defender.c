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
 * @file defender.c
 * @brief Implementation of the AWS IoT Device Defender Client Library.
 */

/* Standard includes. */

#include <assert.h>
#include <stddef.h>
#include <string.h>

/* Defender API include. */
#include "defender.h"

/**
 * @brief Get the topic length for a given defender API.
 *
 * @param[in] thingNameLength The length of the thing name as registered with AWS IoT.
 * @param[in] api The defender API value.
 *
 * @return The topic length for the given defender API.
 */
static uint16_t getTopicLength( uint16_t thingNameLength,
                                DefenderTopic_t api );

/**
 * @brief Write the format and suffix part for the given defender API to the buffer.
 *
 * Format: json or cbor.
 * Suffix: /accepted or /rejected or empty.
 *
 * @param[in] pBuffer The buffer to write the format and suffix part into.
 * @param[in] api The defender API value.
 *
 * @note This function assumes that the buffer is large enough to hold the
 * value.
 */
static void writeFormatAndSuffix( char * pBuffer,
                                  DefenderTopic_t api );

/**
 * @brief Check if the unparsed topic so far starts with the defender prefix.
 *
 * The defender prefix is "$aws/things/".
 *
 * @param[in] pRemainingTopic Starting location of the unparsed topic.
 * @param[in] remainingTopicLength The length of the unparsed topic.
 *
 * @return #DefenderSuccess if the unparsed topic starts with the defender
 * prefix; #DefenderNoMatch otherwise.
 */
static DefenderStatus_t matchPrefix( const char * pRemainingTopic,
                                     uint16_t remainingTopicLength );

/**
 * @brief Extract the length of thing name in the unparsed topic so far.
 *
 * The end of thing name is marked by a forward slash. A zero length thing name
 * is not valid.
 *
 * This function extracts the same thing name from the following topic strings:
 *   - $aws/things/THING_NAME/defender/metrics/json
 *   - $aws/things/THING_NAME
 * The second topic is not a valid defender topic and the matching will fail
 * when we try to match the bridge part.
 *
 * @param[in] pRemainingTopic Starting location of the unparsed topic.
 * @param[in] remainingTopicLength The length of the unparsed topic.
 * @param[out] pOutThingNameLength The length of the thing name in the topic string.
 *
 * @return #DefenderSuccess if a valid thing name is found; #DefenderNoMatch
 * otherwise.
 */
static DefenderStatus_t extractThingNameLength( const char * pRemainingTopic,
                                                uint16_t remainingTopicLength,
                                                uint16_t * pOutThingNameLength );

/**
 * @brief Check if the unparsed topic so far starts with the defender bridge.
 *
 * The defender bridge is "/defender/metrics/".
 *
 * @param[in] pRemainingTopic Starting location of the unparsed topic.
 * @param[in] remainingTopicLength The length of the unparsed topic.
 *
 * @return #DefenderSuccess if the unparsed topic starts with the defender
 * bridge; #DefenderNoMatch otherwise.
 */
static DefenderStatus_t matchBridge( const char * pRemainingTopic,
                                     uint16_t remainingTopicLength );

/**
 * @brief Check if the unparsed topic so far exactly matches one of the defender
 * api topics.
 *
 * The defender api topics are the following:
 *   - json
 *   - json/accepted
 *   - json/rejected
 *   - cbor
 *   - cbor/accepted
 *   - cbor/rejected
 *
 * The function also outputs the defender API value if a match is found.
 *
 * @param[in] pRemainingTopic Starting location of the unparsed topic.
 * @param[in] remainingTopicLength The length of the unparsed topic.
 * @param[out] pOutApi The defender topic API value.
 *
 * @return #DefenderSuccess if the unparsed topic exactly matches one of the
 * defender api topics; #DefenderNoMatch otherwise.
 */
static DefenderStatus_t matchApi( const char * pRemainingTopic,
                                  uint16_t remainingTopicLength,
                                  DefenderTopic_t * pOutApi );
/*-----------------------------------------------------------*/

static uint16_t getTopicLength( uint16_t thingNameLength,
                                DefenderTopic_t api )
{
    uint16_t topicLength = 0U;

    assert( ( thingNameLength != 0U ) && ( thingNameLength <= DEFENDER_THINGNAME_MAX_LENGTH ) );
    assert( ( api > DefenderInvalidTopic ) && ( api < DefenderMaxTopic ) );

    switch( api )
    {
        case DefenderJsonReportPublish:
            topicLength = DEFENDER_API_LENGTH_JSON_PUBLISH( thingNameLength );
            break;

        case DefenderJsonReportAccepted:
            topicLength = DEFENDER_API_LENGTH_JSON_ACCEPTED( thingNameLength );
            break;

        case DefenderJsonReportRejected:
            topicLength = DEFENDER_API_LENGTH_JSON_REJECTED( thingNameLength );
            break;

        case DefenderCborReportPublish:
            topicLength = DEFENDER_API_LENGTH_CBOR_PUBLISH( thingNameLength );
            break;

        case DefenderCborReportAccepted:
            topicLength = DEFENDER_API_LENGTH_CBOR_ACCEPTED( thingNameLength );
            break;

        /* The default is here just to silence compiler warnings in a way which
         * does not bring coverage down. The assert at the beginning of this
         * function ensures that the only api value hitting this case can be
         * DefenderCborReportRejected. */
        case DefenderCborReportRejected:
        default:
            topicLength = DEFENDER_API_LENGTH_CBOR_REJECTED( thingNameLength );
            break;
    }

    return topicLength;
}
/*-----------------------------------------------------------*/

static void writeFormatAndSuffix( char * pBuffer,
                                  DefenderTopic_t api )
{
    /* The following variables are to address MISRA Rule 7.4 violation of
     * passing const char * for const void * param of memcpy. */
    const char * pDefenderApiJsonFormat = DEFENDER_API_JSON_FORMAT;
    const char * pDefenderApiCborFormat = DEFENDER_API_CBOR_FORMAT;
    const char * pDefenderApiAcceptedSuffix = DEFENDER_API_ACCEPTED_SUFFIX;
    const char * pDefenderApiRejectedSuffix = DEFENDER_API_REJECTED_SUFFIX;

    assert( pBuffer != NULL );
    assert( ( api > DefenderInvalidTopic ) && ( api < DefenderMaxTopic ) );

    switch( api )
    {
        case DefenderJsonReportPublish:
            ( void ) memcpy( ( void * ) pBuffer,
                             ( const void * ) pDefenderApiJsonFormat,
                             ( size_t ) DEFENDER_API_LENGTH_JSON_FORMAT );
            break;

        case DefenderJsonReportAccepted:
            ( void ) memcpy( ( void * ) pBuffer,
                             ( const void * ) pDefenderApiJsonFormat,
                             ( size_t ) DEFENDER_API_LENGTH_JSON_FORMAT );
            ( void ) memcpy( ( void * ) &( pBuffer[ DEFENDER_API_LENGTH_JSON_FORMAT ] ),
                             ( const void * ) pDefenderApiAcceptedSuffix,
                             ( size_t ) DEFENDER_API_LENGTH_ACCEPTED_SUFFIX );
            break;

        case DefenderJsonReportRejected:
            ( void ) memcpy( ( void * ) pBuffer,
                             ( const void * ) pDefenderApiJsonFormat,
                             DEFENDER_API_LENGTH_JSON_FORMAT );
            ( void ) memcpy( ( void * ) &( pBuffer[ DEFENDER_API_LENGTH_JSON_FORMAT ] ),
                             ( const void * ) pDefenderApiRejectedSuffix,
                             ( size_t ) DEFENDER_API_LENGTH_REJECTED_SUFFIX );
            break;

        case DefenderCborReportPublish:
            ( void ) memcpy( ( void * ) pBuffer,
                             ( const void * ) pDefenderApiCborFormat,
                             ( size_t ) DEFENDER_API_LENGTH_CBOR_FORMAT );
            break;

        case DefenderCborReportAccepted:
            ( void ) memcpy( ( void * ) pBuffer,
                             ( const void * ) pDefenderApiCborFormat,
                             DEFENDER_API_LENGTH_CBOR_FORMAT );
            ( void ) memcpy( ( void * ) &( pBuffer[ DEFENDER_API_LENGTH_CBOR_FORMAT ] ),
                             ( const void * ) pDefenderApiAcceptedSuffix,
                             ( size_t ) DEFENDER_API_LENGTH_ACCEPTED_SUFFIX );
            break;

        /* The default is here just to silence compiler warnings in a way which
         * does not bring coverage down. The assert at the beginning of this
         * function ensures that the only api value hitting this case can be
         * DefenderCborReportRejected. */
        case DefenderCborReportRejected:
        default:
            ( void ) memcpy( ( void * ) pBuffer,
                             ( const void * ) pDefenderApiCborFormat,
                             ( size_t ) DEFENDER_API_LENGTH_CBOR_FORMAT );
            ( void ) memcpy( ( void * ) &( pBuffer[ DEFENDER_API_LENGTH_CBOR_FORMAT ] ),
                             ( const void * ) pDefenderApiRejectedSuffix,
                             ( size_t ) DEFENDER_API_LENGTH_REJECTED_SUFFIX );
            break;
    }
}
/*-----------------------------------------------------------*/

static DefenderStatus_t matchPrefix( const char * pRemainingTopic,
                                     uint16_t remainingTopicLength )
{
    DefenderStatus_t ret = DefenderNoMatch;

    assert( pRemainingTopic != NULL );

    if( remainingTopicLength >= DEFENDER_API_LENGTH_PREFIX )
    {
        if( strncmp( pRemainingTopic,
                     DEFENDER_API_PREFIX,
                     ( size_t ) DEFENDER_API_LENGTH_PREFIX ) == 0 )
        {
            ret = DefenderSuccess;
        }
    }

    return ret;
}
/*-----------------------------------------------------------*/

static DefenderStatus_t extractThingNameLength( const char * pRemainingTopic,
                                                uint16_t remainingTopicLength,
                                                uint16_t * pOutThingNameLength )
{
    DefenderStatus_t ret = DefenderNoMatch;
    uint16_t i = 0U;

    assert( pRemainingTopic != NULL );
    assert( pOutThingNameLength != NULL );

    /* Find the first forward slash. It marks the end of the thing name. */
    for( i = 0U; i < remainingTopicLength; i++ )
    {
        if( pRemainingTopic[ i ] == '/' )
        {
            break;
        }
    }

    /* Zero length thing name is not valid. */
    if( i > 0U )
    {
        *pOutThingNameLength = i;
        ret = DefenderSuccess;
    }

    return ret;
}
/*-----------------------------------------------------------*/

static DefenderStatus_t matchBridge( const char * pRemainingTopic,
                                     uint16_t remainingTopicLength )
{
    DefenderStatus_t ret = DefenderNoMatch;

    assert( pRemainingTopic != NULL );

    if( remainingTopicLength >= DEFENDER_API_LENGTH_BRIDGE )
    {
        if( strncmp( pRemainingTopic,
                     DEFENDER_API_BRIDGE,
                     ( size_t ) DEFENDER_API_LENGTH_BRIDGE ) == 0 )
        {
            ret = DefenderSuccess;
        }
    }

    return ret;
}
/*-----------------------------------------------------------*/

static DefenderStatus_t matchApi( const char * pRemainingTopic,
                                  uint16_t remainingTopicLength,
                                  DefenderTopic_t * pOutApi )
{
    DefenderStatus_t ret = DefenderNoMatch;
    uint16_t i = 0U;
    /* Table of defender APIs. */
    static const DefenderTopic_t defenderApi[] =
    {
        DefenderJsonReportPublish,
        DefenderJsonReportAccepted,
        DefenderJsonReportRejected,
        DefenderCborReportPublish,
        DefenderCborReportAccepted,
        DefenderCborReportRejected,
    };
    /* Table of topic API strings in the same order as the above defenderApi table. */
    static const char * const defenderApiTopic[] =
    {
        DEFENDER_API_JSON_FORMAT,
        DEFENDER_API_JSON_FORMAT DEFENDER_API_ACCEPTED_SUFFIX,
        DEFENDER_API_JSON_FORMAT DEFENDER_API_REJECTED_SUFFIX,
        DEFENDER_API_CBOR_FORMAT,
        DEFENDER_API_CBOR_FORMAT DEFENDER_API_ACCEPTED_SUFFIX,
        DEFENDER_API_CBOR_FORMAT DEFENDER_API_REJECTED_SUFFIX,
    };
    /* Table of topic API string lengths in the same order as the above defenderApi table. */
    static const uint16_t defenderApiTopicLength[] =
    {
        DEFENDER_API_LENGTH_JSON_FORMAT,
        DEFENDER_API_LENGTH_JSON_FORMAT + DEFENDER_API_LENGTH_ACCEPTED_SUFFIX,
        DEFENDER_API_LENGTH_JSON_FORMAT + DEFENDER_API_LENGTH_REJECTED_SUFFIX,
        DEFENDER_API_LENGTH_CBOR_FORMAT,
        DEFENDER_API_LENGTH_CBOR_FORMAT + DEFENDER_API_LENGTH_ACCEPTED_SUFFIX,
        DEFENDER_API_LENGTH_CBOR_FORMAT + DEFENDER_API_LENGTH_REJECTED_SUFFIX,
    };

    for( i = 0U; i < ( sizeof( defenderApi ) / sizeof( defenderApi[ 0 ] ) ); i++ )
    {
        if( ( remainingTopicLength == defenderApiTopicLength[ i ] ) &&
            ( strncmp( pRemainingTopic,
                       defenderApiTopic[ i ],
                       ( size_t ) defenderApiTopicLength[ i ] ) == 0 ) )
        {
            *pOutApi = defenderApi[ i ];
            ret = DefenderSuccess;

            break;
        }
    }

    return ret;
}
/*-----------------------------------------------------------*/

DefenderStatus_t Defender_GetTopic( char * pBuffer,
                                    uint16_t bufferLength,
                                    const char * pThingName,
                                    uint16_t thingNameLength,
                                    DefenderTopic_t api,
                                    uint16_t * pOutLength )
{
    DefenderStatus_t ret = DefenderSuccess;
    uint16_t topicLength = 0U, offset = 0U;

    /* The following variables are to address MISRA Rule 7.4 violation of
     * passing const char * for const void * param of memcpy. */
    const char * pDefenderApiPrefix = DEFENDER_API_PREFIX;
    const char * pDefenderApiBridge = DEFENDER_API_BRIDGE;

    if( ( pBuffer == NULL ) ||
        ( pThingName == NULL ) ||
        ( thingNameLength == 0U ) || ( thingNameLength > DEFENDER_THINGNAME_MAX_LENGTH ) ||
        ( api <= DefenderInvalidTopic ) || ( api >= DefenderMaxTopic ) ||
        ( pOutLength == NULL ) )
    {
        ret = DefenderBadParameter;

        LogError( ( "Invalid input parameter. pBuffer: %p, bufferLength: %u, "
                    "pThingName: %p, thingNameLength: %u, api: %d, pOutLength: %p.",
                    ( const void * ) pBuffer,
                    ( unsigned int ) bufferLength,
                    ( const void * ) pThingName,
                    ( unsigned int ) thingNameLength,
                    api,
                    ( void * ) pOutLength ) );
    }

    if( ret == DefenderSuccess )
    {
        topicLength = getTopicLength( thingNameLength, api );

        if( bufferLength < topicLength )
        {
            ret = DefenderBufferTooSmall;

            LogError( ( "The buffer is too small to hold the topic string. "
                        "Provided buffer size: %u, Required buffer size: %u.",
                        ( unsigned int ) bufferLength,
                        ( unsigned int ) topicLength ) );
        }
    }

    if( ret == DefenderSuccess )
    {
        /* At this point, it is certain that we have a large enough buffer to
         * write the topic string into. */

        /* Write prefix first. */
        ( void ) memcpy( ( void * ) &( pBuffer[ offset ] ),
                         ( const void * ) pDefenderApiPrefix,
                         ( size_t ) DEFENDER_API_LENGTH_PREFIX );
        offset += DEFENDER_API_LENGTH_PREFIX;

        /* Write thing name next. */
        ( void ) memcpy( ( void * ) &( pBuffer[ offset ] ),
                         ( const void * ) pThingName,
                         ( size_t ) thingNameLength );
        offset += thingNameLength;

        /* Write bridge next. */
        ( void ) memcpy( ( void * ) &( pBuffer[ offset ] ),
                         ( const void * ) pDefenderApiBridge,
                         ( size_t ) DEFENDER_API_LENGTH_BRIDGE );
        offset += DEFENDER_API_LENGTH_BRIDGE;

        /* Write report format and suffix. */
        writeFormatAndSuffix( &( pBuffer[ offset ] ), api );

        *pOutLength = topicLength;
    }

    return ret;
}
/*-----------------------------------------------------------*/

DefenderStatus_t Defender_MatchTopic( const char * pTopic,
                                      uint16_t topicLength,
                                      DefenderTopic_t * pOutApi,
                                      const char ** ppOutThingName,
                                      uint16_t * pOutThingNameLength )
{
    DefenderStatus_t ret = DefenderSuccess;
    uint16_t remainingTopicLength = 0U, consumedTopicLength = 0U, thingNameLength = 0U;

    if( ( pTopic == NULL ) || ( pOutApi == NULL ) )
    {
        ret = DefenderBadParameter;
        LogError( ( "Invalid input parameter. pTopic: %p, pOutApi: %p.",
                    ( const void * ) pTopic,
                    ( void * ) pOutApi ) );
    }

    /* Nothing is consumed yet. */
    remainingTopicLength = topicLength;
    consumedTopicLength = 0;

    if( ret == DefenderSuccess )
    {
        ret = matchPrefix( &( pTopic[ consumedTopicLength ] ),
                           remainingTopicLength );

        if( ret == DefenderSuccess )
        {
            remainingTopicLength -= DEFENDER_API_LENGTH_PREFIX;
            consumedTopicLength += DEFENDER_API_LENGTH_PREFIX;
        }
        else
        {
            LogDebug( ( "The topic does not contain defender prefix $aws/things/." ) );
        }
    }

    if( ret == DefenderSuccess )
    {
        ret = extractThingNameLength( &( pTopic[ consumedTopicLength ] ),
                                      remainingTopicLength,
                                      &( thingNameLength ) );

        if( ret == DefenderSuccess )
        {
            remainingTopicLength -= thingNameLength;
            consumedTopicLength += thingNameLength;
        }
        else
        {
            LogDebug( ( "The topic does not contain a valid thing name." ) );
        }
    }

    if( ret == DefenderSuccess )
    {
        ret = matchBridge( &( pTopic[ consumedTopicLength ] ),
                           remainingTopicLength );

        if( ret == DefenderSuccess )
        {
            remainingTopicLength -= DEFENDER_API_LENGTH_BRIDGE;
            consumedTopicLength += DEFENDER_API_LENGTH_BRIDGE;
        }
        else
        {
            LogDebug( ( "The topic does not contain the defender bridge /defender/metrics/." ) );
        }
    }

    if( ret == DefenderSuccess )
    {
        ret = matchApi( &( pTopic[ consumedTopicLength ] ),
                        remainingTopicLength,
                        pOutApi );

        if( ret != DefenderSuccess )
        {
            LogDebug( ( "The topic does not contain valid report format or suffix "
                        " needed to be a valid defender topic." ) );
        }
    }

    /* Update the out parameters for thing name and thing length location, if we
     * successfully matched the topic. */
    if( ret == DefenderSuccess )
    {
        if( ppOutThingName != NULL )
        {
            /* Thing name comes after the defender prefix. */
            *ppOutThingName = &( pTopic[ DEFENDER_API_LENGTH_PREFIX ] );
        }

        if( pOutThingNameLength != NULL )
        {
            *pOutThingNameLength = thingNameLength;
        }
    }

    /* Update the output parameter for API if the topic did not match. In case
     * of a match, it is updated in the matchApi function. */
    if( ret == DefenderNoMatch )
    {
        *pOutApi = DefenderInvalidTopic;
    }

    return ret;
}
/*-----------------------------------------------------------*/
