/*
 * AWS IoT Jobs v1.5.1
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
 * @file jobs.h
 * @brief Client library APIs for the AWS IoT Jobs service.
 *
 * https://docs.aws.amazon.com/iot/latest/developerguide/jobs-api.html#jobs-mqtt-api
 */

#ifndef JOBS_H_
#define JOBS_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/**
 * @ingroup jobs_constants
 * @brief  Size of Topic Buffer
 */
#define TOPIC_BUFFER_SIZE            256U

/**
 * @ingroup jobs_constants
 * @brief Size of Jobs Start Next Message Buffer
 */
#define START_JOB_MSG_LENGTH         147U

/**
 * @ingroup jobs_constants
 * @brief Size of Jobs Update Message Buffer
 */
#define UPDATE_JOB_MSG_LENGTH        48U

/**
 * @ingroup jobs_constants
 * @brief Maximum length of a thing name for the AWS IoT Jobs Service.
 */
#define JOBS_THINGNAME_MAX_LENGTH    128U      /* per AWS IoT API Reference */

/**
 * @ingroup jobs_constants
 * @brief Maximum length of a job ID for the AWS IoT Jobs Service.
 */
#define JOBS_JOBID_MAX_LENGTH        64U       /* per AWS IoT API Reference */

#ifndef THINGNAME_MAX_LENGTH

/**
 * @brief User defined maximum length of a thing name for the application.
 *
 * <br><b>Default value</b>: @ref JOBS_THINGNAME_MAX_LENGTH "JOBS_THINGNAME_MAX_LENGTH"
 */
    #define THINGNAME_MAX_LENGTH    JOBS_THINGNAME_MAX_LENGTH
#endif

#ifndef JOBID_MAX_LENGTH

/**
 * @brief User defined maximum length of a job ID for the application.
 *
 * <br><b>Default value</b>: @ref JOBS_JOBID_MAX_LENGTH "JOBS_JOBID_MAX_LENGTH"
 */
    #define JOBID_MAX_LENGTH    JOBS_JOBID_MAX_LENGTH
#endif

#if ( THINGNAME_MAX_LENGTH > JOBS_THINGNAME_MAX_LENGTH )
    #error "The value of THINGNAME_MAX_LENGTH exceeds the AWS IoT Jobs Service limit."
#endif

#if ( JOBID_MAX_LENGTH > JOBS_JOBID_MAX_LENGTH )
    #error "The value of JOBID_MAX_LENGTH exceeds the AWS IoT Jobs Service limit."
#endif

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore these macros as they are private.
 */

#define JOBS_API_PREFIX                     "$aws/things/"
#define JOBS_API_PREFIX_LENGTH              ( sizeof( JOBS_API_PREFIX ) - 1U )

#define JOBS_API_BRIDGE                     "/jobs/"
#define JOBS_API_BRIDGE_LENGTH              ( sizeof( JOBS_API_BRIDGE ) - 1U )

#define JOBS_API_SUCCESS                    "/accepted"
#define JOBS_API_SUCCESS_LENGTH             ( sizeof( JOBS_API_SUCCESS ) - 1U )

#define JOBS_API_FAILURE                    "/rejected"
#define JOBS_API_FAILURE_LENGTH             ( sizeof( JOBS_API_FAILURE ) - 1U )

#define JOBS_API_JOBSCHANGED                "notify"
#define JOBS_API_JOBSCHANGED_LENGTH         ( sizeof( JOBS_API_JOBSCHANGED ) - 1U )

#define JOBS_API_NEXTJOBCHANGED             "notify-next"
#define JOBS_API_NEXTJOBCHANGED_LENGTH      ( sizeof( JOBS_API_NEXTJOBCHANGED ) - 1U )

#define JOBS_API_GETPENDING                 "get"
#define JOBS_API_GETPENDING_LENGTH          ( sizeof( JOBS_API_GETPENDING ) - 1U )

#define JOBS_API_STARTNEXT                  "start-next"
#define JOBS_API_STARTNEXT_LENGTH           ( sizeof( JOBS_API_STARTNEXT ) - 1U )

#define JOBS_API_DESCRIBE                   "get"
#define JOBS_API_DESCRIBE_LENGTH            ( sizeof( JOBS_API_DESCRIBE ) - 1U )

#define JOBS_API_UPDATE                     "update"
#define JOBS_API_UPDATE_LENGTH              ( sizeof( JOBS_API_UPDATE ) - 1U )

#define JOBS_API_JOBID_NEXT                 "$next"
#define JOBS_API_JOBID_NEXT_LENGTH          ( sizeof( JOBS_API_JOBID_NEXT ) - 1U )

#define JOBS_API_JOBID_NULL                 ""
#define JOBS_API_LEVEL_SEPARATOR            "/"

#define JOBS_API_CLIENTTOKEN                "{\"clientToken\":\""
#define JOBS_API_CLIENTTOKEN_LENGTH         ( sizeof( JOBS_API_CLIENTTOKEN ) - 1U )

#define JOBS_API_STATUS                     "{\"status\":\""
#define JOBS_API_STATUS_LENGTH              ( sizeof( JOBS_API_STATUS ) - 1U )

#define JOBS_API_EXPECTED_VERSION           "\",\"expectedVersion\":\""
#define JOBS_API_EXPECTED_VERSION_LENGTH    ( sizeof( JOBS_API_EXPECTED_VERSION ) - 1U )

#define JOBS_API_COMMON_LENGTH( thingNameLength ) \
    ( JOBS_API_PREFIX_LENGTH + ( thingNameLength ) + JOBS_API_BRIDGE_LENGTH )

/** @endcond */


/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this macro as it is private.
 */

/* AWS IoT Jobs API topics. */
#define JOBS_TOPIC_COMMON( thingName, jobId, jobsApi ) \
    ( JOBS_API_PREFIX                                  \
      thingName                                        \
      JOBS_API_BRIDGE                                  \
      jobId                                            \
      jobsApi )
/** @endcond */

/**
 * @ingroup jobs_constants
 * @brief Topic string for subscribing to the NextJobExecutionChanged API.
 *
 * This macro should be used when the thing name is known at the compile time.
 * If the thing name is not known at compile time, the #Jobs_GetTopic API
 * should be used instead.
 *
 * @param thingName The thing name as registered with AWS IoT Core.
 */
#define JOBS_API_SUBSCRIBE_NEXTJOBCHANGED( thingName ) \
    JOBS_TOPIC_COMMON( thingName, JOBS_API_JOBID_NULL, JOBS_API_NEXTJOBCHANGED )

/**
 * @ingroup jobs_constants
 * @brief Topic string for subscribing to the JobExecutionsChanged API.
 *
 * This macro should be used when the thing name is known at the compile time.
 * If the thing name is not known at compile time, the #Jobs_GetTopic API
 * should be used instead.
 *
 * @param thingName The thing name as registered with AWS IoT Core.
 */
#define JOBS_API_SUBSCRIBE_JOBSCHANGED( thingName ) \
    JOBS_TOPIC_COMMON( thingName, JOBS_API_JOBID_NULL, JOBS_API_JOBSCHANGED )

/**
 * @ingroup jobs_constants
 * @brief Topic string for publishing to the StartNextPendingJobExecution API.
 *
 * This macro should be used when the thing name is known at the compile time.
 * If the thing name is not known at compile time, the #Jobs_StartNext API
 * should be used instead.
 *
 * @param thingName The thing name as registered with AWS IoT Core.
 */
#define JOBS_API_PUBLISH_STARTNEXT( thingName ) \
    JOBS_TOPIC_COMMON( thingName, JOBS_API_JOBID_NULL, JOBS_API_STARTNEXT )

/**
 * @ingroup jobs_constants
 * @brief Topic string for publishing to the GetPendingJobExecutions API.
 *
 * This macro should be used when the thing name is known at the compile time.
 * If the thing name is not known at compile time, the #Jobs_GetPending API
 * should be used instead.
 *
 * @param thingName The thing name as registered with AWS IoT Core.
 */
#define JOBS_API_PUBLISH_GETPENDING( thingName ) \
    JOBS_TOPIC_COMMON( thingName, JOBS_API_JOBID_NULL, JOBS_API_GETPENDING )

/**
 * @ingroup jobs_constants
 * @brief Topic string for querying the next pending job from the
 * DescribeJobExecution API.
 *
 * This macro should be used when the thing name and jobID are known at the
 * compile time. If next pending job is being queried, use $next as job ID.
 * If the thing name or job ID are not known at compile time, the #Jobs_Describe API
 * should be used instead.
 *
 * @param thingName The thing name as registered with AWS IoT Core.
 */
#define JOBS_API_PUBLISH_DESCRIBENEXTJOB( thingName ) \
    JOBS_TOPIC_COMMON( thingName, JOBS_API_JOBID_NEXT JOBS_API_LEVEL_SEPARATOR, JOBS_API_DESCRIBE )

/**
 * @ingroup jobs_constants
 * @brief The size needed to hold the longest topic for a given thing name length.
 * @note This includes space for a terminating NUL character.
 */
#define JOBS_API_MAX_LENGTH( thingNameLength )                    \
    ( JOBS_API_COMMON_LENGTH( thingNameLength ) +                 \
      JOBID_MAX_LENGTH + sizeof( '/' ) + JOBS_API_UPDATE_LENGTH + \
      JOBS_API_SUCCESS_LENGTH + 1U )

/**
 * @ingroup jobs_enum_types
 * @brief Return codes from jobs functions.
 */
typedef enum
{
    JobsError = 0,
    JobsSuccess,       /**< @brief The buffer was properly written or a match was found. */
    JobsNoMatch,       /**< @brief The buffer does not contain a jobs topic. */
    JobsBadParameter,  /**< @brief A function parameter was NULL or has an illegal value. */
    JobsBufferTooSmall /**< @brief The buffer write was truncated. */
} JobsStatus_t;

/**
 * @brief Status codes for jobs
 */
typedef enum
{
    Queued,
    InProgress,
    Failed,
    Succeeded,
    Rejected
} JobCurrentStatus_t;

/**
 * @brief Status codes for job update status
 */
typedef enum
{
    JobUpdateStatus_Accepted,
    JobUpdateStatus_Rejected
} JobUpdateStatus_t;

/**
 * @ingroup jobs_enum_types
 * @brief Topic values for subscription requests.
 *
 * @note The enum values for valid topics must be contiguous,
 * starting with 0.  The last valid topic must be followed
 * by JobsMaxTopic.  This arrangement is necessary since the
 * enum values are used as indexes to arrays of topic strings
 * and lengths.
 *
 * @note The ordering is important, providing a means
 * to divide topics into those that use a job ID
 * and those that do not.
 *
 * @note These constraints are enforced by a unit test.
 */
typedef enum
{
    JobsInvalidTopic = -1,
    JobsJobsChanged,
    JobsNextJobChanged,
    JobsGetPendingSuccess,
    JobsGetPendingFailed,
    JobsStartNextSuccess,
    JobsStartNextFailed,
    /* Topics below use a job ID. */
    JobsDescribeSuccess,
    JobsDescribeFailed,
    JobsUpdateSuccess,
    JobsUpdateFailed,
    JobsMaxTopic
} JobsTopic_t;

/*-----------------------------------------------------------*/

/**
 * @brief Populate a topic string for a subscription request.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[in] api  The desired Jobs API, e.g., JobsNextJobChanged.
 * @param[out] outLength  The length of the topic string written to the buffer.
 *
 * @return #JobsSuccess if the topic was written to the buffer;
 * #JobsBadParameter if invalid parameters are passed;
 * #JobsBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * When all parameters are valid, the topic string is written to
 * the buffer up to one less than the buffer size.  The topic is
 * ended with a NUL character.
 *
 * @note The thingName parameter does not need a NUL terminator.
 *
 * @note The AWS IoT Jobs service does not require clients to subscribe
 * to the "/accepted" and "/rejected" response topics for the APIs that
 * accept requests on PUBLISH topics. The Jobs service will send responses
 * to requests from clients irrespective of whether they have subscribed to
 * response topics or not. For more information, refer to the AWS docs here:
 * https://docs.aws.amazon.com/iot/latest/developerguide/jobs-mqtt-api.html
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows usage of the Jobs_GetTopic API to
 * // generate topic string for the NextJobExecutionChanged API
 * // of AWS IoT Jobs service.
 *
 * // Every device should have a unique thing name registered with AWS IoT Core.
 * // This example uses a dummy serial number for the thing name.
 * #define THING_NAME           "11223445566"
 * #define THING_NAME_LENGTH    ( sizeof( THING_NAME ) - 1U )
 *
 * // This example allocates a buffer of maximum length for a Jobs topic
 * // possible for the thing name using the JOBS_API_MAX_LENGTH macro.
 * char topicBuffer[ JOBS_API_MAX_LENGTH( THING_NAME_LENGTH ) ] = { 0 };
 * uint16_t topicLength = 0U;
 * JobsStatus_t status = JobsSuccess;
 * status = Jobs_GetTopic( topicBuffer,
 *                         sizeof( topicBuffer ),
 *                         THING_NAME,
 *                         THING_NAME_LENGTH,
 *                         &( topicLength ) );
 *
 * if( status == JobsSuccess )
 * {
 *     // The topic string of length, topicLength, has been
 *     // generated in the buffer, topicBuffer, for the NextJobExecutionChanged API.
 *     // Subscribe to this topic using an MQTT client of your choice.
 * }
 * @endcode
 */
/* @[declare_jobs_gettopic] */
JobsStatus_t Jobs_GetTopic( char * buffer,
                            size_t length,
                            const char * thingName,
                            uint16_t thingNameLength,
                            JobsTopic_t api,
                            size_t * outLength );
/* @[declare_jobs_gettopic] */

/**
 * @brief Output a topic value if a Jobs API topic string is present.
 * Optionally, output a pointer to a jobID within the topic and its
 * length.
 *
 * @param[in] topic  The topic string to check.
 * @param[in] length  The length of the topic string.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[out] outApi  The jobs topic API value if present, e.g., JobsUpdateSuccess.
 * @param[out] outJobId  The beginning of the jobID in the topic string.
 * @param[out] outJobIdLength  The length of the jobID in the topic string.
 *
 * @return #JobsSuccess if a matching topic was found;
 * #JobsNoMatch if a matching topic was NOT found
 *   (parameter outApi gets JobsInvalidTopic );
 * #JobsBadParameter if invalid parameters are passed.
 *
 * @note The topic and thingName parameters do not need a NUL terminator.
 *
 * @note Not all Jobs APIs have jobIDs within the topic string.
 * NULL and 0 are output when no jobID is present.
 * The parameters jobId and jobIdLength may be NULL.
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows how to use the Jobs_MatchTopic API to
 * // check if an incoming MQTT publish message is from the AWS IoT Jobs
 * // service.
 *
 * // Assuming that these variables contain incoming topic data received
 * // from the MQTT client used.
 * char * pIncomingTopic;
 * size_t topicLength;
 *
 * // Every device should have a unique thing name registered with AWS IoT Core.
 * // This example uses a dummy serial number for the thing name.
 * // The Jobs_MatchTopic API will check that the incoming message topic contains
 * // this thing name.
 * #define THING_NAME           "11223445566"
 * #define THING_NAME_LENGTH    ( sizeof( THING_NAME ) - 1U )
 *
 * JobsTopic_t api;
 * char * pJobId = NULL;
 * uint16_t jobIdLength;
 * JobsStatus_t status = JobsSuccess;
 *
 * status = Jobs_MatchTopic( pIncomingTopic,
 *                           topicLength,
 *                           THING_NAME,
 *                           THING_NAME_LENGTH,
 *                           &api,
 *                           &pJobId,
 *                           &jobIdLength );
 *
 * if( status == JobsSuccess )
 * {
 *     // The Jobs_MatchTopic API has determined that the incoming topic is from
 *     // AWS IoT Jobs service for the expected thing name.
 *     // If the topic contains a jobID, then the pJobId and jobIdLength parameters
 *     // populated by the API.
 *
 *     if( api == JobsJobsChanged )
 *     { // Message from JobExecutionsChanged API.
 *     }
 *
 *     else if( api == JobsNextJobChanged )
 *     { // Message from NextJobExecutionChanged API.
 *     }
 *
 *     else if( api == JobsGetPendingSuccess )
 *     { // Received accepted response for request to GetPendingJobExecutions API.
 *     }
 *
 *     else if( api == JobsGetPendingFailed )
 *     { // Received rejected response for request to GetPendingJobExecutions API.
 *     }
 *
 *     else if( api == JobsStartNextSuccess )
 *     { // Received accepted response for request to StartNextPendingJobExecution API.
 *     }
 *
 *     else if( api == JobsStartNextFailed )
 *     { // Received rejected response for request to StartNextPendingJobExecution API.
 *     }
 *
 *     else if( api == JobsDescribeSuccess )
 *     { // Received accepted response for request to DescribeJobExecution API.
 *     }
 *
 *     else if( api == JobsDescribeFailed )
 *     { // Received rejected response for request to DescribeJobExecution API.
 *     }
 *
 *     else if( api == JobsUpdateSuccess )
 *     { // Received accepted response for request to UpdateJobExecution API.
 *     }
 *
 *     else if( api == JobsUpdateFailed )
 *     { // Received rejected response for request to UpdateJobExecution API.
 *     }
 *     else
 *     {
 *         // Unexpected response.
 *     }
 * }
 * @endcode
 */
/* @[declare_jobs_matchtopic] */
JobsStatus_t Jobs_MatchTopic( char * topic,
                              size_t length,
                              const char * thingName,
                              uint16_t thingNameLength,
                              JobsTopic_t * outApi,
                              char ** outJobId,
                              uint16_t * outJobIdLength );
/* @[declare_jobs_matchtopic] */

/**
 * @brief Populate a topic string for a GetPendingJobExecutions request.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[out] outLength  The length of the topic string written to the buffer.
 *
 * @return #JobsSuccess if the topic was written to the buffer;
 * #JobsBadParameter if invalid parameters are passed;
 * #JobsBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * When all parameters are valid, the topic string is written to
 * the buffer up to one less than the buffer size.  The topic is
 * ended with a NUL character.
 *
 * @note The thingName parameter does not need a NUL terminator.
 *
 * @note The AWS IoT Jobs service does not require clients to subscribe
 * to the "/accepted" and "/rejected" response topics of the
 * GetPendingJobExecutions API.
 * The Jobs service will send responses to requests published to the API
 * from clients irrespective of whether they have subscribed to response topics
 * or not. For more information, refer to the AWS docs here:
 * https://docs.aws.amazon.com/iot/latest/developerguide/jobs-mqtt-api.html
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows usage of the Jobs_GetPending API to
 * // generate topic string for the GetPendingJobExecutions API
 * // of the AWS IoT Jobs service.
 *
 * // Every device should have a unique thing name registered with AWS IoT Core.
 * // This example uses a dummy serial number for the thing name.
 * #define THING_NAME           "11223445566"
 * #define THING_NAME_LENGTH    ( sizeof( THING_NAME ) - 1U )
 *
 * // This example allocates a buffer of maximum length for a Jobs topic
 * // possible for the thing name using the JOBS_API_MAX_LENGTH macro.
 * char topicBuffer[ JOBS_API_MAX_LENGTH( THING_NAME_LENGTH ) ] = { 0 };
 * uint16_t topicLength = 0U;
 * JobsStatus_t status = JobsSuccess;
 * status = Jobs_GetPending( topicBuffer,
 *                           sizeof( topicBuffer ),
 *                           THING_NAME,
 *                           THING_NAME_LENGTH,
 *                           &( topicLength ) );
 *
 * if( status == JobsSuccess )
 * {
 *     // The topic string of length, topicLength, has been
 *     // generated in the buffer, topicBuffer, for the GetPendingJobExecutions API.
 *     // Publish to this topic using an MQTT client of your choice.
 * }
 * @endcode
 */
/* @[declare_jobs_getpending] */
JobsStatus_t Jobs_GetPending( char * buffer,
                              size_t length,
                              const char * thingName,
                              uint16_t thingNameLength,
                              size_t * outLength );
/* @[declare_jobs_getpending] */

/**
 * @brief Populate a topic string for a StartNextPendingJobExecution request.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[out] outLength  The length of the topic string written to the buffer.
 *
 * @return #JobsSuccess if the topic was written to the buffer;
 * #JobsBadParameter if invalid parameters are passed;
 * #JobsBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * When all parameters are valid, the topic string is written to
 * the buffer up to one less than the buffer size.  The topic is
 * ended with a NUL character.
 *
 * @note The thingName parameter does not need a NUL terminator.
 *
 * @note The AWS IoT Jobs service does not require clients to subscribe
 * to the "/accepted" and "/rejected" response topics of the
 * StartNextPendingJobExecution API.
 * The Jobs service will send responses to requests published to the API
 * from clients irrespective of whether they have subscribed to response topics
 * or not. For more information, refer to the AWS docs here:
 * https://docs.aws.amazon.com/iot/latest/developerguide/jobs-mqtt-api.html
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows usage of the Jobs_StartNext API to
 * // generate topic string for the StartNextPendingJobExecution API
 * // of the AWS IoT Jobs service.
 *
 * // Every device should have a unique thing name registered with AWS IoT Core.
 * // This example uses a dummy serial number for the thing name.
 * #define THING_NAME           "11223445566"
 * #define THING_NAME_LENGTH    ( sizeof( THING_NAME ) - 1U )
 *
 * // This example allocates a buffer of maximum length for a Jobs topic
 * // possible for the thing name using the JOBS_API_MAX_LENGTH macro.
 * char topicBuffer[ JOBS_API_MAX_LENGTH( THING_NAME_LENGTH ) ] = { 0 };
 * uint16_t topicLength = 0U;
 * JobsStatus_t status = JobsSuccess;
 * status = Jobs_StartNext( topicBuffer,
 *                          sizeof( topicBuffer ),
 *                          THING_NAME,
 *                          THING_NAME_LENGTH,
 *                          &( topicLength ) );
 *
 * if( status == JobsSuccess )
 * {
 *     // The topic string of length, topicLength, has been generated in
 *     // the buffer, topicBuffer, for the StartNextPendingJobExecution API.
 *     // Publish to this topic using an MQTT client of your choice.
 * }
 * @endcode
 */
/* @[declare_jobs_startnext] */
JobsStatus_t Jobs_StartNext( char * buffer,
                             size_t length,
                             const char * thingName,
                             uint16_t thingNameLength,
                             size_t * outLength );
/* @[declare_jobs_startnext] */

/**
 * @brief Populate a message string for a StartNextPendingJobExecution request.
 *
 * @param clientToken The device's token
 * @param clientTokenLength The expected length of the clientToken
 * @param buffer The buffer to be written to
 * @param bufferSize The size of the buffer
 *
 * @return 0 if write to buffer fails
 * @return The message length if the write is successful
 *
 * <b>Example</b>
 * @code{c}
 *
 *
 * // The Following Example shows usage of the Jobs_StartNextMsg API
 * // to generate a message string for a StartNextPendingJobExecution request.
 *
 * const char * clientToken = "test";
 * size_t clientTokenLength = ( sizeof( clientToken ) - 1U );
 * char messageBuffer[ START_JOB_MSG_LENGTH ] = {0};
 * size_t messageLength = 0U;
 *
 * messageLength = Jobs_StartNextMsg( clientToken,
 *                                    clientTokenLength,
 *                                    messageBuffer,
 *                                    START_JOB_MSG_LENGTH );
 *
 * if ( messageLength > 0 )
 * {
 *     // The message string of the clientToken has been generated in
 *     // the buffer, messageBuffer, for the StartNextPendingJobExecution request
 *     // Publish to the topic string generated by Jobs_StartNext() using an
 *     // MQTT client of your choice.
 * }
 * @endcode
 */
/* @[declare_jobs_startnextmsg] */
size_t Jobs_StartNextMsg( const char * clientToken,
                          size_t clientTokenLength,
                          char * buffer,
                          size_t bufferSize );
/* @[declare_jobs_startnextmsg] */

/**
 * @brief Populate a topic string for a DescribeJobExecution request.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[out] jobId  The ID of the job to describe.
 * @param[out] jobIdLength  The length of the job ID.
 * @param[out] outLength  The length of the topic string written to the buffer.
 *
 * @return #JobsSuccess if the topic was written to the buffer;
 * #JobsBadParameter if invalid parameters are passed;
 * #JobsBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * When all parameters are valid, the topic string is written to
 * the buffer up to one less than the buffer size.  The topic is
 * ended with a NUL character.
 *
 * @note A jobId consisting of the string, "$next", is supported to generate
 * a topic string to request the next pending job.
 *
 * @note The thingName and jobId parameters do not need a NUL terminator.
 *
 * @note The AWS IoT Jobs service does not require clients to subscribe
 * to the "/accepted" and "/rejected" response topics of the
 * DescribeJobExecution API.
 * The Jobs service will send responses to requests published to the API
 * from clients irrespective of whether they have subscribed to response topics
 * or not. For more information, refer to the AWS docs here:
 * https://docs.aws.amazon.com/iot/latest/developerguide/jobs-mqtt-api.html
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows usage of the Jobs_Describe API to
 * // generate topic string for the DescribeJobExecution API
 * // of the AWS IoT Jobs service.
 *
 * // Every device should have a unique thing name registered with AWS IoT Core.
 * // This example uses a dummy serial number for the thing name.
 * #define THING_NAME           "11223445566"
 * #define THING_NAME_LENGTH    ( sizeof( THING_NAME ) - 1U )
 *
 * // The job ID is required to send a status update for a job to the AWS IoT
 * // Jobs service.
 * #define JOB_ID               "My_Job"
 * #define JOB_ID_LENGTH        ( sizeof( JOB_ID ) - 1U )
 *
 * // This example allocates a buffer of maximum length for a Jobs topic
 * // possible for the thing name using the JOBS_API_MAX_LENGTH macro.
 * char topicBuffer[ JOBS_API_MAX_LENGTH( THING_NAME_LENGTH ) ] = { 0 };
 * uint16_t topicLength = 0U;
 * JobsStatus_t status = JobsSuccess;
 * status = Jobs_Describe( topicBuffer,
 *                         sizeof( topicBuffer ),
 *                         THING_NAME,
 *                         THING_NAME_LENGTH,
 *                         JOB_ID,
 *                         JOB_ID_LENGTH,
 *                         &( topicLength ) );
 *
 * if( status == JobsSuccess )
 * {
 *     // The topic string of length, topicLength, has been generated in
 *     // the buffer, topicBuffer, for the DescribeJobExecution API.
 *     // Publish to this topic using an MQTT client of your choice.
 * }
 * @endcode
 */
/* @[declare_jobs_describe] */
JobsStatus_t Jobs_Describe( char * buffer,
                            size_t length,
                            const char * thingName,
                            uint16_t thingNameLength,
                            const char * jobId,
                            uint16_t jobIdLength,
                            size_t * outLength );
/* @[declare_jobs_describe] */

/**
 * @brief Populate a topic string for an UpdateJobExecution request.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[out] jobId  The ID of the job to describe.
 * @param[out] jobIdLength  The length of the job ID.
 * @param[out] outLength  The length of the topic string written to the buffer.
 *
 * @return #JobsSuccess if the topic was written to the buffer;
 * #JobsBadParameter if invalid parameters are passed;
 * #JobsBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * When all parameters are valid, the topic string is written to
 * the buffer up to one less than the buffer size.  The topic is
 * ended with a NUL character.
 *
 * @note The thingName and jobId parameters do not need a NUL terminator.
 *
 * @note The AWS IoT Jobs service does not require clients to subscribe
 * to the "/accepted" and "/rejected" response topics of the
 * UpdateJobExecution API.
 * The Jobs service will send responses to requests published to the API
 * from clients irrespective of whether they have subscribed to response topics
 * or not. For more information, refer to the AWS docs here:
 * https://docs.aws.amazon.com/iot/latest/developerguide/jobs-mqtt-api.html
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows usage of the Jobs_Update API to
 * // generate topic string for the UpdateJobExecution API
 * // of the AWS IoT Jobs service.
 *
 * // Every device should have a unique thing name registered with AWS IoT Core.
 * // This example uses a dummy serial number for the thing name.
 * #define THING_NAME           "11223445566"
 * #define THING_NAME_LENGTH    ( sizeof( THING_NAME ) - 1U )
 *
 * // The job ID is required to send a status update for a job to the AWS IoT
 * // Jobs service.
 * #define JOB_ID               "My_Job"
 * #define JOB_ID_LENGTH        ( sizeof( JOB_ID ) - 1U )
 *
 * // This example allocates a buffer of maximum length for a Jobs topic
 * // possible for the thing name using the JOBS_API_MAX_LENGTH macro.
 * char topicBuffer[ JOBS_API_MAX_LENGTH( THING_NAME_LENGTH ) ] = { 0 };
 * uint16_t topicLength = 0U;
 * JobsStatus_t status = JobsSuccess;
 * status = Jobs_Update( topicBuffer,
 *                         sizeof( topicBuffer ),
 *                         THING_NAME,
 *                         THING_NAME_LENGTH,
 *                         JOB_ID,
 *                         JOB_ID_LENGTH,
 *                         &( topicLength ) );
 *
 * if( status == JobsSuccess )
 * {
 *     // The topic string of length, topicLength, has been
 *     // generated in the buffer, topicBuffer, for the UpdateJobExecution API.
 *     // Publish to this topic using an MQTT client of your choice.
 * }
 * @endcode
 */
/* @[declare_jobs_update] */
JobsStatus_t Jobs_Update( char * buffer,
                          size_t length,
                          const char * thingName,
                          uint16_t thingNameLength,
                          const char * jobId,
                          uint16_t jobIdLength,
                          size_t * outLength );
/* @[declare_jobs_update] */

/**
 * @brief Populate a message string for an UpdateJobExecution request.
 *
 * @param status Current status of the job
 * @param expectedVersion The version that is expected
 * @param expectedVersionLength The length of the expectedVersion string
 * @param buffer The buffer to be written to
 * @param bufferSize the size of the buffer
 *
 * @return 0 if write to buffer fails
 * @return messageLength if the write is successful
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The Following Example shows usage of the Jobs_UpdateMsg API to
 * // generate a message string for the UpdateJobExecution API
 * // of the AWS IoT Jobs Service
 * const char * expectedVersion = "2";
 * size_t expectedVersionLength = ( sizeof(expectedVersion ) - 1U );
 * JobCurrentStatus_t status = Succeeded;
 * char messageBuffer[ UPDATE_JOB_MSG_LENGTH ]  = {0};
 * size_t messageLength = 0U;
 *
 * messageLength = Jobs_UpdateMsg( status,
 *                                 expectedVersion,
 *                                 expectedVersionLength,
 *                                 messageBuffer,
 *                                 UPDATE_JOB_MSG_LENGTH );
 *
 * if (messageBufferLength > 0 )
 * {
 *     // The message string of length, messageLength, has been
 *     // generated in the buffer, messageBuffer, for the UpdateJobExecution API
 *     // Publish this message to the topic generated by Jobs_Update using an
 *     // MQTT client of your choice.
 * }
 * @endcode
 */
/* @[declare_jobs_updatemsg] */
size_t Jobs_UpdateMsg( JobCurrentStatus_t status,
                       const char * expectedVersion,
                       size_t expectedVersionLength,
                       char * buffer,
                       size_t bufferSize );
/* @[declare_jobs_updatemsg] */

/**
 * @brief Retrieves the job ID from a given message (if applicable)
 *
 * @param message [In] A JSON formatted message
 * @param messageLength [In] The length of the message
 * @param jobId [Out] The job ID
 * @return size_t The job ID length
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows the usage of the Jobs_GetJobId API to
 * // extract the jobId and its length from a message, if present.
 *
 * const char * message;    // A JSON formatted message from the IoT core
 * size_t messageLength;    // Length of the JSON formatted message
 * const char * jobId;      // variable to hold jobId
 * size_t jobIdLength = 0U; // Holds length of the jobId
 *
 * jobIdLength = Jobs_GetJobId( message,
 *                              messageLength,
 *                              &jobId);
 *
 * if ( jobIdLength > 0 )
 * {
 *     // Job ID was successfully extracted from the message
 *     // Store the Job ID so that it can be used as needed by other functions.
 *     // For example, as an input to Jobs_Update.
 * }
 * @endcode
 */
/* @[declare_jobs_getjobid] */
size_t Jobs_GetJobId( const char * message,
                      size_t messageLength,
                      const char ** jobId );
/* @[declare_jobs_getjobid] */

/**
 * @brief Retrieves the job document from a given message (if applicable)
 *
 * @param message [In] A JSON formatted message which
 * @param messageLength [In] The length of the message
 * @param jobDoc [Out] The job document
 * @return size_t The length of the job document
 *
 * <b>Example</b>
 * @code{c}
 *
 * // The following example shows the usage of the Jobs_GetJobId API to
 * // extract the jobId and its length from a message, if present.
 *
 * const char * message;     // A JSON formatted message from the IoT core
 * size_t messageLength;     // Length of the JSON formatted message
 * const char * jobDoc;      // variable to hold the job doc
 * size_t jobDocLength = 0U; // Holds length of the job doc
 *
 * jobDocLength = Jobs_GetJobDocument( message,
 *                                     messageLength,
 *                                     &jobDoc);
 *
 * if ( jobDocLength > 0 )
 * {
 *     // JobDoc was successfully extracted from the message.
 *     // Pass JobDoc as input to otaParser_parseJobDocFile to
 *     // extract the fields from the job document and store them
 *     // in a AfrOtaJobDocumentFields_t stuct.
 * }
 * @endcode
 */
/* @[declare_jobs_getjobdocument] */
size_t Jobs_GetJobDocument( const char * message,
                            size_t messageLength,
                            const char ** jobDoc );
/* @[declare_jobs_getjobdocument] */

/**
 * @brief Checks if a message comes from the start-next/accepted reserved topic
 *
 * @param topic The topic to check against
 * @param topicLength The expected topic length
 * @param thingName The device's thingName as registered with AWS IoT.
 * @param thingNameLength The length of the thingName.
 * @return true If the topic is the start-next/accepted topic
 * @return false If the topic is not the start-next/accepted topic
 *
 */
/* @[declare_jobs_isstartnextaccepted] */
bool Jobs_IsStartNextAccepted( const char * topic,
                               const size_t topicLength,
                               const char * thingName,
                               const size_t thingNameLength );
/* @[declare_jobs_isstartnextaccepted] */

/**
 * @brief Checks if a message comes from the update/accepted reserved topic
 *
 * @param topic The topic to check against
 * @param topicLength The expected topic length
 * @param jobId Corresponding Job ID which the update was accepted for
 * @param jobIdLength The Job ID length
 * @param thingName The device's thingName as registered with AWS IoT.
 * @param thingNameLength The length of the thingName.
 * @param expectedStatus The job update status reported by AWS IoT Jobs
 * @return true If the topic is the update/\<expectedStatus\> topic
 * @return false If the topic is not the update/\<expectedStatus\> topic
 */
/* @[declare_jobs_isjobupdatestatus] */
bool Jobs_IsJobUpdateStatus( const char * topic,
                             const size_t topicLength,
                             const char * jobId,
                             const size_t jobIdLength,
                             const char * thingName,
                             const size_t thingNameLength,
                             JobUpdateStatus_t expectedStatus );
/* @[declare_jobs_isjobupdatestatus] */


/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef JOBS_H_ */
