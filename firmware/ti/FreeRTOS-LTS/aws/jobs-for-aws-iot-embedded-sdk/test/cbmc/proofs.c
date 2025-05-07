#include <stdbool.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>

#include "jobs.h"
#include "core_json.h"
#include "jobs_annex.h"
#include "../../source/otaJobParser/include/job_parser.h"
#include "../../source/otaJobParser/include/ota_job_processor.h"

#ifndef UNWIND_COUNT
    #define UNWIND_COUNT          10
#endif

#define CBMC_MAX_OBJECT_SIZE      ( PTRDIFF_MAX )
#define CBMC_MAX_BUFSIZE          ( UNWIND_COUNT )
#define CBMC_THINGNAME_MAX_LEN    ( UNWIND_COUNT - 1 )
#define CBMC_JOBID_MAX_LEN        ( UNWIND_COUNT - 1 )
#define CBMC_JOBDOC_MAX_LEN       ( UNWIND_COUNT - 1 )
#define CBMC_TOPIC_MAX_LEN        ( UNWIND_COUNT - 1 )

/* utils */
int nondet_int( void );

JobCurrentStatus_t nondet_JobCurrentStatus( void )
{
    int jobStatus[] = { Queued, InProgress, Failed, Succeeded, Rejected };

    int index = nondet_int();

    __CPROVER_assume( ( index >= 0 ) && ( index <= ( sizeof( jobStatus ) / sizeof( jobStatus[ 0 ] ) ) - 1 ) );

    return jobStatus[ index ];
}

JobUpdateStatus_t nondet_JobUpdateStatus( void )
{
    int updateStatus[] = { JobUpdateStatus_Accepted, JobUpdateStatus_Rejected };

    int index = nondet_int();

    __CPROVER_assume( ( index >= 0 ) && ( index <= ( sizeof( updateStatus ) / sizeof( updateStatus[ 0 ] ) ) - 1 ) );

    return updateStatus[ index ];
}

JobsTopic_t nondet_JobsTopic_t( void )
{
    int jobsTopics[] =
    {
        JobsInvalidTopic,      JobsJobsChanged,      JobsNextJobChanged,
        JobsGetPendingSuccess, JobsGetPendingFailed, JobsStartNextSuccess,
        JobsStartNextFailed,   JobsDescribeSuccess,  JobsDescribeFailed,
        JobsUpdateSuccess,     JobsUpdateFailed,     JobsMaxTopic
    };

    int index = nondet_int();

    __CPROVER_assume( ( index >= 0 ) && ( index <= ( sizeof( jobsTopics ) / sizeof( jobsTopics[ 0 ] ) ) - 1 ) );

    return jobsTopics[ index ];
}
/* end of utils */

void proof_Jobs_Describe( void )
{
    char * buffer;
    size_t bufferLength;
    const char * thingName;
    uint16_t thingNameLength;
    const char * jobId;
    uint16_t jobIdLength;
    size_t * outLength;
    JobsStatus_t ret;

    /* The buffer length must not exceed the maximum object size supported by CBMC. */
    __CPROVER_assume( bufferLength < CBMC_MAX_OBJECT_SIZE );
    buffer = malloc( bufferLength );

    /* The thing name length must not exceed unwindings. */
    __CPROVER_assume( thingNameLength <= CBMC_THINGNAME_MAX_LEN );
    thingName = malloc( thingNameLength );

    /* The job ID length must not exceed unwindings. */
    __CPROVER_assume( jobIdLength <= CBMC_JOBID_MAX_LEN );
    jobId = malloc( jobIdLength );

    outLength = malloc( sizeof( *outLength ) );

    ret = Jobs_Describe( buffer,
                         bufferLength,
                         thingName,
                         thingNameLength,
                         jobId,
                         jobIdLength,
                         outLength );

    __CPROVER_assert( jobsDescribeEnum( ret ), "The return value is a subset of JobsStatus_t." );

    if( ( ret != JobsBadParameter ) && ( outLength != NULL ) )
    {
        __CPROVER_assert( ( *outLength < bufferLength ), "Buffer writes do not exceed buffer length." );

        __CPROVER_assert( ( buffer[ *outLength ] == '\0' ), "Buffer is NULL terminated." );
    }
}

void proof_Jobs_GetPending( void )
{
    char * buffer;
    size_t bufferLength;
    const char * thingName;
    uint16_t thingNameLength;
    size_t * outLength;
    JobsStatus_t ret;

    /* The buffer length must not exceed the maximum object size supported by CBMC. */
    __CPROVER_assume( bufferLength < CBMC_MAX_OBJECT_SIZE );
    buffer = malloc( bufferLength );

    /* The thing name length must not exceed unwindings. */
    __CPROVER_assume( thingNameLength <= CBMC_THINGNAME_MAX_LEN );
    thingName = malloc( thingNameLength );

    outLength = malloc( sizeof( *outLength ) );

    ret = Jobs_GetPending( buffer,
                           bufferLength,
                           thingName,
                           thingNameLength,
                           outLength );

    __CPROVER_assert( jobsGetPendingEnum( ret ), "The return value is a subset of JobsStatus_t." );

    if( ( ret != JobsBadParameter ) && ( outLength != NULL ) )
    {
        __CPROVER_assert( ( *outLength < bufferLength ), "Buffer writes do not exceed buffer length." );

        __CPROVER_assert( ( buffer[ *outLength ] == '\0' ), "Buffer is NUL terminated." );
    }
}

void proof_Jobs_GetTopic( void )
{
    char * buffer;
    size_t bufferLength;
    const char * thingName;
    uint16_t thingNameLength;
    JobsTopic_t api = nondet_JobsTopic_t();
    size_t * outLength;
    JobsStatus_t ret;

    /* The buffer length must not exceed the maximum object size supported by CBMC. */
    __CPROVER_assume( bufferLength < CBMC_MAX_OBJECT_SIZE );
    buffer = malloc( bufferLength );

    /* The thing name length must not exceed unwindings. */
    __CPROVER_assume( thingNameLength <= CBMC_THINGNAME_MAX_LEN );
    thingName = malloc( thingNameLength );

    outLength = malloc( sizeof( *outLength ) );

    ret = Jobs_GetTopic( buffer,
                         bufferLength,
                         thingName,
                         thingNameLength,
                         api,
                         outLength );

    __CPROVER_assert( jobsGetTopicEnum( ret ), "The return value is a subset of JobsStatus_t." );

    if( ( ret != JobsBadParameter ) && ( outLength != NULL ) )
    {
        __CPROVER_assert( ( *outLength < bufferLength ), "Buffer writes do not exceed buffer length." );

        __CPROVER_assert( ( buffer[ *outLength ] == '\0' ), "Buffer is NUL terminated." );
    }
}

void proof_Jobs_MatchTopic( void )
{
    char * topic;
    size_t topicLength;
    const char * thingName;
    uint16_t thingNameLength;
    JobsTopic_t * outApi;
    char ** outJobId;
    uint16_t * outJobIdLength;
    JobsStatus_t ret;

    /* The buffer length must not exceed the maximum object size supported by CBMC. */
    __CPROVER_assume( topicLength < CBMC_TOPIC_MAX_LEN );
    topic = malloc( topicLength );

    /* The thing name length must not exceed unwindings. */
    __CPROVER_assume( thingNameLength <= CBMC_THINGNAME_MAX_LEN );
    thingName = malloc( thingNameLength );

    outApi = malloc( sizeof( *outApi ) );
    outJobId = malloc( sizeof( *outJobId ) );
    outJobIdLength = malloc( sizeof( *outJobIdLength ) );

    ret = Jobs_MatchTopic( topic,
                           topicLength,
                           thingName,
                           thingNameLength,
                           outApi,
                           outJobId,
                           outJobIdLength );

    __CPROVER_assert( jobsMatchTopicEnum( ret ), "The return value is a subset of JobsStatus_t." );

    if( ret == JobsSuccess )
    {
        if( outApi != NULL )
        {
            __CPROVER_assert( jobsTopicEnum( *outApi ), "The API value is a JobsTopic_t enum." );
        }

        if( ( outJobId != NULL ) && ( *outJobId != NULL ) )
        {
            __CPROVER_assert( ( ( *outJobId > topic ) && ( *outJobId < ( topic + topicLength ) ) ),
                              "The output parameter for jobId points within the topic string." );
        }

        if( ( outJobIdLength != NULL ) && ( *outJobIdLength > 0 ) )
        {
            __CPROVER_assert( ( *outJobIdLength < topicLength ),
                              "The length of the jobId part of the topic is less than the length of the topic." );
        }
    }
}

void proof_Jobs_StartNext( void )
{
    char * buffer;
    size_t bufferLength;
    const char * thingName;
    uint16_t thingNameLength;
    size_t * outLength;
    JobsStatus_t ret;

    /* The buffer length must not exceed the maximum object size supported by CBMC. */
    __CPROVER_assume( bufferLength < CBMC_MAX_OBJECT_SIZE );
    buffer = malloc( bufferLength );

    /* The thing name length must not exceed unwindings. */
    __CPROVER_assume( thingNameLength <= CBMC_THINGNAME_MAX_LEN );
    thingName = malloc( thingNameLength );

    outLength = malloc( sizeof( *outLength ) );

    ret = Jobs_StartNext( buffer,
                          bufferLength,
                          thingName,
                          thingNameLength,
                          outLength );

    __CPROVER_assert( jobsStartNextEnum( ret ), "The return value is a subset of JobsStatus_t." );

    if( ( ret != JobsBadParameter ) && ( outLength != NULL ) )
    {
        __CPROVER_assert( ( *outLength < bufferLength ), "Buffer writes do not exceed buffer length." );

        __CPROVER_assert( ( buffer[ *outLength ] == '\0' ), "Buffer is NULL terminated." );
    }
}

void proof_Jobs_Update( void )
{
    char * buffer;
    size_t bufferLength;
    const char * thingName;
    uint16_t thingNameLength;
    const char * jobId;
    uint16_t jobIdLength;
    size_t * outLength;
    JobsStatus_t ret;

    /* The buffer length must not exceed the maximum object size supported by CBMC. */
    __CPROVER_assume( bufferLength < CBMC_MAX_OBJECT_SIZE );
    buffer = malloc( bufferLength );

    /* The thing name length must not exceed unwindings. */
    __CPROVER_assume( thingNameLength <= CBMC_THINGNAME_MAX_LEN );
    thingName = malloc( thingNameLength );

    /* The job ID length must not exceed unwindings. */
    __CPROVER_assume( jobIdLength <= CBMC_JOBID_MAX_LEN );
    jobId = malloc( jobIdLength );

    outLength = malloc( sizeof( *outLength ) );

    ret = Jobs_Update( buffer,
                       bufferLength,
                       thingName,
                       thingNameLength,
                       jobId,
                       jobIdLength,
                       outLength );

    __CPROVER_assert( jobsUpdateEnum( ret ), "The return value is a subset of JobsStatus_t." );

    if( ( ret != JobsBadParameter ) && ( outLength != NULL ) )
    {
        __CPROVER_assert( ( *outLength < bufferLength ), "Buffer writes do not exceed buffer length." );

        __CPROVER_assert( ( buffer[ *outLength ] == '\0' ), "Buffer is NUL terminated." );
    }
}

void proof_Jobs_IsStartNextAccepted( void )
{
    bool ret;
    const char * topic;
    const size_t topicLength;
    const char * thingName;
    const size_t thingNameLength;

    __CPROVER_assume( topicLength < CBMC_TOPIC_MAX_LEN );
    topic = malloc( topicLength );

    __CPROVER_assume( thingNameLength < CBMC_THINGNAME_MAX_LEN );
    thingName = malloc( thingNameLength );


    ret = Jobs_IsStartNextAccepted( topic,
                                    topicLength,
                                    thingName,
                                    thingNameLength );

    __CPROVER_assert( ( ret == 0 || ret == 1 ), "Return value is bool" );
}

void proof_Jobs_IsJobUpdateStatus( void )
{
    bool ret;
    const char * topic;
    const size_t topicLength;
    const char * thingName;
    const size_t thingNameLength;
    const char * jobId;
    const size_t jobIdLength;
    JobUpdateStatus_t expectedStatus = nondet_JobUpdateStatus();

    __CPROVER_assume( topicLength < CBMC_TOPIC_MAX_LEN );
    topic = malloc( topicLength );

    __CPROVER_assume( thingNameLength < CBMC_THINGNAME_MAX_LEN );
    thingName = malloc( thingNameLength );

    __CPROVER_assume( jobIdLength < CBMC_JOBID_MAX_LEN );
    jobId = malloc( jobIdLength );

    ret = Jobs_IsJobUpdateStatus( topic,
                                  topicLength,
                                  jobId,
                                  jobIdLength,
                                  thingName,
                                  thingNameLength,
                                  expectedStatus );

    __CPROVER_assert( ( ret == 0 || ret == 1 ), "Return value is bool" );
}

void proof_Jobs_GetJobId( void )
{
    const char * message;
    const size_t messageLength;
    char * jobId = NULL;
    size_t ret;

    __CPROVER_assume( messageLength <= CBMC_MAX_OBJECT_SIZE );
    message = malloc( messageLength );

    ret = Jobs_GetJobId( message,
                         messageLength,
                         &jobId );
}

void proof_Jobs_GetJobDocument( void )
{
    const char * message;
    size_t messageLength;
    char * jobdoc;
    size_t ret;

    __CPROVER_assume( messageLength <= CBMC_MAX_OBJECT_SIZE );
    message = malloc( messageLength );

    ret = Jobs_GetJobDocument( message,
                               messageLength,
                               &jobdoc );
}


void proof_Jobs_StartNextMsg( void )
{
    const char * clientToken;
    size_t clientTokenLength;
    const char * buffer;
    size_t bufferLength;
    size_t ret;

    __CPROVER_assume( clientTokenLength <= CBMC_MAX_BUFSIZE );
    clientToken = malloc( clientTokenLength );

    __CPROVER_assume( bufferLength <= CBMC_MAX_OBJECT_SIZE );
    buffer = malloc( bufferLength );

    ret = Jobs_StartNextMsg( clientToken,
                             clientTokenLength,
                             buffer,
                             bufferLength );
}

void proof_Jobs_UpdateMsg( void )
{
    JobCurrentStatus_t status = nondet_JobCurrentStatus();
    char * expectedVersion;
    size_t expectedVersionLength;
    char * buffer;
    size_t bufferLength;
    size_t ret;

    __CPROVER_assume( expectedVersionLength <= CBMC_THINGNAME_MAX_LEN );
    expectedVersion = malloc( expectedVersionLength );

    __CPROVER_assume( bufferLength <= 64 );
    buffer = malloc( bufferLength );

    ret = Jobs_UpdateMsg( status,
                          expectedVersion,
                          expectedVersionLength,
                          buffer,
                          bufferLength );
}

void proof_populateJobDocFields( void )
{
    const char * jobDoc;
    const size_t jobDocLength;
    int fileIndex;
    AfrOtaJobDocumentFields_t result = { 0 };
    bool ret;

    __CPROVER_assume( jobDocLength <= CBMC_JOBDOC_MAX_LEN );
    jobDoc = malloc( jobDocLength );

    __CPROVER_assume( fileIndex >= 0 );

    ret = populateJobDocFields( jobDoc,
                                jobDocLength,
                                fileIndex,
                                &result );
}

void proof_otaParser_parseJobDocFile( void )
{
    const char * jobDoc;
    const size_t jobDocLength;
    const uint8_t fileIndex;
    AfrOtaJobDocumentFields_t fields = { 0 };
    int8_t ret;

    __CPROVER_assume( jobDocLength <= CBMC_JOBDOC_MAX_LEN );
    jobDoc = malloc( jobDocLength );

    ret = otaParser_parseJobDocFile( jobDoc,
                                     jobDocLength,
                                     fileIndex,
                                     &fields );
}

int main()
{
    proof_Jobs_Describe();
    proof_Jobs_GetPending();
    proof_Jobs_GetTopic();
    proof_Jobs_MatchTopic();
    proof_Jobs_StartNext();
    proof_Jobs_Update();
    proof_Jobs_IsStartNextAccepted();
    proof_Jobs_IsJobUpdateStatus();
    proof_Jobs_StartNextMsg();
    proof_Jobs_UpdateMsg();
    proof_Jobs_GetJobId();
    proof_Jobs_GetJobDocument();
    proof_populateJobDocFields();
    proof_otaParser_parseJobDocFile();
}
