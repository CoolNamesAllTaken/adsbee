/*
 * AWS IoT Jobs v1.3.0
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

#ifndef JOBS_ANNEX_H_
#define JOBS_ANNEX_H_

#include "jobs.h"

/**
 * @brief check that an enum belongs to JobsTopic_t
 */
#define jobsTopicEnum( x )         ( ( x >= JobsInvalidTopic ) && ( x < JobsMaxTopic ) )

/**
 * @brief check that an enum belongs to a subset of JobsStatus_t
 * returned by the named function
 */
#define parameterEnum( x )         ( x == JobsBadParameter )
#define strnAppendFailEnum( x )    ( x == JobsBufferTooSmall )
#define strnAppendEnum( x )        ( ( x == JobsSuccess ) || strnAppendFailEnum( x ) )
#define jobsCommonEnum( x )        ( parameterEnum( x ) || strnAppendEnum( x ) )
#define jobsGetTopicEnum( x )      jobsCommonEnum( x )
#define jobsGetPendingEnum( x )    jobsCommonEnum( x )
#define jobsStartNextEnum( x )     jobsCommonEnum( x )
#define jobsDescribeEnum( x )      jobsCommonEnum( x )
#define jobsUpdateEnum( x )        jobsCommonEnum( x )
#define strnEqFailEnum( x )        ( x == JobsNoMatch )
#define strnEqEnum( x )            ( ( x == JobsSuccess ) || strnEqFailEnum( x ) )
#define jobsMatchTopicEnum( x )    ( parameterEnum( x ) || strnEqEnum( x ) )

/*
 * These are declarations for the (normally) static functions from jobs.c.
 * Please see jobs.c for documentation.
 */

JobsStatus_t strnAppend( char * buffer,
                         size_t * start,
                         size_t max,
                         const char * value,
                         size_t valueLength );

JobsStatus_t strnEq( const char * a,
                     const char * b,
                     size_t n );

#endif /* ifndef JOBS_ANNEX_H_ */
