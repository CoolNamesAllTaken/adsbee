/*
 * backoffAlgorithm v1.4.1
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

#include <string.h>
#include <stdbool.h>
#include <stdlib.h>

/* Unity include. */
#include "unity.h"

/* Include utility for catching assert failures. */
#include "catch_assert.h"

/* Backoff Algorithm library include */
#include "backoff_algorithm.h"

#define TEST_BACKOFF_BASE_VALUE    ( 1000 )
#define TEST_BACKOFF_MAX_VALUE     ( 10000 )
#define TEST_MAX_ATTEMPTS          ( 5 )
/* Parameters to track the next max jitter or number of attempts done. */
static BackoffAlgorithmContext_t retryParams;
/* Return value of #BackoffAlgorithm_GetNextBackoff. */
static BackoffAlgorithmStatus_t BackoffAlgorithmStatus;
static uint16_t nextBackoff;
static uint32_t testRandomVal;

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    /* Initialize context. */
    BackoffAlgorithm_InitializeParams( &retryParams,
                                       TEST_BACKOFF_BASE_VALUE,
                                       TEST_BACKOFF_MAX_VALUE,
                                       TEST_MAX_ATTEMPTS );
}

/* Called after each test method. */
void tearDown()
{
    testRandomVal = 0;
    BackoffAlgorithmStatus = BackoffAlgorithmSuccess;
    nextBackoff = 0;
}

/* Called at the beginning of the whole suite. */
void suiteSetUp()
{
}

/* Called at the end of the whole suite. */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

/* ========================================================================== */

/**
 * @brief Helper method to make assertions on data of the context object.
 */
static void verifyContextData( BackoffAlgorithmContext_t * pContext,
                               uint32_t expectedAttemptsDone,
                               uint16_t expectedNextJitterMax,
                               uint16_t expectedMaxBackoff,
                               uint32_t expectedMaxAttempts )
{
    TEST_ASSERT_EQUAL( expectedNextJitterMax, pContext->nextJitterMax );
    TEST_ASSERT_EQUAL( expectedAttemptsDone, pContext->attemptsDone );
    TEST_ASSERT_EQUAL( expectedMaxAttempts, pContext->maxRetryAttempts );
    TEST_ASSERT_EQUAL( expectedMaxBackoff, pContext->maxBackoffDelay );
}

/**
 * @brief Test that #BackoffAlgorithm_InitializeParams encounters an assert
 * failure when a NULL context parameter is passed.
 */
void test_BackoffAlgorithm_InitializeParams_Invalid_Context( void )
{
    catch_assert( BackoffAlgorithm_InitializeParams( NULL /* Invalid context */,
                                                     TEST_BACKOFF_BASE_VALUE,
                                                     TEST_BACKOFF_MAX_VALUE,
                                                     TEST_MAX_ATTEMPTS ) );
}

/**
 * @brief Test that #BackoffAlgorithm_InitializeParams initializes the context
 * data as expected.
 */
void test_BackoffAlgorithm_InitializeParams_Sets_Jitter_Correctly( void )
{
    BackoffAlgorithm_InitializeParams( &retryParams,
                                       TEST_BACKOFF_BASE_VALUE,
                                       TEST_BACKOFF_MAX_VALUE,
                                       TEST_MAX_ATTEMPTS );
    verifyContextData( &retryParams,
                       0,
                       TEST_BACKOFF_BASE_VALUE,
                       TEST_BACKOFF_MAX_VALUE,
                       TEST_MAX_ATTEMPTS );
}

/**
 * @brief Test that #BackoffAlgorithm_GetNextBackoff returns the expected next back-off
 * value and updates the contents of the context as expected when the random value
 * generated is lower than the max jitter value for the retry attempts.
 *
 * This test assumes that the max jitter value has not reached the configured
 * maximum back-off value.
 */
void test_BackoffAlgorithm_GetNextBackoff_Success_RandVal_Less_Than_Jitter_Max( void )
{
    int iter = 1;
    uint16_t expectedAttemptsDone = 0;
    uint16_t expectedNextJitterMax = TEST_BACKOFF_BASE_VALUE;
    uint16_t expectedNextBackoff = 0;

    for( ; iter < 2; iter++ )
    {
        /* Set the random value as a value lower than
         * the jitter max value for the next retry attempt. */
        testRandomVal = retryParams.nextJitterMax / 2;

        /* As the random value is less than the max jitter value, the expected
         * next backoff value should remain the same as the random value. */
        expectedNextBackoff = testRandomVal;

        /* The jitter max value should double with the above call for use in next call. */
        expectedNextJitterMax *= 2;

        /* The number of attempts should be updated by the above API call. */
        expectedAttemptsDone++;

        TEST_ASSERT_LESS_THAN( TEST_BACKOFF_MAX_VALUE, expectedNextJitterMax );

        /* Call the BackoffAlgorithm_GetNextBackoff API a couple times. */
        TEST_ASSERT_EQUAL( BackoffAlgorithmSuccess,
                           BackoffAlgorithm_GetNextBackoff( &retryParams, testRandomVal, &nextBackoff ) );
        TEST_ASSERT_EQUAL( expectedNextBackoff, nextBackoff );

        /* Verify that the context data for expected data after the API call. */
        verifyContextData( &retryParams,
                           expectedAttemptsDone,
                           expectedNextJitterMax,
                           TEST_BACKOFF_MAX_VALUE,
                           TEST_MAX_ATTEMPTS );
    }
}

/**
 * @brief Test that #BackoffAlgorithm_GetNextBackoff returns the expected next back-off
 * value and updates the contents of the context when the random value generated
 * is higher than the max jitter value for the retry attempts.
 *
 * This test assumes that the max jitter value has not reached the configured
 * maximum back-off value.
 */
void test_BackoffAlgorithm_GetNextBackoff_Success_RandVal_More_Than_Jitter_Max( void )
{
    int iter = 1;
    uint16_t expectedAttemptsDone = 0;
    uint16_t expectedNextJitterMax = TEST_BACKOFF_BASE_VALUE;

    for( ; iter < 2; iter++ )
    {
        /* Set the random value as a value greater than
         * the jitter max value for the next retry attempt. */
        testRandomVal = retryParams.nextJitterMax + 1;

        /* The jitter max value should double with the above call for use in next call. */
        expectedNextJitterMax *= 2;
        TEST_ASSERT_LESS_THAN( TEST_BACKOFF_MAX_VALUE, expectedNextJitterMax );

        /* The number of attempts should be updated by the above API call. */
        expectedAttemptsDone++;

        /* As the random value is greater than the jitter max value, the expected
         * next backoff value should be truncated to a value within the jitter window
         * for the retry attempt. */
        uint16_t expectedNextBackoff = ( testRandomVal % ( retryParams.nextJitterMax + 1U ) );

        /* Call the BackoffAlgorithm_GetNextBackoff API a couple times. */
        TEST_ASSERT_EQUAL( BackoffAlgorithmSuccess,
                           BackoffAlgorithm_GetNextBackoff( &retryParams, testRandomVal, &nextBackoff ) );
        TEST_ASSERT_EQUAL( expectedNextBackoff, nextBackoff );

        /* Verify that the context data for expected data after the API call. */
        verifyContextData( &retryParams,
                           expectedAttemptsDone,
                           expectedNextJitterMax,
                           TEST_BACKOFF_MAX_VALUE,
                           TEST_MAX_ATTEMPTS );
    }
}

/**
 * @brief Tests the #BackoffAlgorithm_GetNextBackoff API when the next back-off value
 * is requested for exhausted retry attempts.
 */
void test_BackoffAlgorithm_GetNextBackoff_Attempts_Exhausted()
{
    /* Update the context data to represent that maximum configured number of
     * retry attempts have been completed. */
    retryParams.attemptsDone = TEST_MAX_ATTEMPTS;

    /* Call the BackoffAlgorithm_GetNextBackoff API. */
    TEST_ASSERT_EQUAL( BackoffAlgorithmRetriesExhausted,
                       BackoffAlgorithm_GetNextBackoff( &retryParams, testRandomVal, &nextBackoff ) );
    /* Make sure that the value of the output parameter has not changed. */
    TEST_ASSERT_EQUAL( 0, nextBackoff );

    /* Make sure that the context data has not changed as the call to
     * BackoffAlgorithm_GetNextBackoff failed. */
    verifyContextData( &retryParams,
                       TEST_MAX_ATTEMPTS /* Number of attempts shouldn't change */,
                       TEST_BACKOFF_BASE_VALUE,
                       TEST_BACKOFF_MAX_VALUE,
                       TEST_MAX_ATTEMPTS );
}

/**
 * @brief Tests that the #BackoffAlgorithm_GetNextBackoff API does not calculate a backoff period
 * beyond the configured maximum backoff period.
 */
void test_BackoffAlgorithm_GetNextBackoff_Returns_Cap_Backoff( void )
{
    /* Initialize to 0 attempts, so the max value of next jitter will increase. */
    retryParams.attemptsDone = 0U;

    /* Update the next jitter value to greater than half the maximum backoff so
     * that the BackoffAlgorithm_GetNextBackoff API updates the next jitter value to
     * the configured maximum backoff value. */
    retryParams.nextJitterMax = ( TEST_BACKOFF_MAX_VALUE / 2U ) + 1;

    /* Set the random value equal to the current jitter max value.
     * Thus, the BackoffAlgorithm_GetNextBackoff API should return the random value as
     * the next back-off value. */
    testRandomVal = retryParams.nextJitterMax;
    uint16_t expectedBackoffVal = testRandomVal;

    /* Call the BackoffAlgorithm_GetNextBackoff API. */
    TEST_ASSERT_EQUAL( BackoffAlgorithmSuccess,
                       BackoffAlgorithm_GetNextBackoff( &retryParams, testRandomVal, &nextBackoff ) );
    /* Make sure that the expected value is returned for the next backoff. */
    TEST_ASSERT_EQUAL( expectedBackoffVal, nextBackoff );

    /* Verify that the next jitter max value has been set to the cap back-off value
     * configured in the context. */
    verifyContextData( &retryParams,
                       1,
                       TEST_BACKOFF_MAX_VALUE /* New jitter max */,
                       TEST_BACKOFF_MAX_VALUE,
                       TEST_MAX_ATTEMPTS );


    /* Now, set the random value as the maximum back-off value to
     * expect that the next back-off value returned by the API is the maximum
     * back-off value.*/
    testRandomVal = TEST_BACKOFF_MAX_VALUE;

    /* Call BackoffAlgorithm_GetNextBackoff API again to verify that it now returns the
     * cap value as the next back-off value. */
    TEST_ASSERT_EQUAL( BackoffAlgorithmSuccess,
                       BackoffAlgorithm_GetNextBackoff( &retryParams, testRandomVal, &nextBackoff ) );
    /* Make sure that the capped backoff value is returned as the next backoff value . */
    TEST_ASSERT_EQUAL( TEST_BACKOFF_MAX_VALUE, nextBackoff );

    /* Verify that the context data for expected data after the API call. */
    verifyContextData( &retryParams,
                       2,
                       TEST_BACKOFF_MAX_VALUE /* jitter max remains unchanged */,
                       TEST_BACKOFF_MAX_VALUE,
                       TEST_MAX_ATTEMPTS );
}

/**
 * @brief Tests the #BackoffAlgorithm_GetNextBackoff API when the next jitter max value
 * is one lower than half of the maximum backoff value. This tests that the API does not
 * update the next jitter max to the maximum backoff value in this case.
 */
void test_BackoffAlgorithm_GetNextBackoff_NextJitterMax_Below_Cap_Backoff( void )
{
    /* Initialize context.
     * Use the configuration constant of retrying forever to achieve branch coverage in tests
     * for the configuration. */
    BackoffAlgorithm_InitializeParams( &retryParams,
                                       TEST_BACKOFF_BASE_VALUE,
                                       TEST_BACKOFF_MAX_VALUE,
                                       BACKOFF_ALGORITHM_RETRY_FOREVER );

    /* Initialize to 0 attempts, so the max value of next jitter will increase. */
    retryParams.attemptsDone = 0U;

    /* Set the random value to zero to test that the BackoffAlgorithm_GetNextBackoff
     * API will return zero as the next back-off value.*/
    testRandomVal = 0;

    /* Update the next jitter max value to one less than half of max backoff
     * to make sure that the BackoffAlgorithm_GetNextBackoff API does not update it
     * to the cap value in the call.*/
    retryParams.nextJitterMax = ( TEST_BACKOFF_MAX_VALUE / 2U ) - 1;

    /* Call the BackoffAlgorithm_GetNextBackoff API. */
    TEST_ASSERT_EQUAL( BackoffAlgorithmSuccess,
                       BackoffAlgorithm_GetNextBackoff( &retryParams, testRandomVal, &nextBackoff ) );
    /* Make sure that zero is returned as the next backoff value . */
    TEST_ASSERT_EQUAL( 0, nextBackoff );

    /* Verify that the context data for expected data after the API call. */
    verifyContextData( &retryParams,
                       1,
                       TEST_BACKOFF_MAX_VALUE - 2U /* next jitter max value */,
                       TEST_BACKOFF_MAX_VALUE,
                       BACKOFF_ALGORITHM_RETRY_FOREVER );
}

/**
 * @brief Tests that the #BackoffAlgorithm_GetNextBackoff API encounters assert failures
 *  when called with invalid parameters.
 */
void test_BackoffAlgorithm_GetNextBackoff_Invalid_Params()
{
    /* Invalid context. */
    catch_assert( BackoffAlgorithm_GetNextBackoff( NULL, testRandomVal, &nextBackoff ) );

    /* Invalid output parameter for next back-off. */
    catch_assert( BackoffAlgorithm_GetNextBackoff( &retryParams, testRandomVal, NULL ) );
}
