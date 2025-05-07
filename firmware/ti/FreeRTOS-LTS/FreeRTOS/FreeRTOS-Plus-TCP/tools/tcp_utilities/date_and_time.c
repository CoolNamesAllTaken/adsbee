/*
 * FreeRTOS+TCP V4.2.2
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */


#include <stdio.h>
#include <string.h>
#include <time.h>

#include "FreeRTOS.h"
#include "task.h"

#include "date_and_time.h"

int iTimeZone;

uint32_t ulSeconds, ulMsec;

/*
 * You can add the following code to you FreeRTOSConfig file:
 *
 *  extern TickType_t ulSeconds, ulMsec;
 *
 #define traceINCREASE_TICK_COUNT( xTicksToJump ) \
 *  { \
 *      ulMsec += xTicksToJump; \
 *      if( ulMsec >= 1000 ) \
 *      { \
 *          ulSeconds += ( ulMsec / 1000ul ); \
 *          ulMsec = ( ulMsec % 1000ul ); \
 *      } \
 *  }
 *
 *
 #define traceTASK_INCREMENT_TICK( xTickCount ) \
 *  if( uxSchedulerSuspended == ( UBaseType_t ) pdFALSE ) \
 *  { \
 *      if( ++ulMsec >= 1000 ) \
 *      { \
 *          ulMsec = 0; \
 *          ulSeconds++; \
 *      } \
 *  }
 *
 */


time_t FreeRTOS_time( time_t * pxTime )
{
    time_t uxTime;

    /* Critical section required if running on a 16 bit processor. */
    portTICK_TYPE_ENTER_CRITICAL();
    {
        uxTime = ( time_t ) ulSeconds;
    }
    portTICK_TYPE_EXIT_CRITICAL();

    if( pxTime != NULL )
    {
        *pxTime = uxTime;
    }

    return uxTime;
}
/*-----------------------------------------------------------*/

void FreeRTOS_settime( time_t * pxTime )
{
    /* Critical section required if running on a 16 bit processor. */
    portTICK_TYPE_ENTER_CRITICAL();
    {
        ulSeconds = ( uint32_t ) *pxTime;
        ulMsec = ( uint32_t ) 0;
    }
    portTICK_TYPE_EXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

time_t FreeRTOS_get_secs_msec( time_t * pulMsec )
{
    time_t uxReturn;

    /* Critical section required if running on a 16 bit processor. */
    portTICK_TYPE_ENTER_CRITICAL();
    {
        uxReturn = ( time_t ) ulSeconds;

        if( pulMsec != NULL )
        {
            *pulMsec = ulMsec;
        }
    }
    portTICK_TYPE_EXIT_CRITICAL();

    return uxReturn;
}
/*-----------------------------------------------------------*/


void FreeRTOS_set_secs_msec( time_t * pulSeconds,
                             time_t * pulMsec )
{
    /* Critical section required if running on a 16 bit processor. */
    portTICK_TYPE_ENTER_CRITICAL();
    {
        ulSeconds = *pulSeconds;

        if( pulMsec != NULL )
        {
            ulMsec = *pulMsec;
        }
    }
    portTICK_TYPE_EXIT_CRITICAL();
}
/*-----------------------------------------------------------*/
