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
 * @file Defender_GetTopic_harness.c
 * @brief Implements the proof harness for Defender_GetTopic function.
 */

#include "defender.h"

void harness()
{
    char * pTopicBuffer;
    uint16_t topicBufferLength;
    char * pThingName;
    uint16_t thingNameLength;
    DefenderTopic_t api;
    uint16_t * pOutLength;

    __CPROVER_assume( topicBufferLength < CBMC_MAX_OBJECT_SIZE );

    /* +1 is to ensure that we run the function for invalid thing name length as
     * well. */
    __CPROVER_assume( thingNameLength <= ( DEFENDER_THINGNAME_MAX_LENGTH + 1 ) );

    pTopicBuffer = malloc( topicBufferLength );
    pThingName = malloc( thingNameLength );
    pOutLength = malloc( sizeof( *pOutLength ) );

    Defender_GetTopic( pTopicBuffer,
                       topicBufferLength,
                       pThingName,
                       thingNameLength,
                       api,
                       pOutLength );
}
/*-----------------------------------------------------------*/
