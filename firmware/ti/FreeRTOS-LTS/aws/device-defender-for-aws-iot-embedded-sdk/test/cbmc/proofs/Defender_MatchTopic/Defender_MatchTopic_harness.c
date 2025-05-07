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
 * @file Defender_MatchTopic_harness.c
 * @brief Implements the proof harness for Defender_MatchTopic function.
 */

#include "defender.h"

void harness()
{
    const char * pTopic;
    uint16_t topicLength;
    DefenderTopic_t * pOutApi;
    const char ** ppOutThingName;
    uint16_t * pOutThingNameLength;

    __CPROVER_assume( topicLength < TOPIC_STRING_LENGTH_MAX );

    pTopic = malloc( topicLength );
    pOutApi = malloc( sizeof( *pOutApi ) );
    ppOutThingName = malloc( sizeof( *ppOutThingName ) );
    pOutThingNameLength = malloc( sizeof( *pOutThingNameLength ) );

    Defender_MatchTopic( pTopic,
                         topicLength,
                         pOutApi,
                         ppOutThingName,
                         pOutThingNameLength );
}
/*-----------------------------------------------------------*/
