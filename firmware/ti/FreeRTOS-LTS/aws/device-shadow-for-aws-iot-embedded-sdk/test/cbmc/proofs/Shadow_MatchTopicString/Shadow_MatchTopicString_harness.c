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
 * @file Shadow_MatchTopicString_harness.c
 * @brief Implements the proof harness for Shadow_MatchTopicString function.
 */

#include "shadow.h"

#include <stdlib.h>

void harness()
{
    const char * pTopicName;
    uint16_t topicNameLength;
    ShadowMessageType_t * pMessageType;
    const char ** pThingName;
    uint16_t * pThingNameLength;
    const char ** pShadowName;
    uint16_t * pShadowNameLength;

    __CPROVER_assume( topicNameLength < TOPIC_STRING_LENGTH_MAX );
    pTopicName = malloc( topicNameLength );

    pMessageType = malloc( sizeof( *pMessageType ) );

    pThingName = malloc( sizeof( *pThingName ) );
    pThingNameLength = malloc( sizeof( *pThingNameLength ) );

    pShadowName = malloc( sizeof( *pShadowName ) );
    pShadowNameLength = malloc( sizeof( *pShadowNameLength ) );

    Shadow_MatchTopicString( pTopicName,
                             topicNameLength,
                             pMessageType,
                             pThingName,
                             pThingNameLength,
                             pShadowName,
                             pShadowNameLength );
}
