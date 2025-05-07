/*
 * AWS IoT Fleet Provisioning v1.2.1
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file FleetProvisioning_GetRegisterThingTopic_harness.c
 * @brief Implements the proof harness for FleetProvisioning_GetRegisterThingTopic function.
 */

#include <stdlib.h>
#include "fleet_provisioning.h"

void harness()
{
    char * pTopicBuffer;
    uint16_t topicBufferLength;
    FleetProvisioningFormat_t format;
    FleetProvisioningApiTopics_t topic;
    const char * pTemplateName;
    uint16_t templateNameLength;
    uint16_t * pOutLength;

    __CPROVER_assume( topicBufferLength < CBMC_MAX_OBJECT_SIZE );

    /* +1 is to ensure that we run the function for invalid template name
     * lengths as well. */
    __CPROVER_assume( templateNameLength <= ( FP_TEMPLATENAME_MAX_LENGTH + 1 ) );

    pTopicBuffer = malloc( topicBufferLength );
    pTemplateName = malloc( templateNameLength );
    pOutLength = malloc( sizeof( *pOutLength ) );

    FleetProvisioning_GetRegisterThingTopic( pTopicBuffer,
                                             topicBufferLength,
                                             format,
                                             topic,
                                             pTemplateName,
                                             templateNameLength,
                                             pOutLength );
}
