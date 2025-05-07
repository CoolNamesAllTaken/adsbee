/*
 * coreHTTP v3.1.1
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#include "transport_interface_stubs.h"

int32_t TransportInterfaceSendStub( NetworkContext_t * pNetworkContext,
                                    void * pBuffer,
                                    size_t bytesToSend )
{
    /* The number of tries to send the message before this invocation */
    static int32_t tries = 0;
    /* The number of bytes considered sent after this invocation */
    int32_t ret;

    __CPROVER_assert( pBuffer != NULL,
                      "TransportInterfaceSendStub pBuffer is NULL" );

    /****************************************************************
    * The send method sends some portion of the message and returns the
    * total number of bytes in the prefix sent so far.  The send method
    * is used in a loop of the form
    *
    *   while ( send( conn, msg, len )  < len ) { ... }
    *
    * We need to bound the number of loop iterations, so we need to
    * bound the number of times it takes for send to finish sending the
    * message.  We use a static variable 'tries' to count the number of
    * times send has tried to send the message, and we force send to
    * finish the message after MAX_TRIES tries.
    ****************************************************************/

    if( bytesToSend <= INT32_MAX )
    {
        __CPROVER_assume( ret <= ( int32_t ) bytesToSend );
    }

    tries++;

    if( tries >= MAX_TRIES )
    {
        tries = 0;

        /* In order to stop the looping on send we must return an error or
         * bytesToSend. We return an error instead of bytesToSend because
         * bytesToSend may be a value larger than INT32_MAX. */
        ret = -1;
    }

    return ret;
}

int32_t TransportInterfaceReceiveStub( NetworkContext_t * pNetworkContext,
                                       void * pBuffer,
                                       size_t bytesToRecv )
{
    /* The number of bytes considered received after this invocation */
    int32_t ret;

    __CPROVER_assert( pBuffer != NULL,
                      "TransportInterfaceReceiveStub pBuffer is NULL" );

    if( bytesToRecv <= INT32_MAX )
    {
        __CPROVER_assume( ret <= ( int32_t ) bytesToRecv );
    }

    return ret;
}
