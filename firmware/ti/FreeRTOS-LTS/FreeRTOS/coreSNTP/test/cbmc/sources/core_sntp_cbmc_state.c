/*
 * coreSNTP v1.3.1
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
 * @file core_sntp_cbmc_state.c
 * @brief Implements the functions defined in core_sntp_cbmc_state.h.
 */
#include <stdint.h>
#include <stdlib.h>
#include "core_sntp_client.h"
#include "core_sntp_cbmc_state.h"
#include "core_sntp_stubs.h"

SntpContext_t * unconstrainedCoreSntpContext()
{
    SntpServerInfo_t * pTimeServers;
    SntpContext_t * pContext;
    size_t currentServerIndex;
    size_t numOfServers;
    uint32_t serverResponseTimeoutMs;
    uint8_t * pNetworkBuffer;
    size_t bufferSize;
    UdpTransportInterface_t * pNetworkIntf;
    SntpAuthenticationInterface_t * pAuthIntf;
    SntpStatus_t sntpStatus = SntpSuccess;

    pContext = malloc( sizeof( SntpContext_t ) );

    __CPROVER_assume( numOfServers < MAX_NO_OF_SERVERS );
    __CPROVER_assume( serverResponseTimeoutMs < CBMC_MAX_OBJECT_SIZE );
    __CPROVER_assume( currentServerIndex < CBMC_MAX_OBJECT_SIZE );

    if( numOfServers == 0 )
    {
        pTimeServers = NULL;
    }
    else
    {
        pTimeServers = malloc( numOfServers * sizeof( SntpServerInfo_t ) );
    }

    if( pTimeServers != NULL )
    {
        for( size_t i = 0; i < numOfServers; i++ )
        {
            __CPROVER_assume( pTimeServers[ i ].serverNameLen < CBMC_MAX_OBJECT_SIZE );
            __CPROVER_assume( pTimeServers[ i ].port < CBMC_MAX_OBJECT_SIZE );
            pTimeServers[ i ].pServerName = malloc( pTimeServers[ i ].serverNameLen );
        }
    }

    __CPROVER_assume( bufferSize < CBMC_MAX_OBJECT_SIZE );
    pNetworkBuffer = malloc( bufferSize );

    pNetworkIntf = malloc( sizeof( UdpTransportInterface_t ) );

    if( pNetworkIntf != NULL )
    {
        pNetworkIntf->pUserContext = malloc( sizeof( NetworkContext_t ) );
        pNetworkIntf->sendTo = NetworkInterfaceSendStub;
        pNetworkIntf->recvFrom = NetworkInterfaceReceiveStub;
    }

    pAuthIntf = malloc( sizeof( SntpAuthenticationInterface_t ) );

    if( pAuthIntf != NULL )
    {
        pAuthIntf->pAuthContext = malloc( sizeof( SntpAuthContext_t ) );
        pAuthIntf->generateClientAuth = GenerateClientAuthStub;
        pAuthIntf->validateServerAuth = ValidateServerAuthStub;
    }

    /* It is part of the API contract to call Sntp_Init() with the SntpContext_t
     * before any other function in core_sntp_client.h. */
    if( pContext != NULL )
    {
        pContext->currentServerIndex = currentServerIndex;
        sntpStatus = Sntp_Init( pContext, pTimeServers, numOfServers, serverResponseTimeoutMs, pNetworkBuffer,
                                bufferSize, ResolveDnsFuncStub, GetTimeFuncStub, SetTimeFuncStub,
                                pNetworkIntf, pAuthIntf );
    }

    /* If the SntpContext_t initialization failed, then set the context to NULL
     * so that function under harness will return immediately upon a NULL
     * parameter check. */
    if( sntpStatus != SntpSuccess )
    {
        pContext = NULL;
    }

    return pContext;
}
