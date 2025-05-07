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


/* Include Unity header */
#include <unity.h>

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* =========================  EXTERN VARIABLES  ========================= */

BaseType_t xTCPWindowLoggingLevel = 0;

static Socket_t xHandleConnectedSocket;
static size_t xHandleConnectedLength;

/* Defined in FreeRTOS_Sockets.c */
#if ( ipconfigUSE_TCP == 1 )
    List_t xBoundTCPSocketsList;
#endif

/* ======================== Stub Callback Functions ========================= */

/**
 * @brief Process the received TCP packet.
 */
BaseType_t xProcessReceivedTCPPacket_IPV6( NetworkBufferDescriptor_t * pxDescriptor )
{
    return pdTRUE;
}

static void HandleConnected( Socket_t xSocket,
                             size_t xLength )
{
    TEST_ASSERT_EQUAL( xHandleConnectedSocket, xSocket );
    TEST_ASSERT_EQUAL( xHandleConnectedLength, xLength );
}

/**
 * @brief Set the ACK message to NULL.
 */
static void prvTCPReturnPacket_StubReturnNULL( FreeRTOS_Socket_t * pxSocket,
                                               NetworkBufferDescriptor_t * pxDescriptor,
                                               uint32_t ulLen,
                                               BaseType_t xReleaseAfterSend,
                                               int timesCalled )
{
    ( void ) pxDescriptor;
    ( void ) ulLen;
    ( void ) xReleaseAfterSend;
    ( void ) timesCalled;
    pxSocket->u.xTCP.pxAckMessage = NULL;
}
