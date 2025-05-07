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

/** @brief The expected IP version and header length coded into the IP header itself. */
uint16_t usPacketIdentifier;
BaseType_t xTCPWindowLoggingLevel;
BaseType_t xBufferAllocFixedSize = pdFALSE;

BaseType_t NetworkInterfaceOutputFunction_Stub_Called = 0;

/* ======================== Stub Callback Functions ========================= */

BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    NetworkInterfaceOutputFunction_Stub_Called++;
    return 0;
}

/*
 * Return or send a packet to the other party.
 */
void prvTCPReturnPacket_IPV6( FreeRTOS_Socket_t * pxSocket,
                              NetworkBufferDescriptor_t * pxDescriptor,
                              uint32_t ulLen,
                              BaseType_t xReleaseAfterSend )
{
    /* Do Nothing */
}

/*
 * Let ARP look-up the MAC-address of the peer and initialise the first SYN
 * packet.
 */
BaseType_t prvTCPPrepareConnect_IPV6( FreeRTOS_Socket_t * pxSocket )
{
    return pdTRUE;
}

/*
 * Common code for sending a TCP protocol control packet (i.e. no options, no
 * payload, just flags).
 */
BaseType_t prvTCPSendSpecialPktHelper_IPV6( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                            uint8_t ucTCPFlags )
{
    return pdTRUE;
}
