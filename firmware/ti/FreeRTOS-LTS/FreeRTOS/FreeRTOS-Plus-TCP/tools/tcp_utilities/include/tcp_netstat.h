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

#ifndef TCP_NETSTAT_H

#define TCP_NETSTAT_H

#ifndef nstatMAX_UDP_PORTS
    #define nstatMAX_UDP_PORTS    12U
#endif

#ifndef nstatMAX_TCP_PORTS
    #define nstatMAX_TCP_PORTS    12U
#endif

#ifndef nstatMAX_UDP_SOCKETS
    #define nstatMAX_UDP_SOCKETS    12U
#endif

#ifndef nstatMAX_TCP_SOCKETS
    #define nstatMAX_TCP_SOCKETS    12U
#endif

typedef struct xIOCounters
{
    size_t uxByteCount;
    size_t uxPacketCount;
} IOCounters_t;

extern IOCounters_t xInputCounters, xOutputCounters;

typedef struct
{
    uint16_t usUDPPortList[ nstatMAX_UDP_PORTS ];
    size_t uxCount;
} UDPPortList_t;

typedef struct
{
    uint16_t usTCPPortList[ nstatMAX_TCP_PORTS ];
    size_t uxCount;
} TCPPortList_t;


typedef struct
{
    uint16_t usLocalPort;
    uint16_t usRemotePort;
    uint32_t ulRemoteIP;
} TCPEntry_t;

typedef struct
{
    TCPEntry_t xTCPList[ nstatMAX_TCP_SOCKETS ];
    size_t uxCount;
} TCPSocketList_t;

typedef struct
{
    uint16_t usLocalPort;
} UDPEntry_t;

typedef struct
{
    UDPEntry_t xUDPList[ nstatMAX_UDP_SOCKETS ];
    size_t uxCount;
} UDPSocketList_t;

typedef struct
{
    UDPPortList_t xUDPPortList;
    TCPPortList_t xTCPPortList;
    TCPSocketList_t xTCPSocketList;
    UDPSocketList_t xUDPSocketList;
    IOCounters_t xInput;
    IOCounters_t xOutput;
} MetricsType_t;

extern BaseType_t vGetMetrics( MetricsType_t * pxMetrics );
extern void vShowMetrics( const MetricsType_t * pxMetrics );


#define iptraceNETWORK_INTERFACE_INPUT( uxDataLength, pucEthernetBuffer ) \
    xInputCounters.uxByteCount += uxDataLength;                           \
    xInputCounters.uxPacketCount++;

#define iptraceNETWORK_INTERFACE_OUTPUT( uxDataLength, pucEthernetBuffer ) \
    xOutputCounters.uxByteCount += uxDataLength;                           \
    xOutputCounters.uxPacketCount++;


#endif /* TCP_NETSTAT_H */
