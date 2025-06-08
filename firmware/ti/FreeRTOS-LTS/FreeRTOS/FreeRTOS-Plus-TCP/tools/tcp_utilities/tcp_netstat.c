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

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"

#include "tcp_netstat.h"

extern List_t xBoundUDPSocketsList;

#if ( ipconfigUSE_TCP == 1 )
    extern List_t xBoundTCPSocketsList;
#endif /* ipconfigUSE_TCP == 1 */

IOCounters_t xInputCounters, xOutputCounters;

BaseType_t vGetMetrics( MetricsType_t * pxMetrics )
{
    BaseType_t xResult = 0;

    /* Show a simple listing of all created sockets and their connections */
    const ListItem_t * pxIterator;
    uint16_t usLastPort;

    memset( pxMetrics, 0, sizeof *pxMetrics );

    pxMetrics->xInput = xInputCounters;
    pxMetrics->xOutput = xOutputCounters;

    if( !listLIST_IS_INITIALISED( &xBoundUDPSocketsList ) )
    {
        FreeRTOS_printf( ( "PLUS-TCP not initialized\n" ) );
        xResult = -1;
    }
    else
    {
        #if ( ipconfigUSE_TCP == 1 )
            const ListItem_t * pxEndTCP = listGET_END_MARKER( &xBoundTCPSocketsList );
        #endif
        const ListItem_t * pxEndUDP = listGET_END_MARKER( &xBoundUDPSocketsList );

        usLastPort = 0U;

        #if ( ipconfigUSE_TCP == 1 )
        {
            vTaskSuspendAll();
            {
                for( pxIterator = listGET_HEAD_ENTRY( &xBoundTCPSocketsList );
                     pxIterator != pxEndTCP;
                     pxIterator = listGET_NEXT( pxIterator ) )
                {
                    const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator );

                    if( pxMetrics->xTCPPortList.uxCount < nstatMAX_TCP_PORTS )
                    {
                        if( usLastPort != pxSocket->usLocalPort )
                        {
                            pxMetrics->xTCPPortList.usTCPPortList[ pxMetrics->xTCPPortList.uxCount ] = pxSocket->usLocalPort;
                            pxMetrics->xTCPPortList.uxCount++;
                            usLastPort = pxSocket->usLocalPort;
                        }
                    }

                    if( pxMetrics->xTCPSocketList.uxCount < nstatMAX_TCP_PORTS )
                    {
                        size_t uxCount = pxMetrics->xTCPSocketList.uxCount;

                        pxMetrics->xTCPSocketList.xTCPList[ uxCount ].usLocalPort = pxSocket->usLocalPort;
                        pxMetrics->xTCPSocketList.xTCPList[ uxCount ].ulRemoteIP = pxSocket->u.xTCP.xRemoteIP.ulIP_IPv4;
                        pxMetrics->xTCPSocketList.xTCPList[ uxCount ].usRemotePort = pxSocket->u.xTCP.usRemotePort;
                        pxMetrics->xTCPSocketList.uxCount++;
                    }
                }
            }

            if( xTaskResumeAll() == 0 )
            {
                taskYIELD();
            }
        }
        #endif /* ( ipconfigUSE_TCP == 1 ) */

        vTaskSuspendAll();
        {
            for( pxIterator = listGET_HEAD_ENTRY( &xBoundUDPSocketsList );
                 pxIterator != pxEndUDP;
                 pxIterator = listGET_NEXT( pxIterator ) )
            {
                const FreeRTOS_Socket_t * pxSocket = ( const FreeRTOS_Socket_t * ) listGET_LIST_ITEM_OWNER( pxIterator );

                if( pxMetrics->xUDPPortList.uxCount < nstatMAX_UDP_PORTS )
                {
                    pxMetrics->xUDPPortList.usUDPPortList[ pxMetrics->xUDPPortList.uxCount ] = pxSocket->usLocalPort;
                    pxMetrics->xUDPPortList.uxCount++;
                }

                if( pxMetrics->xUDPSocketList.uxCount < nstatMAX_UDP_PORTS )
                {
                    size_t uxCount = pxMetrics->xUDPSocketList.uxCount;
                    pxMetrics->xUDPSocketList.xUDPList[ uxCount ].usLocalPort = pxSocket->usLocalPort;
                    pxMetrics->xUDPSocketList.uxCount++;
                }
            }
        }
        ( void ) xTaskResumeAll();
    }

    return xResult;
}

void vShowMetrics( const MetricsType_t * pxMetrics )
{
    size_t uxIndex;

    FreeRTOS_printf( ( "Bytes in/out:\n" ) );
    FreeRTOS_printf( ( "    Input  : %5lu packets, %5lu bytes\n",
                       pxMetrics->xInput.uxPacketCount,
                       pxMetrics->xInput.uxByteCount ) );
    FreeRTOS_printf( ( "    Output : %5lu packets, %5lu bytes\n",
                       pxMetrics->xOutput.uxPacketCount,
                       pxMetrics->xOutput.uxByteCount ) );

    #if ( ipconfigUSE_TCP == 1 )
    {
        FreeRTOS_printf( ( "TCP ports:\n" ) );

        for( uxIndex = 0; uxIndex < pxMetrics->xTCPPortList.uxCount; uxIndex++ )
        {
            FreeRTOS_printf( ( "    local port: %u\n",
                               pxMetrics->xTCPPortList.usTCPPortList[ uxIndex ] ) );
        }

        FreeRTOS_printf( ( "TCP sockets:\n" ) );

        for( uxIndex = 0; uxIndex < pxMetrics->xTCPSocketList.uxCount; uxIndex++ )
        {
            FreeRTOS_printf( ( "    local port: %u remote IP %xip:%u\n",
                               pxMetrics->xTCPSocketList.xTCPList[ uxIndex ].usLocalPort,
                               pxMetrics->xTCPSocketList.xTCPList[ uxIndex ].ulRemoteIP,
                               pxMetrics->xTCPSocketList.xTCPList[ uxIndex ].usRemotePort ) );
        }
    }
    #endif /* ( ipconfigUSE_TCP == 1 ) */

    FreeRTOS_printf( ( "UDP ports:\n" ) );

    for( uxIndex = 0; uxIndex < pxMetrics->xUDPPortList.uxCount; uxIndex++ )
    {
        FreeRTOS_printf( ( "    local port: %u\n",
                           pxMetrics->xUDPPortList.usUDPPortList[ uxIndex ] ) );
    }

    FreeRTOS_printf( ( "UDP sockets:\n" ) );

    for( uxIndex = 0; uxIndex < pxMetrics->xUDPSocketList.uxCount; uxIndex++ )
    {
        FreeRTOS_printf( ( "    local port: %u\n",
                           pxMetrics->xUDPSocketList.xUDPList[ uxIndex ].usLocalPort ) );
    }
}
