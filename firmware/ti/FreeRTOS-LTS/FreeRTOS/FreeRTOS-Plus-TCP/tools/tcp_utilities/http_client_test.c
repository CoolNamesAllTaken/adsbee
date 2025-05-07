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


/**
 * @file http_client.c
 * @brief Implements the Domain Name System for the FreeRTOS+TCP network stack.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_Routing.h"

#include "http_client_test.h"

/* Exclude the whole file if FreeRTOSIPConfig.h is configured to use UDP only. */
#if ( ipconfigUSE_TCP == 1 )

    #ifndef echoNUM_HTTP_CLIENTS
        /* The number of instances of the echo client task to create. */
        #define echoNUM_HTTP_CLIENTS    ( 2 )
    #endif

    #ifndef httpREMOTE_FILENAME
        #define httpREMOTE_FILENAME    "/index.html"
    #endif

/* The echo tasks create a socket, send out a number of echo requests, listen
 * for the echo reply, then close the socket again before starting over.  This
 * delay is used between each iteration to ensure the network does not get too
 * congested. */
    #define echoLOOP_DELAY    ( ( TickType_t ) 150 / portTICK_PERIOD_MS )

/* The echo server is assumed to be on port 7, which is the standard echo
 * protocol port. */

    #define echoECHO_PORT    ( 80 )

/* If ipconfigUSE_TCP_WIN is 1 then the Tx socket will use a buffer size set by
 * ipconfigTCP_TX_BUF_LEN, and the Tx window size will be
 * configECHO_CLIENT_TX_WINDOW_SIZE times the buffer size.  Note
 * ipconfigTCP_TX_BUF_LEN is set in FreeRTOSIPConfig.h as it is a standard TCP/IP
 * stack constant, whereas configECHO_CLIENT_TX_WINDOW_SIZE is set in
 * FreeRTOSConfig.h as it is a demo application constant. */
    #ifndef configECHO_CLIENT_TX_WINDOW_SIZE
        #define configECHO_CLIENT_TX_WINDOW_SIZE    2
    #endif

/* If ipconfigUSE_TCP_WIN is 1 then the Rx socket will use a buffer size set by
 * ipconfigTCP_RX_BUFFER_LENGTH, and the Rx window size will be
 * configECHO_CLIENT_RX_WINDOW_SIZE times the buffer size.  Note
 * ipconfigTCP_RX_BUFFER_LENGTH is set in FreeRTOSIPConfig.h as it is a standard TCP/IP
 * stack constant, whereas configECHO_CLIENT_RX_WINDOW_SIZE is set in
 * FreeRTOSConfig.h as it is a demo application constant. */
    #ifndef configECHO_CLIENT_RX_WINDOW_SIZE
        #define configECHO_CLIENT_RX_WINDOW_SIZE    2
    #endif

    static uint16_t usUsePortNumber = echoECHO_PORT;

/*2404:6800:4003:c02::5e */
/*66.96.149.18 */
/*-----------------------------------------------------------*/

/*
 * Uses a socket to send data to, then receive data from, the standard echo
 * port number 7.
 */
    static void prvEchoClientTask( void * pvParameters );

    void printBuffer( const char * apBuffer,
                      int aLen,
                      int aLineLen,
                      const char * apPrefix );

/*-----------------------------------------------------------*/

/* Counters for each created task - for inspection only. */
    static uint32_t ulTxRxCycles[ echoNUM_HTTP_CLIENTS ] = { 0 },
                    ulConnections[ echoNUM_HTTP_CLIENTS ] = { 0 },
                    xIPVersion[ echoNUM_HTTP_CLIENTS ] = { 0 };

    static TaskHandle_t xSocketTaskHandles[ echoNUM_HTTP_CLIENTS ];

/* When element is non-zero, the corresponding task may run. */
    static BaseType_t xAllowedToStart[ echoNUM_HTTP_CLIENTS ] = { 0 };

/* Each task connects to its own host. */
    static char pcHostNames[ echoNUM_HTTP_CLIENTS ][ ipconfigDNS_CACHE_NAME_LENGTH ];

/* Each task retrieves its own file. */
    static char pcFileNames[ echoNUM_HTTP_CLIENTS ][ ipconfigDNS_CACHE_NAME_LENGTH ];

    const char get_command[] =
        "GET %s HTTP/1.1\x0d\x0a"
        "Host: %s\x0d\x0a"
        "User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:68.0) Gecko/20100101 Firefox/68.0\x0d\x0a"
        "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\x0d\x0a"
        "Accept-Language: en-US,en;q=0.5\x0d\x0a"
        "DNT: 1\x0d\x0a"
        "Connection: keep-alive\x0d\x0a"
        "Upgrade-Insecure-Requests: 1\x0d\x0a"
        "If-Modified-Since: Fri, 16 Aug 2019 05:18:19 GMT\x0d\x0a"
        "\x0d\x0a";

/*-----------------------------------------------------------*/

    void vStartHTTPClientTest( uint16_t usTaskStackSize,
                               UBaseType_t uxTaskPriority )
    {
        BaseType_t x;
        static char pcNames[ echoNUM_HTTP_CLIENTS ][ configMAX_TASK_NAME_LEN + 1 ];
        static BaseType_t xHasStarted = pdFALSE;

        if( xHasStarted == pdFALSE )
        {
            xHasStarted = pdTRUE;

            /* Create the echo client tasks. */
            for( x = 0; x < echoNUM_HTTP_CLIENTS; x++ )
            {
                snprintf( pcNames[ x ], sizeof pcNames[ x ], "Client_%ld", x );
                xTaskCreate( prvEchoClientTask,              /* The function that implements the task. */
                             pcNames[ x ],                   /* Just a text name for the task to aid debugging. */
                             usTaskStackSize,                /* The stack size is defined in FreeRTOSIPConfig.h. */
                             ( void * ) x,                   /* The task parameter, not used in this case. */
                             uxTaskPriority,                 /* The priority assigned to the task is defined in FreeRTOSConfig.h. */
                             &( xSocketTaskHandles[ x ] ) ); /* Remember the handle. */
            }
        }
    }
/*-----------------------------------------------------------*/

/**
 * @brief Wake-up a HTTP client task. aIndex
 * @param[in] uxIndex: the task number ( 0 .. echoNUM_HTTP_CLIENTS-1 ).
 * @param[in] pcHost: the name of the host from which to download index.html
 */
    void wakeupHTTPClient( size_t uxIndex,
                           const char * pcHost,
                           const char * pcFileName,
                           uint16_t usPortNumber,
                           BaseType_t xIPType )
    {
        if( ( uxIndex < echoNUM_HTTP_CLIENTS ) && ( xSocketTaskHandles[ uxIndex ] != NULL ) )
        {
            xIPVersion[ uxIndex ] = xIPType;
            usUsePortNumber = usPortNumber;
            snprintf( pcHostNames[ uxIndex ], sizeof pcHostNames[ uxIndex ], "%s", pcHost );

            if( ( pcFileName != NULL ) && ( pcFileName[ 0 ] != 0 ) )
            {
                snprintf( pcFileNames[ uxIndex ], sizeof( pcFileNames[ uxIndex ] ), pcFileName );
            }
            else
            {
                snprintf( pcFileNames[ uxIndex ], sizeof( pcFileNames[ uxIndex ] ), httpREMOTE_FILENAME );
            }

            xAllowedToStart[ uxIndex ]++;
            xTaskNotifyGive( xSocketTaskHandles[ uxIndex ] );
        }
    }

/**
 * @brief Wake-up a HTTP client task. aIndex
 * @param[in] pvParameters: the task number as a void pointer.
 */
    static void prvEchoClientTask( void * pvParameters )
    {
        Socket_t xSocket = NULL;

        struct freertos_sockaddr xEchoServerAddress;

        size_t uxInstance;
        int32_t xReturned, xReceivedBytes;
        BaseType_t lTransmitted;
        TickType_t xTimeOnEntering;

        #if ( ipconfigUSE_TCP_WIN == 1 )
            WinProperties_t xWinProps;

            /* Fill in the buffer and window sizes that will be used by the socket. */
            xWinProps.lTxBufSize = ipconfigTCP_TX_BUFFER_LENGTH;
            xWinProps.lTxWinSize = configECHO_CLIENT_TX_WINDOW_SIZE;
            xWinProps.lRxBufSize = ipconfigTCP_RX_BUFFER_LENGTH;
            xWinProps.lRxWinSize = configECHO_CLIENT_RX_WINDOW_SIZE;
        #endif /* ipconfigUSE_TCP_WIN */

        #if ( ipconfigUSE_IPv6 != 0 )
            struct freertos_sockaddr * pxAddress = ( struct freertos_sockaddr * ) &xEchoServerAddress;
        #else
            struct freertos_sockaddr * pxAddress = &xEchoServerAddress;
        #endif

        /* This task can be created a number of times.  Each instance is numbered
         * to enable each instance to use a different Rx and Tx buffer.  The number is
         * passed in as the task's parameter. */
        {
            /* A two-step assignment. */
            intptr_t uxIntPtr = ( intptr_t ) pvParameters;
            uxInstance = ( size_t ) uxIntPtr;
            configASSERT( uxInstance < echoNUM_HTTP_CLIENTS );
        }

        if( uxInstance < echoNUM_HTTP_CLIENTS )
        {
            xSocketTaskHandles[ uxInstance ] = xTaskGetCurrentTaskHandle();
        }

        for( ; ; )
        {
            int rc;
            struct freertos_sockaddr xBindAddress;
            const char * pcHostname;
            uint32_t ulIPAddress = 0U;
            BaseType_t xHasIPv6Address = pdFALSE;
            char pcBuffer[ 512 ];

            /* Rx and Tx time outs are used to ensure the sockets do not wait too long for
             * missing data. */
            TickType_t xReceiveTimeOut = pdMS_TO_TICKS( 2500U );
            TickType_t xSendTimeOut = pdMS_TO_TICKS( 2000U );
            #if ( ipconfigUSE_IPv6 != 0 )
                IPv6_Address_t xIPAddress_IPv6;
            #endif
            struct freertos_sockaddr xLocalAddress;
            struct freertos_addrinfo * pxResult = NULL;
            struct freertos_addrinfo xHints;
            NetworkEndPoint_t * pxEndPoint;

            if( xSocketValid( xSocket ) == pdTRUE )
            {
                FreeRTOS_closesocket( xSocket );
            }

            xSocket = NULL;

            while( xAllowedToStart[ uxInstance ] == 0 )
            {
                ulTaskNotifyTake( pdTRUE, 100 );
            }

            xAllowedToStart[ uxInstance ] = 0;

            if( xIPVersion[ uxInstance ] != 6 )
            {
                xHints.ai_family = FREERTOS_AF_INET;
            }
            else
            {
                xHints.ai_family = FREERTOS_AF_INET6;
            }

            pcHostname = pcHostNames[ uxInstance ];

            {
                #if ( ipconfigUSE_IPv4 != 0 )
                    pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv4 );

                    if( ( pxEndPoint != NULL ) && ( pxEndPoint->ipv4_settings.ulGatewayAddress != 0U ) )
                    {
                        xARPWaitResolution( pxEndPoint->ipv4_settings.ulGatewayAddress, pdMS_TO_TICKS( 1000U ) );
                    }
                #endif /* ( ipconfigUSE_IPv4 != 0 ) */

                BaseType_t rc_dns = FreeRTOS_getaddrinfo(
                    pcHostname,  /* The node. */
                    NULL,        /* const char *pcService: ignored for now. */
                    &xHints,     /* If not NULL: preferences. */
                    &pxResult ); /* An allocated struct, containing the results. */
                FreeRTOS_printf( ( "httpTest: FreeRTOS_getaddrinfo: rc %d\n", ( int ) rc_dns ) );

                if( ( rc_dns != 0 ) || ( pxResult == NULL ) )
                {
                    continue;
                }

                if( pxResult->ai_family == FREERTOS_AF_INET4 )
                {
/*				ulIPAddress = ( ( struct freertos_sockaddr * ) pxResult->ai_addr )->sin_address.ulIP_IPv4; */
                    ulIPAddress = pxResult->ai_addr->sin_address.ulIP_IPv4;
                }

                #if ( ipconfigUSE_IPv6 != 0 )
                    else if( pxResult->ai_family == FREERTOS_AF_INET6 )
                    {
                        struct freertos_sockaddr * pxAddr6;

                        pxAddr6 = ( struct freertos_sockaddr * ) pxResult->ai_addr;
                        memcpy( xIPAddress_IPv6.ucBytes, pxAddr6->sin_address.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                        xHasIPv6Address = pdTRUE;
                    }
                #endif
                else
                {
                    continue;
                }
            }

            #if ( ipconfigUSE_IPv6 != 0 )
                if( xHasIPv6Address != 0 )
                {
                    xEchoServerAddress.sin_len = sizeof( struct freertos_sockaddr );
                    xEchoServerAddress.sin_family = FREERTOS_AF_INET6;
                    xEchoServerAddress.sin_port = FreeRTOS_htons( usUsePortNumber );
                    memcpy( xEchoServerAddress.sin_address.xIP_IPv6.ucBytes, xIPAddress_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                }
                else
            #endif

            if( ulIPAddress != 0U )
            {
                pxAddress->sin_len = sizeof( struct freertos_sockaddr );
                pxAddress->sin_family = FREERTOS_AF_INET;
                pxAddress->sin_port = FreeRTOS_htons( usUsePortNumber );
                pxAddress->sin_address.ulIP_IPv4 = ulIPAddress;
            }
            else
            {
                configASSERT( 0 == 1 );
            }

            /* Create a TCP socket. */
            xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP );
            configASSERT( xSocketValid( xSocket ) == pdTRUE );

            memset( &( xBindAddress ), 0, sizeof( xBindAddress ) );

            #if ( ipconfigUSE_IPv6 != 0 )
                if( xEchoServerAddress.sin_family == FREERTOS_AF_INET6 )
                {
                    pxEndPoint = FreeRTOS_FindEndPointOnNetMask_IPv6( &( xEchoServerAddress.sin_address.xIP_IPv6 ) );

                    if( pxEndPoint == NULL )
                    {
                        pxEndPoint = FreeRTOS_FindGateWay( ipTYPE_IPv6 );
                    }

                    if( pxEndPoint != NULL )
                    {
                        /*memcpy( xEchoServerAddress.sin_address.xIP_IPv6.ucBytes, pxEndPoint->ipv6.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS ); */
                    }
                }
                else
            #endif /* if ( ipconfigUSE_IPv6 != 0 ) */
            {
                pxEndPoint = FreeRTOS_FindEndPointOnNetMask( pxAddress->sin_address.ulIP_IPv4, 9999 );

                if( pxEndPoint != NULL )
                {
                    xBindAddress.sin_address.ulIP_IPv4 = pxEndPoint->ipv4_settings.ulIPAddress;
                    xBindAddress.sin_family = FREERTOS_AF_INET;
                }
            }

            rc = FreeRTOS_bind( xSocket, &( xBindAddress ), sizeof( xBindAddress ) );

            if( rc != 0 )
            {
                FreeRTOS_printf( ( "httpTest: bind fails with errno %d\n", rc ) );
                configASSERT( rc == 0 );
            }

            /* Set a time out so a missing reply does not cause the task to block
             * indefinitely. */
            FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );
            FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendTimeOut, sizeof( xSendTimeOut ) );

            #if ( ipconfigUSE_TCP_WIN == 1 )
            {
                /* Set the window and buffer sizes. */
                FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_WIN_PROPERTIES, ( void * ) &xWinProps, sizeof( xWinProps ) );
            }
            #endif /* ipconfigUSE_TCP_WIN */

            FreeRTOS_GetLocalAddress( xSocket, &xLocalAddress );
            /* Connect to the echo server. */
            rc = FreeRTOS_connect( xSocket, ( struct freertos_sockaddr * ) &xEchoServerAddress, sizeof( xEchoServerAddress ) );

            #if ( ipconfigUSE_IPv6 != 0 )
                struct freertos_sockaddr * pxLocalAddress = ( struct freertos_sockaddr * ) &xLocalAddress;
            #else
                struct freertos_sockaddr * pxLocalAddress = &xLocalAddress;
            #endif

            #if ( ipconfigUSE_IPv6 != 0 )
                if( pxAddress->sin_family == FREERTOS_AF_INET6 )
                {
                    FreeRTOS_printf( ( "httpTest: FreeRTOS_connect to %pip port %u: rc %d\n",
                                       xEchoServerAddress.sin_address.xIP_IPv6.ucBytes,
                                       FreeRTOS_ntohs( pxAddress->sin_port ),
                                       rc ) );
                }
                else
            #endif
            {
                FreeRTOS_printf( ( "httpTest: FreeRTOS_connect from %lxip port %u to %lxip port %u: rc %d\n",
                                   FreeRTOS_ntohl( pxLocalAddress->sin_address.ulIP_IPv4 ),
                                   FreeRTOS_ntohs( pxLocalAddress->sin_port ),
                                   FreeRTOS_ntohl( pxAddress->sin_address.ulIP_IPv4 ),
                                   FreeRTOS_ntohs( pxAddress->sin_port ),
                                   rc ) );
            }

            if( rc == 0 )
            {
                ulConnections[ uxInstance ]++;

                /* Send a HTTP request. */
                {
                    BaseType_t xLoop;
                    size_t uxLength;
                    /* Send the string to the socket. */
                    uxLength = snprintf( pcBuffer, sizeof( pcBuffer ), get_command, pcFileNames[ uxInstance ], pcHostname );
                    lTransmitted = FreeRTOS_send( xSocket,             /* The socket being sent to. */
                                                  ( void * ) pcBuffer, /* The data being sent. */
                                                  uxLength,            /* The length of the data being sent. */
                                                  0 );                 /* No flags. */
                    FreeRTOS_printf( ( "httpTest: FreeRTOS_send : rc %ld\n", lTransmitted ) );

                    if( lTransmitted < 0 )
                    {
                        /* Error? */
                        break;
                    }

                    /* Clear the buffer into which the echoed string will be
                     * placed. */
                    memset( ( void * ) pcBuffer, 0x00, sizeof( pcBuffer ) );
                    xReceivedBytes = 0;

                    /* Receive data echoed back to the socket. */
                    for( xLoop = 0; xLoop < 10; xLoop++ )
                    {
                        xReturned = FreeRTOS_recv( xSocket,            /* The socket being received from. */
                                                   pcBuffer,           /* The buffer into which the received data will be written. */
                                                   sizeof( pcBuffer ), /* The size of the buffer provided to receive the data. */
                                                   0 );                /* No flags. */

                        FreeRTOS_printf( ( "httpTest: FreeRTOS_recv : rc %ld\n", xReturned ) );

                        if( xReturned < 0 )
                        {
                            /* Error occurred.  Latch it so it can be detected
                             * below. */
                            xReceivedBytes = xReturned;
                            break;
                        }
                        else if( xReturned == 0 )
                        {
                            /* Timed out. */
                            break;
                        }
                        else
                        {
                            /* Use a short RX time-out the next time. */
                            xReceiveTimeOut = pdMS_TO_TICKS( 500U );
                            FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );
                            /* Keep a count of the bytes received so far. */
                            xReceivedBytes += xReturned;
                            printBuffer( pcBuffer, xReturned, 129, "" );
                        }
                    } /* for( xLoop = 0; xLoop < 10; xLoop++ ) */
                }

                /* Finished using the connected socket, initiate a graceful close:
                 * FIN, FIN+ACK, ACK. */
                FreeRTOS_printf( ( "httpTest: prvEchoClientTask: shut down connection\n" ) );
                FreeRTOS_shutdown( xSocket, FREERTOS_SHUT_RDWR );

                /* Expect FreeRTOS_recv() to return an error once the shutdown is
                 * complete. */
                xTimeOnEntering = xTaskGetTickCount();

                do
                {
                    xReturned = FreeRTOS_recv( xSocket,            /* The socket being received from. */
                                               pcBuffer,           /* The buffer into which the received data will be written. */
                                               sizeof( pcBuffer ), /* The size of the buffer provided to receive the data. */
                                               0 );

                    if( xReturned < 0 )
                    {
                        break;
                    }
                } while( ( xTaskGetTickCount() - xTimeOnEntering ) < xReceiveTimeOut );

                FreeRTOS_printf( ( "httpTest: connection is down\n" ) );
            }

            /* Close this socket before looping back to create another. */
            FreeRTOS_closesocket( xSocket );
            xSocket = NULL;
            FreeRTOS_printf( ( "httpTest: test is ready\n" ) );

            /* Pause for a short while to ensure the network is not too
             * congested. */
/*		vTaskDelay( echoLOOP_DELAY ); */
        }
    }
/*-----------------------------------------------------------*/

    void printBuffer( const char * apBuffer,
                      int aLen,
                      int aLineLen,
                      const char * apPrefix )
    {
        const char * ptr = apBuffer;
        const char * end = apBuffer + aLen;

        for( ; ; )
        {
            const char * next = ptr;
            const char * eot;

            /* Find the first null, newline of end of text. */
            for( ; ; )
            {
                if( ( next >= end ) || ( *next == '\0' ) )
                {
                    eot = next;
                    next = NULL;
                    break;
                }

                if( ( *next == '\n' ) || ( *next == '\r' ) )
                {
                    char eol = *next == '\n' ? '\r' : '\n';
                    eot = next;

                    do
                    {
                        next++;
                    } while( *next == eol );

                    break;
                }

                if( ( int ) ( next - ptr ) >= aLineLen )
                {
                    eot = next;
                    break;
                }

                next++;
            }

            {
                char save = *eot;
                *( ( char * ) eot ) = '\0';
                FreeRTOS_printf( ( "%s%s\n", apPrefix, ptr ) );
                *( ( char * ) eot ) = save;
            }

            if( next == NULL )
            {
                break;
            }

            ptr = next;
        }
    }

#endif /* ipconfigUSE_TCP */
