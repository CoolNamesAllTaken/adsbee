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
 * @file plus_tcp_demo_cli.c
 * @brief This module will handle a set of commands that help with integration testing.
 *        It is used for integration tests, both IPv4 and IPv6.
 */

/* Standard includes. */
#include <stdio.h>
#include <time.h>
#include <ctype.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "timers.h"
#include "queue.h"
#include "semphr.h"
#include "message_buffer.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DHCP.h"
#include "FreeRTOS_DNS.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_IP_Private.h"

#include "FreeRTOS_Routing.h"
#if ( ipconfigUSE_IPv6 != 0 )
    #include "FreeRTOS_ND.h"
#endif

#include "plus_tcp_demo_cli.h"
#include "http_client_test.h"

#if ( ipconfigUSE_NTP_DEMO != 0 )
    #include "NTPDemo.h"
#endif

#if ( USE_IPERF != 0 )
    #include "iperf_task.h"
#endif

int verboseLevel;

static uint32_t ulWorkCount, ulLastWorkCount;

extern SemaphoreHandle_t xServerSemaphore;

extern uint64_t ullGetHighResolutionTime( void );

/* Some compilers do not support __attribute__( ( weak ) ) for a function declaration,
 * hence updating the declaration.
 */
#pragma WEAK ( ullGetHighResolutionTime )
uint64_t ullGetHighResolutionTime( void )
{
    /* In case you don't have a usec timer function. */
    return xTaskGetTickCount();
}

#define PING_TIMEOUT    100U

typedef struct xCommandOptions
{
    BaseType_t xDoClear;
    BaseType_t xIPVersion; /* Zero means: do not change version, otherwise 4 or 6. */
    BaseType_t xAsynchronous;
    BaseType_t xLogging;
} CommandOptions_t;

size_t uxGetOptions( CommandOptions_t * pxOptions,
                     const char ** ppcCommand );

int PING_COUNT_MAX = 10;

static TaskHandle_t xServerWorkTaskHandle = NULL;

extern void vApplicationPingReplyHook( ePingReplyStatus_t eStatus,
                                       uint16_t usIdentifier );
#if ( ipconfigUSE_IPv6 != 0 )
    static IPv6_Address_t xPing6IPAddress;
    volatile BaseType_t xPing6Count = -1;
#endif
uint32_t ulPingIPAddress;
size_t uxPingSize = 32U;
volatile BaseType_t xPing4Count = -1;
volatile BaseType_t xPingReady;
static TickType_t uxPingTimes[ 2 ];

static int pingLogging = pdFALSE;

static void handle_udp( char * pcBuffer );
static void handle_arpq( char * pcBuffer );
static void handle_dnsq( char * pcBuffer );
static void handle_ping( char * pcBuffer );
#if ( ipconfigUSE_NTP_DEMO != 0 )
    static void handle_ntp( char * pcBuffer );
#endif
static void handle_rand( char * pcBuffer );
static void handle_http( char * pcBuffer );
static void handle_whatismyipaddress( char * pcBuffer );
static void handle_ifconfig( char * pcBuffer );
static void handle_gw( char * pcBuffer );
static void handle_help( char * pcBuffer );

void handle_user_test( char * pcBuffer );

static void clear_caches( void );

static volatile BaseType_t xDNSCount = 0;

static struct freertos_addrinfo * pxDNSLookup( char * pcHost,
                                               BaseType_t xIPVersion,
                                               BaseType_t xAsynchronous,
                                               BaseType_t xDoClear );

static void vDNSEvent( const char * pcName,
                       void * pvSearchID,
                       struct freertos_addrinfo * pxAddrInfo );

/* Defined in FreeRTOS_DNS.c */
void show_addressinfo( const struct freertos_addrinfo * pxAddress );

/*-----------------------------------------------------------*/

typedef void ( * pfhandler ) ( char * /*pcBuffer */ );

struct xCommandCouple
{
    char * pcCommand;
    size_t uxCommandLength;
    pfhandler pHandler;
    const char * pcHelp;
};

static struct xCommandCouple xCommands[] =
{
    { "arpq",       4U,  handle_arpq,              "Lookup the MAC-address of an IPv4 or IPv6 address."         },
    { "udp",        3U,  handle_udp,               "Send a text message to any UDP port."                       },
    { "ping",       4U,  handle_ping,              "Look up a host and ping it 10 times."                       },
    { "dnsq",       4U,  handle_dnsq,              "Look up a host using DNS, mDNS or LLMNR."                   },
    { "rand",       4U,  handle_rand,              "Call the randomiser and print the resulting number.\n"      },
    { "http",       4U,  handle_http,              "Connect to port 80 of a host and download \"index.html\"\n" },
    { "user_test",  9U,  handle_user_test,         "A user-supplied function \"handle_user_test()\" is called." },
    { "whatismyip", 10U, handle_whatismyipaddress, "Print my IP-address\n"                                      },
    { "gw",         2U,  handle_gw,                "Show the configured gateway address\n"                      },
    { "ifconfig",   8U,  handle_ifconfig,          "Show a few network parameters\n"                            },
    { "help",       4U,  handle_help,              "Show this help\n"                                           },
    #if ( ipconfigUSE_NTP_DEMO != 0 )
    { "ntp",        3U,  handle_ntp,               "Contact an NTP server and ask the time.\n"                  },
    #endif
};

static BaseType_t can_handle( char * pcBuffer,
                              char * pcCommand,
                              size_t uxLength,
                              pfhandler phandler )
{
    BaseType_t xReturn = pdFALSE;

    if( strncmp( pcBuffer, pcCommand, uxLength ) == 0 )
    {
        phandler( pcBuffer + uxLength );
        xReturn = pdTRUE;
    }

    return xReturn;
}

/**
 *
 * @brief Create a task that runs the CLI.
 * @return zero when the command was recognised and handled.
 */
BaseType_t xHandleTestingCommand( char * pcBuffer,
                                  size_t uxBufferSize )
{
    /* Becomes true if the command is handled. */
    BaseType_t xReturn = pdFALSE;

    ( void ) uxBufferSize;

    if( ulLastWorkCount == ulWorkCount )
    {
        FreeRTOS_printf( ( "xHandleTestingCommand: the function xHandleTesting() was not called\n" ) );
    }
    else
    {
        ulLastWorkCount = ulWorkCount;
    }

    if( xServerWorkTaskHandle == NULL )
    {
        xServerWorkTaskHandle = xTaskGetCurrentTaskHandle();
    }

    if( strncmp( pcBuffer, "ver", 3 ) == 0 )
    {
        int level;

        if( sscanf( pcBuffer + 3, "%d", &level ) == 1 )
        {
            verboseLevel = level;
        }

        FreeRTOS_printf( ( "Verbose level %d\n", verboseLevel ) );
        xReturn = pdTRUE;
    }
    else
    {
        BaseType_t xIndex;

        for( xIndex = 0; xIndex < ARRAY_SIZE( xCommands ); xIndex++ )
        {
            struct xCommandCouple * pxCommand = &( xCommands[ xIndex ] );

            if( can_handle( pcBuffer, pxCommand->pcCommand, pxCommand->uxCommandLength, pxCommand->pHandler ) == pdTRUE )
            {
                xReturn = pdTRUE;
                break;
            }
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static void handle_ifconfig( char * pcBuffer )
{
    NetworkInterface_t * pxInterface;
    NetworkEndPoint_t * pxEndPoint;

    ( void ) pcBuffer;

    for( pxInterface = FreeRTOS_FirstNetworkInterface();
         pxInterface != NULL;
         pxInterface = FreeRTOS_NextNetworkInterface( pxInterface ) )
    {
        FreeRTOS_printf( ( "Interface %s\n", pxInterface->pcName ) );

        for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
             pxEndPoint != NULL;
             pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
        {
            showEndPoint( pxEndPoint );
        }
    }
}
/*-----------------------------------------------------------*/

static const char * pcARPReturnType( eARPLookupResult_t eResult )
{
    const char * pcReturn = "Unknown";

    switch( eResult )
    {
        case eARPCacheMiss:
            pcReturn = "Miss";
            break;

        case eARPCacheHit:
            pcReturn = "Hit";
            break;

        case eCantSendPacket:
            pcReturn = "Can not send";
            break;
    }

    return pcReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_IPv6 != 0 )
    static NetworkEndPoint_t * pxFindEndpoint( IPv6_Address_t * pxAddress )
    {
        NetworkEndPoint_t * pxEndpoint;

        for( pxEndpoint = FreeRTOS_FirstEndPoint( NULL );
             pxEndpoint != NULL;
             pxEndpoint = FreeRTOS_NextEndPoint( NULL, pxEndpoint ) )
        {
            if( memcmp( pxEndpoint->ipv6_settings.xGatewayAddress.ucBytes, pxAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS ) == 0 )
            {
                break;
            }
        }

        return pxEndpoint;
    }
/*-----------------------------------------------------------*/
#endif /* ( ipconfigUSE_IPv6 != 0 ) */

static void handle_udp( char * pcBuffer )
{
    /* e.g. "udp 192.168.2.11@1020 Hello world" */
    CommandOptions_t xOptions;
    char * ptr = pcBuffer;
    char pcAtToken = '@';
    char * pcToken = strchr( ptr, pcAtToken );
    BaseType_t xIPType = 0;
    IP_Address_t xAddress;

    uxGetOptions( &( xOptions ), ( const char ** ) &( ptr ) );

    if( xOptions.xDoClear )
    {
        clear_caches();
        vNTPClearCache();
    }

    if( pcToken != NULL )
    {
        BaseType_t rc;

        *pcToken = 0;

        rc = FreeRTOS_inet_pton( FREERTOS_AF_INET4, ptr, ( void * ) &xAddress );

        if( rc == pdPASS )
        {
            xIPType = ipTYPE_IPv4;
        }
        else
        {
            rc = FreeRTOS_inet_pton( FREERTOS_AF_INET6, ptr, ( void * ) &xAddress );

            if( rc == pdPASS )
            {
                xIPType = ipTYPE_IPv6;
            }
        }

        *pcToken = pcAtToken;

        if( xIPType != 0 )
        {
            unsigned uPort;

            if( sscanf( pcToken + 1, "%u", &uPort ) >= 1 )
            {
                BaseType_t uxFamily;

                if( xIPType == ipTYPE_IPv6 )
                {
                    uxFamily = FREERTOS_AF_INET6;
                    FreeRTOS_printf( ( "Send packet to UDP %pip port %u\n", xAddress.xIP_IPv6.ucBytes, uPort ) );
                }
                else
                {
                    uxFamily = FREERTOS_AF_INET;
                    FreeRTOS_printf( ( "Send packet to UDP %xip port %u\n", ( unsigned ) FreeRTOS_ntohl( xAddress.ulIP_IPv4 ), uPort ) );
                }

                static Socket_t xSocket = NULL;
                struct freertos_sockaddr xDestinationAddress;

                if( xSocket == NULL )
                {
                    struct freertos_sockaddr xSourceAddress;

                    memset( &xSourceAddress, 0, sizeof xSourceAddress );
                    xSourceAddress.sin_family = uxFamily;
                    xSourceAddress.sin_len = sizeof( xSourceAddress );
                    xSourceAddress.sin_port = FreeRTOS_htons( uPort );
                    xSocket = FreeRTOS_socket( uxFamily, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
                    FreeRTOS_bind( xSocket, &xSourceAddress, sizeof xSourceAddress );
                }

                if( xSocket != NULL )
                {
                    size_t uxLength = strlen( pcBuffer );
                    memset( &xDestinationAddress, 0, sizeof xDestinationAddress );

                    if( xIPType == ipTYPE_IPv6 )
                    {
                        memcpy( xDestinationAddress.sin_address.xIP_IPv6.ucBytes, xAddress.xIP_IPv6.ucBytes, 16 );
                    }
                    else
                    {
                        xDestinationAddress.sin_address.ulIP_IPv4 = xAddress.ulIP_IPv4;
                    }

                    xDestinationAddress.sin_family = uxFamily;
                    xDestinationAddress.sin_len = sizeof( xDestinationAddress );
                    xDestinationAddress.sin_port = FreeRTOS_htons( uPort );
                    char * pcCopy = ( char * ) pvPortMalloc( uxLength + 3 );

                    if( pcCopy != NULL )
                    {
                        memcpy( pcCopy, pcBuffer, uxLength );
                        pcCopy[ uxLength + 0 ] = '\r';
                        pcCopy[ uxLength + 1 ] = '\n';
                        pcCopy[ uxLength + 2 ] = 0;
                        rc = FreeRTOS_sendto( xSocket,
                                              pcCopy,
                                              uxLength + 2,
                                              0,
                                              &xDestinationAddress,
                                              ( socklen_t ) sizeof( xDestinationAddress ) );
                        vPortFree( pcCopy );
                    }
                    else
                    {
                        FreeRTOS_printf( ( "handle_udp: malloc failed\n" ) );
                    }

                    vTaskDelay( pdMS_TO_TICKS( 500 ) );
                }
            }
        }
    }

    if( ( pcToken == NULL ) || ( xIPType == 0 ) )
    {
        FreeRTOS_printf( ( "handle_udp: bad parameters: '%s'\n", pcBuffer ) );
    }
}
/*-----------------------------------------------------------*/

static void handle_arpq( char * pcBuffer )
{
    CommandOptions_t xOptions;
    char * ptr = pcBuffer;
    eARPLookupResult_t eResult = eARPCacheMiss;
    uint32_t ulIPAddress;
    uint32_t ulLookUpIP;
    MACAddress_t xMACAddress;
    NetworkEndPoint_t * pxEndPoint = NULL;
    BaseType_t xIPType = 0;
    IP_Address_t xAddress;
    IP_Address_t xLookupAddress;
    BaseType_t rc;

    uxGetOptions( &( xOptions ), ( const char ** ) &( ptr ) );

    if( xOptions.xDoClear )
    {
        clear_caches();
        vNTPClearCache();
    }

    if( *ptr )
    {
        char * pcBegin = ptr;

        for( ; *ptr != 0; ptr++ )
        {
            if( !isxdigit( *ptr ) && ( *ptr != '.' ) && ( *ptr != ':' ) )
            {
                *ptr = 0;
                break;
            }
        }

        memset( &xAddress, 0, sizeof xAddress );

        rc = FreeRTOS_inet_pton( FREERTOS_AF_INET4, pcBegin, ( void * ) &xAddress );

        if( rc == pdPASS )
        {
            xIPType = ipTYPE_IPv4;
        }
        else
        {
            rc = FreeRTOS_inet_pton( FREERTOS_AF_INET6, pcBegin, ( void * ) &xAddress );

            if( rc == pdPASS )
            {
                xIPType = ipTYPE_IPv6;
            }
        }

        if( xIPType <= 0 )
        {
            FreeRTOS_printf( ( "handle_arpq: bad arguments: '%s'\n", pcBuffer ) );
            return;
        }

        ulIPAddress = xAddress.ulIP_IPv4;

        ulLookUpIP = ulIPAddress;
        xLookupAddress = xAddress;

        switch( xIPType )
        {
            #if ( ipconfigUSE_IPv4 != 0 )
                case ipTYPE_IPv4:
                    eResult = eARPGetCacheEntry( &ulLookUpIP, &xMACAddress, &pxEndPoint );
                    FreeRTOS_printf( ( "ARPGetCacheEntry returns \"%s\" Look for %xip. Found end-point: %s\n",
                                       pcARPReturnType( eResult ), ( unsigned ) FreeRTOS_htonl( ulLookUpIP ), ( pxEndPoint != NULL ) ? "yes" : "no" ) );
                    break;
            #endif /* ( ipconfigUSE_IPv4 != 0 ) */

            #if ( ipconfigUSE_IPv6 != 0 )
                case ipTYPE_IPv6:
                    eResult = eNDGetCacheEntry( &( xLookupAddress.xIP_IPv6 ), &xMACAddress, &pxEndPoint );
                    FreeRTOS_printf( ( "ARPGetCacheEntry returns \"%s\" Look for %pip. Found end-point: %s\n",
                                       pcARPReturnType( eResult ), xAddress.xIP_IPv6.ucBytes, ( pxEndPoint != NULL ) ? "yes" : "no" ) );
                    break;
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */

            default:
                /* MISRA 16.4 Compliance */
                FreeRTOS_debug_printf( ( "handle_arpq: Undefined IP Type \n" ) );
                break;
        }

        if( ( eResult == eARPCacheMiss ) && ( pxEndPoint != NULL ) )
        {
            size_t uxNeededSize = sizeof( ARPPacket_t );

            if( xIPType == ipTYPE_IPv6 )
            {
                uxNeededSize = ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t );
            }

            NetworkBufferDescriptor_t * pxBuffer;

            switch( xIPType )
            {
                #if ( ipconfigUSE_IPv4 != 0 )
                    case ipTYPE_IPv4:
                        FreeRTOS_printf( ( "handle_arpq: Looking up %xip\n",
                                           ( unsigned ) FreeRTOS_ntohl( ulLookUpIP ) ) );

                        xARPWaitResolution( ulLookUpIP, 1000U );
                        break;
                #endif /* ( ipconfigUSE_IPv4 != 0 ) */

                #if ( ipconfigUSE_IPv6 != 0 )
                    case ipTYPE_IPv6:
                        pxBuffer = pxGetNetworkBufferWithDescriptor( BUFFER_FROM_WHERE_CALL( 180 ) uxNeededSize, pdMS_TO_TICKS( 100U ) );

                        if( pxBuffer != NULL )
                        {
                            UDPPacket_t * pxUDPPacket = ( ( UDPPacket_t * ) pxBuffer->pucEthernetBuffer );

                            /* 'ulLookUpIP' might be the IP-address of a gateway. */
                            memcpy( pxBuffer->xIPAddress.xIP_IPv6.ucBytes, xLookupAddress.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                            pxUDPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;
                            pxBuffer->pxEndPoint = pxEndPoint;
                            pxBuffer->pxInterface = pxBuffer->pxEndPoint->pxNetworkInterface;
                            FreeRTOS_printf( ( "handle_arpq: Looking up %pip with%s end-point\n",
                                               pxBuffer->xIPAddress.xIP_IPv6.ucBytes,
                                               ( pxBuffer->pxEndPoint != NULL ) ? "" : "out" ) );

                            vNDSendNeighbourSolicitation( pxBuffer, &( pxBuffer->xIPAddress.xIP_IPv6 ) );
                        }
                        else
                        {
                            FreeRTOS_printf( ( "handle_arpq: pxGetNetworkBufferWithDescriptor failed\n" ) );
                        }
                        break;
                #endif /* ( ipconfigUSE_IPv6 != 0 ) */

                default:
                    /* MISRA 16.4 Compliance */
                    FreeRTOS_debug_printf( ( "handle_arpq: Undefined IP Type \n" ) );
                    break;
            }

            /* Let the IP-task do its work, and wait 500 ms. */
            FreeRTOS_printf( ( "... Pause ...\n" ) );
            vTaskDelay( pdMS_TO_TICKS( 500U ) );

            switch( xIPType )
            {
                #if ( ipconfigUSE_IPv4 != 0 )
                    case ipTYPE_IPv4:
                        eResult = eARPGetCacheEntry( &ulLookUpIP, &xMACAddress, &pxEndPoint );
                        break;
                #endif /* ( ipconfigUSE_IPv4 != 0 ) */

                #if ( ipconfigUSE_IPv6 != 0 )
                    case ipTYPE_IPv6:
                        eResult = eNDGetCacheEntry( &( xLookupAddress.xIP_IPv6 ), &xMACAddress, &pxEndPoint );
                        break;
                #endif /* ( ipconfigUSE_IPv6 != 0 ) */

                default:
                    /* MISRA 16.4 Compliance */
                    FreeRTOS_debug_printf( ( "handle_arpq: Undefined IP Type \n" ) );
                    break;
            }

            FreeRTOS_printf( ( "handle_arpq: after lookup: \"%s\"\n",
                               pcARPReturnType( eResult ) ) );
        }
    }
}
/*-----------------------------------------------------------*/

static void handle_dnsq( char * pcBuffer )
{
    CommandOptions_t xOptions;
    char * ptr = pcBuffer;

    uxGetOptions( &( xOptions ), ( const char ** ) &( ptr ) );

    if( *ptr )
    {
        struct freertos_addrinfo * pxResult;

        pxResult = pxDNSLookup( ptr, xOptions.xIPVersion, xOptions.xAsynchronous, xOptions.xDoClear );

        if( pxResult != NULL )
        {
            FreeRTOS_freeaddrinfo( pxResult );
        }
    }
    else
    {
        FreeRTOS_printf( ( "Usage: dnsq <name>\n" ) );
    }
}
/*-----------------------------------------------------------*/

static void handle_rand( char * pcBuffer )
{
    uint32_t ulNumber = 0x5a5a5a5a;
    BaseType_t rc = xApplicationGetRandomNumber( &ulNumber );

    ( void ) pcBuffer;

    if( rc == pdPASS )
    {
        char buffer[ 33 ];
        int index;
        uint32_t ulMask = 0x80000000uL;

        for( index = 0; index < 32; index++ )
        {
            buffer[ index ] = ( ( ulNumber & ulMask ) != 0 ) ? '1' : '0';
            ulMask >>= 1;
        }

        buffer[ index ] = '\0';
        FreeRTOS_printf( ( "Random %08lx (%s)\n", ulNumber, buffer ) );
    }
    else
    {
        FreeRTOS_printf( ( "Random failed\n" ) );
    }
}
/*-----------------------------------------------------------*/

size_t uxGetOptions( CommandOptions_t * pxOptions,
                     const char ** ppcCommand )
{
    size_t uxLength = 0U;
    const char * pcCommand = *ppcCommand;

    memset( pxOptions, 0, sizeof( *pxOptions ) );
    pxOptions->xIPVersion = 4;

    while( ( pcCommand[ uxLength ] != 0 ) && ( !isspace( ( uint8_t ) pcCommand[ uxLength ] ) ) )
    {
        switch( pcCommand[ uxLength ] )
        {
            case 'a':
                pxOptions->xAsynchronous = pdTRUE;
                break;

            case 'c':
                pxOptions->xDoClear = pdTRUE;
                break;

            case 'v':
                pxOptions->xLogging = pdTRUE;
                break;

            case '4':
                pxOptions->xIPVersion = 4;
                break;

            case '6':
                pxOptions->xIPVersion = 6;
                break;
        }

        uxLength++;
    }

    if( uxLength > 0U )
    {
        *ppcCommand = &( pcCommand[ uxLength ] );
    }

    while( isspace( ( uint8_t ) ( *ppcCommand )[ 0 ] ) )
    {
        ( *ppcCommand )++;
    }

    return uxLength;
}

#if ( ipconfigUSE_NTP_DEMO != 0 )
    static void handle_ntp( char * pcBuffer )
    {
        CommandOptions_t xOptions;
        char * ptr = pcBuffer;

        uxGetOptions( &( xOptions ), ( const char ** ) &( ptr ) );

        if( xOptions.xDoClear )
        {
            clear_caches();
            vNTPClearCache();
        }

        vNTPSetNTPType( xOptions.xIPVersion, xOptions.xAsynchronous, xOptions.xLogging );
        /* vStartNTPTask() may be called multiple times. */
        vStartNTPTask( configMINIMAL_STACK_SIZE * 12, tskIDLE_PRIORITY + 1 );
    }
#endif /* if ( ipconfigUSE_NTP_DEMO != 0 ) */

#if ( ipconfigUSE_IPv6 != 0 )
    static void handle_whatismyipaddress( char * pcBuffer )
    {
        NetworkEndPoint_t * pxEndPoint;

        ( void ) pcBuffer;
        FreeRTOS_printf( ( "Showing all end-points\n" ) );

        for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
             pxEndPoint != NULL;
             pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                if( pxEndPoint->bits.bIPv6 )
                {
                    FreeRTOS_printf( ( "IPv6: %pip on '%s'\n", pxEndPoint->ipv6_settings.xIPAddress.ucBytes, pxEndPoint->pxNetworkInterface->pcName ) );
                }
                else
            #endif
            {
                FreeRTOS_printf( ( "IPv4: %xip on '%s'\n", ( unsigned ) FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulIPAddress ), pxEndPoint->pxNetworkInterface->pcName ) );
            }
        }
    }
#else /* if ( ipconfigUSE_IPv6 != 0 ) */
    static void handle_whatismyipaddress( char * pcBuffer )
    {
        ( void ) pcBuffer;
        FreeRTOS_printf( ( "IPv4: %xip\n", ( unsigned ) FreeRTOS_ntohl( FreeRTOS_GetIPAddress() ) ) );
    }
#endif /* if ( ipconfigUSE_IPv6 != 0 ) */

static void handle_help( char * pcBuffer )
{
    BaseType_t xIndex;

    ( void ) pcBuffer;
    FreeRTOS_printf( ( "Available commands:\n" ) );

    for( xIndex = 0; xIndex < ARRAY_SIZE( xCommands ); xIndex++ )
    {
        FreeRTOS_printf( ( "%-11.11s: %s\n", xCommands[ xIndex ].pcCommand, xCommands[ xIndex ].pcHelp ) );
    }
}

static void handle_gw( char * pcBuffer )
{
    NetworkEndPoint_t * pxEndPoint;

    ( void ) pcBuffer;
    FreeRTOS_printf( ( "Showing all gateways\n" ) );

    for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
         pxEndPoint != NULL;
         pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
    {
        #if ( ipconfigUSE_IPv6 != 0 )
            if( pxEndPoint->bits.bIPv6 )
            {
                if( memcmp( pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, FreeRTOS_in6addr_any.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) != 0 )
                {
                    FreeRTOS_printf( ( "IPv6: %pip on '%s'\n", pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, pxEndPoint->pxNetworkInterface->pcName ) );
                }
            }
            else
        #endif
        {
            if( pxEndPoint->ipv4_settings.ulGatewayAddress != 0U )
            {
                FreeRTOS_printf( ( "IPv4: %xip on '%s'\n", ( unsigned ) FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulGatewayAddress ), pxEndPoint->pxNetworkInterface->pcName ) );
            }
        }
    }
}

static void handle_ping( char * pcBuffer )
{
    struct freertos_addrinfo * pxDNSResult = NULL;
    char * ptr = pcBuffer;
    CommandOptions_t xOptions;
    IP_Address_t xAddress;
    BaseType_t xResult;

    uxGetOptions( &( xOptions ), ( const char ** ) &( ptr ) );

    pingLogging = xOptions.xLogging;

    char * pcHostname = ptr;

    if( *pcHostname == '\0' )
    {
        FreeRTOS_printf( ( "handle_ping: please provide a hostname of an IP-address\n" ) );
        return;
    }

    memset( &xAddress, 0, sizeof xAddress );

    xResult = FreeRTOS_inet_pton( FREERTOS_AF_INET4, pcHostname, ( void * ) &xAddress );

    if( xResult == pdPASS )
    {
        xOptions.xIPVersion = 4;
    }
    else
    {
        xResult = FreeRTOS_inet_pton( FREERTOS_AF_INET6, pcHostname, ( void * ) &xAddress );

        if( xResult == pdPASS )
        {
            xOptions.xIPVersion = 6;
        }
    }

    if( xOptions.xIPVersion == 6 )
    {
        FreeRTOS_printf( ( "ping6: looking up name '%s' (%pip)\n", pcHostname, xAddress.xIP_IPv6.ucBytes ) );
    }
    else
    {
        FreeRTOS_printf( ( "ping4: looking up name '%s' (%xip)\n", pcHostname, ( unsigned ) FreeRTOS_ntohl( xAddress.ulIP_IPv4 ) ) );
    }

    if( xOptions.xDoClear )
    {
        clear_caches();
    }

    FreeRTOS_printf( ( "Calling pxDNSLookup\n" ) );
    pxDNSResult = pxDNSLookup( pcHostname, xOptions.xIPVersion, xOptions.xAsynchronous, xOptions.xDoClear );

    if( pxDNSResult != NULL )
    {
        switch( xOptions.xIPVersion )
        {
            #if ( ipconfigUSE_IPv4 != 0 )
                case 4:
                    FreeRTOS_printf( ( "ping4 to '%s' (%xip)\n", pcHostname, ( unsigned ) FreeRTOS_ntohl( pxDNSResult->ai_addr->sin_address.ulIP_IPv4 ) ) );
                    xPing4Count = 0;
                    #if ( ipconfigUSE_IPv6 != 0 )
                        xPing6Count = -1;
                    #endif
                    ulPingIPAddress = pxDNSResult->ai_addr->sin_address.ulIP_IPv4;
                    xARPWaitResolution( ulPingIPAddress, pdMS_TO_TICKS( 5000U ) );
                    FreeRTOS_SendPingRequest( ulPingIPAddress, uxPingSize, PING_TIMEOUT );
                    uxPingTimes[ 0 ] = ( TickType_t ) ullGetHighResolutionTime();
                    break;
            #endif /* ( ipconfigUSE_IPv4 != 0 ) */

            #if ( ipconfigUSE_IPv6 != 0 )
                case 6:
                    FreeRTOS_printf( ( "ping6 to '%s' (%pip)\n", pcHostname, pxDNSResult->ai_addr->sin_address.xIP_IPv6.ucBytes ) );
                    xPing4Count = -1;
                    xPing6Count = 0;
                    memcpy( xPing6IPAddress.ucBytes, pxDNSResult->ai_addr->sin_address.xIP_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                    FreeRTOS_SendPingRequestIPv6( &xPing6IPAddress, uxPingSize, PING_TIMEOUT );
                    uxPingTimes[ 0 ] = ( TickType_t ) ullGetHighResolutionTime();
                    break;
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */

            default:
                /* MISRA 16.4 Compliance */
                FreeRTOS_debug_printf( ( "handle_ping: Undefined IP Type \n" ) );
                break;
        }
    }
    else
    {
        FreeRTOS_printf( ( "ping -%d: '%s' not found\n", ( int ) xOptions.xIPVersion, ptr ) );
    }
}
/*-----------------------------------------------------------*/

static void handle_http( char * pcBuffer )
{
    char * ptr = pcBuffer;
    CommandOptions_t xOptions;

    pingLogging = pdFALSE;

    uxGetOptions( &( xOptions ), ( const char ** ) &( ptr ) );

    if( xOptions.xIPVersion == 6 )
    {
        FreeRTOS_printf( ( "http IPv6\n" ) );
    }

    if( *ptr != 0 )
    {
        unsigned portNr = 80U;
        char * pcHost = ptr;
        char * pcFileName;
        char * next = ptr;

        while( ( *next != 0 ) && ( isspace( *next ) == 0 ) )
        {
            next++;
        }

        while( isspace( *next ) != 0 )
        {
            /* Erase the space. */
            *next = 0;
            next++;
        }

        pcFileName = next;

        while( ( *next != 0 ) && ( isspace( *next ) == 0 ) )
        {
            next++;
        }

        while( isspace( *next ) != 0 )
        {
            /* Erase the space. */
            *next = 0;
            next++;
        }

        if( isdigit( *next ) )
        {
            ( void ) sscanf( next, "%u", &portNr );
        }

        if( xOptions.xDoClear )
        {
            clear_caches();
        }

        {
            IP_Address_t xAddress;
            BaseType_t rc = FreeRTOS_inet_pton( FREERTOS_AF_INET6, pcHost, ( void * ) &xAddress );

            if( rc == pdPASS )
            {
                xOptions.xIPVersion = 6;
            }
            else
            {
                rc = FreeRTOS_inet_pton( FREERTOS_AF_INET4, pcHost, ( void * ) &xAddress );

                if( rc == pdPASS )
                {
                    xOptions.xIPVersion = 4;
                }
            }
        }

        /* Get '192.168.2.11' from '/index.html' at port 33001 */
        FreeRTOS_printf( ( "Get '%s' from '%s' at port %u\n", pcFileName, pcHost, portNr ) );
        #if ( USE_ECHO_TASK != 0 )
            vStartHTTPClientTest( configMINIMAL_STACK_SIZE * 8, tskIDLE_PRIORITY + 1 );
            wakeupHTTPClient( 0U, pcHost, pcFileName, portNr, xOptions.xIPVersion );
        #else
            FreeRTOS_printf( ( "handle_http: please define 'USE_ECHO_TASK'\n" ) );
        #endif
    }
    else
    {
        FreeRTOS_printf( ( "Usage: http <hostname>\n" ) );
    }
}
/*-----------------------------------------------------------*/

void vApplicationPingReplyHook( ePingReplyStatus_t eStatus,
                                uint16_t usIdentifier )
{
    uxPingTimes[ 1 ] = ( TickType_t ) ullGetHighResolutionTime();

    if( ( xPing4Count >= 0 ) && ( xPing4Count < PING_COUNT_MAX ) )
    {
        xPing4Count++;

        if( pingLogging || ( xPing4Count == PING_COUNT_MAX ) )
        {
            FreeRTOS_printf( ( "Received reply %d: status %d ID %04x\n", ( int ) xPing4Count, ( int ) eStatus, usIdentifier ) );
        }
    }

    #if ( ipconfigUSE_IPv6 != 0 )
        if( ( xPing6Count >= 0 ) && ( xPing6Count < PING_COUNT_MAX ) )
        {
            xPing6Count++;

            if( pingLogging || ( xPing6Count == PING_COUNT_MAX ) )
            {
                FreeRTOS_printf( ( "Received reply %d: status %d ID %04x\n", ( int ) xPing6Count, ( int ) eStatus, usIdentifier ) );
            }
        }
    #endif
    xPingReady = pdTRUE;

    if( xServerSemaphore != NULL )
    {
        xSemaphoreGive( xServerSemaphore );
    }
}
/*-----------------------------------------------------------*/

void xHandleTesting()
{
    /* A counter to check if the application calls this work function.
     * It should be called regularly from the application.
     * he application will block on 'xServerSemaphore'. */
    ulWorkCount++;

    if( xPingReady )
    {
        TickType_t uxTimeTicks = uxPingTimes[ 1 ] - uxPingTimes[ 0 ];
        #if ( ipconfigUSE_IPv6 != 0 )
            FreeRTOS_printf( ( "xPingReady %d xPing4 %d xPing6 %d  Delta %u\n",
                               ( int ) xPingReady, ( int ) xPing4Count, ( int ) xPing6Count, ( unsigned ) uxTimeTicks ) );
        #else
            FreeRTOS_printf( ( "xPingReady %d xPing4 %d  Delta %u\n", ( int ) xPingReady, ( int ) xPing4Count, ( unsigned ) uxTimeTicks ) );
        #endif
        xPingReady = pdFALSE;

        if( ( xPing4Count >= 0 ) && ( xPing4Count < PING_COUNT_MAX ) )
        {
            /* 10 bytes, 100 clock ticks. */
            FreeRTOS_SendPingRequest( ulPingIPAddress, uxPingSize, PING_TIMEOUT );
            uxPingTimes[ 0 ] = ( TickType_t ) ullGetHighResolutionTime();
        }

        #if ( ipconfigUSE_IPv6 != 0 )
            if( ( xPing6Count >= 0 ) && ( xPing6Count < PING_COUNT_MAX ) )
            {
                FreeRTOS_SendPingRequestIPv6( &xPing6IPAddress, uxPingSize, PING_TIMEOUT );
                uxPingTimes[ 0 ] = ( TickType_t ) ullGetHighResolutionTime();
            }
        #endif
    }
}
/*-----------------------------------------------------------*/

static struct freertos_addrinfo * pxDNSLookup( char * pcHost,
                                               BaseType_t xIPVersion,
                                               BaseType_t xAsynchronous,
                                               BaseType_t xDoClear )
{
    struct freertos_addrinfo xHints;
    struct freertos_addrinfo * pxResult = NULL;

    memset( &( xHints ), 0, sizeof( xHints ) );

    if( xIPVersion == 6 )
    {
        xHints.ai_family = FREERTOS_AF_INET6;
    }
    else
    {
        xHints.ai_family = FREERTOS_AF_INET;
    }

    FreeRTOS_printf( ( "pxDNSLookup: '%s' IPv%d %s DNS-clear = %s\n",
                       pcHost, ( int ) xIPVersion, ( xAsynchronous != 0 ) ? "Async" : "Sync", ( xDoClear != 0 ) ? "true" : "false" ) );

    if( xDoClear )
    {
        #if ( ipconfigUSE_DNS_CACHE != 0 )
        {
            FreeRTOS_dnsclear();
            FreeRTOS_printf( ( "Clear DNS cache\n" ) );
        }
        #endif /* ipconfigUSE_DNS_CACHE */
        FreeRTOS_ClearARP( NULL );
        FreeRTOS_printf( ( "Clear ARP cache\n" ) );
    }

    xDNSCount = 0;
    #if ( ipconfigDNS_USE_CALLBACKS != 0 )
        if( xAsynchronous != 0 )
        {
            uint32_t ulReturn;
            xApplicationGetRandomNumber( &( ulReturn ) );
            void * pvSearchID = ( void * ) ulReturn;

            BaseType_t rc = FreeRTOS_getaddrinfo_a(
                pcHost,    /* The node. */
                NULL,      /* const char *pcService: ignored for now. */
                &xHints,   /* If not NULL: preferences. */
                &pxResult, /* An allocated struct, containing the results. */
                vDNSEvent,
                pvSearchID,
                5000 );

            FreeRTOS_printf( ( "dns query%d: '%s' = %d\n", ( int ) xIPVersion, pcHost, ( int ) rc ) );

            if( pxResult != NULL )
            {
                show_addressinfo( pxResult );
            }
        }
        else
    #endif /* if ( ipconfigDNS_USE_CALLBACKS != 0 ) */
    {
        #if ( ipconfigDNS_USE_CALLBACKS == 0 )
            if( xAsynchronous != 0 )
            {
                FreeRTOS_printf( ( "ipconfigDNS_USE_CALLBACKS is not defined\n" ) );
            }
        #endif
        BaseType_t rc = FreeRTOS_getaddrinfo(
            pcHost,      /* The node. */
            NULL,        /* const char *pcService: ignored for now. */
            &xHints,     /* If not NULL: preferences. */
            &pxResult ); /* An allocated struct, containing the results. */
        FreeRTOS_printf( ( "FreeRTOS_getaddrinfo: rc %d\n", ( int ) rc ) );

        if( pxResult != NULL )
        {
            show_addressinfo( pxResult );
        }

        if( rc != 0 )
        {
            FreeRTOS_printf( ( "dns query%d: '%s' No results\n", ( int ) xIPVersion, pcHost ) );
        }
        else
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                if( xIPVersion == 6 )
                {
                    struct freertos_sockaddr * pxAddr6;
                    pxAddr6 = ( struct freertos_sockaddr * ) pxResult->ai_addr;

                    FreeRTOS_printf( ( "dns query%d: '%s' = %pip rc = %d\n", ( int ) xIPVersion, pcHost, pxAddr6->sin_address.xIP_IPv6.ucBytes, ( int ) rc ) );
                }
                else
            #endif /* ipconfigUSE_IPv6 */
            {
                uint32_t luIPAddress = pxResult->ai_addr->sin_address.ulIP_IPv4;
                FreeRTOS_printf( ( "dns query%d: '%s' = %lxip rc = %d\n", ( int ) xIPVersion, pcHost, FreeRTOS_ntohl( luIPAddress ), ( int ) rc ) );
            }
        }
    }

    #if ( ipconfigDNS_USE_CALLBACKS != 0 )
        if( ( pxResult == NULL ) && ( xAsynchronous != 0 ) )
        {
            #if ( ipconfigUSE_IPv6 != 0 )
                IPv6_Address_t xAddress_IPv6;
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */
            uint32_t ulIpAddress;
            int iCount;

            for( iCount = 0; iCount < 10; iCount++ )
            {
                ulTaskNotifyTake( pdTRUE, pdMS_TO_TICKS( 1000 ) );

                if( xDNSCount != 0 )
                {
                    break;
                }
            }

            vTaskDelay( 333 );
            pxResult = ( struct freertos_addrinfo * ) pvPortMalloc( sizeof( *pxResult ) );

            if( pxResult != NULL )
            {
                memset( pxResult, '\0', sizeof( *pxResult ) );
                pxResult->ai_canonname = pxResult->xPrivateStorage.ucName;
                strncpy( pxResult->xPrivateStorage.ucName, pcHost, sizeof( pxResult->xPrivateStorage.ucName ) );

                pxResult->ai_addr = &( pxResult->xPrivateStorage.sockaddr );

                switch( xIPVersion )
                {
                    #if ( ipconfigUSE_IPv4 != 0 )
                        case 4:
                            #if ( ipconfigUSE_DNS_CACHE != 0 )
                                ulIpAddress = FreeRTOS_dnslookup( pcHost );
                                FreeRTOS_printf( ( "Lookup4 '%s' = %lxip\n", pcHost, FreeRTOS_ntohl( ulIpAddress ) ) );
                                pxResult->ai_addr->sin_address.ulIP_IPv4 = ulIpAddress;
                                pxResult->ai_family = FREERTOS_AF_INET4;
                                pxResult->ai_addrlen = ipSIZE_OF_IPv4_ADDRESS;
                            #endif
                            break;
                    #endif /* ( ipconfigUSE_IPv4 != 0 ) */

                    #if ( ipconfigUSE_IPv6 != 0 )
                        case 6:
                            memset( xAddress_IPv6.ucBytes, '\0', sizeof( xAddress_IPv6.ucBytes ) );

                            if( xIPVersion == 6 )
                            {
                                FreeRTOS_dnslookup6( pcHost, &( xAddress_IPv6 ) );
                                FreeRTOS_printf( ( "Lookup6 '%s' = %pip\n", pcHost, xAddress_IPv6.ucBytes ) );
                                pxResult->ai_family = FREERTOS_AF_INET6;
                                pxResult->ai_addrlen = ipSIZE_OF_IPv6_ADDRESS;
                                memcpy( pxResult->xPrivateStorage.sockaddr.sin_address.xIP_IPv6.ucBytes, xAddress_IPv6.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
                            }
                            break;
                    #endif /* ( ipconfigUSE_IPv6 != 0 ) */

                    default:
                        /* MISRA 16.4 Compliance */
                        FreeRTOS_debug_printf( ( "pxDNSLookup: Undefined IP Version Type \n" ) );
                        break;
                }
            }
        }
    #endif /* if ( ipconfigDNS_USE_CALLBACKS != 0 ) */
    /* Don't forget to call FreeRTOS_freeaddrinfo() */
    return pxResult;
}
/*-----------------------------------------------------------*/


static void vDNSEvent( const char * pcName,
                       void * pvSearchID,
                       struct freertos_addrinfo * pxAddrInfo )
{
    ( void ) pvSearchID;

    if( pxAddrInfo == NULL )
    {
        FreeRTOS_printf( ( "vDNSEvent(%s) : nothing found\n", pcName ) );
    }
    else
    {
        FreeRTOS_printf( ( "vDNSEvent: family = %d\n", ( int ) pxAddrInfo->ai_family ) );

        switch( pxAddrInfo->ai_family )
        {
            #if ( ipconfigUSE_IPv4 != 0 )
                case FREERTOS_AF_INET:
                   {
                       uint32_t ulIPaddress = pxAddrInfo->ai_addr->sin_address.ulIP_IPv4;

                       if( ulIPaddress == 0uL )
                       {
                           FreeRTOS_printf( ( "vDNSEvent/v4: '%s' timed out\n", pcName ) );
                       }
                       else
                       {
                           FreeRTOS_printf( ( "vDNSEvent/v4: found '%s' on %lxip\n", pcName, FreeRTOS_ntohl( ulIPaddress ) ) );
                       }
                   }
                   break;
            #endif /* ( ipconfigUSE_IPv4 != 0 ) */

            #if ( ipconfigUSE_IPv6 != 0 )
                case FREERTOS_AF_INET6:
                   {
                       BaseType_t xIsEmpty = pdTRUE, xIndex;

                       for( xIndex = 0; xIndex < ( BaseType_t ) ARRAY_SIZE( pxAddrInfo->ai_addr->sin_address.xIP_IPv6.ucBytes ); xIndex++ )
                       {
                           if( pxAddrInfo->ai_addr->sin_address.xIP_IPv6.ucBytes[ xIndex ] != ( uint8_t ) 0u )
                           {
                               xIsEmpty = pdFALSE;
                               break;
                           }
                       }

                       if( xIsEmpty )
                       {
                           FreeRTOS_printf( ( "vDNSEvent/v6: '%s' timed out\n", pcName ) );
                       }
                       else
                       {
                           FreeRTOS_printf( ( "vDNSEvent/v6: found '%s' on %pip\n", pcName, pxAddrInfo->ai_addr->sin_address.xIP_IPv6.ucBytes ) );
                       }
                   }
                   break;
            #endif /* ( ipconfigUSE_IPv6 != 0 ) */

            default:
                /* MISRA 16.4 Compliance */
                FreeRTOS_debug_printf( ( "vDNSEvent: Undefined Family Type \n" ) );
                break;
        }
    }

    if( xServerWorkTaskHandle != NULL )
    {
        xDNSCount++;
        xTaskNotifyGive( xServerWorkTaskHandle );
    }
}

/*-----------------------------------------------------------*/

void showEndPoint( NetworkEndPoint_t * pxEndPoint )
{
    int bWantDHCP, bWantRA;
    const char * pcMethodName;
    size_t uxDNSIndex;

    #if ( ipconfigUSE_DHCP != 0 )
        bWantDHCP = pxEndPoint->bits.bWantDHCP;
    #else
        bWantDHCP = 0;
    #endif
    #if ( ipconfigUSE_RA != 0 )
        bWantRA = pxEndPoint->bits.bWantRA;
    #else
        bWantRA = 0;
    #endif /* ( ipconfigUSE_RA != 0 ) */

    if( bWantDHCP != 0 )
    {
        pcMethodName = "DHCP";
    }
    else if( bWantRA != 0 )
    {
        pcMethodName = "RA";
    }
    else
    {
        pcMethodName = "static";
    }

    #if ( ipconfigUSE_IPv6 != 0 )
        if( pxEndPoint->bits.bIPv6 )
        {
            IPv6_Address_t xPrefix;

            /* Extract the prefix from the IP-address */
            FreeRTOS_CreateIPv6Address( &( xPrefix ), &( pxEndPoint->ipv6_settings.xIPAddress ), pxEndPoint->ipv6_settings.uxPrefixLength, pdFALSE );

            FreeRTOS_printf( ( "IP-address : %pip\n", pxEndPoint->ipv6_settings.xIPAddress.ucBytes ) );

            if( memcmp( pxEndPoint->ipv6_defaults.xIPAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) != 0 )
            {
                FreeRTOS_printf( ( "Default IP : %pip\n", pxEndPoint->ipv6_defaults.xIPAddress.ucBytes ) );
            }

            FreeRTOS_printf( ( "End-point  : up = %s method %s\n", ( pxEndPoint->bits.bEndPointUp != 0 ) ? "yes" : "no", pcMethodName ) );
            FreeRTOS_printf( ( "Prefix     : %pip/%d\n", xPrefix.ucBytes, ( int ) pxEndPoint->ipv6_settings.uxPrefixLength ) );
            FreeRTOS_printf( ( "GW         : %pip\n", pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes ) );

            for( uxDNSIndex = 0U; uxDNSIndex < ipconfigENDPOINT_DNS_ADDRESS_COUNT; uxDNSIndex++ )
            {
                FreeRTOS_printf( ( "DNS-%u      : %pip\n", uxDNSIndex, pxEndPoint->ipv6_settings.xDNSServerAddresses[ uxDNSIndex ].ucBytes ) );
            }
        }
        else
    #endif /* ( ipconfigUSE_IPv6 != 0 ) */
    {
        FreeRTOS_printf( ( "IP-address : %lxip\n",
                           FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulIPAddress ) ) );

        if( pxEndPoint->ipv4_settings.ulIPAddress != pxEndPoint->ipv4_defaults.ulIPAddress )
        {
            FreeRTOS_printf( ( "Default IP : %lxip\n", FreeRTOS_ntohl( pxEndPoint->ipv4_defaults.ulIPAddress ) ) );
        }

        FreeRTOS_printf( ( "End-point  : up = %s method %s\n", pxEndPoint->bits.bEndPointUp ? "yes" : "no", pcMethodName ) );

        FreeRTOS_printf( ( "Net mask   : %lxip\n", FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulNetMask ) ) );
        FreeRTOS_printf( ( "GW         : %lxip\n", FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulGatewayAddress ) ) );

        for( uxDNSIndex = 0U; uxDNSIndex < ipconfigENDPOINT_DNS_ADDRESS_COUNT; uxDNSIndex++ )
        {
            FreeRTOS_printf( ( "DNS-%u      : %xip\n", uxDNSIndex, ( unsigned ) FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulDNSServerAddresses[ uxDNSIndex ] ) ) );
        }

        FreeRTOS_printf( ( "Broadcast  : %lxip\n", FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulBroadcastAddress ) ) );
    }

    FreeRTOS_printf( ( "MAC address: %02x-%02x-%02x-%02x-%02x-%02x\n",
                       pxEndPoint->xMACAddress.ucBytes[ 0 ],
                       pxEndPoint->xMACAddress.ucBytes[ 1 ],
                       pxEndPoint->xMACAddress.ucBytes[ 2 ],
                       pxEndPoint->xMACAddress.ucBytes[ 3 ],
                       pxEndPoint->xMACAddress.ucBytes[ 4 ],
                       pxEndPoint->xMACAddress.ucBytes[ 5 ] ) );
    FreeRTOS_printf( ( " \n" ) );
}
/*-----------------------------------------------------------*/

static void clear_caches()
{
    #if ( ipconfigUSE_DNS_CACHE != 0 )
    {
        FreeRTOS_dnsclear();
        #if ( ipconfigUSE_IPv6 != 0 )
            FreeRTOS_ClearND();
        #endif /* ( ipconfigUSE_IPv6 != 0 ) */
    }
    #endif /* ipconfigUSE_DNS_CACHE */
    FreeRTOS_ClearARP( NULL );
    FreeRTOS_printf( ( "Cleared caches.\n" ) );
}
/*-----------------------------------------------------------*/
