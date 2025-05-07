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
 * @file main.c
 * @brief Implements the main function.
 */

/* FreeRTOS include. */
#include <FreeRTOS.h>
#include "task.h"

/* System application includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DHCP.h"

#include <string.h>
#include <stdarg.h>
#include <time.h>

#define mainHOST_NAME           "Build Combination"
#define mainDEVICE_NICK_NAME    "Build_Combination"

#if defined( _MSC_VER ) && ( _MSC_VER <= 1600 )
    #define local_stricmp       _stricmp
#else
    #define local_stricmp       strcasecmp
#endif
/*-----------------------------------------------------------*/

/* Notes if the trace is running or not. */
static BaseType_t xTraceRunning = pdTRUE;

/* Default MAC address configuration.  The demo creates a virtual network
 * connection that uses this MAC address by accessing the raw Ethernet data
 * to and from a real network connection on the host PC.  See the
 * configNETWORK_INTERFACE_TO_USE definition for information on how to configure
 * the real network connection to use. */
const uint8_t ucMACAddress[ 6 ] =
{
    configMAC_ADDR0,
    configMAC_ADDR1,
    configMAC_ADDR2,
    configMAC_ADDR3,
    configMAC_ADDR4,
    configMAC_ADDR5
};

/* The default IP and MAC address used by the code. It is used as a place holder.
 */
static const uint8_t ucIPAddress[ 4 ] =
{
    configIP_ADDR0,
    configIP_ADDR1,
    configIP_ADDR2,
    configIP_ADDR3
};
static const uint8_t ucNetMask[ 4 ] =
{
    configNET_MASK0,
    configNET_MASK1,
    configNET_MASK2,
    configNET_MASK3
};
static const uint8_t ucGatewayAddress[ 4 ] =
{
    configGATEWAY_ADDR0,
    configGATEWAY_ADDR1,
    configGATEWAY_ADDR2,
    configGATEWAY_ADDR3
};
static const uint8_t ucDNSServerAddress[ 4 ] =
{
    configDNS_SERVER_ADDR0,
    configDNS_SERVER_ADDR1,
    configDNS_SERVER_ADDR2,
    configDNS_SERVER_ADDR3
};

/* Use by the pseudo random number generator. */
static UBaseType_t ulNextRand;

/*-----------------------------------------------------------*/
int main( void )
{
    /* Initialize the network interface.
     *
     ***NOTE*** Tasks that use the network are created in the network event hook
     * when the network is connected and ready for use (see the definition of
     * vApplicationIPNetworkEventHook() below).  The address values passed in here
     * are used if ipconfigUSE_DHCP is set to 0, or if ipconfigUSE_DHCP is set to 1
     * but a DHCP server cannot be contacted. */
    #if ( ipconfigIPv4_BACKWARD_COMPATIBLE != 0 ) && ( ipconfigUSE_IPv4 != 0 )
        FreeRTOS_printf( ( "FreeRTOS_IPInit\n" ) );
        FreeRTOS_IPInit(
            ucIPAddress,
            ucNetMask,
            ucGatewayAddress,
            ucDNSServerAddress,
            ucMACAddress );
    #else
        FreeRTOS_printf( ( "FreeRTOS_IPInit_Multi\n" ) );
        FreeRTOS_IPInit_Multi();
    #endif

    vTaskStartScheduler();

    return 0;
}
/*-----------------------------------------------------------*/
/* *INDENT-OFF* */
#if ( ipconfigIPv4_BACKWARD_COMPATIBLE == 1 )
    void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
#else
    void vApplicationIPNetworkEventHook_Multi( eIPCallbackEvent_t eNetworkEvent,
                                               struct xNetworkEndPoint * pxEndPoint )
#endif
/* *INDENT-ON* */
{
    static BaseType_t xTasksAlreadyCreated = pdFALSE;

    /* If the network has just come up...*/
    if( ( eNetworkEvent == eNetworkUp ) && ( xTasksAlreadyCreated == pdFALSE ) )
    {
        /* Do nothing. Just a stub. */

        xTasksAlreadyCreated = pdTRUE;
    }
}

/*-----------------------------------------------------------*/

#if ( ( ipconfigUSE_LLMNR != 0 ) || \
    ( ipconfigUSE_NBNS != 0 ) ||    \
    ( ipconfigDHCP_REGISTER_HOSTNAME == 1 ) )

    const char * pcApplicationHostnameHook( void )
    {
        /* This function will be called during the DHCP: the machine will be registered
         * with an IP address plus this name. */
        return mainHOST_NAME;
    }

#endif /* if ( ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) || ( ipconfigDHCP_REGISTER_HOSTNAME == 1 ) ) */
/*-----------------------------------------------------------*/

#if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 )

    BaseType_t xApplicationDNSQueryHook( const char * pcName )
    {
        BaseType_t xReturn;

        /* Determine if a name lookup is for this node.  Two names are given
         * to this node: that returned by pcApplicationHostnameHook() and that set
         * by mainDEVICE_NICK_NAME. */
        if( local_stricmp( pcName, pcApplicationHostnameHook() ) == 0 )
        {
            xReturn = pdPASS;
        }
        else if( local_stricmp( pcName, mainDEVICE_NICK_NAME ) == 0 )
        {
            xReturn = pdPASS;
        }
        else
        {
            xReturn = pdFAIL;
        }

        return xReturn;
    }

#endif /* if ( ipconfigUSE_LLMNR != 0 ) || ( ipconfigUSE_NBNS != 0 ) */
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
    const uint32_t ulMSToSleep = 1;
    const TickType_t xKitHitCheckPeriod = pdMS_TO_TICKS( 1000UL );
    static TickType_t xTimeNow, xLastTimeCheck = 0;

    if( ( xTimeNow - xLastTimeCheck ) > xKitHitCheckPeriod )
    {
        xLastTimeCheck = xTimeNow;
    }

    /* Exit. Just a stub. */
}

/*-----------------------------------------------------------*/

void vLoggingPrintf( const char * pcFormat,
                     ... )
{
    va_list arg;

    va_start( arg, pcFormat );
    vprintf( pcFormat, arg );
    va_end( arg );
}
/*-----------------------------------------------------------*/

void getUserCmd( char * pucUserCmd )
{
    /* Provide a stub for this function. */
}
/*-----------------------------------------------------------*/

UBaseType_t uxRand( void )
{
    const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL;

    /* Utility function to generate a pseudo random number. */

    ulNextRand = ( ulMultiplier * ulNextRand ) + ulIncrement;
    return( ( int ) ( ulNextRand ) & 0x7fffUL );
}

BaseType_t xApplicationGetRandomNumber( uint32_t * pulNumber )
{
    *pulNumber = ( uint32_t ) uxRand();

    return pdTRUE;
}

/*-----------------------------------------------------------*/

void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                    StackType_t ** ppxIdleTaskStackBuffer,
                                    configSTACK_DEPTH_TYPE * pulIdleTaskStackSize )
{
    /* Provide a stub for this function. */
}

/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
    /* Provide a stub for this function. */
}

/*-----------------------------------------------------------*/

void vApplicationDaemonTaskStartupHook( void )
{
    /* Provide a stub for this function. */
}

/*
 * Callback that provides the inputs necessary to generate a randomized TCP
 * Initial Sequence Number per RFC 6528.  THIS IS ONLY A DUMMY IMPLEMENTATION
 * THAT RETURNS A PSEUDO RANDOM NUMBER SO IS NOT INTENDED FOR USE IN PRODUCTION
 * SYSTEMS.
 */
extern uint32_t ulApplicationGetNextSequenceNumber( uint32_t ulSourceAddress,
                                                    uint16_t usSourcePort,
                                                    uint32_t ulDestinationAddress,
                                                    uint16_t usDestinationPort )
{
    ( void ) ulSourceAddress;
    ( void ) usSourcePort;
    ( void ) ulDestinationAddress;
    ( void ) usDestinationPort;

    return ( uint32_t ) uxRand();
}

void vApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
                                     StackType_t ** ppxTimerTaskStackBuffer,
                                     configSTACK_DEPTH_TYPE * pulTimerTaskStackSize )
{
    /* Provide a stub for this function. */
}

void vApplicationMallocFailedHook( void )
{
    /* Provide a stub for this function. */
}

BaseType_t xNetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                    NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t bReleaseAfterSend )
{
    /* Provide a stub for this function. */
    return pdTRUE;
}

BaseType_t xNetworkInterfaceInitialise( void )
{
    /* Provide a stub for this function. */
    return pdTRUE;
}

struct xNetworkInterface * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                      struct xNetworkInterface * pxInterface )
{
    return pxInterface;
}

#if ( ipconfigUSE_DHCP_HOOK != 0 )
    #if ( ipconfigIPv4_BACKWARD_COMPATIBLE == 1 )
        eDHCPCallbackAnswer_t xApplicationDHCPHook( eDHCPCallbackPhase_t eDHCPPhase,
                                                    uint32_t ulIPAddress )
    #else
        eDHCPCallbackAnswer_t xApplicationDHCPHook_Multi( eDHCPCallbackPhase_t eDHCPPhase,
                                                          struct xNetworkEndPoint * pxEndPoint,
                                                          IP_Address_t * pxIPAddress )
    #endif
    {
        /* Provide a stub for this function. */
        return eDHCPContinue;
    }
#endif /* ( ipconfigUSE_DHCP_HOOK != 0 ) */

#if ( ipconfigPROCESS_CUSTOM_ETHERNET_FRAMES != 0 )

/*
 * The stack will call this user hook for all Ethernet frames that it
 * does not support, i.e. other than IPv4, IPv6 and ARP ( for the moment )
 * If this hook returns eReleaseBuffer or eProcessBuffer, the stack will
 * release and reuse the network buffer.  If this hook returns
 * eReturnEthernetFrame, that means user code has reused the network buffer
 * to generate a response and the stack will send that response out.
 * If this hook returns eFrameConsumed, the user code has ownership of the
 * network buffer and has to release it when it's done.
 */
    eFrameProcessingResult_t eApplicationProcessCustomFrameHook( NetworkBufferDescriptor_t * const pxNetworkBuffer )
    {
        ( void ) ( pxNetworkBuffer );
        return eProcessBuffer;
    }

#endif
void vApplicationPingReplyHook( ePingReplyStatus_t eStatus,
                                uint16_t usIdentifier )
{
    /* Provide a stub for this function. */
}

#if ( ipconfigUSE_IPv6 != 0 ) && ( ipconfigUSE_DHCPv6 != 0 )
    /* DHCPv6 needs a time-stamp, seconds after 1970. */
    uint32_t ulApplicationTimeHook( void )
    {
        return ( uint32_t ) time( NULL );
    }
#endif
