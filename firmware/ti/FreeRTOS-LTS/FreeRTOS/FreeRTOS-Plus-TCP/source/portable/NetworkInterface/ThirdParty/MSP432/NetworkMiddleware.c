/*
 * FreeRTOS+TCP V4.2.2
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Driver code:
 * Copyright (C) Nicholas J. Kinar <n.kinar@usask.ca>, Centre for Hydrology, University of Saskatchewan
 *
 * MSP432 Driverlib (C) 2017-2019 Texas Instruments Incorporated <https://www.ti.com/>
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

#include <stdint.h>

#include "FreeRTOS.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_private.h"
#include "FreeRTOS_Sockets.h"

#include "NetworkMiddleware.h"
#include "NetworkInterface.h"

/* Waiting time between network EMAC hardware up and down */
#define TIME_TO_WAIT_BETWEEN_NETUP_DOWN    2000

/* Stack for up and down thread */
#define NETWORK_TASK_MIDDLEWARE_STACK      1000

/* Holds the device name used for LLMNR */
static char DEV_NAME[ MAX_NAME_LLMNR ];

/* This function is provided by external code to obtain a random number */
extern uint32_t obtain_rand32();

static SemaphoreHandle_t xSemaphore = NULL;
static TaskHandle_t xTaskToNotifyReset = NULL;
static uint32_t xDelay;

static void prvNetworkResetTask( void * pvParameters );


/*  Call this function before starting the scheduler and after the MAC address and device name has been loaded.
 *  The function can only be called once to set up the tasks. */
void vPublicSetupFreeRTOSTasks( const struct InternalNetworkMiddlewareData data )
{
    /* setup a device name */
    vPublicSetupDeviceName( data.deviceName );

    /* get the MAC address from the driver code (assuming this is also set up) */
    uint8_t uc8MACAddr[ ipMAC_ADDRESS_LENGTH_BYTES ];
    vPublicGetMACAddr( uc8MACAddr );

    /* set up the task to reset the network every so often */
    if( data.resetNetworkTaskRunning == pdTRUE )
    {
        xDelay = data.resetNetworkTaskEveryXSeconds;
        xSemaphore = xSemaphoreCreateMutex();
        xTaskCreate( prvNetworkResetTask,
                     "resetNet",
                     NETWORK_TASK_MIDDLEWARE_STACK,
                     NULL,
                     tskIDLE_PRIORITY,
                     &xTaskToNotifyReset );
    }

    /* init the network stack */
    FreeRTOS_IPInit( data.ucIPAddress,
                     data.ucNetMask,
                     data.ucGatewayAddress,
                     data.ucDNSServerAddress,
                     uc8MACAddr );
}


/* Helper function to assign bytes to an array used to indicate the IP address */
void vConvertOctetsToAddr( uint8_t arr[ ipIP_ADDRESS_LENGTH_BYTES ],
                           uint8_t b0,
                           uint8_t b1,
                           uint8_t b2,
                           uint8_t b3 )
{
    arr[ 0 ] = b0;
    arr[ 1 ] = b1;
    arr[ 2 ] = b2;
    arr[ 3 ] = b3;
} /* end */


/* Task that resets the network every so often */
void prvNetworkResetTask( void * pvParameters )
{
    uint32_t cnt;

    cnt = 0;

    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 1000 ) );
        cnt++;

        if( cnt > xDelay )
        {
            cnt = 0;

            if( xSemaphoreTake( xSemaphore, 0 ) == pdTRUE )
            {
                FreeRTOS_NetworkDown();
                xSemaphoreGive( xSemaphore );
            }
        }
    }
}


/* Call this function from a task to prevent a network reset during a critical section of the code */
BaseType_t publicPreventNetworkReset( const BaseType_t preventReset,
                                      const uint32_t waitTime )
{
    if( preventReset == pdTRUE )
    {
        if( xSemaphoreTake( xSemaphore, pdMS_TO_TICKS( waitTime ) ) == pdTRUE )
        {
            return pdTRUE;
        }
        else
        {
            return pdFALSE;
        }
    }
    else /* do not prevent reset */
    {
        xSemaphoreGive( xSemaphore );
    }

    return pdTRUE;
}


/*  CALLED BY FREERTOS
 *  Function that sets pulNumber to a random number, and then returns pdTRUE.
 *  If the random number could not be obtained, then the function will return pdFALSE. */
BaseType_t xApplicationGetRandomNumber( uint32_t * pulNumber )
{
    *pulNumber = 0;
    uint32_t num = obtain_rand32();

    if( num == 0 )
    {
        return pdFALSE;
    }

    *pulNumber = num;
    return pdTRUE;
}

/*  CALLED BY FREERTOS
 *  Function that returns a random number for TCP.  This is taken to be a random number. */
uint32_t ulApplicationGetNextSequenceNumber( uint32_t ulSourceAddress,
                                             uint16_t usSourcePort,
                                             uint32_t ulDestinationAddress,
                                             uint16_t usDestinationPort )
{
    uint32_t pulNumber = 0;

    xApplicationGetRandomNumber( &pulNumber );
    return pulNumber;
}


/*  CALLED BY FREERTOS
 *  Function to obtain random number */
UBaseType_t uxRand()
{
    uint32_t num = obtain_rand32();

    return num;
}


/*  CALLED BY FREERTOS
 *   Function called when the network connects or disconnects */
void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent )
{
    uint32_t ulIPAddress, ulNetMask, ulGatewayAddress, ulDNSServerAddress;
    static BaseType_t xNetworkTasksAlreadyCreated = pdFALSE;
    char cBuffer[ 16 ];

    if( eNetworkEvent == eNetworkUp )
    {
        if( xNetworkTasksAlreadyCreated == pdFALSE )
        {
            /*  Unblock any necessary tasks here when the network is up
             *  Set a flag to indicate that the tasks do not need to be created again */
            xNetworkTasksAlreadyCreated = pdTRUE;
        }

        FreeRTOS_GetAddressConfiguration( &ulIPAddress,
                                          &ulNetMask,
                                          &ulGatewayAddress,
                                          &ulDNSServerAddress );

        FreeRTOS_inet_ntoa( ulIPAddress, cBuffer );
        vLoggingPrintf( "IP Address: %s\r\n", cBuffer );

        FreeRTOS_inet_ntoa( ulNetMask, cBuffer );
        vLoggingPrintf( "Subnet Mask: %s\r\n", cBuffer );

        FreeRTOS_inet_ntoa( ulGatewayAddress, cBuffer );
        vLoggingPrintf( "Gateway IP Address: %s\r\n", cBuffer );

        FreeRTOS_inet_ntoa( ulDNSServerAddress, cBuffer );
        vLoggingPrintf( "DNS server IP Address: %s\r\n", cBuffer );
    } /* end if */
    else if( eNetworkEvent == eNetworkDown )
    {
        xNetworkTasksAlreadyCreated = pdFALSE; /* clear a flag to indicate that the tasks needs to be created again */
        /* Stop or block any running tasks here */
    } /* end if */
} /* end */


/*  CALLED BY FREERTOS
 *  Function that indicates there is a ping response
 *  Called from IPTraceMacroDefaults.h
 *  NOTE: This function can cause the stack to slow down, so it should
 *  only be used for debugging. */

/*
 #ifndef iptraceSENDING_PING_REPLY
 *  extern void pingReply( uint32_t ulIPAddress );
 #define iptraceSENDING_PING_REPLY( ulIPAddress )  pingReply(ulIPAddress )
 #endif
 */
void pingReply( uint32_t ulIPAddress )
{
    #ifdef SEND_PING_PRINT_REPLY
        char cBuffer[ 16 ];
        FreeRTOS_inet_ntoa( ulIPAddress, cBuffer );
        vLoggingPrintf( "Ping response to: %s\r\n", cBuffer );
    #endif
}


/*  CALLED BY FREERTOS when conducting a DNS query
 *  Function that returns pdTRUE if the pcName matches the LLMNR node name */
BaseType_t xApplicationDNSQueryHook( const char * pcName )
{
    if( strcmp( pcName, DEV_NAME ) )
    {
        return pdTRUE;
    }

    return pdFALSE;
}


/*  CALLED BY FREERTOS
 *  Hook to return a human-readable name */
const char * pcApplicationHostnameHook( void )
{
    const char * name;

    name = DEV_NAME;
    return name;
}


/* Call this function to assign a device name before the stack is up */
void vPublicSetupDeviceName( const char * deviceName )
{
    memset( DEV_NAME, 0, sizeof( DEV_NAME ) );
    strncpy( DEV_NAME, deviceName, MAX_NAME_LLMNR - 1 );
}
