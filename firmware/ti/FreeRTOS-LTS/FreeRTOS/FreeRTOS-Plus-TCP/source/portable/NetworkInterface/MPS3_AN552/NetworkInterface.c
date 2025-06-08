/*
 * FreeRTOS+TCP V4.2.2
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Copyright 2023 Arm Limited and/or its affiliates
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
 * https://github.com/FreeRTOS
 * https://www.FreeRTOS.org
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "task.h"
#include "semphr.h"

/* Standard library definitions */
#include <string.h>
#include <limits.h>

/* FreeRTOS+TCP includes. */
#include <FreeRTOS_IP.h>
#include <FreeRTOS_IP_Private.h>
#include <NetworkInterface.h>
#include <NetworkBufferManagement.h>

/* Ethernet driver includes. */
#include "Driver_ETH_MAC.h"
#include "Driver_ETH_PHY.h"

/* ETH_LAN91C111 driver (ETH_LAN91C111.c) maintains it's own TX buffer to which
* ethenet packet is copied into during transmission and during reception, the
* driver expects a buffer into which the received ethernet packet is copied. */
#if ( ipconfigZERO_COPY_TX_DRIVER != 0 ) || ( ipconfigZERO_COPY_RX_DRIVER != 0 )
    #error ETH_LAN91C111 driver (ETH_LAN91C111.c) does not support zero copy.
#endif

/* Ethernet interface */
typedef struct xEthernetInterface
{
    ARM_DRIVER_ETH_MAC * pxEthernetMACDriver;
    ARM_DRIVER_ETH_PHY * pxEthernetPHYDriver;
    ARM_ETH_LINK_STATE eEthernetLinkState;
}
xEthernetInterface_t;

/* Ethernet MAC & PHY Driver */
extern ARM_DRIVER_ETH_MAC ARM_Driver_ETH_MAC_( 0 );
extern ARM_DRIVER_ETH_PHY ARM_Driver_ETH_PHY_( 0 );

/* Initialise Ethernet interface */
static xEthernetInterface_t xEthernetInterface0 =
{
    .pxEthernetMACDriver = &ARM_Driver_ETH_MAC_( 0 ),
    .pxEthernetPHYDriver = &ARM_Driver_ETH_PHY_( 0 ),
    .eEthernetLinkState  = ARM_ETH_LINK_DOWN
};

/* The function xLAN91C111_NetworkInterfaceInitialise() will be called as
 * long as it returns the value pdFAIL.
 * It will go through several stages as described in 'eEMACState'.
 */
typedef enum xEMAC_STATE
{
    xEMAC_Init,
    xEMAC_WaitPHY,
    xEMAC_Ready,
    xEMAC_Fatal,
} EMACState_t;

static EMACState_t eEMACState = xEMAC_Init;

/* Sets the size of the stack (in words, not bytes) of the task that reads bytes
 * from the network. */
#ifndef nwRX_TASK_STACK_SIZE
    #define nwRX_TASK_STACK_SIZE    ( configMINIMAL_STACK_SIZE * 2 )
#endif

#ifndef nwETHERNET_RX_HANDLER_TASK_PRIORITY
    /* #define nwETHERNET_RX_HANDLER_TASK_PRIORITY    ( configMAX_PRIORITIES - 1 ) */
    #define nwETHERNET_RX_HANDLER_TASK_PRIORITY    ( tskIDLE_PRIORITY + 4 )
#endif

/* Maximum size of ethernet frame that can transmitted using ETH_LAN91C111
 * driver (ETH_LAN91C111.c). The value of this macro is based on ETH_BUF_SIZE
 * macro defined in ETH_LAN91C111.c. */
#define ETHERNET_FRAME_MAX_SIZE    1536

/*-----------------------------------------------------------*/

/*
 * The task that processes incoming Ethernet packets.  It is unblocked by the
 * Ethernet Rx interrupt.
 */
static void prvRxTask( void * pvParameters );

/*
 * Performs low level reads to obtain data from the Ethernet hardware.
 */
static uint32_t prvLowLevelInput( NetworkBufferDescriptor_t ** pxNetworkBuffer );

/* Check Ethernet link status */
static void prvLAN91C111_CheckEthertnetLinkStatus();

/*-----------------------------------------------------------*/

/*
 * A pointer to the network interface is needed later when receiving packets.
 */
static NetworkInterface_t * pxMyInterface;

static void prvEthernetDriverNotifications( uint32_t event );
static BaseType_t xLAN91C111_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface );
static BaseType_t xLAN91C111_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                     NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                     BaseType_t bReleaseAfterSend );
static BaseType_t xLAN91C111_GetPhyLinkStatus( NetworkInterface_t * pxInterface );

NetworkInterface_t * pxLAN91C111_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                          NetworkInterface_t * pxInterface );

/*-----------------------------------------------------------*/

static TaskHandle_t xRxTaskHandle = NULL;

/*-----------------------------------------------------------*/

static void prvLAN91C111_CheckEthertnetLinkStatus()
{
    ARM_ETH_LINK_STATE eEthernetLinkState;
    IPStackEvent_t xRxEvent;

    eEthernetLinkState = xEthernetInterface0.pxEthernetPHYDriver->GetLinkState();

    /* If the ethernet link status has not changed, then return without taking
     * any actions */
    if( eEthernetLinkState != xEthernetInterface0.eEthernetLinkState )
    {
        xEthernetInterface0.eEthernetLinkState = eEthernetLinkState;

        /* The ethernet link is down, notify the IP stack and set driver
         * initialisation state machine to xEMAC_Init. The IP stack calls
         * xLAN91C111_NetworkInterfaceInitialise when it receives
         * eNetworkDownEvent event. */
        if( eEthernetLinkState == ARM_ETH_LINK_DOWN )
        {
            FreeRTOS_printf( ( "NetworkInterface: Ethernet link is down" ) );
            eEMACState = xEMAC_Init;
            xRxEvent.eEventType = eNetworkDownEvent;
            xRxEvent.pvData = ( void * ) pxMyInterface;
            xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0 );
        }
    }
}

/*-----------------------------------------------------------*/

static void prvRxTask( void * pvParameters )
{
    const TickType_t xBlockTime = pdMS_TO_TICKS( 100UL );
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
    NetworkBufferDescriptor_t * pxNetworkBuffer = NULL;
    uint32_t ulDataRead;
    BaseType_t xReleaseNetworkBuffer = pdFALSE;

    ( void ) pvParameters;

    for( ; ; )
    {
        /* Wait for the Ethernet ISR to receive a packet or a timeout (100ms). */
        ulTaskNotifyTake( pdFALSE, xBlockTime );

        ulDataRead = prvLowLevelInput( &pxNetworkBuffer );

        if( ulDataRead > 0 )
        {
            xRxEvent.pvData = ( void * ) pxNetworkBuffer;

            pxNetworkBuffer->pxInterface = pxMyInterface;
            pxNetworkBuffer->pxEndPoint = FreeRTOS_MatchingEndpoint( pxMyInterface, pxNetworkBuffer->pucEthernetBuffer );

            if( pxNetworkBuffer->pxEndPoint == NULL )
            {
                FreeRTOS_printf( ( "NetworkInterface: can not find a proper endpoint\n" ) );
                xReleaseNetworkBuffer = pdTRUE;
            }
            else
            {
                if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0 ) == pdFAIL )
                {
                    xReleaseNetworkBuffer = pdTRUE;
                }
            }

            if( xReleaseNetworkBuffer == pdTRUE )
            {
                vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
            }
        }

        prvLAN91C111_CheckEthertnetLinkStatus();
    }
}
/*-----------------------------------------------------------*/

static uint32_t prvLowLevelInput( NetworkBufferDescriptor_t ** pxNetworkBuffer )
{
    const TickType_t xDescriptorWaitTime = pdMS_TO_TICKS( 0 );
    uint32_t ulMessageLength = 0;
    int32_t lReceivedBytes = 0;

    ulMessageLength = xEthernetInterface0.pxEthernetMACDriver->GetRxFrameSize();

    if( ulMessageLength != 0 )
    {
        *pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( ulMessageLength,
                                                             xDescriptorWaitTime );

        if( *pxNetworkBuffer != NULL )
        {
            lReceivedBytes = xEthernetInterface0.pxEthernetMACDriver->ReadFrame(
                ( ( *pxNetworkBuffer )->pucEthernetBuffer ),
                ulMessageLength );

            if( lReceivedBytes >= 0 )
            {
                ( *pxNetworkBuffer )->xDataLength = lReceivedBytes;
            }
            else
            {
                FreeRTOS_debug_printf( ( "NetworkInterface: Ethernet driver ReadFrame returned %d \n", lReceivedBytes ) );
                lReceivedBytes = 0;
            }
        }
        else
        {
            FreeRTOS_printf( ( "NetworkInterface: pxNetworkBuffer = NULL\n" ) );
            /* No memory available for NetworkBuffer, drop the frame */
            xEthernetInterface0.pxEthernetMACDriver->ReadFrame(
                NULL,
                0 );
        }
    }

    return lReceivedBytes;
}
/*-----------------------------------------------------------*/

static BaseType_t xLAN91C111_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    BaseType_t xReturn = pdFAIL;
    BaseType_t xDriverReturn = ARM_DRIVER_ERROR;
    const TickType_t xEthernetLinkStateTimeOut = pdMS_TO_TICKS( 1000 );
    ARM_ETH_MAC_CAPABILITIES xEthernetMACCapabilities;
    ARM_ETH_LINK_INFO xEthernetLinkInfo;
    uint32_t ulMACControlArg;

    ( void ) pxInterface;

    switch( eEMACState )
    {
        case xEMAC_Init:

            /* Initialise Ethernet Driver */
            xDriverReturn = xEthernetInterface0.pxEthernetMACDriver->Initialize( prvEthernetDriverNotifications );

            if( xDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: Failed to initialise MAC Driver: %d\n", xDriverReturn ) );
                break;
            }

            xDriverReturn = xEthernetInterface0.pxEthernetMACDriver->PowerControl( ARM_POWER_FULL );

            if( xDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: Failed to set power to ethernet MAC device: %d\n", xDriverReturn ) );
                break;
            }

            xDriverReturn = xEthernetInterface0.pxEthernetMACDriver->SetMacAddress( ( ARM_ETH_MAC_ADDR * ) &pxInterface->pxEndPoint->xMACAddress );

            if( xDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: Failed to set MAC address: %d\n", xDriverReturn ) );
                break;
            }

            /* Initialise PHY Driver */
            xDriverReturn = xEthernetInterface0.pxEthernetPHYDriver->Initialize(
                xEthernetInterface0.pxEthernetMACDriver->PHY_Read,
                xEthernetInterface0.pxEthernetMACDriver->PHY_Write );

            if( xDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: Failed to initialise PHY Driver: %d\n", xDriverReturn ) );
                break;
            }

            xDriverReturn = xEthernetInterface0.pxEthernetPHYDriver->PowerControl( ARM_POWER_FULL );

            if( xDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: Failed to set power to PHY device: %d\n", xDriverReturn ) );
                break;
            }

            xDriverReturn = xEthernetInterface0.pxEthernetPHYDriver->SetInterface( xEthernetMACCapabilities.media_interface );

            if( xDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: Failed to set ethernet media interface: %d\n", xDriverReturn ) );
                break;
            }

            xDriverReturn = xEthernetInterface0.pxEthernetPHYDriver->SetMode( ARM_ETH_PHY_AUTO_NEGOTIATE );

            if( xDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: Failed to set ethernet PHY device operation mode: %d\n", xDriverReturn ) );
                break;
            }

            eEMACState = xEMAC_WaitPHY;

        case xEMAC_WaitPHY:

            /* Wait for the Ethernet link to be up */
            vTaskDelay( xEthernetLinkStateTimeOut );
            xEthernetInterface0.eEthernetLinkState = xEthernetInterface0.pxEthernetPHYDriver->GetLinkState();

            if( xEthernetInterface0.eEthernetLinkState == ARM_ETH_LINK_DOWN )
            {
                break;
            }

            xEthernetLinkInfo = xEthernetInterface0.pxEthernetPHYDriver->GetLinkInfo();
            ulMACControlArg = xEthernetLinkInfo.speed << ARM_ETH_MAC_SPEED_Pos |
                              xEthernetLinkInfo.duplex << ARM_ETH_MAC_DUPLEX_Pos |
                              ARM_ETH_MAC_ADDRESS_BROADCAST;
            /* Configure Ethernet MAC based on PHY status */
            xDriverReturn = xEthernetInterface0.pxEthernetMACDriver->Control( ARM_ETH_MAC_CONFIGURE, ulMACControlArg );

            if( xDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: Failed to configure ethernet MAC device: %d\n", xDriverReturn ) );
                break;
            }

            /* Enable RX */
            xDriverReturn = xEthernetInterface0.pxEthernetMACDriver->Control( ARM_ETH_MAC_CONTROL_RX, 1 );

            if( xDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: Failed to enable ethernet MAC reception: %d\n", xDriverReturn ) );
                break;
            }

            /* Enable TX */
            xDriverReturn = xEthernetInterface0.pxEthernetMACDriver->Control( ARM_ETH_MAC_CONTROL_TX, 1 );

            if( xDriverReturn != ARM_DRIVER_OK )
            {
                eEMACState = xEMAC_Fatal;
                FreeRTOS_printf( ( "NetworkInterface: Failed to enable ethernet MAC transmission: %d\n", xDriverReturn ) );
                break;
            }

            if( xRxTaskHandle == NULL )
            {
                /* Task that reads incoming Ethernet frames and sends it FreeRTOS
                 * TCP/IP stack. */
                xDriverReturn = xTaskCreate( prvRxTask,
                                             "EMAC ",
                                             nwRX_TASK_STACK_SIZE,
                                             NULL,
                                             nwETHERNET_RX_HANDLER_TASK_PRIORITY,
                                             &xRxTaskHandle );

                if( xDriverReturn != pdPASS )
                {
                    eEMACState = xEMAC_Fatal;
                    FreeRTOS_printf( ( "NetworkInterface: Unable to create prvRxTask: %d\n", xDriverReturn ) );
                    break;
                }
            }

            eEMACState = xEMAC_Ready;

        case xEMAC_Ready:

            /* Ethernet driver is ready. */
            xReturn = pdPASS;
            break;

        case xEMAC_Fatal:

            /* A fatal error has occurred, and the ethernet driver
             * can not start. */
            break;
    }

    return xReturn;
}

static void prvEthernetDriverNotifications( uint32_t event )
{
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    configASSERT( xRxTaskHandle );

    if( event == ARM_ETH_MAC_EVENT_RX_FRAME )
    {
        /* Ethernet frame received. Send notification to Receive task. */
        vTaskNotifyGiveFromISR( xRxTaskHandle, &xHigherPriorityTaskWoken );
    }

    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static BaseType_t xLAN91C111_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                     NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                     BaseType_t xReleaseAfterSend )
{
    BaseType_t xReturn = pdPASS;

    ( void ) pxInterface;

    if( xEthernetInterface0.eEthernetLinkState == ARM_ETH_LINK_UP )
    {
        if( pxNetworkBuffer->xDataLength > ETHERNET_FRAME_MAX_SIZE )
        {
            FreeRTOS_debug_printf( ( "NetworkInterface: Too big Ethernet frame, Size:", pxNetworkBuffer->xDataLength ) );
            xReturn = pdFAIL;
        }

        if( xReturn == pdPASS )
        {
            xReturn = xEthernetInterface0.pxEthernetMACDriver->SendFrame(
                pxNetworkBuffer->pucEthernetBuffer,
                pxNetworkBuffer->xDataLength,
                0 );

            if( xReturn < 0 )
            {
                FreeRTOS_debug_printf( ( "NetworkInterface: Ethernet driver SendFrame returned %d ", xReturn ) );
            }
        }
    }

    if( xReleaseAfterSend == pdTRUE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    /* FIX ME if you want to use BufferAllocation_1.c, which uses statically
     * allocated network buffers. */

    /* Hard force an assert as this driver cannot be used with BufferAllocation_1.c
     * without implementing this function. */
    configASSERT( 0 );
    ( void ) pxNetworkBuffers;
}
/*-----------------------------------------------------------*/


static BaseType_t xLAN91C111_GetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    ( void ) pxInterface;

    return ( BaseType_t ) xEthernetInterface0.pxEthernetPHYDriver->GetLinkState();
}

/*-----------------------------------------------------------*/

#if ( ipconfigIPv4_BACKWARD_COMPATIBLE != 0 )

/* Do not call the following function directly. It is there for downward compatibility.
 * The function FreeRTOS_IPInit() will call it to initialise the interface and end-point
 * objects.  See the description in FreeRTOS_Routing.h. */
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface )
    {
        return pxLAN91C111_FillInterfaceDescriptor( xEMACIndex, pxInterface );
    }

#endif
/*-----------------------------------------------------------*/

NetworkInterface_t * pxLAN91C111_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                          NetworkInterface_t * pxInterface )
{
    static char pcName[ 17 ];

    /* This function adds a network-interface.
     * Make sure that the object pointed to by 'pxInterface'
     * is declared static or global, and that it will remain to exist. */

    pxMyInterface = pxInterface;

    snprintf( pcName, sizeof( pcName ), "eth % ld ", xEMACIndex );

    memset( pxInterface, '\0', sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;                    /* Just for logging, debugging. */
    pxInterface->pvArgument = ( void * ) xEMACIndex; /* Has only meaning for the driver functions. */
    pxInterface->pfInitialise = xLAN91C111_NetworkInterfaceInitialise;
    pxInterface->pfOutput = xLAN91C111_NetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = xLAN91C111_GetPhyLinkStatus;

    FreeRTOS_AddNetworkInterface( pxInterface );

    return pxInterface;
}
/*-----------------------------------------------------------*/
