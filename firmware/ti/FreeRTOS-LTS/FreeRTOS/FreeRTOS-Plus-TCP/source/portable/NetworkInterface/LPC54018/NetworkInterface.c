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

/* FreeRTOS includes. */
#include "LPC54018.h"
#include "FreeRTOS.h"
#include "list.h"

#include <stdbool.h>

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"

#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"

#include "fsl_enet.h"
#include "fsl_phy.h"

#include "fsl_enet_mdio.h"
#include "fsl_phylan8720a.h"
#include "fsl_debug_console.h"

#define PHY_ADDRESS         ( 0x00U )
/* MDIO operations. */
#define EXAMPLE_MDIO_OPS    lpc_enet_ops
/* PHY operations. */
#define EXAMPLE_PHY_OPS     phylan8720a_ops
#define ENET_RXBD_NUM       ( 4 )
#define ENET_TXBD_NUM       ( 4 )
#define ENET_RXBUFF_SIZE    ( ENET_FRAME_MAX_FRAMELEN )
#define ENET_BuffSizeAlign( n )    ENET_ALIGN( n, ENET_BUFF_ALIGNMENT )
#define ENET_ALIGN( x, align )     ( ( unsigned int ) ( ( x ) + ( ( align ) - 1 ) ) & ( unsigned int ) ( ~( unsigned int ) ( ( align ) - 1 ) ) )

#if defined( __GNUC__ )
    #ifndef __ALIGN_END
        #define __ALIGN_END    __attribute__( ( aligned( ENET_BUFF_ALIGNMENT ) ) )
    #endif
    #ifndef __ALIGN_BEGIN
        #define __ALIGN_BEGIN
    #endif
#else
    #ifndef __ALIGN_END
        #define __ALIGN_END
    #endif
    #ifndef __ALIGN_BEGIN
        #if defined( __CC_ARM ) || defined( __ARMCC_VERSION )
            #define __ALIGN_BEGIN    __attribute__( ( aligned( ENET_BUFF_ALIGNMENT ) ) )
        #elif defined( __ICCARM__ )
            #define __ALIGN_BEGIN
        #endif
    #endif
#endif /* if defined( __GNUC__ ) */

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
 * driver will filter incoming packets and only pass the stack those packets it
 * considers need processing. */
#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

#ifndef NETWORK_INTERFACE_RX_PRIORITY
    #define NETWORK_INTERFACE_RX_PRIORITY    ( configMAX_PRIORITIES - 1 )
#endif

/*******************************************************************************
 * Variables
 ******************************************************************************/
#if defined( __ICCARM__ )
    #pragma data_alignment = ENET_BUFF_ALIGNMENT
#endif
__ALIGN_BEGIN enet_rx_bd_struct_t g_rxBuffDescrip[ ENET_RXBD_NUM ] __ALIGN_END;
#if defined( __ICCARM__ )
    #pragma data_alignment = ENET_BUFF_ALIGNMENT
#endif
__ALIGN_BEGIN enet_tx_bd_struct_t g_txBuffDescrip[ ENET_TXBD_NUM ] __ALIGN_END;

enet_handle_t g_handle = { 0 };
/* The MAC address for ENET device. */
uint8_t g_macAddr[ 6 ] = { 0xde, 0xad, 0x00, 0xbe, 0xef, 0x01 };

bool g_linkStatus = false;

/*! @brief Enet PHY and MDIO interface handler. */
static mdio_handle_t mdioHandle = { .ops = &EXAMPLE_MDIO_OPS };
static phy_handle_t phyHandle = { .phyAddr = PHY_ADDRESS, .mdioHandle = &mdioHandle, .ops = &EXAMPLE_PHY_OPS };

__ALIGN_BEGIN uint32_t receiveBuffer[ ENET_RXBD_NUM ][ ENET_RXBUFF_SIZE / sizeof( uint32_t ) + 1 ] __ALIGN_END;
uint32_t rxbuffer[ ENET_RXBD_NUM ];

TaskHandle_t receiveTaskHandle;

void ENET_IntCallback( ENET_Type * base,
                       enet_handle_t * handle,
                       enet_event_t event,
                       uint8_t channel,
                       void * param )
{
    BaseType_t needsToYield = pdFALSE;

    switch( event )
    {
        case kENET_TxIntEvent:
            break;

        case kENET_RxIntEvent:
            vTaskNotifyGiveFromISR( receiveTaskHandle, &needsToYield );
            portEND_SWITCHING_ISR( needsToYield );
            break;

        default:
            break;
    }
}

static void prvProcessFrame( int length )
{
    NetworkBufferDescriptor_t * pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( length, 0 );

    if( pxBufferDescriptor != NULL )
    {
        ENET_ReadFrame( ENET, &g_handle, pxBufferDescriptor->pucEthernetBuffer, length, 0 );
        pxBufferDescriptor->xDataLength = length;

        if( ipCONSIDER_FRAME_FOR_PROCESSING( pxBufferDescriptor->pucEthernetBuffer ) == eProcessBuffer )
        {
            IPStackEvent_t xRxEvent;
            xRxEvent.eEventType = eNetworkRxEvent;
            xRxEvent.pvData = ( void * ) pxBufferDescriptor;

            if( xSendEventStructToIPTask( &xRxEvent, 0 ) == pdFALSE )
            {
                vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
                iptraceETHERNET_RX_EVENT_LOST();
                PRINTF( "RX Event Lost\n" );
            }
        }
        else
        {
            PRINTF( "RX Event not to be considered\n" );
            vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
            /* Not sure if a trace is required.  The stack did not want this message */
        }
    }
    else
    {
        PRINTF( "RX No Buffer Available\n" );
        ENET_ReadFrame( ENET, &g_handle, NULL, 0, 0 );
        /* No buffer available to receive this message */
        iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER();
    }
}

static void rx_task( void * parameter )
{
    while( pdTRUE )
    {
        if( ulTaskNotifyTake( pdTRUE, pdMS_TO_TICKS( 500 ) ) == pdFALSE ) /* no RX packets for a bit so check for a link */
        {
            PHY_GetLinkStatus( &phyHandle, &g_linkStatus );
        }
        else
        {
            BaseType_t receiving = pdTRUE;

            while( receiving == pdTRUE )
            {
                uint32_t length;
                const status_t status = ENET_GetRxFrameSize( ENET, &g_handle, &length, 0 );

                switch( status )
                {
                    case kStatus_Success: /* there is a frame.  process it */

                        if( length )
                        {
                            prvProcessFrame( length );
                        }

                        break;

                    case kStatus_ENET_RxFrameEmpty: /* Received an empty frame.  Ignore it */
                        receiving = pdFALSE;
                        break;

                    case kStatus_ENET_RxFrameError: /* Received an error frame.  Read & drop it */
                        PRINTF( "RX Receive Error\n" );
                        ENET_ReadFrame( ENET, &g_handle, NULL, 0, 0 );
                        /* Not sure if a trace is required.  The MAC had an error and needed to dump bytes */
                        break;

                    default:
                        PRINTF( "RX Receive default\n" );
                        break;
                }
            }
        }
    }
}

BaseType_t xGetPhyLinkStatus( void )
{
    return g_linkStatus ? pdTRUE : pdFALSE;
}


BaseType_t xNetworkInterfaceInitialise( void )
{
    BaseType_t returnValue = pdFAIL;
    static enum
    {
        initPhy, waitForLink, startReceiver, configurePhy
    }
    networkInitialisePhase = initPhy;

    switch( networkInitialisePhase )
    {
        default:
            networkInitialisePhase = initPhy;

        /* fall through */
        case initPhy:
           {
               phy_config_t phyConfig;
               phyConfig.phyAddr = PHY_ADDRESS;
               phyConfig.autoNeg = true;
               mdioHandle.resource.base = ENET;

               status_t status = PHY_Init( &phyHandle, &phyConfig );

               if( status == kStatus_PHY_AutoNegotiateFail )
               {
                   PRINTF( "\nPHY Auto-negotiation failed. Please check the cable connection and link partner setting.\n" );
                   break;
               }
           }

        case startReceiver:
            networkInitialisePhase = startReceiver;

            if( xTaskCreate( rx_task, "rx_task", 512, NULL, NETWORK_INTERFACE_RX_PRIORITY, &receiveTaskHandle ) != pdPASS )
            {
                PRINTF( "Network Receive Task creation failed!.\n" );
                break;
            }

        /* fall through */
        case waitForLink:
            networkInitialisePhase = waitForLink;
            {
                if( !xGetPhyLinkStatus() )
                {
                    PRINTF( "No Link\n" );
                    break;
                }
            }

        /* fall through */
        case configurePhy:
           {
               networkInitialisePhase = configurePhy;
               enet_config_t config;
               phy_speed_t speed;
               phy_duplex_t duplex;
               PHY_GetLinkSpeedDuplex( &phyHandle, &speed, &duplex );
               /* Get default configuration 100M RMII. */
               ENET_GetDefaultConfig( &config );

               /* Use the actual speed and duplex when phy success to finish the autonegotiation. */
               config.miiSpeed = ( enet_mii_speed_t ) speed;
               config.miiDuplex = ( enet_mii_duplex_t ) duplex;

               /* Initialize ENET. */
               uint32_t refClock = 50000000; /* 50MHZ for rmii reference clock. */
               ENET_Init( ENET, &config, g_macAddr, refClock );

               /* Enable the rx interrupt. */
               ENET_EnableInterrupts( ENET, ( kENET_DmaRx ) );

               /* Initialize Descriptor. */
               int bufferIndex;

               for( bufferIndex = 0; bufferIndex < ENET_RXBD_NUM; bufferIndex++ )
               {
                   rxbuffer[ bufferIndex ] = ( uint32_t ) &receiveBuffer[ bufferIndex ];
               }

               /* prepare the buffer configuration. */
               enet_buffer_config_t buffConfig[ 1 ] =
               {
                   {
                       ENET_RXBD_NUM, ENET_TXBD_NUM,
                       &g_txBuffDescrip[ 0 ], &g_txBuffDescrip[ 0 ],
                       &g_rxBuffDescrip[ 0 ], &g_rxBuffDescrip[ ENET_RXBD_NUM ],
                       &rxbuffer[ 0 ], ENET_BuffSizeAlign( ENET_RXBUFF_SIZE ),
                   }
               };
               ENET_DescriptorInit( ENET, &config, &buffConfig[ 0 ] );

               /* Create the handler. */
               ENET_CreateHandler( ENET, &g_handle, &config, &buffConfig[ 0 ], ENET_IntCallback, NULL );
               NVIC_SetPriority( 65 - 16, 4 ); /* This is a workaround and using a more robust ENET API for priority setting would be preferable . */

               /* Active TX/RX. */
               ENET_StartRxTx( ENET, 1, 1 );
           }
            returnValue = pdPASS;
            break;
    }

    return returnValue;
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t xReleaseAfterSend )
{
    BaseType_t response = pdFALSE;
    status_t status;

    if( xGetPhyLinkStatus() )
    {
        status = ENET_SendFrame( ENET, &g_handle, pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength );

        switch( status )
        {
            default: /* anything not Success will be a failure */
            case kStatus_ENET_TxFrameBusy:
                PRINTF( "TX Frame Busy\n" );
                break;

            case kStatus_Success:
                iptraceNETWORK_INTERFACE_TRANSMIT();
                response = pdTRUE;
                break;
        }
    }

    if( xReleaseAfterSend != pdFALSE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

    return response;
}

/* statically allocate the buffers */
/* allocating them as uint32_t's to force them into word alignment, a requirement of the DMA. */
__ALIGN_BEGIN static uint32_t buffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ ( ipBUFFER_PADDING + ENET_RXBUFF_SIZE ) / sizeof( uint32_t ) + 1 ] __ALIGN_END;
void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    for( int x = 0; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++ )
    {
        pxNetworkBuffers[ x ].pucEthernetBuffer = ( uint8_t * ) &buffers[ x ][ 0 ] + ipBUFFER_PADDING;
        buffers[ x ][ 0 ] = ( uint32_t ) &pxNetworkBuffers[ x ];
    }
}
