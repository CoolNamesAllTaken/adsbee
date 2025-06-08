/*
 * FreeRTOS+TCP V4.2.2
 * Copyright (C) 2023 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 */

/**
 * @file NetworkInterface.c
 * @brief Implements the Network Interface driver for the NXP MIMXRT1060 board.
 */
/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

#include "fsl_device_registers.h"
#include "fsl_debug_console.h"
#include "board.h"

#include "fsl_phy.h"

#include "fsl_phyksz8081.h"
#include "fsl_enet_mdio.h"
#include "fsl_enet.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Routing.h"
#include "FreeRTOS_ARP.h"
#include "NetworkInterface.h"

#if ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES != 1
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/* MDIO operations. */
#define EXAMPLE_MDIO_OPS      enet_ops

/* PHY operations. */
#define EXAMPLE_PHY_OPS       phyksz8081_ops

/* ENET clock frequency. */
#define EXAMPLE_CLOCK_FREQ    CLOCK_GetFreq( kCLOCK_IpgClk )


/*******************************************************************************
 * Definitions
 ******************************************************************************/
#define ENET_RING_NUM    ( 1 )

/* The length or RX buffer. */
#ifndef ENET_RXBUFF_SIZE
    #define ENET_RXBUFF_SIZE    ( ENET_FRAME_MAX_FRAMELEN )
#endif

/* ENET IRQ priority. Used in FreeRTOS. */
/* Interrupt priorities. */
#ifdef __CA7_REV
    #ifndef ENET_PRIORITY
        #define ENET_PRIORITY         ( 21U )
    #endif
    #ifndef ENET_1588_PRIORITY
        #define ENET_1588_PRIORITY    ( 20U )
    #endif
#else
    #ifndef ENET_PRIORITY
        #define ENET_PRIORITY         ( 6U )
    #endif
    #ifndef ENET_1588_PRIORITY
        #define ENET_1588_PRIORITY    ( 5U )
    #endif
#endif /* ifdef __CA7_REV */

/* The number of ENET buffers needed to receive frame of maximum length. */
#define MAX_BUFFERS_PER_FRAME \
    ( ( ENET_FRAME_MAX_FRAMELEN / ENET_RXBUFF_SIZE ) + ( ( ENET_FRAME_MAX_FRAMELEN % ENET_RXBUFF_SIZE == 0 ) ? 0 : 1 ) )

/* The length or TX buffer. */
#ifndef ENET_TXBUFF_SIZE
    #define ENET_TXBUFF_SIZE    ( ENET_FRAME_MAX_FRAMELEN )
#endif

/* The number of buffer descriptors in ENET RX ring. */
#ifndef ENET_RXBD_NUM
    #define ENET_RXBD_NUM    ( 5 )
#endif

/* Ring should be able to receive at least 1 frame with maximum length. */
#if ENET_RXBD_NUM < MAX_BUFFERS_PER_FRAME
    #error "ENET_RXBD_NUM < MAX_BUFFERS_PER_FRAME"
#endif

/* The number of RX buffers. ENET_RXBD_NUM is always held by ENET driver. */
#ifndef ENET_RXBUFF_NUM
    #define ENET_RXBUFF_NUM    ( ENET_RXBD_NUM * 2 )
#endif

/* At least ENET_RXBD_NUM number of buffers is always held by ENET driver
 * for RX. */
#if ENET_RXBUFF_NUM < ( ENET_RXBD_NUM + MAX_BUFFERS_PER_FRAME )
    #error "ENET_RXBUFF_NUM < (ENET_RXBD_NUM + MAX_BUFFERS_PER_FRAME)"
#endif

/* The number of buffer descriptors in ENET TX ring. */
#ifndef ENET_TXBD_NUM
    #define ENET_TXBD_NUM    ( 3 )
#endif

/* Set the timeout values such that the total timeout adds up to 4000ms. */
#define MAX_AUTONEG_FAILURE_COUNT    ( 40 )
#define SINGLE_ITERATION_TIMEOUT     ( 100 )

#if defined( FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL ) && FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL
    #if defined( FSL_FEATURE_L2CACHE_LINESIZE_BYTE ) && \
    ( ( !defined( FSL_SDK_DISBLE_L2CACHE_PRESENT ) ) || ( FSL_SDK_DISBLE_L2CACHE_PRESENT == 0 ) )
        #if defined( FSL_FEATURE_L1DCACHE_LINESIZE_BYTE )
            #define FSL_CACHE_LINESIZE_MAX     MAX( FSL_FEATURE_L1DCACHE_LINESIZE_BYTE, FSL_FEATURE_L2CACHE_LINESIZE_BYTE )
            #define FSL_ENET_BUFF_ALIGNMENT    MAX( ENET_BUFF_ALIGNMENT, FSL_CACHE_LINESIZE_MAX )
        #else
            #define FSL_ENET_BUFF_ALIGNMENT    MAX( ENET_BUFF_ALIGNMENT, FSL_FEATURE_L2CACHE_LINESIZE_BYTE )
        #endif
    #elif defined( FSL_FEATURE_L1DCACHE_LINESIZE_BYTE )
        #define FSL_ENET_BUFF_ALIGNMENT        MAX( ENET_BUFF_ALIGNMENT, FSL_FEATURE_L1DCACHE_LINESIZE_BYTE )
    #else
        #define FSL_ENET_BUFF_ALIGNMENT        ENET_BUFF_ALIGNMENT
    #endif /* if defined( FSL_FEATURE_L2CACHE_LINESIZE_BYTE ) && ( ( !defined( FSL_SDK_DISBLE_L2CACHE_PRESENT ) ) || ( FSL_SDK_DISBLE_L2CACHE_PRESENT == 0 ) ) */
#else /* if defined( FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL ) && FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL */
    #define FSL_ENET_BUFF_ALIGNMENT            ENET_BUFF_ALIGNMENT
#endif /* if defined( FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL ) && FSL_SDK_ENABLE_DRIVER_CACHE_CONTROL */

/* A bigger value is chosen so that the previous notification values are
 * not interfering with the driver ready notifications. */
#define DRIVER_READY    ( 0x40 )
#define DRIVER_FATAL    ( DRIVER_READY << 1 )

#if defined( ENET_ENHANCEDBUFFERDESCRIPTOR_MODE )
    #error "ENET_ENHANCEDBUFFERDESCRIPTOR_MODE is not supported by this driver"
#endif

typedef uint8_t   rx_buffer_t[ SDK_SIZEALIGN( ENET_RXBUFF_SIZE, FSL_ENET_BUFF_ALIGNMENT ) ];
typedef uint8_t   tx_buffer_t[ SDK_SIZEALIGN( ENET_TXBUFF_SIZE, FSL_ENET_BUFF_ALIGNMENT ) ];

/**
 * @brief Used to wrap received data a buffer to be passed into the stack.
 */
typedef struct rx_pbuf_wrapper
{
    void * buffer;             /*!< Original buffer wrapped. */
    volatile bool buffer_used; /*!< Wrapped buffer is used by ENET or FreeRTOS+TCP. */
} rx_pbuf_wrapper_t;

/**
 * Helper structure to hold private data used to operate your Ethernet interface.
 */
struct ethernetif
{
    ENET_Type * base;
    enet_handle_t handle;
    enet_rx_bd_struct_t * RxBuffDescrip;
    enet_tx_bd_struct_t * TxBuffDescrip;
    rx_buffer_t * RxDataBuff;
    tx_buffer_t * TxDataBuff;
    rx_pbuf_wrapper_t RxPbufs[ ENET_RXBUFF_NUM ];
};

typedef enum xEMAC_STATE
{
    xEMAC_SetupPHY,
    xEMAC_WaitPHY,
    xEMAC_Init,
    xEMAC_Ready,
} EMACState_t;

static EMACState_t eEMACState = xEMAC_SetupPHY;

static mdio_handle_t mdioHandle = { .ops = &EXAMPLE_MDIO_OPS };

static phy_handle_t phyHandle = { .phyAddr = 0x00, .mdioHandle = &mdioHandle, .ops = &EXAMPLE_PHY_OPS };

/**
 * The task-handle for deferred interrupt handler task that processes
 * incoming packets.
 */
static TaskHandle_t receiveTaskHandle = NULL;

static struct ethernetif EthernetInterface1;
static struct ethernetif * ethernetifLocal = &EthernetInterface1;

static bool bGlobalLinkStatus = false;

static NetworkInterface_t * pxMyInterface = NULL;

/*-----------------------------------------------------------*/

AT_NONCACHEABLE_SECTION_ALIGN( static enet_rx_bd_struct_t rxBuffDescrip_0[ ENET_RXBD_NUM ], FSL_ENET_BUFF_ALIGNMENT );
AT_NONCACHEABLE_SECTION_ALIGN( static enet_tx_bd_struct_t txBuffDescrip_0[ ENET_TXBD_NUM ], FSL_ENET_BUFF_ALIGNMENT );
SDK_ALIGN( static rx_buffer_t rxDataBuff_0[ ENET_RXBUFF_NUM ], FSL_ENET_BUFF_ALIGNMENT );
SDK_ALIGN( static tx_buffer_t txDataBuff_0[ ENET_TXBD_NUM ], FSL_ENET_BUFF_ALIGNMENT );

/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*------------ PHY configuration parameters. ----------------*/
static phy_config_t xConfig =
{
    .autoNeg   = pdTRUE,                  /* Allow auto-negotiation. */
    .duplex    = kPHY_FullDuplex,         /* Use full duplex mode. In case
                                           * auto-negotiation is turned on,
                                           * this is not used. */
    .phyAddr   = BOARD_ENET0_PHY_ADDRESS, /* The PHY address. */
    .speed     = kPHY_Speed100M,          /* Use 100 Mbps configuration (maximum possible
                                           * for this PHY). In case auto-negotiation is
                                           * turned on, this is not used. */
    .enableEEE = pdFALSE                  /* Disable the energy efficient PHY. */
};

/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/

static void prvEMACHandlerTask( void * pvParameters );

static void ethernet_callback( ENET_Type * base,
                               enet_handle_t * handle,
                               enet_event_t event,
                               enet_frame_info_t * frameInfo,
                               void * userData );

static void prvProcessFrame( int length );

static status_t xSetupPHY( phy_config_t * pxConfig );

static status_t xWaitPHY( phy_config_t xConfig );

static status_t xEMACInit( phy_speed_t speed,
                           phy_duplex_t duplex );

static BaseType_t prvNXP1060_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface );

static BaseType_t prvNXP1060_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                     NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                     BaseType_t xReleaseAfterSend );

static BaseType_t prvNXP1060_GetPhyLinkStatus( NetworkInterface_t * pxInterface );

NetworkInterface_t * pxNXP1060_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                        NetworkInterface_t * pxInterface );
/*-----------------------------------------------------------*/

#if ( ipconfigIPv4_BACKWARD_COMPATIBLE != 0 )

/* Do not call the following function directly. It is there for downward compatibility.
 * The function FreeRTOS_IPInit() will call it to initialice the interface and end-point
 * objects.  See the description in FreeRTOS_Routing.h. */
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface )
    {
        return pxNXP1060_FillInterfaceDescriptor( xEMACIndex, pxInterface );
    }

#endif /* ( ipconfigIPv4_BACKWARD_COMPATIBLE != 0 ) */
/*-----------------------------------------------------------*/

NetworkInterface_t * pxNXP1060_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                        NetworkInterface_t * pxInterface )
{
    static char pcName[ 10 ];

    /* This function pxNXP1060_FillInterfaceDescriptor() adds a network-interface.
     * Make sure that the object pointed to by 'pxInterface'
     * is declared static or global, and that it will remain to exist. */

    snprintf( pcName, sizeof( pcName ), "NXP1060%ld", xEMACIndex );

    memset( pxInterface, '\0', sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;                    /* Just for logging, debugging. */
    pxInterface->pvArgument = ( void * ) xEMACIndex; /* Has only meaning for the driver functions. */
    pxInterface->pfInitialise = prvNXP1060_NetworkInterfaceInitialise;
    pxInterface->pfOutput = prvNXP1060_NetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = prvNXP1060_GetPhyLinkStatus;

    FreeRTOS_AddNetworkInterface( pxInterface );
    pxMyInterface = pxInterface;

    return pxInterface;
}
/*-----------------------------------------------------------*/

static BaseType_t prvNXP1060_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    status_t xStatus;
    BaseType_t xResult = pdFAIL;
    phy_speed_t speed;
    phy_duplex_t duplex;
    BaseType_t xTaskCreated;
    static BaseType_t xFirstCall = pdTRUE;

    configASSERT( FSL_FEATURE_ENET_QUEUE == 1 );

    switch( eEMACState )
    {
        case xEMAC_SetupPHY:
            xStatus = xSetupPHY( &xConfig );

            if( xStatus != kStatus_Success )
            {
                break;
            }
            else
            {
                eEMACState = xEMAC_WaitPHY;
            }

        /* Fall through. */
        case xEMAC_WaitPHY:
            FreeRTOS_printf( ( "Configuration successful. Waiting for link to go up"
                               " and auto-negotiation to complete." ) );

            xStatus = xWaitPHY( xConfig );

            if( xStatus == kStatus_Success )
            {
                xStatus = PHY_GetLinkSpeedDuplex( &phyHandle, &speed, &duplex );
            }

            if( xStatus != kStatus_Success )
            {
                if( !xFirstCall )
                {
                    xTaskNotify( receiveTaskHandle, DRIVER_READY, eSetValueWithOverwrite );
                }

                break;
            }
            else
            {
                eEMACState = xEMAC_Init;
            }

        /* Fall through. */
        case xEMAC_Init:
            xStatus = xEMACInit( speed, duplex );

            if( ( xFirstCall == pdTRUE ) || ( receiveTaskHandle == NULL ) )
            {
                if( xStatus == kStatus_Success )
                {
                    /* The link is now up. */
                    bGlobalLinkStatus = true;

                    /* The handler task is created at the highest possible priority to
                     * ensure the interrupt handler can return directly to it. */
                    xTaskCreated = xTaskCreate( prvEMACHandlerTask,
                                                "EMAC-Handler",
                                                configMINIMAL_STACK_SIZE * 3,
                                                pxInterface,
                                                configMAX_PRIORITIES - 1,
                                                &receiveTaskHandle );

                    if( ( receiveTaskHandle == NULL ) || ( xTaskCreated != pdPASS ) )
                    {
                        FreeRTOS_printf( ( "Failed to create the handler task." ) );
                        break;
                    }

                    /* Enable the interrupt and set its priority to the minimum
                     * interrupt priority.  */
                    NVIC_SetPriority( ENET_IRQn, ENET_PRIORITY );
                    NVIC_EnableIRQ( ENET_IRQn );

                    eEMACState = xEMAC_Ready;

                    /* After this, the task should not be created. */
                    xFirstCall = pdFALSE;
                }
                else
                {
                    break;
                }
            }
            else
            {
                eEMACState = xEMAC_Ready;
            }

        /* Fall through. */
        case xEMAC_Ready:
            FreeRTOS_printf( ( "Driver ready for use." ) );

            /* Kick the task once the driver is ready. */
            if( receiveTaskHandle != NULL )
            {
                xTaskNotify( receiveTaskHandle, DRIVER_READY, eSetValueWithOverwrite );
            }

            xResult = pdPASS;

            break;
    }

    return xResult;
}
/*-----------------------------------------------------------*/

static BaseType_t prvNXP1060_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                     NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                     BaseType_t xReleaseAfterSend )
{
    status_t result;
    BaseType_t xReturn = pdFAIL;

    /* Avoid warning about unused parameter. */
    ( void ) pxInterface;

    do
    {
        if( bGlobalLinkStatus == true )
        {
            /* ENET_SendFrame copies the data before sending it. Therefore, the network buffer can
             * be released without worrying about the buffer memory being used by the ENET_SendFrame
             * function. */
            result = ENET_SendFrame( ethernetifLocal->base,
                                     &ethernetifLocal->handle,
                                     pxNetworkBuffer->pucEthernetBuffer,
                                     pxNetworkBuffer->xDataLength,
                                     0,
                                     false,
                                     NULL );

            switch( result )
            {
                case kStatus_ENET_TxFrameBusy:
                    FreeRTOS_printf( ( "Failed to send the frame - driver busy!" ) );
                    break;

                case kStatus_Success:
                    iptraceNETWORK_INTERFACE_TRANSMIT();
                    xReturn = pdPASS;
                    break;
            }
        }
    } while( ipFALSE_BOOL );

    if( xReleaseAfterSend == pdTRUE )
    {
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvNXP1060_GetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    BaseType_t xReturn = pdFALSE;

    /* Avoid warning about unused parameter. */
    ( void ) pxInterface;

    if( bGlobalLinkStatus == true )
    {
        xReturn = pdTRUE;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static void prvEMACHandlerTask( void * parameter )
{
    bool bLinkUp = false;
    status_t readStatus;

    /* Wait for the driver to finish starting. */
    ( void ) ulTaskNotifyTake( pdTRUE, portMAX_DELAY );

    while( pdTRUE )
    {
        if( ulTaskNotifyTake( pdTRUE, pdMS_TO_TICKS( 500 ) ) == pdFALSE )
        {
            /* No RX packets for a bit so check for a link. */
            const IPStackEvent_t xNetworkEventDown = { .eEventType = eNetworkDownEvent, .pvData = parameter };

            do
            {
                readStatus = PHY_GetLinkStatus( &phyHandle, &bLinkUp );

                if( readStatus == kStatus_Success )
                {
                    if( bLinkUp == pdFALSE )
                    {
                        /* The link is down. */
                        bGlobalLinkStatus = false;
                        /* We need to setup the PHY again. */
                        eEMACState = xEMAC_WaitPHY;

                        FreeRTOS_printf( ( "Link down!" ) );

                        xSendEventStructToIPTask( &xNetworkEventDown, 0U );

                        /* Wait for the driver to finish initialization. */
                        uint32_t ulNotificationValue;

                        do
                        {
                            ulNotificationValue = ulTaskNotifyTake( pdTRUE, portMAX_DELAY );
                        } while( !( ulNotificationValue & DRIVER_READY ) );
                    }
                    else
                    {
                        /* The link is still up. */
                        bGlobalLinkStatus = true;
                    }
                }
            } while( bGlobalLinkStatus == false );
        }
        else
        {
            BaseType_t receiving = pdTRUE;

            /* A packet was received, the link must be up. */
            bGlobalLinkStatus = true;

            while( receiving == pdTRUE )
            {
                uint32_t length;
                const status_t status = ENET_GetRxFrameSize( &( ethernetifLocal->handle ), &length, 0 );

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
                        FreeRTOS_printf( ( "RX Receive Error\n" ) );
                        ENET_ReadFrame( ethernetifLocal->base, &( ethernetifLocal->handle ), NULL, 0, 0, NULL );
                        /* Not sure if a trace is required.  The MAC had an error and needed to dump bytes */
                        break;

                    default:
                        FreeRTOS_printf( ( "RX Receive default" ) );
                        break;
                }
            }
        }
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Callback for ENET interrupts. We have only enabled the Ethernet receive interrupts
 * in the case of this driver.
 */
static void ethernet_callback( ENET_Type * base,
                               enet_handle_t * handle,
                               enet_event_t event,
                               enet_frame_info_t * frameInfo,
                               void * userData )
{
    BaseType_t needsToYield = pdFALSE;

    ( void ) base;
    ( void ) handle;
    ( void ) frameInfo;
    ( void ) userData;

    switch( event )
    {
        case kENET_RxEvent:
            vTaskNotifyGiveFromISR( receiveTaskHandle, &needsToYield );
            portEND_SWITCHING_ISR( needsToYield );
            break;

        default:
            FreeRTOS_printf( ( "Unknown interrupt callback %u!", event ) );
            break;
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief This function verifies that the incoming frame needs processing.
 *        If the frame is deemed to be appropriate, then the frame is sent to the
 *        TCP stack for further processing.
 * @param[in] length: The length of the incoming frame. This length should be read
 *                    using a call to ENET_GetRxFrameSize.
 */
static void prvProcessFrame( int length )
{
    NetworkBufferDescriptor_t * pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( length, 0 );
    BaseType_t xRelease = pdFALSE;

    if( pxBufferDescriptor != NULL )
    {
        ENET_ReadFrame( ethernetifLocal->base, &( ethernetifLocal->handle ), pxBufferDescriptor->pucEthernetBuffer, length, 0, NULL );
        pxBufferDescriptor->xDataLength = length;
        pxBufferDescriptor->pxInterface = pxMyInterface;
        pxBufferDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint( pxMyInterface, pxBufferDescriptor->pucEthernetBuffer );

        if( pxBufferDescriptor->pxEndPoint == NULL )
        {
            /* Endpoint not found, drop the packet. */
            xRelease = pdTRUE;
        }
        else
        {
            if( ipCONSIDER_FRAME_FOR_PROCESSING( pxBufferDescriptor->pucEthernetBuffer ) == eProcessBuffer )
            {
                IPStackEvent_t xRxEvent;
                xRxEvent.eEventType = eNetworkRxEvent;
                xRxEvent.pvData = ( void * ) pxBufferDescriptor;

                if( xSendEventStructToIPTask( &xRxEvent, 0 ) == pdFALSE )
                {
                    xRelease = pdTRUE;
                    iptraceETHERNET_RX_EVENT_LOST();
                    FreeRTOS_printf( ( "RX Event Lost\n" ) );
                }
            }
            else
            {
                #if ( ( ipconfigHAS_DEBUG_PRINTF == 1 ) && defined( FreeRTOS_debug_printf ) )
                    const EthernetHeader_t * pxEthernetHeader;
                    char ucSource[ 18 ];
                    char ucDestination[ 18 ];

                    pxEthernetHeader = ( ( const EthernetHeader_t * ) pxBufferDescriptor->pucEthernetBuffer );

                    FreeRTOS_EUI48_ntop( pxEthernetHeader->xSourceAddress.ucBytes, ucSource, 'A', ':' );
                    FreeRTOS_EUI48_ntop( pxEthernetHeader->xDestinationAddress.ucBytes, ucDestination, 'A', ':' );

                    FreeRTOS_debug_printf( ( "Invalid target MAC: dropping frame from: %s to: %s", ucSource, ucDestination ) );
                #endif /* if ( ( ipconfigHAS_DEBUG_PRINTF == 1 ) && defined( FreeRTOS_debug_printf ) ) */
                xRelease = pdTRUE;
                /* Not sure if a trace is required.  The stack did not want this message */
            }
        }

        if( xRelease != pdFALSE )
        {
            vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
        }
    }
    else
    {
        #if ( ( ipconfigHAS_DEBUG_PRINTF == 1 ) && defined( FreeRTOS_debug_printf ) )
            FreeRTOS_debug_printf( ( "No Buffer Available: dropping incoming frame!!" ) );
        #endif
        ENET_ReadFrame( ENET, &( ethernetifLocal->handle ), NULL, length, 0, NULL );

        /* No buffer available to receive this message */
        iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER();
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief This function is used to setup the PHY in auto-negotiation mode.
 *
 * @param[out] pxConfig: the configuration parameters.
 *
 * @return kStatus_Success if the PHY was initialized; error code otherwise.
 */
static status_t xSetupPHY( phy_config_t * pxConfig )
{
    status_t xStatus;

    /* Set the clock frequency. MDIO handle is pointed to by the PHY handle. */
    mdioHandle.resource.csrClock_Hz = EXAMPLE_CLOCK_FREQ;
    mdioHandle.resource.base = ( void * ) ENET_BASE;

    FreeRTOS_printf( ( "Starting PHY initialization." ) );

    xStatus = PHY_Init( &phyHandle, pxConfig );

    if( xStatus != kStatus_Success )
    {
        FreeRTOS_printf( ( "Failed to initialize the PHY." ) );
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

/**
 * @brief This function is used wait on the auto-negotiation completion.
 *
 * @param[in] xConfig: the configuration parameters.
 *
 * @return kStatus_Success if the PHY was initialized; error code otherwise.
 */
static status_t xWaitPHY( phy_config_t xConfig )
{
    status_t xStatus;
    bool bLinkUp;
    bool bAutoNegotiationComplete;
    uint8_t ucCounter = 0;

    do
    {
        xStatus = PHY_GetLinkStatus( &phyHandle, &bLinkUp );

        if( bLinkUp == true )
        {
            break;
        }

        /* Try for only a limited number of times. */
        if( ucCounter++ > MAX_AUTONEG_FAILURE_COUNT )
        {
            break;
        }

        vTaskDelay( pdMS_TO_TICKS( SINGLE_ITERATION_TIMEOUT ) );
    }
    while( xStatus == kStatus_Success );

    if( bLinkUp == false )
    {
        FreeRTOS_printf( ( "Failed to get the link up." ) );
        xStatus = kStatus_Fail;
    }
    else
    {
        FreeRTOS_printf( ( "Link up." ) );
    }

    if( ( xStatus == kStatus_Success ) &&
        ( bLinkUp == true ) &&
        ( xConfig.autoNeg == true ) )
    {
        /* Reset the counter for next use. */
        ucCounter = 0;

        FreeRTOS_printf( ( "Waiting for auto-negotiation to complete." ) );

        do
        {
            xStatus = PHY_GetAutoNegotiationStatus( &phyHandle, &bAutoNegotiationComplete );

            if( bAutoNegotiationComplete == true )
            {
                break;
            }

            /* Try for only a limited number of times. */
            if( ucCounter++ > MAX_AUTONEG_FAILURE_COUNT )
            {
                break;
            }

            vTaskDelay( pdMS_TO_TICKS( SINGLE_ITERATION_TIMEOUT ) );
        }
        while( xStatus == kStatus_Success );

        if( bAutoNegotiationComplete == false )
        {
            FreeRTOS_printf( ( "Failed to complete auto-negotiation." ) );
            xStatus = kStatus_Fail;
        }
        else
        {
            /* Success in auto-negotiation and the link is up. */
            FreeRTOS_printf( ( "Auto-negotiation complete." ) );
        }
    }

    return xStatus;
}
/*-----------------------------------------------------------*/

/**
 * @brief This function is used to initialize the ENET module. It initializes the network buffers
 *        and buffer descriptors.
 *
 * @param[in] speed: The speed of communication (either set by auto-negotiation or the default
 *                   value).
 * @param[in] duplex: The nature of the channel. This must be set to kPHY_FullDuplex by
 *                   auto-negotiation.
 *
 * @return kStatus_Success if the ENET module was initialized; error code otherwise.
 */
static status_t xEMACInit( phy_speed_t speed,
                           phy_duplex_t duplex )
{
    enet_config_t config;
    uint32_t sysClock;
    enet_buffer_config_t buffCfg[ ENET_RING_NUM ];
    status_t xStatus;
    uint32_t instance;
    static ENET_Type * const enetBases[] = ENET_BASE_PTRS;
    static const IRQn_Type enetTxIrqId[] = ENET_Transmit_IRQS;
    /*! @brief Pointers to enet receive IRQ number for each instance. */
    static const IRQn_Type enetRxIrqId[] = ENET_Receive_IRQS;
    int i;
    NetworkEndPoint_t * pxEndPoint;

    ethernetifLocal->RxBuffDescrip = &( rxBuffDescrip_0[ 0 ] );
    ethernetifLocal->TxBuffDescrip = &( txBuffDescrip_0[ 0 ] );
    ethernetifLocal->RxDataBuff = &( rxDataBuff_0[ 0 ] );
    ethernetifLocal->TxDataBuff = &( txDataBuff_0[ 0 ] );
    ethernetifLocal->base = ( void * ) ENET_BASE;

    /* prepare the buffer configuration. */
    buffCfg[ 0 ].rxBdNumber = ENET_RXBD_NUM;                  /* Number of RX buffer descriptors. */
    buffCfg[ 0 ].txBdNumber = ENET_TXBD_NUM;                  /* Transmit buffer descriptor number. */
    buffCfg[ 0 ].rxBuffSizeAlign = sizeof( rx_buffer_t );     /* Aligned receive data buffer size. */
    buffCfg[ 0 ].txBuffSizeAlign = sizeof( tx_buffer_t );     /* Aligned transmit data buffer size. */
    buffCfg[ 0 ].rxBdStartAddrAlign =
        &( rxBuffDescrip_0[ 0 ] );                            /* Aligned receive buffer descriptor start address. */
    buffCfg[ 0 ].txBdStartAddrAlign =
        &( txBuffDescrip_0[ 0 ] );                            /* Aligned transmit buffer descriptor start address. */
    buffCfg[ 0 ].rxBufferAlign =
        &( rxDataBuff_0[ 0 ][ 0 ] );                          /* Receive data buffer start address. */
    buffCfg[ 0 ].txBufferAlign = &( txDataBuff_0[ 0 ][ 0 ] ); /* Transmit data buffer start address. */
    buffCfg[ 0 ].txFrameInfo = NULL;                          /* Transmit frame information start address. Set only if using zero-copy transmit. */
    buffCfg[ 0 ].rxMaintainEnable = true;                     /* Receive buffer cache maintain. */
    buffCfg[ 0 ].txMaintainEnable = true;                     /* Transmit buffer cache maintain. */

    sysClock = phyHandle.mdioHandle->resource.csrClock_Hz;

    ENET_GetDefaultConfig( &config );

    config.ringNum = ENET_RING_NUM;
    config.rxBuffAlloc = NULL;
    config.rxBuffFree = NULL;
    config.userData = ethernetifLocal;
    config.miiSpeed = ( enet_mii_speed_t ) speed;
    config.miiDuplex = ( enet_mii_duplex_t ) duplex;

    /* Only get interrupt for incoming messages. */
    config.interrupt = kENET_RxFrameInterrupt;
    config.callback = ethernet_callback;

    for( instance = 0; instance < ARRAY_SIZE( enetBases ); instance++ )
    {
        if( enetBases[ instance ] == ethernetifLocal->base )
        {
            NVIC_SetPriority( enetRxIrqId[ instance ], ENET_PRIORITY );
            NVIC_SetPriority( enetTxIrqId[ instance ], ENET_PRIORITY );
            break;
        }
    }

    configASSERT( instance != ARRAY_SIZE( enetBases ) );

    if( instance == ARRAY_SIZE( enetBases ) )
    {
        xStatus = kStatus_Fail;
    }
    else
    {
        pxEndPoint = FreeRTOS_FirstEndPoint( pxMyInterface );
        configASSERT( pxEndPoint != NULL );

        for( i = 0; i < ENET_RXBUFF_NUM; i++ )
        {
            ethernetifLocal->RxPbufs[ i ].buffer = &( ethernetifLocal->RxDataBuff[ i ][ 0 ] );
            ethernetifLocal->RxPbufs[ i ].buffer_used = false;
        }

        /* Initialize the ENET module. */
        xStatus = ENET_Init( ethernetifLocal->base,
                             &ethernetifLocal->handle,
                             &config,
                             &buffCfg[ 0 ],
                             pxEndPoint->xMACAddress.ucBytes,
                             sysClock );

        #if ( ipconfigUSE_LLMNR == 1 )
            ENET_AddMulticastGroup( ethernetifLocal->base, ( uint8_t * ) xLLMNR_MacAddress.ucBytes );
        #endif /* ipconfigUSE_LLMNR */

        #if ( ipconfigUSE_IPv6 != 0 )
            #if ( ipconfigUSE_LLMNR == 1 )
                ENET_AddMulticastGroup( ethernetifLocal->base, ( uint8_t * ) xLLMNR_MacAddressIPv6.ucBytes );
            #endif /* ipconfigUSE_LLMNR */

            for( pxEndPoint = FreeRTOS_FirstEndPoint( pxMyInterface );
                 pxEndPoint != NULL;
                 pxEndPoint = FreeRTOS_NextEndPoint( pxMyInterface, pxEndPoint ) )
            {
                if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
                {
                    /* Allow traffic from IPv6 solicited-node multicast MAC address for
                     * each endpoint */
                    uint8_t ucMACAddress[ 6 ] = { 0x33, 0x33, 0xff, 0, 0, 0 };

                    ucMACAddress[ 3 ] = pxEndPoint->ipv6_settings.xIPAddress.ucBytes[ 13 ];
                    ucMACAddress[ 4 ] = pxEndPoint->ipv6_settings.xIPAddress.ucBytes[ 14 ];
                    ucMACAddress[ 5 ] = pxEndPoint->ipv6_settings.xIPAddress.ucBytes[ 15 ];
                    ENET_AddMulticastGroup( ethernetifLocal->base, ucMACAddress );
                }
            }
        #endif /* ( ipconfigUSE_IPv6 != 0 ) */

        if( xStatus == kStatus_Success )
        {
            FreeRTOS_printf( ( "ENET initialized." ) );
            ENET_ActiveRead( ethernetifLocal->base );
        }
        else
        {
            FreeRTOS_printf( ( "Failed to initialize ENET." ) );
        }
    }

    return xStatus;
}
/*-----------------------------------------------------------*/
