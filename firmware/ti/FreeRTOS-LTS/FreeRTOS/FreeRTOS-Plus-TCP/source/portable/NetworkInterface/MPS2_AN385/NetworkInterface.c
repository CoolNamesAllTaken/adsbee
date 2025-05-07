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

/* PHY includes. */
#include "SMM_MPS2.h"
#include "ether_lan9118/smsc9220_eth_drv.h"
#include "ether_lan9118/smsc9220_emac_config.h"

/* Sets the size of the stack (in words, not bytes) of the task that reads bytes
 * from the network. */
#ifndef nwRX_TASK_STACK_SIZE
    #define nwRX_TASK_STACK_SIZE    ( configMINIMAL_STACK_SIZE * 2 )
#endif

#ifndef nwETHERNET_RX_HANDLER_TASK_PRIORITY
    #define nwETHERNET_RX_HANDLER_TASK_PRIORITY    ( configMAX_PRIORITIES - 3 )
#endif

/* The number of attempts to get a successful call to smsc9220_send_by_chunks()
 * when transmitting a packet before giving up. */
#define niMAX_TX_ATTEMPTS    ( 5 )

/* Address of ISER and ICER registers in the Cortex-M NVIC. */
#define nwNVIC_ISER          ( *( ( volatile uint32_t * ) 0xE000E100UL ) )
#define nwNVIC_ICER          ( *( ( volatile uint32_t * ) 0xE000E180UL ) )

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

static void prvWait_ms( uint32_t ulSleep_ms );
static void prvSetMACAddress( void );

/*-----------------------------------------------------------*/

/*
 * A pointer to the network interface is needed later when receiving packets.
 */
static NetworkInterface_t * pxMyInterface;

static BaseType_t xMPS2_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface );
static BaseType_t xMPS2_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t bReleaseAfterSend );
static BaseType_t xMPS2_GetPhyLinkStatus( NetworkInterface_t * pxInterface );

NetworkInterface_t * pxMPS2_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                     NetworkInterface_t * pxInterface );

/*-----------------------------------------------------------*/

static const struct smsc9220_eth_dev_cfg_t SMSC9220_ETH_DEV_CFG =
{
    .base = SMSC9220_BASE
};

static struct smsc9220_eth_dev_data_t SMSC9220_ETH_DEV_DATA =
{
    .state = 0
};

static const struct smsc9220_eth_dev_t SMSC9220_ETH_DEV =
{
    &( SMSC9220_ETH_DEV_CFG ),
    &( SMSC9220_ETH_DEV_DATA )
};

static TaskHandle_t xRxTaskHandle = NULL;

/*-----------------------------------------------------------*/

static void prvWait_ms( uint32_t ulSleep_ms )
{
    vTaskDelay( pdMS_TO_TICKS( ulSleep_ms ) );
}
/*-----------------------------------------------------------*/

static void prvSetMACAddress( void )
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    uint32_t ucMACLow = 0;
    uint32_t ucMACHigh = 0;

    /* Using local variables to make sure the right alignment is used.  The MAC
     * address is 6 bytes, hence the copy of 4 bytes followed by 2 bytes. */
    memcpy( ( void * ) &ucMACLow, ( void * ) pxMyInterface->pxEndPoint->xMACAddress.ucBytes, 4 );
    memcpy( ( void * ) &ucMACHigh, ( void * ) ( pxMyInterface->pxEndPoint->xMACAddress.ucBytes + 4 ), 2 );

    if( smsc9220_mac_regwrite( dev, SMSC9220_MAC_REG_OFFSET_ADDRL, ucMACLow ) != 0 )
    {
        smsc9220_mac_regwrite( dev, SMSC9220_MAC_REG_OFFSET_ADDRH, ucMACHigh );
    }
}
/*-----------------------------------------------------------*/

static void prvRxTask( void * pvParameters )
{
    const TickType_t xBlockTime = pdMS_TO_TICKS( 1500UL );
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
    NetworkBufferDescriptor_t * pxNetworkBuffer = NULL;
    uint32_t ulDataRead;

    ( void ) pvParameters;

    for( ; ; )
    {
        /* Wait for the Ethernet ISR to receive a packet. */
        ulTaskNotifyTake( pdFALSE, xBlockTime );

        while( ( ulDataRead = prvLowLevelInput( &pxNetworkBuffer ) ) != 0UL )
        {
            xRxEvent.pvData = ( void * ) pxNetworkBuffer;

            pxNetworkBuffer->pxInterface = pxMyInterface;
            pxNetworkBuffer->pxEndPoint = FreeRTOS_MatchingEndpoint( pxMyInterface, pxNetworkBuffer->pucEthernetBuffer );
            pxNetworkBuffer->pxEndPoint = pxNetworkEndPoints; /*temporary change for single end point */

            if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0 ) == pdFAIL )
            {
                vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
            }
        }

        smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL ); /*_RB_ Can this move up. */
    }
}
/*-----------------------------------------------------------*/

static uint32_t prvLowLevelInput( NetworkBufferDescriptor_t ** pxNetworkBuffer )
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    const TickType_t xDescriptorWaitTime = pdMS_TO_TICKS( 250UL );
    uint32_t ulMessageLength = 0, ulReceivedBytes = 0;

    ulMessageLength = smsc9220_peek_next_packet_size( dev );

    if( ulMessageLength != 0 )
    {
        *pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( ulMessageLength,
                                                             xDescriptorWaitTime );

        if( *pxNetworkBuffer != NULL )
        {
            ( *pxNetworkBuffer )->xDataLength = ulMessageLength;

            ulReceivedBytes = smsc9220_receive_by_chunks( dev,
                                                          ( char * ) ( ( *pxNetworkBuffer )->pucEthernetBuffer ),
                                                          ulMessageLength ); /* not used */
            ( *pxNetworkBuffer )->xDataLength = ulReceivedBytes;
        }
        else
        {
            FreeRTOS_printf( ( "pxNetworkBuffer = NULL\n" ) );
        }
    }

    return ulReceivedBytes;
}
/*-----------------------------------------------------------*/

void EthernetISR( void )
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    uint32_t ulIRQStatus;
    const uint32_t ulRXFifoStatusIRQBit = 1UL << SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL;
    extern uint32_t get_irq_status( const struct smsc9220_eth_dev_t * dev );

    /* Should not enable this interrupt until after the handler task has been
     * created. */
    configASSERT( xRxTaskHandle );

    ulIRQStatus = get_irq_status( dev );

    if( ( ulIRQStatus & ulRXFifoStatusIRQBit ) != 0 )
    {
        /* Unblock the task that will process this interrupt. */
        vTaskNotifyGiveFromISR( xRxTaskHandle, &xHigherPriorityTaskWoken );
        smsc9220_clear_interrupt( dev, SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL );

        /* Re-enabled by the task that handles the incoming packet. */ /*_RB_ Is this necessary? */
        smsc9220_disable_interrupt( dev, SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL );
    }

    smsc9220_clear_all_interrupts( dev );

    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static BaseType_t xMPS2_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    const uint32_t ulEthernetIRQ = 13UL;
    BaseType_t xReturn = pdFAIL;
    enum smsc9220_error_t err;

    ( void ) pxInterface;

    if( xRxTaskHandle == NULL )
    {
        /* Task has not been created before. */
        xReturn = xTaskCreate( prvRxTask,
                               "EMAC",
                               nwRX_TASK_STACK_SIZE,
                               NULL,
                               nwETHERNET_RX_HANDLER_TASK_PRIORITY,
                               &xRxTaskHandle );
        configASSERT( xReturn != pdFALSE );
    }

    if( xReturn == pdPASS )
    {
        err = smsc9220_init( dev, prvWait_ms );

        if( err != SMSC9220_ERROR_NONE )
        {
            FreeRTOS_debug_printf( ( "%s: %d\n", "smsc9220_init failed", err ) );
            xReturn = pdFAIL;
        }
        else
        {
            /* Disable the Ethernet interrupt in the NVIC. */
            nwNVIC_ICER = ( uint32_t ) ( 1UL << ( ulEthernetIRQ & 0x1FUL ) );

            smsc9220_disable_all_interrupts( dev );
            smsc9220_clear_all_interrupts( dev );

            smsc9220_set_fifo_level_irq( dev, SMSC9220_FIFO_LEVEL_IRQ_RX_STATUS_POS,
                                         SMSC9220_FIFO_LEVEL_IRQ_LEVEL_MIN );
            smsc9220_set_fifo_level_irq( dev, SMSC9220_FIFO_LEVEL_IRQ_TX_STATUS_POS,
                                         SMSC9220_FIFO_LEVEL_IRQ_LEVEL_MIN );
            smsc9220_set_fifo_level_irq( dev, SMSC9220_FIFO_LEVEL_IRQ_TX_DATA_POS,
                                         SMSC9220_FIFO_LEVEL_IRQ_LEVEL_MAX );
            prvSetMACAddress();

            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_GPIO0 );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_GPIO1 );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_GPIO2 );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_RX_STATUS_FIFO_LEVEL );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_RX_STATUS_FIFO_FULL );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_RX_DROPPED_FRAME );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_TX_STATUS_FIFO_LEVEL );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_TX_STATUS_FIFO_FULL );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_TX_DATA_FIFO_AVAILABLE );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_TX_DATA_FIFO_OVERRUN );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_TX_ERROR );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_RX_ERROR );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_RX_WATCHDOG_TIMEOUT );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_TX_STATUS_OVERFLOW );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_TX_POWER_MANAGEMENT );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_PHY );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_GP_TIMER );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_RX_DMA );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_TX_IOC );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_RX_DROPPED_FRAME_HALF );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_RX_STOPPED );
            smsc9220_enable_interrupt( dev, SMSC9220_INTERRUPT_TX_STOPPED );

            /* Enable the Ethernet interrupt in the NVIC. */
            nwNVIC_ISER = ( uint32_t ) ( 1UL << ( ulEthernetIRQ & 0x1FUL ) );

            xReturn = pdPASS;
        }
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t xMPS2_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    enum smsc9220_error_t error = SMSC9220_ERROR_NONE;
    BaseType_t xReturn = pdFAIL, x;

    ( void ) pxInterface;

    for( x = 0; x < niMAX_TX_ATTEMPTS; x++ )
    {
        if( pxNetworkBuffer->xDataLength < SMSC9220_ETH_MAX_FRAME_SIZE )
        {
            error = smsc9220_send_by_chunks( dev,
                                             pxNetworkBuffer->xDataLength,
                                             true,
                                             ( char * ) ( pxNetworkBuffer->pucEthernetBuffer ),
                                             pxNetworkBuffer->xDataLength );

            if( error == SMSC9220_ERROR_NONE )
            {
                xReturn = pdPASS;
                break;
            }
            else
            {
                xReturn = pdFAIL;
                FreeRTOS_debug_printf( ( "Error send by chunks: %d\n",
                                         error ) );
            }
        }
        else
        {
            xReturn = pdFAIL;
            FreeRTOS_debug_printf( ( "Packet size too large:%d\n",
                                     pxNetworkBuffer->xDataLength ) );
            break;
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
    configASSERT( xRxTaskHandle == ( TaskHandle_t ) 1 );
    ( void ) pxNetworkBuffers;
}
/*-----------------------------------------------------------*/


static BaseType_t xMPS2_GetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    const struct smsc9220_eth_dev_t * dev = &SMSC9220_ETH_DEV;
    uint32_t ulPHYBasicStatusValue;
    BaseType_t xLinkStatusUp;

    ( void ) pxInterface;
    /* Get current status */
    smsc9220_phy_regread( dev, SMSC9220_PHY_REG_OFFSET_BSTATUS,
                          &ulPHYBasicStatusValue );
    xLinkStatusUp = ( bool ) ( ulPHYBasicStatusValue &
                               ( 1ul << ( PHY_REG_BSTATUS_LINK_STATUS_INDEX ) ) );
    return xLinkStatusUp;
}

/*-----------------------------------------------------------*/

#if ( ipconfigIPv4_BACKWARD_COMPATIBLE != 0 )

/* Do not call the following function directly. It is there for downward compatibility.
 * The function FreeRTOS_IPInit() will call it to initialice the interface and end-point
 * objects.  See the description in FreeRTOS_Routing.h. */
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface )
    {
        return pxMPS2_FillInterfaceDescriptor( xEMACIndex, pxInterface );
    }

#endif
/*-----------------------------------------------------------*/

NetworkInterface_t * pxMPS2_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                     NetworkInterface_t * pxInterface )
{
    static char pcName[ 17 ];

/* This function pxFillInterfaceDescriptor() adds a network-interface.
 * Make sure that the object pointed to by 'pxInterface'
 * is declared static or global, and that it will remain to exist. */

    pxMyInterface = pxInterface;

    snprintf( pcName, sizeof( pcName ), "eth%ld", xEMACIndex );

    memset( pxInterface, '\0', sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;                    /* Just for logging, debugging. */
    pxInterface->pvArgument = ( void * ) xEMACIndex; /* Has only meaning for the driver functions. */
    pxInterface->pfInitialise = xMPS2_NetworkInterfaceInitialise;
    pxInterface->pfOutput = xMPS2_NetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = xMPS2_GetPhyLinkStatus;

    FreeRTOS_AddNetworkInterface( pxInterface );

    return pxInterface;
}
/*-----------------------------------------------------------*/
