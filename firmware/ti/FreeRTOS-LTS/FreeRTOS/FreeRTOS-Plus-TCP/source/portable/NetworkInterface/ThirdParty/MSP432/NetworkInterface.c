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

#include <string.h>
#include <stdint.h>
#include <ti/devices/msp432e4/driverlib/driverlib.h>
#include <ti/devices/msp432e4/driverlib/emac.h>

#include "FreeRTOS.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_private.h"
#include "FreeRTOSIPConfigDefaults.h"
#include "task.h"
#include "NetworkBufferManagement.h"

#include "NetworkInterface.h"

/*
 * NOTES:
 * This is a driver for the internal MAC of the MSP432E401Y microcontroller from Texas Instruments.
 *
 * (1) See below for defines that configure and override FreeRTOS defines so that the driver can be used.
 * (2) The driver provides link up and down detection that also takes into consideration remote faults
 * and Ethernet cable plug/unplug events during data transmission.
 * (3) The EMAC hardware is automatically re-started if there is an internal error.
 * (4) The MAC address can be set from outside of the driver or read from internal flash.
 * (5) The EMAC hardware can be turned on or off from external tasks.
 * (6) The EMAC hardware is set to 10BASE-T Half Duplex to ensure that the FreeRTOS+TCP stack does not receive
 * data too quickly. This is because the 120 MHz processor cannot respond fast enough to ping floods or
 * other events.  The hardware is thereby set up so that it can respond in a robust fashion.
 * (7) Supports tickless interrupts.
 * (8) To turn on and off the EMAC, it is best to do a hard microcontroller reset.
 *
 * Recommended settings in FreeRTOSIPConfig.h:
 #define ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES 1
 #define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM  1
 #define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM  1
 #define ipconfigIP_TASK_STACK_SIZE_WORDS    ( configMINIMAL_STACK_SIZE * 100 )
 #define ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS      60
 #define configTASK_NOTIFICATION_ARRAY_ENTRIES 2
 *
 #define ipconfigHAS_DEBUG_PRINTF    0
 #define ipconfigHAS_PRINTF          0
 *
 * Recommended settings in FreeRTOSConfig.h:
 #define configTICK_RATE_HZ              ( ( TickType_t ) 1000 )
 #define configUSE_PREEMPTION            1
 #define configUSE_TIME_SLICING          0
 #define configCPU_CLOCK_HZ              ( ( unsigned long ) 120000000 )
 #define configMINIMAL_STACK_SIZE        ( ( unsigned short ) 256 )
 #define configTOTAL_HEAP_SIZE           ( ( size_t ) ( 0x28000 ) )
 #define ipconfigTCP_WIN_SEG_COUNT       240
 *
 * REFERENCES:
 * [1] FreeRTOS Forum
 * [2] Texas Instruments Driverlib code examples
 */

#define RTOS_NET_UP_DOWN_TASK_NAME     "NetUpDownS"
#define RTOS_NET_RX_TASK_NAME          "NetRX"
#define RTOS_NET_TX_TASK_NAME          "NetTX"
#define RTOS_NET_CHECK_TASK_SIZE       configMINIMAL_STACK_SIZE
#define RTOS_RX_POLL_MAC_TASK_SIZE     3 * configMINIMAL_STACK_SIZE
#define RTOS_TX_POLL_MAC_TASK_SIZE     3 * configMINIMAL_STACK_SIZE
#define NUM_TX_DESCRIPTORS             8U
#define NUM_RX_DESCRIPTORS             8U

#define ETH_DOWN_DELAY_MS              1000U
#define ETH_MAX_TIMEOUT_CYCLES         12000000U
#define ETH_STARTUP_TIMEOUT            ETH_MAX_TIMEOUT_CYCLES
#define CHECK_LINK_UP_DOWN_DELAY_MS    1000U

#define ETH_RX_QUEUE_LEN               NUM_TX_DESCRIPTORS
#define ETH_TX_QUEUE_LEN               NUM_RX_DESCRIPTORS

/* TX Queue positions */
#define TX_QUEPOS_FIRST_EVENT          0
#define TX_QUEPOS_SECOND_EVENT         1

/* Minimum packet length is required to ensure that all of the bytes are transmitted
 * even when there are issues with the network (i.e. a network cable pulled out during TX or RX) */
#define ETHERNET_MIN_PACKET_BYTES      60

/* Ensure that the RTOS settings work well for this driver */
#if configTASK_NOTIFICATION_ARRAY_ENTRIES < 2
    #undef configTASK_NOTIFICATION_ARRAY_ENTRIES
    #define configTASK_NOTIFICATION_ARRAY_ENTRIES     2
#endif
#ifndef ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM    1
#endif
#ifndef ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM    1
#endif
#ifdef ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
    #undef ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM    1
#endif
#ifdef ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
    #undef ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM
    #define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM    1
#endif
#ifdef ipconfigETHERNET_MINIMUM_PACKET_BYTES
    #undef ipconfigETHERNET_MINIMUM_PACKET_BYTES
    #define ipconfigETHERNET_MINIMUM_PACKET_BYTES    ETHERNET_MIN_PACKET_BYTES
#endif
#if ipconfigHAS_DEBUG_PRINTF == 1
    #if ( ipconfigPORT_SUPPRESS_WARNING == 0 )
        #warning The network interface may not work properly if ipconfigHAS_DEBUG_PRINTF 1.  Please set ipconfigHAS_DEBUG_PRINTF 0 for production use.
    #endif
#endif
#ifndef __MSP432E401Y__
    #define __MSP432E401Y__
#endif

static BaseType_t loadMACInternal();
static BaseType_t setupEMAC();
static void offEMAC();
static void initDescriptors( uint32_t ul32Base );
static uint32_t packetTransmit( uint8_t * pui8Buf,
                                uint32_t ul32BufLen );
static void ethernetIntHandler( void );
static uint32_t processReceivedPacket( void );
static void applicationProcessFrameRX( uint32_t ul32FrameLen,
                                       uint8_t * uc8Buf,
                                       uint32_t ulindex );
static void prvCheckLinkUpOrDownNetStateTask( void * pvParameters );
static void prvEMACDeferredInterruptHandlerTaskRX( void * pvParameters );
static BaseType_t isEMACLinkUp();
static void DMAFreeDescriptorRX( uint32_t ulindx );
static void prvEMACDeferredInterfaceOutputTaskTX( void * pvParameters );
static void vSetNetworkInterfaceConfig( const struct InternalNetworkInterfaceMSP432EConfig config );

/* EMAC interrupts */
#define EMAC_INTERRUPTS    EMAC_INT_RECEIVE | EMAC_INT_TRANSMIT | EMAC_INT_BUS_ERROR | EMAC_INT_TX_STOPPED | EMAC_INT_RX_STOPPED

/* DMA descriptors */
tEMACDMADescriptor g_psRxDescriptor[ NUM_TX_DESCRIPTORS ];
tEMACDMADescriptor g_psTxDescriptor[ NUM_RX_DESCRIPTORS ];
uint32_t ulg_ui32RxDescIndex;
uint32_t ulg_ui32TxDescIndex;

/* Define the maximum length of a packet buffer. 1536 is ideal because it
 * allows for a perfect alignment. */
#define ETH_MAX_BUFFER_SIZE    1536
#define ETH_RX_BUFFER_SIZE     ETH_MAX_BUFFER_SIZE
#define ETH_TX_BUFFER_SIZE     ETH_MAX_BUFFER_SIZE
uint8_t ucg_ppui8RxBuffer[ NUM_RX_DESCRIPTORS ][ ETH_RX_BUFFER_SIZE ];

/* Task handles */
TaskHandle_t xTaskToNotifyEthernetRX = NULL;
TaskHandle_t xTaskToNotifyEthernetTX = NULL;
TaskHandle_t xHandleCheckLinkUpOrDown = NULL;
TaskHandle_t xHandleCheckNet = NULL;

/* Queue handles */
QueueHandle_t xQueueRX;
QueueHandle_t xQueueTX;

/* MAC address */
uint8_t ucpui8MACAddr[ ipMAC_ADDRESS_LENGTH_BYTES ];

/* State variable that indicates whether the network is up or down */
static BaseType_t networkUP = pdFALSE;
/* Check to see if the device has been setup */
static BaseType_t hasBeenSetup = pdFALSE;
/* Check to see if the network needs to be reset */
static BaseType_t resetNetwork = pdFALSE;

/* RX data input buffer */
struct NetworkInterfaceDataIn
{
    uint8_t * ucbuff;    /* buffer to the data */
    uint32_t ulbuff_siz; /* buffer size */
    uint32_t ulindx;     /* index of buffer in DMA descriptor */
};

/* TX data output buffer */
struct NetworkInterfaceDataOut
{
    NetworkBufferDescriptor_t * pxDescriptor;
    BaseType_t xReleaseAfterSend;
};

/* Local config struct */
static struct InternalNetworkInterfaceMSP432EConfig configLocal;


/* Call this function to check if the network interface is up.
 * The function can be called from code external to this file.
 */
BaseType_t vPublicCheckNetworkInterfaceUp()
{
    return networkUP;
} /* end */


static BaseType_t loadMACInternal()
{
    uint32_t ui32User0, ui32User1;

    /* Read the MAC address from internal flash. Bit[23:0] are stored in user register0, and Bit[47:24] are stored in user register1.
     * The MAC address can be loaded from an external IC or can be loaded from the internal registers if the registers are not zero.
     * The evaluation kit hardware uses reading from internal flash variables but this can also be used for production as well
     * if the internal flash is programmed on the assembly line. */
    FlashUserGet( &ui32User0, &ui32User1 );

    if( ( ( FlashUserGet( &ui32User0, &ui32User1 ) ) != 0 ) ||
        ( ui32User0 == 0xffffffff ) ||
        ( ui32User1 == 0xffffffff ) )
    {
        return pdFALSE;
    }

    configLocal.ucMACAddr[ 0 ] = ( ( ui32User0 >> 0 ) & 0xffU );
    configLocal.ucMACAddr[ 1 ] = ( ( ui32User0 >> 8 ) & 0xffU );
    configLocal.ucMACAddr[ 2 ] = ( ( ui32User0 >> 16 ) & 0xffU );
    configLocal.ucMACAddr[ 3 ] = ( ( ui32User1 >> 0 ) & 0xffU );
    configLocal.ucMACAddr[ 4 ] = ( ( ui32User1 >> 8 ) & 0xffU );
    configLocal.ucMACAddr[ 5 ] = ( ( ui32User1 >> 16 ) & 0xffU );
    return pdTRUE;
}


/* This function sets up the EMAC. Not to be called directly from outside of this file. */
static BaseType_t setupEMAC()
{
    uint32_t ul32Loop;
    BaseType_t rv;
    BaseType_t interruptsMasked = pdFALSE;

    if( xTaskGetSchedulerState() == taskSCHEDULER_RUNNING )
    {
        taskENTER_CRITICAL();
        interruptsMasked = pdTRUE;
    }

    if( configLocal.setMACAddrInternal == pdTRUE )
    {
        rv = loadMACInternal();

        if( rv == pdFALSE )
        {
            return pdFALSE;
        }
    }

    /* enable and reset the internal MAC */
    SysCtlPeripheralPowerOn( SYSCTL_PERIPH_EMAC0 );
    SysCtlPeripheralPowerOn( SYSCTL_PERIPH_EPHY0 );
    SysCtlPeripheralEnable( SYSCTL_PERIPH_EMAC0 );
    SysCtlPeripheralEnable( SYSCTL_PERIPH_EPHY0 );
    SysCtlPeripheralReset( SYSCTL_PERIPH_EMAC0 );
    SysCtlPeripheralReset( SYSCTL_PERIPH_EPHY0 );

    /* The peripheral should always start, but there is a wait with timeout here to prevent an infinite loop*/
    ul32Loop = 0;

    while( !SysCtlPeripheralReady( SYSCTL_PERIPH_EMAC0 ) && ( ul32Loop < ETH_STARTUP_TIMEOUT ) )
    {
        SysCtlDelay( 1 );
        ul32Loop += 1;
    }

    if( ul32Loop == ETH_STARTUP_TIMEOUT )
    {
        return pdFALSE;
    }

    /* configure the internal PHY */
    EMACPHYConfigSet( EMAC0_BASE,
                      ( EMAC_PHY_TYPE_INTERNAL |
                        EMAC_PHY_INT_MDIX_EN |
                        EMAC_PHY_AN_10B_T_HALF_DUPLEX ) );

    /* reset the MAC to latch the configuration */
    EMACReset( EMAC0_BASE );

    /* wait */
    SysCtlDelay( ETH_STARTUP_TIMEOUT );

    /* init the EMAC */
    EMACInit( EMAC0_BASE, configCPU_CLOCK_HZ,
              EMAC_BCONFIG_MIXED_BURST | EMAC_BCONFIG_PRIORITY_FIXED, 4, 4,
              0 );

    /*
     *  Since the checksum is computed in the hardware using EMAC_CONFIG_CHECKSUM_OFFLOAD,
     *  there is also a need to turn on defines in FreeRTOS+TCP as well. This is done automatically
     *  using the defines in this file.
     *
     #define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM  1
     #define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM  1
     */
    EMACConfigSet( EMAC0_BASE,
                   ( EMAC_CONFIG_HALF_DUPLEX |
                     EMAC_CONFIG_CHECKSUM_OFFLOAD |
                     EMAC_CONFIG_IF_GAP_96BITS |
                     EMAC_CONFIG_USE_MACADDR0 |
                     EMAC_CONFIG_BO_LIMIT_1024 ),
                   ( EMAC_MODE_RX_STORE_FORWARD | EMAC_MODE_TX_STORE_FORWARD
                   ), ETH_MAX_BUFFER_SIZE );

    /* DMA descriptors init */
    initDescriptors( EMAC0_BASE );

    /* program MAC address from the cached address */
    EMACAddrSet( EMAC0_BASE, 0, configLocal.ucMACAddr );

    /* Set address filtering */
    EMACAddrFilterSet( EMAC0_BASE, 0, EMAC_FILTER_ADDR_ENABLE | EMAC_FILTER_SOURCE_ADDR );

    /* Set MAC filtering options */
    EMACFrameFilterSet( EMAC0_BASE, EMAC_FRMFILTER_SADDR | EMAC_FRMFILTER_PASS_NO_CTRL );

    /* indicate that the receive descriptors are available to the DMA to start the receive processing */
    for( ul32Loop = 0; ul32Loop < NUM_RX_DESCRIPTORS; ul32Loop++ )
    {
        g_psRxDescriptor[ ul32Loop ].ui32CtrlStatus |= DES0_RX_CTRL_OWN;
    }

    /* Enable the Ethernet MAC transmitter and receiver */
    EMACTxEnable( EMAC0_BASE );
    EMACRxEnable( EMAC0_BASE );

    /* Enable the Ethernet interrupt */
    IntPrioritySet( INT_EMAC0, 0x20 ); /* (0x01 << 5) to set the priority into the last three bits for Cortex M4F */

    /* register the interrupt handler for the Ethernet MAC */
    EMACIntRegister( EMAC0_BASE, ethernetIntHandler );

    /* enable the interrupts for the EMAC */
    EMACIntClear( EMAC0_BASE, EMACIntStatus( EMAC0_BASE, pdFALSE ) );
    IntEnable( INT_EMAC0 );
    EMACIntEnable( EMAC0_BASE, EMAC_INTERRUPTS );

    /* exit the critical section */
    if( interruptsMasked == pdTRUE )
    {
        taskEXIT_CRITICAL();
    }

    return pdTRUE;
}


/* This function only turns off the Ethernet EMAC.  This function does not turn off any
 * of the processing tasks and therefore should not be called directly from external tasks. */
static void offEMAC()
{
    uint32_t ulstatus, ulcnt;
    BaseType_t interruptsMasked;

    interruptsMasked = pdFALSE;

    if( xTaskGetSchedulerState() == taskSCHEDULER_RUNNING )
    {
        taskENTER_CRITICAL();
        interruptsMasked = pdTRUE;
    }

    networkUP = pdFALSE;

    ulcnt = 0;
    ulstatus = EMACStatusGet( EMAC0_BASE );

    while( ulstatus )
    {
        ulstatus = EMACStatusGet( EMAC0_BASE );
        ulcnt++;

        if( ulcnt == ETH_STARTUP_TIMEOUT )
        {
            if( interruptsMasked == pdTRUE )
            {
                taskEXIT_CRITICAL();
            }

            return;
        }
    }

    IntDisable( INT_EMAC0 );
    SysCtlPeripheralDisable( SYSCTL_PERIPH_EMAC0 );
    SysCtlPeripheralDisable( SYSCTL_PERIPH_EPHY0 );
    SysCtlPeripheralPowerOff( SYSCTL_PERIPH_EMAC0 );
    SysCtlPeripheralPowerOff( SYSCTL_PERIPH_EPHY0 );

    if( interruptsMasked == pdTRUE )
    {
        taskEXIT_CRITICAL();
    }
}


/* Interrupt handler */
static void ethernetIntHandler( void )
{
    uint32_t ui32Temp;

    ui32Temp = EMACIntStatus( EMAC0_BASE, pdTRUE );

    if( ui32Temp & EMAC_INT_RECEIVE )
    {
        /* RX */
        processReceivedPacket();
    }

    if( ui32Temp & EMAC_INT_TRANSMIT )
    {
        BaseType_t xHigherPriorityTaskWokenTX = pdFALSE;
        /* TX */
        vTaskNotifyGiveIndexedFromISR( xTaskToNotifyEthernetTX, TX_QUEPOS_SECOND_EVENT, &xHigherPriorityTaskWokenTX );
        portYIELD_FROM_ISR( xHigherPriorityTaskWokenTX );
    }

    if( ( ui32Temp & EMAC_INT_BUS_ERROR ) || ( ui32Temp & EMAC_INT_TX_STOPPED ) || ( ui32Temp & EMAC_INT_RX_STOPPED ) )
    {
        /* Reset the network since something has gone wrong */
        resetNetwork = pdTRUE;
    }

    /* clear the interrupt */
    EMACIntClear( EMAC0_BASE, ui32Temp );
    /* as per Application Note SLAA739 - June 2017 */
    #if configUSE_TICKLESS_IDLE == 1
        SCB->SCR &= ~SCB_SCR_SLEEPONEXIT_Msk;
        __DSB();
    #endif
}


/* Init the DMA descriptors */
static void initDescriptors( uint32_t ul32Base )
{
    uint32_t ul32Loop;

    for( ul32Loop = 0U; ul32Loop < NUM_TX_DESCRIPTORS; ul32Loop++ )
    {
        g_psTxDescriptor[ ul32Loop ].ui32Count = DES1_TX_CTRL_SADDR_INSERT;
        g_psTxDescriptor[ ul32Loop ].DES3.pLink =
            ( ul32Loop == ( NUM_TX_DESCRIPTORS - 1 ) ) ?
            g_psTxDescriptor : &g_psTxDescriptor[ ul32Loop + 1 ];
        g_psTxDescriptor[ ul32Loop ].ui32CtrlStatus =
            ( DES0_TX_CTRL_LAST_SEG | DES0_TX_CTRL_FIRST_SEG |
              DES0_TX_CTRL_INTERRUPT | DES0_TX_CTRL_CHAINED |
              DES0_TX_CTRL_IP_ALL_CKHSUMS );
    }

    for( ul32Loop = 0; ul32Loop < NUM_RX_DESCRIPTORS; ul32Loop++ )
    {
        g_psRxDescriptor[ ul32Loop ].ui32CtrlStatus = 0;
        g_psRxDescriptor[ ul32Loop ].ui32Count =
            ( DES1_RX_CTRL_CHAINED |
              ( ETH_RX_BUFFER_SIZE << DES1_RX_CTRL_BUFF1_SIZE_S ) );
        g_psRxDescriptor[ ul32Loop ].pvBuffer1 = ucg_ppui8RxBuffer[ ul32Loop ];
        g_psRxDescriptor[ ul32Loop ].DES3.pLink =
            ( ul32Loop == ( NUM_RX_DESCRIPTORS - 1 ) ) ?
            g_psRxDescriptor : &g_psRxDescriptor[ ul32Loop + 1 ];
    }

    EMACRxDMADescriptorListSet( ul32Base, g_psRxDescriptor );
    EMACTxDMADescriptorListSet( ul32Base, g_psTxDescriptor );

    ulg_ui32RxDescIndex = 0;
    ulg_ui32TxDescIndex = NUM_TX_DESCRIPTORS - 1;
}


/* Transmit a packet - call this function from the network stack
 *  pui8Buf = the buffer
 *  i32BufLen = length of the buffer
 */
static uint32_t packetTransmit( uint8_t * pui8Buf,
                                uint32_t ul32BufLen )
{
    uint8_t bufferTX[ ETH_TX_BUFFER_SIZE ];

    ulg_ui32TxDescIndex++;

    if( ulg_ui32TxDescIndex == NUM_TX_DESCRIPTORS )
    {
        ulg_ui32TxDescIndex = 0;
    }

    /* The copy needs to be done here since directly assigning a pointer does not seem to work
     * and causes the transmitter to stop.  Some testing indicates that that this can be quicker than
     *  simply assigning the pointer for smaller packets. */
    memcpy( bufferTX, pui8Buf, ul32BufLen );

    g_psTxDescriptor[ ulg_ui32TxDescIndex ].ui32Count = ul32BufLen;
    g_psTxDescriptor[ ulg_ui32TxDescIndex ].pvBuffer1 = bufferTX;
    g_psTxDescriptor[ ulg_ui32TxDescIndex ].ui32CtrlStatus =
        ( DES0_TX_CTRL_LAST_SEG | DES0_TX_CTRL_FIRST_SEG |
          DES0_TX_CTRL_INTERRUPT | DES0_TX_CTRL_IP_ALL_CKHSUMS |
          DES0_TX_CTRL_CHAINED | DES0_TX_CTRL_OWN );

    EMACTxDMAPollDemand( EMAC0_BASE );
    return( ul32BufLen );
}


/* Function to process the received packet */
static uint32_t processReceivedPacket( void )
{
    uint32_t ul32FrameLen;

    ul32FrameLen = 0;

    if( !( g_psRxDescriptor[ ulg_ui32RxDescIndex ].ui32CtrlStatus & DES0_RX_CTRL_OWN ) )
    {
        /* Does it have a valid frame? */
        if( !( g_psRxDescriptor[ ulg_ui32RxDescIndex ].ui32CtrlStatus &
               DES0_RX_STAT_ERR ) )
        {
            if( g_psRxDescriptor[ ulg_ui32RxDescIndex ].ui32CtrlStatus &
                DES0_RX_STAT_LAST_DESC )
            {
                /* get the frame length */
                ul32FrameLen =
                    ( ( g_psRxDescriptor[ ulg_ui32RxDescIndex ].ui32CtrlStatus &
                        DES0_RX_STAT_FRAME_LENGTH_M ) >>
                      DES0_RX_STAT_FRAME_LENGTH_S );

                /* call the function that sends the data to the task */
                applicationProcessFrameRX( ul32FrameLen,
                                           g_psRxDescriptor[ ulg_ui32RxDescIndex ].pvBuffer1, ulg_ui32RxDescIndex );
            }
        }

        /* Move on to the next RX packet */
        ulg_ui32RxDescIndex++;

        if( ulg_ui32RxDescIndex == NUM_RX_DESCRIPTORS )
        {
            ulg_ui32RxDescIndex = 0;
        }
    } /* end if */

    /* return the frame length */
    return ul32FrameLen;
}


/* This function passes the framelength and the RX buffer into the FreeRTOS task.
 * The function is called from the ISR and therefore must use portYIELD_FROM_ISR() */
static void applicationProcessFrameRX( uint32_t ul32FrameLen,
                                       uint8_t * uc8Buf,
                                       uint32_t ulindex )
{
    BaseType_t rv;
    struct NetworkInterfaceDataIn NIDataIn;
    BaseType_t xHigherPriorityTaskWokenRX = pdFALSE;

    NIDataIn.ucbuff = uc8Buf;
    NIDataIn.ulbuff_siz = ul32FrameLen;
    NIDataIn.ulindx = ulindex;

    /* send the data into the queue */
    rv = xQueueSendFromISR( xQueueRX, &NIDataIn, &xHigherPriorityTaskWokenRX );

    if( rv == pdTRUE )
    {
        vTaskNotifyGiveFromISR( xTaskToNotifyEthernetRX, &xHigherPriorityTaskWokenRX );
    }
    else
    {
        DMAFreeDescriptorRX( ulindex );
    }

    portYIELD_FROM_ISR( xHigherPriorityTaskWokenRX );
}

/* Function to free the RX descriptor */
static void DMAFreeDescriptorRX( uint32_t ulindx )
{
    g_psRxDescriptor[ ulindx ].ui32CtrlStatus = DES0_RX_CTRL_OWN;
}

/*
 * -------------------------------------------------------------
 * FREERTOS+TCP FUNCTIONS
 * -------------------------------------------------------------
 */

/* Call this function to populate the driver defaults struct with defaults */
void vGetInternalNetworkInterfaceMSP432EConfigDefaults( struct InternalNetworkInterfaceMSP432EConfig * config )
{
    uint32_t k;

    config->turnOnEMAC = pdTRUE;
    config->setMACAddrInternal = pdFALSE;

    for( k = 0; k < ipMAC_ADDRESS_LENGTH_BYTES; k++ )
    {
        config->ucMACAddr[ k ] = 0xFF;
    }
}


static void vSetNetworkInterfaceConfig( const struct InternalNetworkInterfaceMSP432EConfig config )
{
    configLocal = config;
}


/* Call this function to setup the network */
BaseType_t vPublicSetupEMACNetwork( const struct InternalNetworkInterfaceMSP432EConfig config )
{
    BaseType_t rv;

    rv = pdFALSE;
    BaseType_t tv;

    /* setup the MAC address and turn on the EMAC if required */
    vSetNetworkInterfaceConfig( config );

    if( config.turnOnEMAC )
    {
        rv = setupEMAC();
    }

    if( rv == pdFALSE )
    {
        return pdFALSE;
    }

    /* ensure that the code can only be run once to create the tasks */
    if( hasBeenSetup == pdTRUE )
    {
        return pdTRUE;
    }

    /* create the queues */
    xQueueRX = xQueueCreate( ETH_RX_QUEUE_LEN, sizeof( struct NetworkInterfaceDataIn ) );

    if( xQueueRX == NULL )
    {
        return pdFALSE;
    }

    xQueueTX = xQueueCreate( ETH_TX_QUEUE_LEN, sizeof( struct NetworkInterfaceDataOut ) );

    if( xQueueTX == NULL )
    {
        return pdFALSE;
    }

    /* RX task */
    tv = xTaskCreate( prvEMACDeferredInterruptHandlerTaskRX,
                      RTOS_NET_RX_TASK_NAME,
                      RTOS_RX_POLL_MAC_TASK_SIZE,
                      NULL,
                      configMAX_PRIORITIES - 1,
                      &xTaskToNotifyEthernetRX );

    if( tv != pdPASS )
    {
        return pdFALSE;
    }

    /* TX task */
    tv = xTaskCreate( prvEMACDeferredInterfaceOutputTaskTX,
                      RTOS_NET_TX_TASK_NAME,
                      RTOS_TX_POLL_MAC_TASK_SIZE,
                      NULL,
                      configMAX_PRIORITIES - 1,
                      &xTaskToNotifyEthernetTX );

    if( tv != pdPASS )
    {
        return pdFALSE;
    }

    /* Link Up/Down/Network task */
    tv = xTaskCreate( prvCheckLinkUpOrDownNetStateTask,
                      RTOS_NET_UP_DOWN_TASK_NAME,
                      RTOS_NET_CHECK_TASK_SIZE,
                      NULL,
                      tskIDLE_PRIORITY,
                      &xHandleCheckLinkUpOrDown );

    if( tv != pdPASS )
    {
        return pdFALSE;
    }

    /* latch the setup state */
    hasBeenSetup = pdTRUE;

    /* the setup has succeeded */
    return pdTRUE;
}


/* FreeRTOS task that handles the RX interrupt */
static void prvEMACDeferredInterruptHandlerTaskRX( void * pvParameters )
{
    NetworkBufferDescriptor_t * pxDescriptor = NULL;
    IPStackEvent_t xRxEvent;
    struct NetworkInterfaceDataIn NIDataReceived;
    uint32_t xBytesReceived;

    for( ; ; )
    {
        ulTaskNotifyTake( pdTRUE, portMAX_DELAY );
        xQueueReceive( xQueueRX, &NIDataReceived, 0 );

        if( eConsiderFrameForProcessing( NIDataReceived.ucbuff ) == eProcessBuffer )
        {
            xBytesReceived = NIDataReceived.ulbuff_siz - ipSIZE_OF_ETH_CRC_BYTES; /* do not include the CRC bytes in the received size */
            pxDescriptor = pxGetNetworkBufferWithDescriptor( xBytesReceived, 0 );

            if( pxDescriptor != NULL )
            {
                memcpy( pxDescriptor->pucEthernetBuffer, NIDataReceived.ucbuff, NIDataReceived.ulbuff_siz );
                pxDescriptor->xDataLength = xBytesReceived;
                xRxEvent.eEventType = eNetworkRxEvent;
                xRxEvent.pvData = ( void * ) pxDescriptor;

                if( xSendEventStructToIPTask( &xRxEvent, 0 ) == pdTRUE )
                {
                    /* The buffer does not need to be released here since this will be done internally by the network stack */
                    iptraceNETWORK_INTERFACE_RECEIVE();
                }
                else
                {
                    /* The buffer needs to be released since we cannot send to the network stack */
                    vReleaseNetworkBufferAndDescriptor( pxDescriptor );
                    iptraceETHERNET_RX_EVENT_LOST();
                }
            }
        }

        /* Release the DMA descriptor at a specific index */
        taskENTER_CRITICAL();
        DMAFreeDescriptorRX( NIDataReceived.ulindx );
        taskEXIT_CRITICAL();
    } /* end for */
}


/* Network initialization is already done outside of this function, so this function will only
 * report if the network is initialized by returning a flag. Called directly by FreeRTOS. */
BaseType_t xNetworkInterfaceInitialise( void )
{
    if( networkUP == pdTRUE )
    {
        return pdTRUE;
    }

    return pdFALSE;
}


/*  Task to output the data to the network interface. This allows the network stack to continue
 *  processing while the data is able to be sent. */
static void prvEMACDeferredInterfaceOutputTaskTX( void * pvParameters )
{
    struct NetworkInterfaceDataOut NIDataOutput;

    for( ; ; )
    {
        ulTaskNotifyTakeIndexed( TX_QUEPOS_FIRST_EVENT, pdTRUE, portMAX_DELAY );
        xQueueReceive( xQueueTX, &NIDataOutput, 0 );

        /* For ICMP packets, the checksum must be zero if the network hardware computes the checksum or the buffer will not be properly sent
         * For this driver it is required that ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 1 */
        ProtocolPacket_t * pxPacket;
        pxPacket = ( ProtocolPacket_t * ) ( NIDataOutput.pxDescriptor->pucEthernetBuffer );

        if( pxPacket->xICMPPacket.xIPHeader.ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP )
        {
            pxPacket->xICMPPacket.xICMPHeader.usChecksum = ( uint16_t ) 0u;
        }

        taskENTER_CRITICAL();
        packetTransmit( NIDataOutput.pxDescriptor->pucEthernetBuffer, ( uint32_t ) NIDataOutput.pxDescriptor->xDataLength );
        taskEXIT_CRITICAL();

        /* wait until transmit */
        ulTaskNotifyTakeIndexed( TX_QUEPOS_SECOND_EVENT, pdTRUE, portMAX_DELAY );
        iptraceNETWORK_INTERFACE_TRANSMIT();

        if( NIDataOutput.xReleaseAfterSend )
        {
            vReleaseNetworkBufferAndDescriptor( NIDataOutput.pxDescriptor );
        }
    }
}


/*  Function to output packets to the network.
 *  Called directly by FreeRTOS. This function should not block and therefore passes
 *  all output data to a queue.  If the function blocks the network stack can become unresponsive
 *  so all of the output work is thereby done by another task. */
BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor,
                                    BaseType_t xReleaseAfterSend )
{
    struct NetworkInterfaceDataOut NIDataOutput;
    BaseType_t txResp;
    BaseType_t returnValue = pdFALSE;
    BaseType_t xDescriptorUsed = pdFALSE;

    /* When the following assert is hit, please make sure that
     * ipconfigZERO_COPY_TX_DRIVER is defined as '1' in your
     * FreeRTOSIPConfig.h header file. */
    configASSERT( xReleaseAfterSend != pdFALSE );

    if( networkUP != pdFALSE )
    {
        NIDataOutput.pxDescriptor = pxDescriptor;
        NIDataOutput.xReleaseAfterSend = xReleaseAfterSend;
        txResp = xQueueSend( xQueueTX, &NIDataOutput, 0 );

        if( txResp == pdTRUE )
        {
            xTaskNotifyGiveIndexed( xTaskToNotifyEthernetTX, 0 );
            returnValue = pdTRUE;
            xDescriptorUsed = pdTRUE;
        }
    }
    else
    {
        /* The PHY has no Link Status, packet shall be dropped. */
    }

    if( xDescriptorUsed == pdFALSE )
    {
        vReleaseNetworkBufferAndDescriptor( pxDescriptor );
    }

    return returnValue;
}


/*
 * -----------------------------------------------------------------------------------------------------
 * Network interface UP or DOWN tasks and associated functions
 * -----------------------------------------------------------------------------------------------------
 */

/*  Function to check and see if the network is up or down by polling a register in the Ethernet driver.
 *  Apparently there is no other way to do this other than polling.  The register is checked for link status,
 *  but also for remote faults and this takes into consideration a pulled Ethernet cable during RX and TX.
 */
static BaseType_t isEMACLinkUp()
{
    uint8_t uci8PHYAddr = 0; /* refers to the internal PHY */
    uint16_t check;
    BaseType_t returnValue = pdFALSE;

    check = EMACPHYRead( EMAC0_BASE, uci8PHYAddr, EPHY_BMSR );

    if( ( ( check & EPHY_BMSR_LINKSTAT ) != 0 ) && !( check & EPHY_BMSR_RFAULT ) )
    {
        returnValue = pdTRUE; /* link is up */
    }

    return returnValue; /* return link status  */
}


/* Call this network function to physically turn on the EMAC from an internal task. */
static BaseType_t vPrivateTurnOnEMAC()
{
    if( hasBeenSetup == pdFALSE )
    {
        return pdFALSE;
    }

    setupEMAC();

    if( xTaskGetSchedulerState() == taskSCHEDULER_RUNNING )
    {
        FreeRTOS_NetworkDown();
        vTaskResume( xHandleCheckLinkUpOrDown );
        vTaskResume( xHandleCheckNet );
        vTaskResume( xTaskToNotifyEthernetRX );
        vTaskResume( xTaskToNotifyEthernetTX );
    }

    return pdTRUE;
}


/*  Call this function to physically turn off the EMAC from an external task.
 *  It is recommended to check the network stack for open sockets before calling this task,
 *  and only call the task after all sockets are closed and there are no connected clients.
 *  In an operational sense, the best way to turn off the EMAC is to do a hard reset. */
static BaseType_t vPrivateTurnOffEMAC()
{
    if( hasBeenSetup == pdFALSE )
    {
        return pdFALSE; /* make sure that the MAC has been setup */
    }

    if( xTaskGetSchedulerState() == taskSCHEDULER_RUNNING )
    {
        vTaskSuspend( xHandleCheckLinkUpOrDown );
        vTaskSuspend( xHandleCheckNet );
        vTaskSuspend( xTaskToNotifyEthernetRX );
        vTaskSuspend( xTaskToNotifyEthernetTX );
    }

    networkUP = pdFALSE;

    if( xTaskGetSchedulerState() == taskSCHEDULER_RUNNING )
    {
        FreeRTOS_NetworkDown();                           /* Indicate to FreeRTOS that the network is down */
        vTaskDelay( pdMS_TO_TICKS( ETH_DOWN_DELAY_MS ) ); /* Wait until FreeRTOS has finished processing */
    }

    offEMAC(); /* Turn off the physical hardware */
    return pdTRUE;
}


/* A task to check and see if the link is up or down by polling an EMAC register */
static void prvCheckLinkUpOrDownNetStateTask( void * pvParameters )
{
    BaseType_t checkLinkStatus = pdFALSE;

    for( ; ; )
    {
        checkLinkStatus = isEMACLinkUp();

        if( ( checkLinkStatus == pdTRUE ) && ( networkUP == pdFALSE ) )
        {
            networkUP = pdTRUE;
        }
        else if( ( checkLinkStatus == pdFALSE ) && ( networkUP == pdTRUE ) )
        {
            /*   FreeRTOS will poll xNetworkInterfaceInitialise() to check if the network is up.
             *   So after FreeRTOS_NetworkDown() is called, there is no corresponding FreeRTOS_NetworkUp() function...
             */
            networkUP = pdFALSE;
            FreeRTOS_NetworkDown();
        }

        if( resetNetwork == pdTRUE )
        {
            vPrivateTurnOffEMAC();
            vPrivateTurnOnEMAC();
            resetNetwork = pdFALSE;
        }
    }
}



/* Call this function to obtain the MAC address used by the driver */
void vPublicGetMACAddr( uint8_t uc8MACAddrGet[ ipMAC_ADDRESS_LENGTH_BYTES ] )
{
    memcpy( uc8MACAddrGet, configLocal.ucMACAddr, ipMAC_ADDRESS_LENGTH_BYTES );
}


BaseType_t xGetPhyLinkStatus( void )
{
    return networkUP;
}


/*-----------------------------------------------------------------------------------------------------
 * For BufferAllocation_1.c (see the FreeRTOS documentation for further details and examples)
 * ----------------------------------------------------------------------------------------------------- */
#define BUFFER_SIZE_ALLOC1               ( ipTOTAL_ETHERNET_FRAME_SIZE + ipBUFFER_PADDING )
#define BUFFER_SIZE_ALLOC1_ROUNDED_UP    ( ( BUFFER_SIZE_ALLOC1 + 7 ) & ~0x07UL )
static uint8_t ucBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ BUFFER_SIZE_ALLOC1_ROUNDED_UP ];
void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    BaseType_t x;

    for( x = 0; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++ )
    {
        /* pucEthernetBuffer is set to point ipBUFFER_PADDING bytes in from the
         * beginning of the allocated buffer. */
        pxNetworkBuffers[ x ].pucEthernetBuffer = &( ucBuffers[ x ][ ipBUFFER_PADDING ] );

        /* The following line is also required, but will not be required in
         * future versions. */
        *( ( uint32_t * ) &ucBuffers[ x ][ 0 ] ) = ( uint32_t ) &( pxNetworkBuffers[ x ] );
    }
}
