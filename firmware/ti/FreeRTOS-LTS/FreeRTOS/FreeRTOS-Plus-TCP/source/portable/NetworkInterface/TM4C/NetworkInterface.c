/**
 *       @file: NetworkInterface.c
 *	   @author: jscott <jscott@hotstart.com>
 *       @date: Feb 1, 2022
 *  @copyright: Hotstart 2022 Hotstart Thermal Management. All Rights Reserved.
 *
 *      Permission is hereby granted, free of charge, to any person obtaining a copy of
 *      this software and associated documentation files (the "Software"), to deal in
 *      the Software without restriction, including without limitation the rights to
 *      use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 *      the Software, and to permit persons to whom the Software is furnished to do so,
 *      subject to the following conditions:
 *
 *      The above copyright notice and this permission notice shall be included in all
 *      copies or substantial portions of the Software.
 *
 *      THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 *      IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 *      FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 *      COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 *      IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 *      CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *      @brief:Network Interface driver for the Texas Instruments TM4C line of microcontrollers.
 *
 *      This driver was written and tested with the TM4C1294NCPDT, which includes a built-in MAC and
 *      PHY. The expectation is that this driver should function correctly across all the MAC/PHY
 *      integrated parts of the TM4C129X parts.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>

#include "inc/hw_ints.h"
#include "inc/hw_emac.h"
#include "inc/hw_memmap.h"
#include "inc/hw_nvic.h"

#include "driverlib/flash.h"
#include "driverlib/interrupt.h"
#include "driverlib/gpio.h"
#include "driverlib/rom_map.h"
#include "driverlib/sysctl.h"
#include "driverlib/systick.h"
#include "driverlib/emac.h"

#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"
#include "phyHandling.h"

#define BUFFER_SIZE_WO_PADDING     ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER )
#define BUFFER_SIZE                ( BUFFER_SIZE_WO_PADDING + ipBUFFER_PADDING )
#define BUFFER_SIZE_ROUNDED_UP     ( ( BUFFER_SIZE + 7 ) & ~0x7UL )
#define PHY_PHYS_ADDR              0

#ifndef niEMAC_SYSCONFIG_HZ
    #define niEMAC_SYSCONFIG_HZ    configCPU_CLOCK_HZ
#endif

#ifndef niEMAC_TX_DMA_DESC_COUNT
    #define niEMAC_TX_DMA_DESC_COUNT    8
#endif

#ifndef niEMAC_RX_DMA_DESC_COUNT
    #define niEMAC_RX_DMA_DESC_COUNT    8
#endif

#if ipconfigUSE_LINKED_RX_MESSAGES
    #error Linked RX Messages are not supported by this driver
#endif

/* Default the size of the stack used by the EMAC deferred handler task to twice
 * the size of the stack used by the idle task - but allow this to be overridden in
 * FreeRTOSConfig.h as configMINIMAL_STACK_SIZE is a user definable constant. */
#ifndef configEMAC_TASK_STACK_SIZE
    #define configEMAC_TASK_STACK_SIZE    ( 2 * configMINIMAL_STACK_SIZE )
#endif

#ifndef niEMAC_HANDLER_TASK_PRIORITY
    #define niEMAC_HANDLER_TASK_PRIORITY    configMAX_PRIORITIES - 1
#endif

#if !defined( ipconfigETHERNET_AN_ENABLE )
    /* Enable auto-negotiation */
    #define ipconfigETHERNET_AN_ENABLE    1
#endif

#if !defined( ipconfigETHERNET_USE_100MB )
    #define ipconfigETHERNET_USE_100MB    1
#endif

#if !defined( ipconfigETHERNET_USE_FULL_DUPLEX )
    #define ipconfigETHERNET_USE_FULL_DUPLEX    1
#endif

typedef struct
{
    uint32_t number_descriptors;
    uint32_t write;
    uint32_t read;
} tDescriptorList;

typedef enum
{
    eMACInit,   /* Must initialise MAC. */
    eMACPass,   /* Initialisation was successful. */
    eMACFailed, /* Initialisation failed. */
} eMAC_INIT_STATUS_TYPE;

typedef enum
{
    eMACInterruptNone = 0,        /* No interrupts need servicing */
    eMACInterruptRx = ( 1 << 0 ), /* Service RX interrupt */
    eMACInterruptTx = ( 1 << 1 ), /* Service TX interrupt */
} eMAC_INTERRUPT_STATUS_TYPE;

static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMACInit;

static volatile eMAC_INTERRUPT_STATUS_TYPE xMacInterruptStatus = eMACInterruptNone;

static tEMACDMADescriptor _tx_descriptors[ niEMAC_TX_DMA_DESC_COUNT ];
static tEMACDMADescriptor _rx_descriptors[ niEMAC_RX_DMA_DESC_COUNT ];

static tDescriptorList _tx_descriptor_list = { .number_descriptors = niEMAC_TX_DMA_DESC_COUNT, 0 };
static tDescriptorList _rx_descriptor_list = { .number_descriptors = niEMAC_RX_DMA_DESC_COUNT, 0 };

static uint8_t _network_buffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ][ BUFFER_SIZE_ROUNDED_UP ] __attribute__( ( aligned( 4 ) ) );

static EthernetPhy_t xPhyObject;

static TaskHandle_t _deferred_task_handle = NULL;

const PhyProperties_t xPHYProperties =
{
    #if ( ipconfigETHERNET_AN_ENABLE != 0 )
        .ucSpeed      = PHY_SPEED_AUTO,
        .ucDuplex     = PHY_DUPLEX_AUTO,
    #else
        #if ( ipconfigETHERNET_USE_100MB != 0 )
            .ucSpeed  = PHY_SPEED_100,
        #else
            .ucSpeed  = PHY_SPEED_10,
        #endif

        #if ( ipconfigETHERNET_USE_FULL_DUPLEX != 0 )
            .ucDuplex = PHY_DUPLEX_FULL,
        #else
            .ucDuplex = PHY_DUPLEX_HALF,
        #endif
    #endif /* if ( ipconfigETHERNET_AN_ENABLE != 0 ) */
};

/**
 * Reads the Ethernet MAC from user Flash.
 * @param mac_address_bytes[out] The byte array which will hold the MAC address
 * @return pdPASS on success, pdFAIL if the MAC is invalid from user Flash
 */
static BaseType_t _ethernet_mac_get( uint8_t * mac_address_bytes );

/**
 * Initialize DMA descriptors
 */
static void _dma_descriptors_init( void );

/**
 * Frees previously sent network buffers
 */
static void _process_transmit_complete( void );

/**
 * Processes received packets and forwards those acceptable to the network stack
 */
static BaseType_t _process_received_packet( void );

/**
 * Processes PHY interrupts.
 */
static void _process_phy_interrupts( void );

/**
 * Thread to forward received packets from the ISR to the network stack
 * @param parameters Not used
 */
static void _deferred_task( void * parameters );

/**
 * Phy read implementation for the TM4C
 * @param xAddress
 * @param xRegister
 * @param pulValue
 * @return
 */
static BaseType_t xTM4C_PhyRead( BaseType_t xAddress,
                                 BaseType_t xRegister,
                                 uint32_t * pulValue );

/**
 * Phy write implementation for the TM4C
 * @param xAddress
 * @param xRegister
 * @param ulValue
 * @return
 */
static BaseType_t xTM4C_PhyWrite( BaseType_t xAddress,
                                  BaseType_t xRegister,
                                  uint32_t ulValue );

/**
 * Probe the PHY
 */
static void vMACBProbePhy( void );

BaseType_t xNetworkInterfaceInitialise( void )
{
    uint8_t mac_address_bytes[ 6 ];
    uint16_t ui16Val;
    BaseType_t xResult = pdFAIL;

    if( eMACInit == xMacInitStatus )
    {
        /* Create the RX packet forwarding task */
        if( pdFAIL == xTaskCreate( _deferred_task, "EMAC", configEMAC_TASK_STACK_SIZE, NULL, niEMAC_HANDLER_TASK_PRIORITY, &_deferred_task_handle ) )
        {
            xMacInitStatus = eMACFailed;
        }
        else
        {
            /* Read the MAC from user Flash */
            if( pdPASS != _ethernet_mac_get( &mac_address_bytes[ 0 ] ) )
            {
                xMacInitStatus = eMACFailed;
            }
            else
            {
                MAP_SysCtlPeripheralReset( SYSCTL_PERIPH_EMAC0 );

                while( !MAP_SysCtlPeripheralReady( SYSCTL_PERIPH_EMAC0 ) )
                {
                }

                MAP_SysCtlPeripheralReset( SYSCTL_PERIPH_EPHY0 );

                while( !MAP_SysCtlPeripheralReady( SYSCTL_PERIPH_EPHY0 ) )
                {
                }

                MAP_EMACInit( EMAC0_BASE, niEMAC_SYSCONFIG_HZ,
                              EMAC_BCONFIG_MIXED_BURST | EMAC_BCONFIG_PRIORITY_FIXED, 4,
                              4, 0 );

                MAP_EMACConfigSet(
                    EMAC0_BASE,
                    (
                        EMAC_CONFIG_100MBPS |
                        EMAC_CONFIG_FULL_DUPLEX |
                        EMAC_CONFIG_CHECKSUM_OFFLOAD |
                        EMAC_CONFIG_7BYTE_PREAMBLE |
                        EMAC_CONFIG_IF_GAP_96BITS |
                        EMAC_CONFIG_USE_MACADDR0 |
                        EMAC_CONFIG_SA_FROM_DESCRIPTOR |
                        EMAC_CONFIG_BO_LIMIT_1024 |
                        EMAC_CONFIG_STRIP_CRC
                    ),
                    (
                        EMAC_MODE_RX_STORE_FORWARD |
                        EMAC_MODE_TX_STORE_FORWARD |
                        EMAC_MODE_RX_THRESHOLD_64_BYTES |
                        EMAC_MODE_TX_THRESHOLD_64_BYTES ),
                    0 );


                /* Clear any stray MISR1 PHY interrupts that may be set. */
                ui16Val = MAP_EMACPHYRead( EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1 );
                /* Enable link status change interrupts */
                ui16Val |=
                    ( EPHY_MISR1_LINKSTATEN |
                      EPHY_MISR1_SPEEDEN |
                      EPHY_MISR1_DUPLEXMEN |
                      EPHY_MISR1_ANCEN
                    );
                MAP_EMACPHYWrite( EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1, ui16Val );

                /* Clear any stray MISR2 PHY interrupts that may be set. */
                ui16Val = MAP_EMACPHYRead( EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR2 );

                /* Configure and enable PHY interrupts */
                ui16Val = MAP_EMACPHYRead( EMAC0_BASE, PHY_PHYS_ADDR, EPHY_SCR );
                ui16Val |= ( EPHY_SCR_INTEN_EXT | EPHY_SCR_INTOE_EXT );
                MAP_EMACPHYWrite( EMAC0_BASE, PHY_PHYS_ADDR, EPHY_SCR, ui16Val );

                /* Read the PHY interrupt status to clear any stray events. */
                ui16Val = MAP_EMACPHYRead( EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1 );

                /* Set MAC filtering options.  We receive all broadcast and mui32ticast */
                /* packets along with those addressed specifically for us. */
                MAP_EMACFrameFilterSet( EMAC0_BASE, ( EMAC_FRMFILTER_HASH_AND_PERFECT |
                                                      EMAC_FRMFILTER_PASS_MULTICAST ) );

                /* Set the MAC address */
                MAP_EMACAddrSet( EMAC0_BASE, 0, &mac_address_bytes[ 0 ] );

                /* Clears any previously asserted interrupts */
                MAP_EMACIntClear( EMAC0_BASE, EMACIntStatus( EMAC0_BASE, false ) );

                /* Initialize the DMA descriptors */
                _dma_descriptors_init();

                /* Enable TX/RX */
                MAP_EMACTxEnable( EMAC0_BASE );
                MAP_EMACRxEnable( EMAC0_BASE );

                /* Set the interrupt to a lower priority than the OS scheduler interrupts */
                MAP_IntPrioritySet( INT_EMAC0, ( 6 << ( 8 - configPRIO_BITS ) ) );

                /* Probe the PHY with the stack driver */
                vMACBProbePhy();

                xMacInitStatus = eMACPass;
            }
        }
    }

    if( eMACPass == xMacInitStatus )
    {
        /* Wait for the link status to come up before enabling interrupts */
        if( xPhyObject.ulLinkStatusMask != 0U )
        {
            /* Enable the Ethernet RX and TX interrupt source. */
            MAP_EMACIntEnable( EMAC0_BASE, ( EMAC_INT_RECEIVE | EMAC_INT_TRANSMIT |
                                             EMAC_INT_TX_STOPPED | EMAC_INT_RX_NO_BUFFER |
                                             EMAC_INT_RX_STOPPED | EMAC_INT_PHY ) );

            /* Enable EMAC interrupts */
            MAP_IntEnable( INT_EMAC0 );

            xResult = pdPASS;
        }
    }

    return xResult;
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t xReleaseAfterSend )
{
    BaseType_t success = pdTRUE;
    tEMACDMADescriptor * dma_descriptor;

    /* As this driver is strictly zero-copy, assert that the stack does not call this function with */
    /* xReleaseAfterSend as false */
    configASSERT( 0 != xReleaseAfterSend );

    dma_descriptor = &_tx_descriptors[ _tx_descriptor_list.write ];

    /* If the DMA controller still owns the descriptor, all DMA descriptors are in use, bail out */
    if( 0U == ( dma_descriptor->ui32CtrlStatus & DES0_RX_CTRL_OWN ) )
    {
        /* Assign the buffer to the DMA descriptor */
        dma_descriptor->pvBuffer1 = pxNetworkBuffer->pucEthernetBuffer;

        /* Inform the DMA of the size of the packet */
        dma_descriptor->ui32Count = ( pxNetworkBuffer->xDataLength & DES1_TX_CTRL_BUFF1_SIZE_M ) << DES1_TX_CTRL_BUFF1_SIZE_S;

        /* Inform the DMA that this is the first and last segment of the packet, calculate the checksums, the descriptors are */
        /* chained, and to use interrupts */
        dma_descriptor->ui32CtrlStatus = DES0_TX_CTRL_FIRST_SEG | DES0_TX_CTRL_IP_ALL_CKHSUMS | DES0_TX_CTRL_CHAINED
                                         | DES0_TX_CTRL_LAST_SEG | DES0_TX_CTRL_INTERRUPT | DES0_TX_CTRL_REPLACE_CRC;

        /* Advance the index in the list */
        _tx_descriptor_list.write++;

        /* Wrap around if required */
        if( _tx_descriptor_list.write == niEMAC_TX_DMA_DESC_COUNT )
        {
            _tx_descriptor_list.write = 0;
        }

        /* Give the DMA descriptor to the DMA controller */
        dma_descriptor->ui32CtrlStatus |= DES0_TX_CTRL_OWN;

        /* Inform the DMA it has a new descriptor */
        MAP_EMACTxDMAPollDemand( EMAC0_BASE );

        iptraceNETWORK_INTERFACE_TRANSMIT();
    }
    else
    {
        /* Release the stack descriptor and buffer to prevent memory leaks. */
        vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );

        success = pdFALSE;
    }

    return success;
}

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    BaseType_t i;

    for( i = 0; i < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; i++ )
    {
        /* Assign buffers to each descriptor */
        pxNetworkBuffers[ i ].pucEthernetBuffer = &_network_buffers[ i ][ ipBUFFER_PADDING ];

        /* Set the 'hidden' reference to the descriptor for use in DMA interrupts */
        *( ( uint32_t * ) &_network_buffers[ i ][ 0 ] ) = ( uint32_t ) &( ( pxNetworkBuffers[ i ] ) );
    }
}

static BaseType_t _ethernet_mac_get( uint8_t * mac_address_bytes )
{
    BaseType_t success = pdPASS;
    uint32_t mac_address_words[ 2 ] = { 0 };

    /* Attempt to read the MAC address */
    MAP_FlashUserGet( &mac_address_words[ 0 ], &mac_address_words[ 1 ] );

    /* If the MAC is not set, fail */
    if( ( 0xFFFFFFFF == mac_address_words[ 0 ] ) || ( 0xFFFFFFFF == mac_address_words[ 1 ] ) )
    {
        success = pdFAIL;
    }
    else
    {
        /* Otherwise return the MAC address in a usable format for the driver */
        *( mac_address_bytes + 0 ) = ( mac_address_words[ 0 ] >> 0 ) & 0xFF;
        *( mac_address_bytes + 1 ) = ( mac_address_words[ 0 ] >> 8 ) & 0xFF;
        *( mac_address_bytes + 2 ) = ( mac_address_words[ 0 ] >> 16 ) & 0xFF;
        *( mac_address_bytes + 3 ) = ( mac_address_words[ 1 ] >> 0 ) & 0xFF;
        *( mac_address_bytes + 4 ) = ( mac_address_words[ 1 ] >> 8 ) & 0xFF;
        *( mac_address_bytes + 5 ) = ( mac_address_words[ 1 ] >> 16 ) & 0xFF;
    }

    return success;
}

static void _dma_descriptors_init( void )
{
    uint32_t i;
    const size_t buffer_size_requested = BUFFER_SIZE_WO_PADDING;
    NetworkBufferDescriptor_t * stack_descriptor;

    /* Initialize the TX DMA descriptors */
    for( i = 0; i < niEMAC_TX_DMA_DESC_COUNT; i++ )
    {
        /* Clear the length of the packet */
        _tx_descriptors[ i ].ui32Count = 0;

        /* Clear the reference to the buffer */
        _tx_descriptors[ i ].pvBuffer1 = NULL;

        /* Set the next link in the DMA descriptor chain, either the next in the chain or the first descriptor in the event */
        /* that this is the last descriptor */
        _tx_descriptors[ i ].DES3.pLink = (
            ( i == ( niEMAC_TX_DMA_DESC_COUNT - 1 ) ) ?
            &_tx_descriptors[ 0 ] : &_tx_descriptors[ i + 1 ] );
        _tx_descriptors[ i ].ui32CtrlStatus = DES0_TX_CTRL_INTERRUPT | DES0_TX_CTRL_CHAINED
                                              | DES0_TX_CTRL_IP_ALL_CKHSUMS;
    }

    /* Set the TX descriptor index */
    _tx_descriptor_list.write = 0;
    _tx_descriptor_list.read = 0;

    for( i = 0; i < niEMAC_RX_DMA_DESC_COUNT; i++ )
    {
        stack_descriptor = pxGetNetworkBufferWithDescriptor( ipTOTAL_ETHERNET_FRAME_SIZE, 0 );

        configASSERT( NULL != stack_descriptor );

        /* Get a buffer from the stack and assign it to the DMA Descriptor */
        _rx_descriptors[ i ].pvBuffer1 = stack_descriptor->pucEthernetBuffer;

        /* Inform the DMA controller that the descriptors are chained and the size of the buffer */
        _rx_descriptors[ i ].ui32Count = DES1_RX_CTRL_CHAINED | ( ( buffer_size_requested << DES1_TX_CTRL_BUFF1_SIZE_S ) & DES1_TX_CTRL_BUFF1_SIZE_M );

        /* Give the DMA descriptor to the DMA controller */
        _rx_descriptors[ i ].ui32CtrlStatus = DES0_RX_CTRL_OWN;

        /* Set the next link the DMA descriptor chain */
        _rx_descriptors[ i ].DES3.pLink = ( ( i == ( niEMAC_RX_DMA_DESC_COUNT - 1 ) ) ? &_rx_descriptors[ 0 ] : &_rx_descriptors[ i + 1 ] );
    }

    /* Set the RX descriptor index */
    _rx_descriptor_list.write = 0;

    /* Set the head of the DMA descriptor list in the EMAC peripheral */
    MAP_EMACTxDMADescriptorListSet( EMAC0_BASE, &_tx_descriptors[ 0 ] );
    MAP_EMACRxDMADescriptorListSet( EMAC0_BASE, &_rx_descriptors[ 0 ] );
}

void freertos_tcp_ethernet_int( void )
{
    uint32_t status;
    BaseType_t higher_priority_task_woken = pdFALSE;

    /* Read the interrupt status */
    status = EMACIntStatus( EMAC0_BASE, true );

    /* Handle power management interrupts */
    if( status & EMAC_INT_POWER_MGMNT )
    {
        MAP_EMACTxEnable( EMAC0_BASE );
        MAP_EMACRxEnable( EMAC0_BASE );

        MAP_EMACPowerManagementStatusGet( EMAC0_BASE );

        status &= ~( EMAC_INT_POWER_MGMNT );
    }

    if( status )
    {
        MAP_EMACIntClear( EMAC0_BASE, status );
    }

    /* Handle PHY interrupts */
    if( EMAC_INT_PHY & status )
    {
        _process_phy_interrupts();
    }

    /* Handle Transmit Complete interrupts */
    if( EMAC_INT_TRANSMIT & status )
    {
        xMacInterruptStatus |= eMACInterruptTx;
    }

    /* Handle Receive interrupts */
    if( ( EMAC_INT_RECEIVE | EMAC_INT_RX_NO_BUFFER | EMAC_INT_RX_STOPPED ) & status )
    {
        xMacInterruptStatus |= eMACInterruptRx;
    }

    /* If interrupts of concern were found, wake the task if present */
    if( ( 0 != xMacInterruptStatus ) && ( NULL != _deferred_task_handle ) )
    {
        vTaskNotifyGiveFromISR( _deferred_task_handle, &higher_priority_task_woken );

        portYIELD_FROM_ISR( higher_priority_task_woken );
    }
}

static void _process_transmit_complete( void )
{
    uint32_t i;
    tEMACDMADescriptor * dma_descriptor;
    NetworkBufferDescriptor_t * stack_descriptor;

    for( i = 0; ( ( i < _tx_descriptor_list.number_descriptors ) && ( _tx_descriptor_list.read != _tx_descriptor_list.write ) ); i++ )
    {
        /* Get a reference to the current DMA descriptor */
        dma_descriptor = &_tx_descriptors[ _tx_descriptor_list.read ];

        /* If the descriptor is still owned by the DMA controller, exit */
        if( dma_descriptor->ui32CtrlStatus & DES0_TX_CTRL_OWN )
        {
            break;
        }

        /* Get the 'hidden' reference to the stack descriptor from the buffer */
        stack_descriptor = pxPacketBuffer_to_NetworkBuffer( dma_descriptor->pvBuffer1 );

        configASSERT( NULL != stack_descriptor );

        /* Release the stack descriptor */
        vReleaseNetworkBufferAndDescriptor( stack_descriptor );

        _tx_descriptor_list.read++;

        if( _tx_descriptor_list.read == _tx_descriptor_list.number_descriptors )
        {
            _tx_descriptor_list.read = 0;
        }
    }
}

static BaseType_t _process_received_packet( void )
{
    NetworkBufferDescriptor_t * new_stack_descriptor;
    NetworkBufferDescriptor_t * cur_stack_descriptor;
    tEMACDMADescriptor * dma_descriptor;
    uint32_t i;
    IPStackEvent_t event;
    BaseType_t result = pdTRUE;
    const TickType_t max_block_time = pdMS_TO_MIN_TICKS( 50 );
    const size_t buffer_size_requested = BUFFER_SIZE_WO_PADDING;

    /* Go through the list of RX DMA descriptors */
    for( i = 0; i < niEMAC_RX_DMA_DESC_COUNT; i++ )
    {
        /* Get a reference to the descriptor */
        dma_descriptor = &_rx_descriptors[ _rx_descriptor_list.write ];

        /* Make sure the buffer is non-null */
        configASSERT( NULL != dma_descriptor->pvBuffer1 );

        /* If the descriptor is still in use by DMA, stop processing here */
        if( DES0_RX_CTRL_OWN == ( dma_descriptor->ui32CtrlStatus & DES0_RX_CTRL_OWN ) )
        {
            break;
        }

        /* If there is NOT an error in the frame */
        if( 0U == ( dma_descriptor->ui32CtrlStatus & DES0_RX_STAT_ERR ) )
        {
            /* Get a new empty descriptor */
            new_stack_descriptor = pxGetNetworkBufferWithDescriptor( ipTOTAL_ETHERNET_FRAME_SIZE, max_block_time );

            /* If a descriptor was provided, else this packet is dropped */
            if( NULL != new_stack_descriptor )
            {
                /* Get a reference to the current stack descriptor held by the DMA descriptor */
                cur_stack_descriptor = pxPacketBuffer_to_NetworkBuffer( dma_descriptor->pvBuffer1 );

                /* Set the length of the buffer on the current descriptor */
                cur_stack_descriptor->xDataLength = ( dma_descriptor->ui32CtrlStatus & DES0_RX_STAT_FRAME_LENGTH_M ) >> DES0_RX_STAT_FRAME_LENGTH_S;

                /* Assign the new stack descriptor to the DMA descriptor */
                dma_descriptor->pvBuffer1 = new_stack_descriptor->pucEthernetBuffer;

                /* Ask the stack if it wants to process the frame. */
                if( eProcessBuffer == eConsiderFrameForProcessing( cur_stack_descriptor->pucEthernetBuffer ) )
                {
                    /* Setup the event */
                    event.eEventType = eNetworkRxEvent;
                    event.pvData = cur_stack_descriptor;

                    /* Forward the event */
                    if( pdFALSE == xSendEventStructToIPTask( &event, 0 ) )
                    {
                        /* Release the buffer if an error was encountered */
                        vReleaseNetworkBufferAndDescriptor( cur_stack_descriptor );

                        iptraceETHERNET_RX_EVENT_LOST();
                    }
                    else
                    {
                        iptraceNETWORK_INTERFACE_RECEIVE();

                        result = pdTRUE;
                    }
                }
                else
                {
                    /* Free the descriptor */
                    vReleaseNetworkBufferAndDescriptor( cur_stack_descriptor );
                }
            } /* end if descriptor is available */
            else
            {
                /* No stack descriptor was available for the next RX DMA descriptor so this packet */
                /* is dropped */

                /* Mark the RX event as lost */
                iptraceETHERNET_RX_EVENT_LOST();
            }
        } /* end if frame had error. In this case, give the buffer back to the DMA for the next RX */

        /* Set up the DMA descriptor for the next receive transaction */
        dma_descriptor->ui32Count = DES1_RX_CTRL_CHAINED | ( ( buffer_size_requested << DES1_RX_CTRL_BUFF1_SIZE_S ) & DES1_RX_CTRL_BUFF1_SIZE_M );

        dma_descriptor->ui32CtrlStatus = DES0_RX_CTRL_OWN;

        _rx_descriptor_list.write++;

        if( _rx_descriptor_list.write == _rx_descriptor_list.number_descriptors )
        {
            _rx_descriptor_list.write = 0;
        }
    }

    return result;
}

/**
 * This deferred interrupt handler process changes from the PHY auto-negotiation to configure the
 * MAC as appropriate.
 */
static void _process_phy_interrupts( void )
{
    uint16_t value;
    uint16_t status;
    uint32_t configuration;
    uint32_t mode;
    uint32_t max_frame_size;

    /* Read the PHY interrupts status */
    value = MAP_EMACPHYRead( EMAC0_BASE, PHY_PHYS_ADDR, EPHY_MISR1 );
    status = MAP_EMACPHYRead( EMAC0_BASE, PHY_PHYS_ADDR, EPHY_STS );

    if( value & ( EPHY_MISR1_SPEED | EPHY_MISR1_DUPLEXM | EPHY_MISR1_ANC ) )
    {
        /* If the speed or duplex has changed */

        MAP_EMACConfigGet( EMAC0_BASE, &configuration, &mode, &max_frame_size );

        if( status & EPHY_STS_SPEED )
        {
            configuration &= ~EMAC_CONFIG_100MBPS;
        }
        else
        {
            configuration |= EMAC_CONFIG_100MBPS;
        }

        if( status & EPHY_STS_DUPLEX )
        {
            configuration |= EMAC_CONFIG_FULL_DUPLEX;
        }
        else
        {
            configuration &= ~EMAC_CONFIG_FULL_DUPLEX;
        }

        MAP_EMACConfigSet( EMAC0_BASE, configuration, mode, max_frame_size );
    }
}

static void _deferred_task( void * parameters )
{
    BaseType_t had_reception;
    IPStackEvent_t link_down_event;
    const TickType_t max_block_time = pdMS_TO_TICKS( 100 );

    /* Ignore parameters */
    ( void ) parameters;

    for( ; ; )
    {
        had_reception = pdFALSE;

        ulTaskNotifyTake( pdTRUE, max_block_time );

        if( eMACInterruptTx == ( xMacInterruptStatus & eMACInterruptTx ) )
        {
            xMacInterruptStatus &= ~( eMACInterruptTx );

            _process_transmit_complete();
        }

        if( eMACInterruptRx == ( xMacInterruptStatus & eMACInterruptRx ) )
        {
            xMacInterruptStatus &= ~( eMACInterruptRx );

            had_reception = _process_received_packet();
        }

        if( pdTRUE == xPhyCheckLinkStatus( &xPhyObject, had_reception ) )
        {
            /* The link has gone done */
            if( 0 == xPhyObject.ulLinkStatusMask )
            {
                link_down_event.eEventType = eNetworkDownEvent;
                link_down_event.pvData = NULL;

                xSendEventStructToIPTask( &link_down_event, 0 );
            }
        }
    }
}

static void vMACBProbePhy( void )
{
    vPhyInitialise( &xPhyObject, xTM4C_PhyRead, xTM4C_PhyWrite );
    xPhyDiscover( &xPhyObject );
    xPhyConfigure( &xPhyObject, &xPHYProperties );
}

static BaseType_t xTM4C_PhyRead( BaseType_t xAddress,
                                 BaseType_t xRegister,
                                 uint32_t * pulValue )
{
    *pulValue = MAP_EMACPHYRead( EMAC0_BASE, ( uint8_t ) xAddress, ( uint8_t ) xRegister );

    return 0;
}

static BaseType_t xTM4C_PhyWrite( BaseType_t xAddress,
                                  BaseType_t xRegister,
                                  uint32_t ulValue )
{
    MAP_EMACPHYWrite( EMAC0_BASE, ( uint8_t ) xAddress, ( uint8_t ) xRegister, ulValue );

    return 0;
}
