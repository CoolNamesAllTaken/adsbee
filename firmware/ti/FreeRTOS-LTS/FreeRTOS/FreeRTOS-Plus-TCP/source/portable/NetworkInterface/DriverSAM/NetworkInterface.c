/*
 * FreeRTOS+TCP V4.2.2
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_Routing.h"
#include "FreeRTOS_ND.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

/* Some files from the Atmel Software Framework */
/* gmac_SAM.[ch] is a combination of the gmac.[ch] for both SAM4E and SAME70. */
#include "gmac_SAM.h"
#include <sysclk.h>
#include "phyHandling.h"

/* This file is included to see if 'CONF_BOARD_ENABLE_CACHE' is defined. */
#include "conf_board.h"

/* The SAME70 family has the possibility of caching RAM.
 * 'NETWORK_BUFFERS_CACHED' can be defined in either "conf_eth.h"
 * or in "FreeRTOSIPConfig.h".
 * For now, NETWORK_BUFFERS_CACHED should be defined as zero.
 * D-cache may be enabled.
 */
#if ( NETWORK_BUFFERS_CACHED != 0 )
    #error please define this macro as zero
#endif

/* Interrupt events to process.  Currently only the Rx event is processed
 * although code for other events is included to allow for possible future
 * expansion. */
#define EMAC_IF_RX_EVENT     1UL
#define EMAC_IF_TX_EVENT     2UL
#define EMAC_IF_ERR_EVENT    4UL
#define EMAC_IF_ALL_EVENT    ( EMAC_IF_RX_EVENT | EMAC_IF_TX_EVENT | EMAC_IF_ERR_EVENT )

#ifndef EMAC_MAX_BLOCK_TIME_MS

/* The task 'prvEMACHandlerTask()' will wake-up every 100 ms, to see
 * if something has to be done, mostly checking if the PHY has a
 * change in Link Status. */
    #define EMAC_MAX_BLOCK_TIME_MS    100ul
#endif

#if ( ipconfigZERO_COPY_RX_DRIVER == 0 )
    #error This driver works optimal if ipconfigZERO_COPY_RX_DRIVER is defined as 1
#endif

#if ( ipconfigZERO_COPY_TX_DRIVER == 0 )
    #error This driver works optimal if ipconfigZERO_COPY_TX_DRIVER is defined as 1
#endif

/* Default the size of the stack used by the EMAC deferred handler task to 4x
 *  the size of the stack used by the idle task - but allow this to be overridden in
 *  FreeRTOSConfig.h as configMINIMAL_STACK_SIZE is a user definable constant. */
#ifndef configEMAC_TASK_STACK_SIZE
    #define configEMAC_TASK_STACK_SIZE    ( 4 * configMINIMAL_STACK_SIZE )
#endif

#ifndef niEMAC_HANDLER_TASK_PRIORITY
    #define niEMAC_HANDLER_TASK_PRIORITY    configMAX_PRIORITIES - 1
#endif

#if ( NETWORK_BUFFERS_CACHED != 0 ) && ( __DCACHE_PRESENT != 0 ) && defined( CONF_BOARD_ENABLE_CACHE )
    #include "core_cm7.h"

    #if ( ipconfigPORT_SUPPRESS_WARNING == 0 )
        #warning This driver assumes the presence of DCACHE
    #endif

    #define     CACHE_LINE_SIZE               32
    #define     NETWORK_BUFFER_HEADER_SIZE    ( ipconfigPACKET_FILLER_SIZE + 8 )

    static void cache_clean_invalidate()
    {
        /* If you application crashes here, make sure that SCB_EnableDCache() has been called. */
        SCB_CleanInvalidateDCache();
    }
    /*-----------------------------------------------------------*/

    static void cache_clean_invalidate_by_addr( uint32_t addr,
                                                uint32_t size )
    {
        /* SAME70 does not have clean/invalidate per area. */
        SCB_CleanInvalidateDCache_by_Addr( ( uint32_t * ) addr, size );
    }
    /*-----------------------------------------------------------*/

    static void cache_invalidate_by_addr( uint32_t addr,
                                          uint32_t size )
    {
        /* SAME70 does not have clean/invalidate per area. */
        SCB_InvalidateDCache_by_Addr( ( uint32_t * ) addr, size );
    }
    /*-----------------------------------------------------------*/

#else /* The DMA buffers are located in non-cached RAM. */
    #if ( ipconfigPORT_SUPPRESS_WARNING == 0 )
        #warning Sure there is no caching?
    #endif

    #define     cache_clean_invalidate()                        do {} while( 0 )
    #define     cache_clean_invalidate_by_addr( addr, size )    do {} while( 0 )
    #define     cache_invalidate_by_addr( addr, size )          do {} while( 0 )
#endif /* if ( NETWORK_BUFFERS_CACHED != 0 ) && ( __DCACHE_PRESENT != 0 ) && defined( CONF_BOARD_ENABLE_CACHE ) */

/*-----------------------------------------------------------*/

/*
 * Update settings in GMAC for speed and duplex.
 */
static void prvEthernetUpdateConfig( BaseType_t xForce );

/*
 * Access functions to the PHY's: read() and write() to be used by
 * phyHandling.c.
 */
static BaseType_t xPHY_Read( BaseType_t xAddress,
                             BaseType_t xRegister,
                             uint32_t * pulValue );
static BaseType_t xPHY_Write( BaseType_t xAddress,
                              BaseType_t xRegister,
                              uint32_t ulValue );

#if ( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 1 ) && ( ipconfigHAS_TX_CRC_OFFLOADING == 0 )
    void vGMACGenerateChecksum( uint8_t * apBuffer,
                                size_t uxLength );
#endif

/*
 * Called from the ASF GMAC driver.
 */
void xRxCallback( uint32_t ulStatus );
void xTxCallback( uint32_t ulStatus,
                  uint8_t * puc_buffer );

/*
 * A deferred interrupt handler task that processes GMAC interrupts.
 */
static void prvEMACHandlerTask( void * pvParameters );

/*
 * Initialise the ASF GMAC driver.
 */
static BaseType_t prvGMACInit( NetworkInterface_t * pxInterface );

/*
 * Try to obtain an Rx packet from the hardware.
 */
static uint32_t prvEMACRxPoll( void );

static BaseType_t prvSAM_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface );
static BaseType_t prvSAM_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                 NetworkBufferDescriptor_t * const pxBuffer,
                                                 BaseType_t bReleaseAfterSend );
static BaseType_t prvSAM_GetPhyLinkStatus( NetworkInterface_t * pxInterface );

NetworkInterface_t * pxSAM_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface );

/*
 * Handle transmission errors.
 */
static void hand_tx_errors( void );

/*-----------------------------------------------------------*/

/*
 * GMAC hash match register definitions and macros and variables
 * The ATSAM GMAC has a 64 bit register for matching multiple unicast or multicast addresses.
 * This implementation keeps a counter for every one of those bits. Those counters allow us to keep track
 * of how many times each bit has been referenced by a call to prvAddAllowedMACAddress().
 * In order to minimize the memory requirement, the counters are of type uint8_t which limits
 * their value to 255. If a counter ever reaches that value, it is never decremented. Reaching this
 * limit is extremely unlikely in any system, let alone an embedded one using an ATSAM MCU.
 */

#define MULTICAST_HASH_IS_ENABLED( pGMAC )     ( ( pGMAC->GMAC_NCFGR & GMAC_NCFGR_MTIHEN ) != 0U )
#define MULTICAST_HASH_IS_DISABLED( pGMAC )    ( ( pGMAC->GMAC_NCFGR & GMAC_NCFGR_MTIHEN ) == 0U )
#define MULTICAST_HASH_ENABLE( pGMAC )         pGMAC->GMAC_NCFGR |= GMAC_NCFGR_MTIHEN
#define MULTICAST_HASH_DISABLE( pGMAC )        pGMAC->GMAC_NCFGR &= ~( GMAC_NCFGR_MTIHEN )
#define UNICAST_HASH_IS_ENABLED( pGMAC )       ( ( pGMAC->GMAC_NCFGR & GMAC_NCFGR_UNIHEN ) != 0U )
#define UNICAST_HASH_IS_DISABLED( pGMAC )      ( ( pGMAC->GMAC_NCFGR & GMAC_NCFGR_UNIHEN ) == 0U )
#define UNICAST_HASH_ENABLE( pGMAC )           pGMAC->GMAC_NCFGR |= GMAC_NCFGR_UNIHEN
#define UNICAST_HASH_DISABLE( pGMAC )          pGMAC->GMAC_NCFGR &= ~( GMAC_NCFGR_UNIHEN )

#define GMAC_ADDRESS_HASH_BITS    ( 64U )
#define GMAC_ADDRESS_HASH_MASK    ( GMAC_ADDRESS_HASH_BITS - 1U )

static uint64_t prvAddressHashBitMask = 0U;
static uint8_t prvAddressHashCounters[ GMAC_ADDRESS_HASH_BITS ] = { 0U };
static uint8_t prvSpecificMatchCounters[ GMACSA_NUMBER ] = { 0U };

/* Functions to set the hash table for multicast addresses. */
static uint16_t prvGenerateCRC16( const uint8_t * pucAddress );
static void prvAddAllowedMACAddress( struct xNetworkInterface * pxInterface,
                                     const uint8_t * pucMacAddress );
static void prvRemoveAllowedMACAddress( struct xNetworkInterface * pxInterface,
                                        const uint8_t * pucMacAddress );

/* Checks IP queue, buffers, and semaphore and logs diagnostic info if configured */
static void vCheckBuffersAndQueue( void );

/* return 'puc_buffer' to the pool of transmission buffers. */
void returnTxBuffer( uint8_t * puc_buffer );

/*-----------------------------------------------------------*/

/* A copy of PHY register 1: 'PHY_REG_01_BMSR' */
static BaseType_t xGMACSwitchRequired;

/* The GMAC object as defined by the ASF drivers. */
static gmac_device_t gs_gmac_dev;

/* MAC address to use. */
extern const uint8_t ucMACAddress[ 6 ];

/* Holds the handle of the task used as a deferred interrupt processor.  The
 * handle is used so direct notifications can be sent to the task for all EMAC/DMA
 * related interrupts. */
TaskHandle_t xEMACTaskHandle = NULL;

static NetworkInterface_t * pxMyInterface = NULL;

/* TX buffers that have been sent must be returned to the driver
 * using this queue. */
static QueueHandle_t xTxBufferQueue;

/* xTXDescriptorSemaphore is a counting semaphore with
 * a maximum count of GMAC_TX_BUFFERS, which is the number of
 * DMA TX descriptors. */
static SemaphoreHandle_t xTXDescriptorSemaphore = NULL;

/* For local use only: describe the PHY's properties: */
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

    #if ( ipconfigETHERNET_AN_ENABLE != 0 ) && ( ipconfigETHERNET_AUTO_CROSS_ENABLE != 0 )
        .ucMDI_X      = PHY_MDIX_AUTO,
    #elif ( ipconfigETHERNET_CROSSED_LINK != 0 )
        .ucMDI_X      = PHY_MDIX_CROSSED,
    #else
        .ucMDI_X      = PHY_MDIX_DIRECT,
    #endif
};

/* All PHY handling code has now been separated from the NetworkInterface.c,
 * see "../Common/phyHandling.c". */
static EthernetPhy_t xPhyObject;

/*-----------------------------------------------------------*/

/*
 * GMAC interrupt handler.
 */
void GMAC_Handler( void )
{
    xGMACSwitchRequired = pdFALSE;

    /* gmac_handler() may call xRxCallback() which may change
     * the value of xGMACSwitchRequired. */
    gmac_handler( &gs_gmac_dev );

    if( xGMACSwitchRequired != pdFALSE )
    {
        portEND_SWITCHING_ISR( xGMACSwitchRequired );
    }
}
/*-----------------------------------------------------------*/

void xRxCallback( uint32_t ulStatus )
{
    if( ( ( ulStatus & GMAC_RSR_REC ) != 0 ) && ( xEMACTaskHandle != NULL ) )
    {
        /* let the prvEMACHandlerTask know that there was an RX event. */
        xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_RX_EVENT, eSetBits, &( xGMACSwitchRequired ) );
    }
}
/*-----------------------------------------------------------*/

/* The following function can be called by gmac_reset_tx_mem().
 */
void returnTxBuffer( uint8_t * puc_buffer )
{
    /* Called from a non-ISR context. */
    if( xTxBufferQueue != NULL )
    {
        /* return 'puc_buffer' to the pool of transmission buffers. */
        xQueueSend( xTxBufferQueue, &puc_buffer, 0 );
        xTaskNotify( xEMACTaskHandle, EMAC_IF_TX_EVENT, eSetBits );
    }
}

void xTxCallback( uint32_t ulStatus,
                  uint8_t * puc_buffer )
{
    if( ( xTxBufferQueue != NULL ) && ( xEMACTaskHandle != NULL ) )
    {
        /* let the prvEMACHandlerTask know that there was an TX event. */
        /* Wakeup prvEMACHandlerTask. */
        if( puc_buffer == NULL )
        {
            /* (GMAC_TSR) Retry Limit Exceeded */
            /* Can not send logging, we're in an ISR. */
        }
        else
        {
            xQueueSendFromISR( xTxBufferQueue, &puc_buffer, ( BaseType_t * ) &xGMACSwitchRequired );
            xTaskNotifyFromISR( xEMACTaskHandle, EMAC_IF_TX_EVENT, eSetBits, &( xGMACSwitchRequired ) );

            /* TX statistics. Only works when 'GMAC_STATS'
             * is defined as 1.  See gmac_SAM.h for more information. */
            TX_STAT_INCREMENT( tx_callback );
        }
    }
}
/*-----------------------------------------------------------*/


/*
 *  The two standard defines 'GMAC_MAN_RW_TYPE' and 'GMAC_MAN_READ_ONLY'
 *  are incorrect.
 *  Therefore, use the following:
 */

#define GMAC_MAINTENANCE_READ_ACCESS     ( 2 )
#define GMAC_MAINTENANCE_WRITE_ACCESS    ( 1 )

static BaseType_t xPHY_Read( BaseType_t xAddress,
                             BaseType_t xRegister,
                             uint32_t * pulValue )
{
    BaseType_t xReturn;
    UBaseType_t uxWasEnabled;

    /* Wait until bus idle */
    while( ( GMAC->GMAC_NSR & GMAC_NSR_IDLE ) == 0 )
    {
    }

    /* Write maintain register */

    /*
     * OP: Operation: 10 is read. 01 is write.
     */
    uxWasEnabled = ( GMAC->GMAC_NCR & GMAC_NCR_MPE ) != 0u;

    if( uxWasEnabled == 0u )
    {
        /* Enable further GMAC maintenance. */
        GMAC->GMAC_NCR |= GMAC_NCR_MPE;
    }

    GMAC->GMAC_MAN = GMAC_MAN_WTN( GMAC_MAN_CODE_VALUE )
                     | GMAC_MAN_CLTTO
                     | GMAC_MAN_PHYA( xAddress )
                     | GMAC_MAN_REGA( xRegister )
                     | GMAC_MAN_OP( GMAC_MAINTENANCE_READ_ACCESS )
                     | GMAC_MAN_DATA( ( uint16_t ) 0u );

    if( gmac_wait_phy( GMAC, MAC_PHY_RETRY_MAX ) == GMAC_TIMEOUT )
    {
        *pulValue = ( uint32_t ) 0xffffu;
        xReturn = -1;
    }
    else
    {
        /* Wait until bus idle */
        while( ( GMAC->GMAC_NSR & GMAC_NSR_IDLE ) == 0 )
        {
        }

        /* Return data */
        *pulValue = ( uint32_t ) ( GMAC->GMAC_MAN & GMAC_MAN_DATA_Msk );

        xReturn = 0;
    }

    if( uxWasEnabled == 0u )
    {
        /* Disable further GMAC maintenance. */
        GMAC->GMAC_NCR &= ~GMAC_NCR_MPE;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t xPHY_Write( BaseType_t xAddress,
                              BaseType_t xRegister,
                              uint32_t ulValue )
{
    BaseType_t xReturn;
    UBaseType_t uxWasEnabled;

    /* Wait until bus idle */
    while( ( GMAC->GMAC_NSR & GMAC_NSR_IDLE ) == 0 )
    {
    }

    /* Write maintain register */
    uxWasEnabled = ( GMAC->GMAC_NCR & GMAC_NCR_MPE ) != 0u;

    if( uxWasEnabled == 0u )
    {
        /* Enable further GMAC maintenance. */
        GMAC->GMAC_NCR |= GMAC_NCR_MPE;
    }

    GMAC->GMAC_MAN = GMAC_MAN_WTN( GMAC_MAN_CODE_VALUE )
                     | GMAC_MAN_CLTTO
                     | GMAC_MAN_PHYA( xAddress )
                     | GMAC_MAN_REGA( xRegister )
                     | GMAC_MAN_OP( GMAC_MAINTENANCE_WRITE_ACCESS )
                     | GMAC_MAN_DATA( ( uint16_t ) ulValue );

    if( gmac_wait_phy( GMAC, MAC_PHY_RETRY_MAX ) == GMAC_TIMEOUT )
    {
        xReturn = -1;
    }
    else
    {
        xReturn = 0;
    }

    if( uxWasEnabled == 0u )
    {
        /* Disable further GMAC maintenance. */
        GMAC->GMAC_NCR &= ~GMAC_NCR_MPE;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvSAM_NetworkInterfaceInitialise( NetworkInterface_t * pxInterface )
{
    if( xEMACTaskHandle == NULL )
    {
        prvGMACInit( pxInterface );

        cache_clean_invalidate();

        /* The handler task is created at the highest possible priority to
         * ensure the interrupt handler can return directly to it. */
        xTaskCreate( prvEMACHandlerTask, "EMAC", configEMAC_TASK_STACK_SIZE, NULL, niEMAC_HANDLER_TASK_PRIORITY, &xEMACTaskHandle );
        configASSERT( xEMACTaskHandle );
        pxMyInterface = pxInterface;
    }

    if( xTxBufferQueue == NULL )
    {
        xTxBufferQueue = xQueueCreate( GMAC_TX_BUFFERS, sizeof( void * ) );
        configASSERT( xTxBufferQueue );
    }

    if( xTXDescriptorSemaphore == NULL )
    {
        /* When there are N TX descriptors, we want to use
         * at most "N-1" simultaneously. */
        xTXDescriptorSemaphore = xSemaphoreCreateCounting( ( UBaseType_t ) GMAC_TX_BUFFERS - 1U, ( UBaseType_t ) GMAC_TX_BUFFERS - 1U );
        configASSERT( xTXDescriptorSemaphore );
    }

    /* When returning non-zero, the stack will become active and
     * start DHCP (in configured) */
    return prvSAM_GetPhyLinkStatus( NULL );
}
/*-----------------------------------------------------------*/

#if ( ipconfigIPv4_BACKWARD_COMPATIBLE != 0 )

/* Do not call the following function directly. It is there for downward compatibility.
 * The function FreeRTOS_IPInit() will call it to initialice the interface and end-point
 * objects.  See the description in FreeRTOS_Routing.h. */
    NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface )
    {
        return pxSAM_FillInterfaceDescriptor( xEMACIndex, pxInterface );
    }

#endif
/*-----------------------------------------------------------*/

NetworkInterface_t * pxSAM_FillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                    NetworkInterface_t * pxInterface )
{
    static char pcName[ 8 ];

/* This function pxSAM_FillInterfaceDescriptor() adds a network-interface.
 * Make sure that the object pointed to by 'pxInterface'
 * is declared static or global, and that it will remain to exist. */

    snprintf( pcName, sizeof( pcName ), "GMAC%ld", xEMACIndex );

    memset( pxInterface, '\0', sizeof( *pxInterface ) );
    pxInterface->pcName = pcName;                    /* Just for logging, debugging. */
    pxInterface->pvArgument = ( void * ) xEMACIndex; /* Has only meaning for the driver functions. */
    pxInterface->pfInitialise = prvSAM_NetworkInterfaceInitialise;
    pxInterface->pfOutput = prvSAM_NetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = prvSAM_GetPhyLinkStatus;
    pxInterface->pfAddAllowedMAC = prvAddAllowedMACAddress;
    pxInterface->pfRemoveAllowedMAC = prvRemoveAllowedMACAddress;

    FreeRTOS_AddNetworkInterface( pxInterface );

    return pxInterface;
}
/*-----------------------------------------------------------*/

static BaseType_t prvSAM_GetPhyLinkStatus( NetworkInterface_t * pxInterface )
{
    BaseType_t xReturn;

    /*_RB_ Will this parameter be used by any port? */

    /*_HT_ I think it will if there are two instances of an EMAC that share
     * the same driver and obviously get a different 'NetworkInterface_t'. */
    /* Avoid warning about unused parameter. */
    ( void ) pxInterface;

    /* This function returns true if the Link Status in the PHY is high. */
    if( xPhyObject.ulLinkStatusMask != 0 )
    {
        xReturn = pdPASS;
    }
    else
    {
        xReturn = pdFAIL;
    }

    return xReturn;
}
/*-----------------------------------------------------------*/

/** The GMAC TX errors to handle */
#define GMAC_TX_ERRORS    ( GMAC_TSR_TFC | GMAC_TSR_HRESP )

static void hand_tx_errors( void )
{
/* Handle GMAC underrun or AHB errors. */
    if( gmac_get_tx_status( GMAC ) & GMAC_TX_ERRORS )
    {
        gmac_enable_transmit( GMAC, false );

        /* Reinit TX descriptors. */
        gmac_reset_tx_mem( &gs_gmac_dev );
        /* Clear error status. */
        gmac_clear_tx_status( GMAC, GMAC_TX_ERRORS );

        gmac_enable_transmit( GMAC, true );
    }
}

volatile IPPacket_t * pxSendPacket;

static BaseType_t prvSAM_NetworkInterfaceOutput( NetworkInterface_t * pxInterface,
                                                 NetworkBufferDescriptor_t * const pxDescriptor,
                                                 BaseType_t bReleaseAfterSend )
{
/* Do not wait too long for a free TX DMA buffer. */
    const TickType_t xBlockTimeTicks = pdMS_TO_TICKS( 50U );
    uint32_t ulTransmitSize;

    /* Avoid warning about unused parameter. */
    ( void ) pxInterface;
    ulTransmitSize = pxDescriptor->xDataLength;

    pxSendPacket = ( IPPacket_t * ) pxDescriptor->pucEthernetBuffer;

    /* 'GMAC_TX_UNITSIZE' is the netto size of a transmission buffer. */
    if( ulTransmitSize > GMAC_TX_UNITSIZE )
    {
        ulTransmitSize = GMAC_TX_UNITSIZE;
    }

    /* A do{}while(0) loop is introduced to allow the use of multiple break
     * statement. */
    do
    {
        uint32_t ulResult;

        if( xPhyObject.ulLinkStatusMask == 0ul )
        {
            /* Do not attempt to send packets as long as the Link Status is low. */
            break;
        }

        if( xTXDescriptorSemaphore == NULL )
        {
            /* Semaphore has not been created yet? */
            break;
        }

        hand_tx_errors();

        if( xSemaphoreTake( xTXDescriptorSemaphore, xBlockTimeTicks ) != pdPASS )
        {
            /* Time-out waiting for a free TX descriptor. */
            TX_STAT_INCREMENT( tx_enqueue_fail );
            break;
        }

        TX_STAT_INCREMENT( tx_enqueue_ok );
        #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
        {
            /* Confirm that the pxDescriptor may be kept by the driver. */
            configASSERT( bReleaseAfterSend != pdFALSE );
        }
        #endif /* ipconfigZERO_COPY_TX_DRIVER */

        #if ( NETWORK_BUFFERS_CACHED != 0 )
        {
            uint32_t xlength = CACHE_LINE_SIZE * ( ( ulTransmitSize + NETWORK_BUFFER_HEADER_SIZE + CACHE_LINE_SIZE - 1 ) / CACHE_LINE_SIZE );
            uint32_t xAddress = ( uint32_t ) ( pxDescriptor->pucEthernetBuffer - NETWORK_BUFFER_HEADER_SIZE );
            cache_clean_invalidate_by_addr( xAddress, xlength );
        }
        #endif

        ulResult = gmac_dev_write( &gs_gmac_dev, ( void * ) pxDescriptor->pucEthernetBuffer, ulTransmitSize );

        if( ulResult != GMAC_OK )
        {
            TX_STAT_INCREMENT( tx_write_fail );

            /* On a successful write to GMAC, the ownership of the TX descriptor will eventually get returned back to the network
             * driver and prvEMACHandlerTask will give back the xTXDescriptorSemaphore counting semaphore. In this case however,
             * writing to the GMAC failed, so there will be no EMAC_IF_TX_EVENT sent to prvEMACHandlerTask and the counting
             * semaphore will not be given back. Give it back now. */
            xSemaphoreGive( xTXDescriptorSemaphore );
        }

        #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
        {
            if( ulResult == GMAC_OK )
            {
                /* The message was send in a zero-copy way.
                 * It will be released after a successful transmission. */
                bReleaseAfterSend = pdFALSE;
            }
        }
        #endif /* ipconfigZERO_COPY_TX_DRIVER */
        /* Not interested in a call-back after TX. */
        iptraceNETWORK_INTERFACE_TRANSMIT();
    } while( ipFALSE_BOOL );

    if( bReleaseAfterSend != pdFALSE )
    {
        vReleaseNetworkBufferAndDescriptor( pxDescriptor );
    }

    return pdTRUE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvGMACInit( NetworkInterface_t * pxInterface )
{
    NetworkEndPoint_t * pxEndPoint;
    size_t uxIndex;

    gmac_options_t gmac_option;

    gmac_enable_management( GMAC, true );
    /* Enable further GMAC maintenance. */
    GMAC->GMAC_NCR |= GMAC_NCR_MPE;

    memset( &gmac_option, '\0', sizeof( gmac_option ) );

    /* Note that 'gmac_option.uc_copy_all_frame' is false, do not copy all frames.
     * And 'gmac_option.uc_no_boardcast' is false, meaning that broadcast is received.
     * 'boardcast' is a typo. */

    /* Note that the gmac_option holds the MAC address that will be enabled for reception.
     * Leave the MAC as zeros. It will be handled properly further down.*/

    gs_gmac_dev.p_hw = GMAC;
    gmac_dev_init( GMAC, &gs_gmac_dev, &gmac_option );

    NVIC_SetPriority( GMAC_IRQn, configMAC_INTERRUPT_PRIORITY );
    NVIC_EnableIRQ( GMAC_IRQn );

    /* The call to gmac_dev_init() above writes gmac_option.uc_mac_addr to the first
     * MAC address register by calling gmac_set_address( GMAC, 0, p_opt->uc_mac_addr )
     * This driver however uses the prvAddAllowedMACAddress() to manipulate the specific match
     * and hash match registers, so undo the setting of the first specific MAC register. */

    /* Disable all specific MAC address match registers */
    for( uxIndex = 0; uxIndex < GMACSA_NUMBER; uxIndex++ )
    {
        /* Writing the bottom register disable this specific MAC register. */
        GMAC->GMAC_SA[ uxIndex ].GMAC_SAB = 0;
    }

    /* Clear the hash table for unicast/multicast MAC addresses. */
    gmac_set_hash( GMAC, 0, 0 );

    /* gmac_enable_multicast_hash() sets the wrong bit, don't use it.
     * There is also no equivalent for unicasts, so manipulate the bits directly.
     * For now, disable both multicast and unicast hash matching.
     * The appropriate bits will be set later */
    MULTICAST_HASH_DISABLE( GMAC );
    UNICAST_HASH_DISABLE( GMAC );

    /* Go through all end-points of the interface and add their MAC addresses to the GMAC. */
    for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
         pxEndPoint != NULL;
         pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
    {
        prvAddAllowedMACAddress( pxInterface, pxEndPoint->xMACAddress.ucBytes );
    }

    #if ( ipconfigIS_ENABLED( ipconfigUSE_IPv4 ) )
        #if ( ipconfigUSE_LLMNR == ipconfigENABLE )
            prvAddAllowedMACAddress( pxInterface, xLLMNR_MacAddress.ucBytes );
        #endif /* ipconfigUSE_LLMNR */

        #if ( ipconfigUSE_MDNS == ipconfigENABLE )
            prvAddAllowedMACAddress( pxInterface, xMDNS_MacAddress.ucBytes );
        #endif /* ipconfigUSE_MDNS */
    #endif /* ipconfigIS_ENABLED( ipconfigUSE_IPv4 */

    #if ( ipconfigUSE_IPv6 == ipconfigENABLE )
    {
        /* Register the Link-Local All-Nodes address */
        /* FF02::1 --> 33-33-00-00-00-01 */
        prvAddAllowedMACAddress( pxInterface, pcLOCAL_ALL_NODES_MULTICAST_MAC );

        #if ( ipconfigUSE_LLMNR == ipconfigENABLE )
        {
            prvAddAllowedMACAddress( pxInterface, xLLMNR_MacAddressIPv6.ucBytes );
        }
        #endif /* ipconfigUSE_LLMNR */

        #if ( ipconfigUSE_MDNS == ipconfigENABLE )
        {
            prvAddAllowedMACAddress( pxInterface, xMDNS_MACAddressIPv6.ucBytes );
        }
        #endif /* ipconfigUSE_MDNS */
    }
    #endif /* ipconfigUSE_IPv6 */

    {
        /* Set MDC clock divider. */
        gmac_set_mdc_clock( GMAC, sysclk_get_peripheral_hz() );

        vPhyInitialise( &xPhyObject, xPHY_Read, xPHY_Write );
        xPhyDiscover( &xPhyObject );
        xPhyConfigure( &xPhyObject, &xPHYProperties );

        /* For a reset / reconfigure of the EMAC. */
        prvEthernetUpdateConfig( pdTRUE );

        /* Select Media Independent Interface type */
        #if ( SAME70 != 0 )
        {
            /* Selecting RMII mode. */
            GMAC->GMAC_UR &= ~GMAC_UR_RMII;
        }
        #else
        {
            gmac_select_mii_mode( GMAC, ETH_PHY_MODE );
        }
        #endif

        gmac_enable_transmit( GMAC, true );
        gmac_enable_receive( GMAC, true );
    }

    gmac_enable_management( GMAC, false );
    /* Disable further GMAC maintenance. */
    GMAC->GMAC_NCR &= ~GMAC_NCR_MPE;

    return 1;
}
/*-----------------------------------------------------------*/

static uint16_t prvGenerateCRC16( const uint8_t * pucAddress )
{
    uint16_t usSum;
    uint16_t usValues[ ipMAC_ADDRESS_LENGTH_BYTES ];
    size_t x;

    /* Get 6 shorts. */
    for( x = 0; x < ipMAC_ADDRESS_LENGTH_BYTES; x++ )
    {
        usValues[ x ] = ( uint16_t ) pucAddress[ x ];
    }

    /* Apply the hash function. */
    usSum = ( usValues[ 0 ] >> 6 ) ^ usValues[ 0 ];
    usSum ^= ( usValues[ 1 ] >> 4 ) ^ ( usValues[ 1 ] << 2 );
    usSum ^= ( usValues[ 2 ] >> 2 ) ^ ( usValues[ 2 ] << 4 );
    usSum ^= ( usValues[ 3 ] >> 6 ) ^ usValues[ 3 ];
    usSum ^= ( usValues[ 4 ] >> 4 ) ^ ( usValues[ 4 ] << 2 );
    usSum ^= ( usValues[ 5 ] >> 2 ) ^ ( usValues[ 5 ] << 4 );

    usSum &= GMAC_ADDRESS_HASH_MASK;
    return usSum;
}
/*-----------------------------------------------------------*/

/**
 * @brief Adds a multicast mac address to the GMAC's registers. Internally, this function
 * keeps track of the 4 specific MAC address register as well as the hash match register.
 * It keeps a counter for how many times the specific registers have been used as well as how
 * many times every bit in the GMAC hash register has been hit. This way, if two multicast MAC
 * addresses map to the same GMAC hash register bit, the internal counter will hold the value of 2.
 * Calling prvRemoveAllowedMACAddress for one of those MACs will only decrement the counter, but
 * the bit in the GMAC hash register will remain set until a call to prvRemoveAllowedMACAddress for
 * the other MAC causes the counter to reach 0 and the bit to get cleared. Same logic applies to
 * the specific match registers.
 *
 * @param[in] pucMacAddress: A pointer to the multicast MAC Address in question.
 */
static void prvAddAllowedMACAddress( struct xNetworkInterface * pxInterface,
                                     const uint8_t * pucMacAddress )
{
    /* Design rationale and implementation details:
     * Most network infrastructure ( both wired and wireless ) will do a pretty good job in
     * limiting how much unicast MAC traffic we receive. In general, we will only be sent
     * unicast frames that are destined to MAC addresses that we send from. Because of this,
     * the EMAC doesn't need to do heavy filtering for unicasts.
     * On the other hand, most networking hardware ( both wired and wireless ) will happily
     * send us all traffic that has a multicast destination MAC. It is therefor much more
     * important to filter out unnecessary multicast traffic. Ideally, we could explicitly
     * allow all multicast MAC addresses that the TCP stack requests, however, this EMAC controller
     * only has 4 specific MAC match registers. Beyond that, we can use the hash match register to
     * match unicast and/or multicast addresses. Every bit in the hash match register corresponds
     * to millions of MAC addresses, so the usage of the hash register should be kept to a minimum.
     * As a side note, setting all bits in the hash register is somewhat equivalent to
     * promiscuous mode and is therefor not very useful.
     * Due to the filtering nature of network infrastructure, It would make sense to use the
     * specific match registers for matching multicasts and use the hash match register for unicasts
     * because they are already well filtered. Due to the EMAC hardware limitations, such approach
     * is only feasible if very few ( no more than 4 ) multicast MAC addresses need to be received.
     *
     * TCP stack multicast requirements notes:
     * - IPv4 only, no IGMP, no LLMNR, no mDNS - 0 multicasts required.
     * - IPv4 only: IGMP 224.0.0.1, LLMNR 224.0.0.252, mDNS 224.0.0.251 - total 3 multicasts required.
     * - IPv6 only, no MLD, no LLMNR, no mDNS - 1 multicast required per IPv6 endpoint for the
     *   solicited node multicast address + all nodes ff02::1 - total of at least 2 multicasts required.
     * - IPv4+v6 with IGMP, LLMNR and mDNS = 6 + 1 for every IPv6 end-point - 7+ multicasts required.
     *
     * This implementation is optimized for use cases where a lot of multicasts and very few unicast
     * MAC addresses need to be received. This implementation prioritizes the use of the exact match
     * register and once used up, begins utilizing the hash match register. It is highly recommended
     * that all the end-points of an interface use the same unicast MAC. If for some reason, the TCP
     * stack adds too many unicast MAC addresses, the hash register will be used for both unicasts
     * and multicasts which will result in a lot of bits being set and consequently very poor
     * multicast filtering.
     * One limitation of this implementation is that once it enables unicast or multicast hash
     * matching, it will never disable them. This should be acceptable for a fairly static system
     * and was chosen because it minimizes RAM usage by not keeping a list of all MAC addresses
     * that the TCP stack has requested. One optimization that this implementation makes is as follows:
     * If the MAC being added is already covered by the hash match register and that specific
     * matching is already enabled, we add that new MAC to the hash register even if there is an
     * empty specific match register available. The reasoning is that the hash match register is already
     * allowing this new MAC address to be received and there is no reason to waste a specific
     * match register.
     * The implementation keep counts of how many times the individual hash bits and specific match
     * registers have been used. */

    /* Note: Only called from the IPTask, so no thread-safety is required. */
    uint8_t ucHashBit;
    size_t uxIndex, uxEmptyIndex;

    uint32_t ulSAB, ulSAT;

    configASSERT( pucMacAddress != NULL );
    configASSERT( pxInterface != NULL ); /* Not used, but the stack should not be sending us NULL parameters. */

    ucHashBit = prvGenerateCRC16( pucMacAddress );
    FreeRTOS_debug_printf( "prvAddAllowedMACAddress: pxIf %p, %02X-%02X-%02X-%02X-%02X-%02X hash-bit %u",
                           pxInterface,
                           pucMacAddress[ 0 ], pucMacAddress[ 1 ], pucMacAddress[ 2 ], pucMacAddress[ 3 ], pucMacAddress[ 4 ], pucMacAddress[ 5 ],
                           ucHashBit );

    /* Calculate what the specific match registers would look like for this MAC address so that
     * we can check if this MAC address is already present in one of the specific match registers. */
    ulSAB = ( ( ( uint32_t ) pucMacAddress[ 3 ] ) << 24 ) |
            ( ( ( uint32_t ) pucMacAddress[ 2 ] ) << 16 ) |
            ( ( ( uint32_t ) pucMacAddress[ 1 ] ) << 8 ) |
            ( ( uint32_t ) pucMacAddress[ 0 ] );
    ulSAT = ( ( ( uint32_t ) pucMacAddress[ 5 ] ) << 8 ) | ( ( uint32_t ) pucMacAddress[ 4 ] );

    /* Always try to find a match within the specific match registers first. */
    uxEmptyIndex = GMACSA_NUMBER;

    for( uxIndex = 0; uxIndex < GMACSA_NUMBER; uxIndex++ )
    {
        if( prvSpecificMatchCounters[ uxIndex ] > 0U )
        {
            /* This specific match register is being used. Check if the address is the same. */
            if( ( ulSAB == GMAC->GMAC_SA[ uxIndex ].GMAC_SAB ) && ( ulSAT == GMAC->GMAC_SA[ uxIndex ].GMAC_SAT ) )
            {
                /* Exact match! Increment the counter and leave. As with the hash counters, make sure we don't overflow. */
                if( prvSpecificMatchCounters[ uxIndex ] < UINT8_MAX )
                {
                    prvSpecificMatchCounters[ uxIndex ]++;
                }

                /* FreeRTOS_debug_printf("prvAddAllowedMACAddress: EXACT MATCH at %u, new counter %u", uxIndex, prvSpecificMatchCounters[ uxIndex ] ); */
                break;
            }
            else
            {
                /* No match. Do nothing. */
            }
        }
        else
        {
            /* This specific match register is empty.
             * Keep track of the first empty register in case we need to use it. */
            if( uxEmptyIndex >= GMACSA_NUMBER )
            {
                uxEmptyIndex = uxIndex;
            }
            else
            {
                /* We have already found an empty specific match register. Do nothing. */
            }
        }
    } /* for( uxIndex = 0; uxIndex < GMACSA_NUMBER; uxIndex++ ) */

    /* do{}while(0) to allow the use of break statements. */
    do
    {
        if( uxIndex < GMACSA_NUMBER )
        {
            /* An exact match was found in the for(;;) loop above. Do nothing. */
            break;
        }

        /* No exact match found in the specific match registers.
         * Is one of them empty so we can add the MAC there? */
        if( uxEmptyIndex < GMACSA_NUMBER )
        {
            /* There is an empty slot in the specific match registers. Using this empty slot should
             * be a priority, except if the hash register already covers the MAC address we were given
             * and the type of address we were given ( unicast/multicast ). If any of those are not
             * met, simply add to the empty slot we found in the specific match registers. */
            if( ( ( MAC_IS_MULTICAST( pucMacAddress ) ) && ( MULTICAST_HASH_IS_DISABLED( GMAC ) ) ) ||
                ( ( MAC_IS_UNICAST( pucMacAddress ) ) && ( UNICAST_HASH_IS_DISABLED( GMAC ) ) ) ||
                ( prvAddressHashCounters[ ucHashBit ] == 0U ) /* hash matching doesn't cover this address yet. */ )
            {
                /* In all cases above, simply add the MAC address to the empty specific match register. */
                gmac_set_address( GMAC, uxEmptyIndex, pucMacAddress );
                prvSpecificMatchCounters[ uxEmptyIndex ] = 1U;
                /* FreeRTOS_debug_printf("prvAddAllowedMACAddress: ADD at %u, new counter %u", uxEmptyIndex, prvSpecificMatchCounters[ uxEmptyIndex ] ); */
                break;
            }
        }

        /* If we reach here, we need to add the MAC address we were given to the hash match register. */
        /* If the bin counter corresponding to this mac address is already non-zero, */
        /* a multicast address with the same hash has already been added, so there's nothing more to do. */
        if( prvAddressHashCounters[ ucHashBit ] == 0 )
        {
            /* This bin counter is zero, so this is the first time we are registering a MAC with this hash
             * and we need to update the hash register. */
            prvAddressHashBitMask |= ( uint64_t ) ( ( uint64_t ) 1 << ucHashBit );
            gmac_set_hash64( GMAC, prvAddressHashBitMask );
        }

        /* Increment the counter, but make sure we don't overflow it. */
        if( prvAddressHashCounters[ ucHashBit ] < UINT8_MAX )
        {
            prvAddressHashCounters[ ucHashBit ]++;
        }

        /* Make sure the unicast or multicast hash enable bits are set properly. */
        if( ( MAC_IS_UNICAST( pucMacAddress ) ) && ( UNICAST_HASH_IS_DISABLED( GMAC ) ) )
        {
            /* This is the first ever unicast address added to the hash register. Enable unicast matching. */
            UNICAST_HASH_ENABLE( GMAC );
        }
        else if( ( MAC_IS_MULTICAST( pucMacAddress ) ) && ( MULTICAST_HASH_IS_DISABLED( GMAC ) ) )
        {
            /* This is the first ever multicast address added to the hash register. Enable multicast matching. */
            MULTICAST_HASH_ENABLE( GMAC );
        }
        else
        {
            /* The proper unicast / multicast matching is already enabled. Do nothing. */
        }
    } while( pdFALSE );
}

/**
 * @brief Removes a MAC address from the GMAC's specific match or hash match registers.
 *
 * @param[in] pucMacAddress: A pointer to the multicast MAC Address in question.
 */
static void prvRemoveAllowedMACAddress( struct xNetworkInterface * pxInterface,
                                        const uint8_t * pucMacAddress )
{
    /* Note: Only called from the IPTask, so no thread-safety is required. */
    uint8_t ucHashBit;
    uint32_t ulSAB, ulSAT;
    size_t uxIndex;

    configASSERT( pucMacAddress != NULL );
    configASSERT( pxInterface != NULL ); /* Not used, but the stack should not be sending us NULL parameters. */

    ucHashBit = prvGenerateCRC16( pucMacAddress );
    FreeRTOS_debug_printf( "prvRemoveAllowedMACAddress: pxIf %p, %02X-%02X-%02X-%02X-%02X-%02X hash-bit %u",
                           pxInterface,
                           pucMacAddress[ 0 ], pucMacAddress[ 1 ], pucMacAddress[ 2 ], pucMacAddress[ 3 ], pucMacAddress[ 4 ], pucMacAddress[ 5 ],
                           ucHashBit );

    /* Calculate what the specific match registers would look like for this MAC address so that
     * we can check if this MAC address is already present in one of the specific match registers. */
    ulSAB = ( ( ( uint32_t ) pucMacAddress[ 3 ] ) << 24 ) |
            ( ( ( uint32_t ) pucMacAddress[ 2 ] ) << 16 ) |
            ( ( ( uint32_t ) pucMacAddress[ 1 ] ) << 8 ) |
            ( ( uint32_t ) pucMacAddress[ 0 ] );
    ulSAT = ( ( ( uint32_t ) pucMacAddress[ 5 ] ) << 8 ) | ( ( uint32_t ) pucMacAddress[ 4 ] );

    /* Check the specific match registers first. */
    for( uxIndex = 0; uxIndex < GMACSA_NUMBER; uxIndex++ )
    {
        if( ( prvSpecificMatchCounters[ uxIndex ] > 0U ) && ( ulSAB == GMAC->GMAC_SA[ uxIndex ].GMAC_SAB ) && ( ulSAT == GMAC->GMAC_SA[ uxIndex ].GMAC_SAT ) )
        {
            /* Exact match! Decrement the counter unless it's maxed out. */
            if( prvSpecificMatchCounters[ uxIndex ] < UINT8_MAX )
            {
                prvSpecificMatchCounters[ uxIndex ]--;
            }

            if( prvSpecificMatchCounters[ uxIndex ] == 0 )
            {
                /* FreeRTOS_debug_printf("prvAddAllowedMACAddress: EXACT MATCH at %u, INDEX DISABLED", uxIndex ); */
                /* This specific match register counter is now zero. Disable it by writing it in reverse order. */
                GMAC->GMAC_SA[ uxIndex ].GMAC_SAT = 0U; /* This is not needed, just clears out the top register.*/
                GMAC->GMAC_SA[ uxIndex ].GMAC_SAB = 0U; /* Writing the bottom register disables this specific match register. */
            }
            else
            {
                /* FreeRTOS_debug_printf("prvAddAllowedMACAddress: EXACT MATCH at %u, new counter %u", uxIndex, prvSpecificMatchCounters[ uxIndex ] ); */
            }

            break;
        }
    }

    if( uxIndex >= GMACSA_NUMBER )
    {
        /* The MAC address was not found amongst the specific match registers, check the hash register. */
        if( prvAddressHashCounters[ ucHashBit ] > 0 )
        {
            /* If so many multicasts with the same hash were added that the bin counter was maxed out, */
            /* we don't really know how many times we can decrement before actually unregistering this hash. */
            /* Because of this, if the bin counter ever maxes out, we can never unregister the hash. */
            if( prvAddressHashCounters[ ucHashBit ] < UINT8_MAX )
            {
                prvAddressHashCounters[ ucHashBit ]--;

                if( 0 == prvAddressHashCounters[ ucHashBit ] )
                {
                    uint64_t hash = ( uint64_t ) ( ( uint64_t ) 1 << ucHashBit );
                    prvAddressHashBitMask &= ~hash;
                    gmac_set_hash64( GMAC, prvAddressHashBitMask );
                }
            }
        }
    }
    else
    {
        /* Nothing left to do. */
    }
}
/*-----------------------------------------------------------*/

static void prvEthernetUpdateConfig( BaseType_t xForce )
{
    FreeRTOS_printf( ( "prvEthernetUpdateConfig: LS mask %02lX Force %d\n",
                       xPhyObject.ulLinkStatusMask,
                       ( int ) xForce ) );

    if( ( xForce != pdFALSE ) || ( xPhyObject.ulLinkStatusMask != 0 ) )
    {
        #if ( ipconfigETHERNET_AN_ENABLE != 0 )
        {
            UBaseType_t uxWasEnabled;

            /* Restart the auto-negotiation. */
            uxWasEnabled = ( GMAC->GMAC_NCR & GMAC_NCR_MPE ) != 0u;

            if( uxWasEnabled == 0u )
            {
                /* Enable further GMAC maintenance. */
                GMAC->GMAC_NCR |= GMAC_NCR_MPE;
            }

            xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) );

            /* Configure the MAC with the Duplex Mode fixed by the
             * auto-negotiation process. */
            if( xPhyObject.xPhyProperties.ucDuplex == PHY_DUPLEX_FULL )
            {
                gmac_enable_full_duplex( GMAC, pdTRUE );
            }
            else
            {
                gmac_enable_full_duplex( GMAC, pdFALSE );
            }

            /* Configure the MAC with the speed fixed by the
             * auto-negotiation process. */
            if( xPhyObject.xPhyProperties.ucSpeed == PHY_SPEED_10 )
            {
                gmac_set_speed( GMAC, pdFALSE );
            }
            else
            {
                gmac_set_speed( GMAC, pdTRUE );
            }

            if( uxWasEnabled == 0u )
            {
                /* Enable further GMAC maintenance. */
                GMAC->GMAC_NCR &= ~GMAC_NCR_MPE;
            }
        }
        #else /* if ( ipconfigETHERNET_AN_ENABLE != 0 ) */
        {
            if( xPHYProperties.ucDuplex == PHY_DUPLEX_FULL )
            {
                xPhyObject.xPhyPreferences.ucDuplex = PHY_DUPLEX_FULL;
                gmac_enable_full_duplex( GMAC, pdTRUE );
            }
            else
            {
                xPhyObject.xPhyPreferences.ucDuplex = PHY_DUPLEX_HALF;
                gmac_enable_full_duplex( GMAC, pdFALSE );
            }

            if( xPHYProperties.ucSpeed == PHY_SPEED_100 )
            {
                xPhyObject.xPhyPreferences.ucSpeed = PHY_SPEED_100;
                gmac_set_speed( GMAC, pdTRUE );
            }
            else
            {
                xPhyObject.xPhyPreferences.ucSpeed = PHY_SPEED_10;
                gmac_set_speed( GMAC, pdFALSE );
            }

            xPhyObject.xPhyPreferences.ucMDI_X = PHY_MDIX_AUTO;

            /* Use predefined (fixed) configuration. */
            xPhyFixedValue( &xPhyObject, xPhyGetMask( &xPhyObject ) );
        }
        #endif /* if ( ipconfigETHERNET_AN_ENABLE != 0 ) */
    }
}
/*-----------------------------------------------------------*/

void vGMACGenerateChecksum( uint8_t * pucBuffer,
                            size_t uxLength )
{
    ProtocolPacket_t * xProtPacket = ( ProtocolPacket_t * ) pucBuffer;

    /* The SAM4E has problems offloading checksums for transmission.
     * The SAME70 does not set the CRC for ICMP or IGMP packets. */

    if( xProtPacket->xICMPPacket.xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE )
    {
        #if ( SAME70 != 0 )
            if( ( xProtPacket->xICMPPacket.xIPHeader.ucProtocol != ipPROTOCOL_UDP ) &&
                ( xProtPacket->xICMPPacket.xIPHeader.ucProtocol != ipPROTOCOL_TCP ) )
        #endif
        {
            IPHeader_t * pxIPHeader = &( xProtPacket->xTCPPacket.xIPHeader );

            /* Calculate the IP header checksum. */
            pxIPHeader->usHeaderChecksum = 0x00;
            pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
            pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );

            /* Calculate the TCP checksum for an outgoing packet. */
            usGenerateProtocolChecksum( pucBuffer, uxLength, pdTRUE );
        }
    }
    else if( xProtPacket->xICMPPacket.xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
    {
        ICMPPacket_IPv6_t * xProtPacket16 = ( ICMPPacket_IPv6_t * ) pucBuffer;
        IPHeader_IPv6_t * pxIPHeader = &( xProtPacket16->xIPHeader );

        #if ( SAME70 != 0 )
            if( ( pxIPHeader->ucNextHeader != ipPROTOCOL_UDP ) &&
                ( pxIPHeader->ucNextHeader != ipPROTOCOL_TCP ) )
        #endif
        {
            /* Calculate the TCP checksum for an outgoing packet. */
            usGenerateProtocolChecksum( pucBuffer, uxLength, pdTRUE );
        }
    }
    else
    {
        /* Possibly ARP. */
    }
}
/*-----------------------------------------------------------*/

static uint32_t prvEMACRxPoll( void )
{
    unsigned char * pucUseBuffer;
    uint32_t ulReceiveCount, ulResult, ulReturnValue = 0;
    static NetworkBufferDescriptor_t * pxNextNetworkBufferDescriptor = NULL;
    const UBaseType_t xMinDescriptorsToLeave = 2UL;
    const TickType_t xBlockTime = pdMS_TO_TICKS( 100UL );
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
    uint8_t * pucDMABuffer = NULL;

    for( ; ; )
    {
        BaseType_t xRelease = pdFALSE;

        /* If pxNextNetworkBufferDescriptor was not left pointing at a valid
         * descriptor then allocate one now. */
        if( ( pxNextNetworkBufferDescriptor == NULL ) && ( uxGetNumberOfFreeNetworkBuffers() > xMinDescriptorsToLeave ) )
        {
            pxNextNetworkBufferDescriptor = pxGetNetworkBufferWithDescriptor( GMAC_RX_UNITSIZE, xBlockTime );
        }

        if( pxNextNetworkBufferDescriptor != NULL )
        {
            /* Point pucUseBuffer to the buffer pointed to by the descriptor. */
            pucUseBuffer = ( unsigned char * ) ( pxNextNetworkBufferDescriptor->pucEthernetBuffer - ipconfigPACKET_FILLER_SIZE );
        }
        else
        {
            /* As long as pxNextNetworkBufferDescriptor is NULL, the incoming
             * messages will be flushed and ignored. */
            pucUseBuffer = NULL;
        }

        /* Read the next packet from the hardware into pucUseBuffer. */
        ulResult = gmac_dev_read( &gs_gmac_dev, pucUseBuffer, GMAC_RX_UNITSIZE, &ulReceiveCount, &pucDMABuffer );

        if( ( ulResult != GMAC_OK ) || ( ulReceiveCount == 0 ) )
        {
            /* No data from the hardware. */
            break;
        }

        if( pxNextNetworkBufferDescriptor == NULL )
        {
            /* Data was read from the hardware, but no descriptor was available
             * for it, so it will be dropped. */
            iptraceETHERNET_RX_EVENT_LOST();
            continue;
        }

        iptraceNETWORK_INTERFACE_RECEIVE();
        #if ( ipconfigZERO_COPY_RX_DRIVER != 0 )
        {
            pxNextNetworkBufferDescriptor = pxPacketBuffer_to_NetworkBuffer( pucDMABuffer );

            if( pxNextNetworkBufferDescriptor == NULL )
            {
                /* Strange: can not translate from a DMA buffer to a Network Buffer. */
                break;
            }
        }
        #endif /* ipconfigZERO_COPY_RX_DRIVER */

        pxNextNetworkBufferDescriptor->xDataLength = ( size_t ) ulReceiveCount;
        pxNextNetworkBufferDescriptor->pxInterface = pxMyInterface;
        pxNextNetworkBufferDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint( pxMyInterface, pxNextNetworkBufferDescriptor->pucEthernetBuffer );

        if( pxNextNetworkBufferDescriptor->pxEndPoint == NULL )
        {
            FreeRTOS_printf( ( "NetworkInterface: can not find a proper endpoint\n" ) );
            xRelease = pdTRUE;
        }
        else
        {
            xRxEvent.pvData = ( void * ) pxNextNetworkBufferDescriptor;

            if( xSendEventStructToIPTask( &xRxEvent, xBlockTime ) != pdTRUE )
            {
                /* xSendEventStructToIPTask() timed out. Release the descriptor. */
                FreeRTOS_printf( ( "prvEMACRxPoll: Can not queue a packet!\n" ) );
                xRelease = pdTRUE;
            }
        }

        /* Release the descriptor in case it can not be delivered. */
        if( xRelease == pdTRUE )
        {
            /* The buffer could not be sent to the stack so must be released
             * again. */
            vReleaseNetworkBufferAndDescriptor( pxNextNetworkBufferDescriptor );
            iptraceETHERNET_RX_EVENT_LOST();
        }

        /* Now the buffer has either been passed to the IP-task,
         * or it has been released in the code above. */
        pxNextNetworkBufferDescriptor = NULL;
        ulReturnValue++;
    }

    return ulReturnValue;
}
/*-----------------------------------------------------------*/

volatile UBaseType_t uxLastMinBufferCount = 0;
#if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
    volatile UBaseType_t uxLastMinQueueSpace;
#endif
volatile UBaseType_t uxCurrentSemCount;
volatile UBaseType_t uxLowestSemCount;

static void vCheckBuffersAndQueue( void )
{
    static UBaseType_t uxCurrentCount;

    #if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
    {
        uxCurrentCount = uxGetMinimumIPQueueSpace();

        if( uxLastMinQueueSpace != uxCurrentCount )
        {
            /* The logging produced below may be helpful
             * while tuning +TCP: see how many buffers are in use. */
            uxLastMinQueueSpace = uxCurrentCount;
            FreeRTOS_printf( ( "Queue space: lowest %lu\n", uxCurrentCount ) );
        }
    }
    #endif /* ipconfigCHECK_IP_QUEUE_SPACE */
    uxCurrentCount = uxGetMinimumFreeNetworkBuffers();

    if( uxLastMinBufferCount != uxCurrentCount )
    {
        /* The logging produced below may be helpful
         * while tuning +TCP: see how many buffers are in use. */
        uxLastMinBufferCount = uxCurrentCount;
        FreeRTOS_printf( ( "Network buffers: %lu lowest %lu\n",
                           uxGetNumberOfFreeNetworkBuffers(), uxCurrentCount ) );
    }

    if( xTXDescriptorSemaphore != NULL )
    {
        uxCurrentSemCount = uxSemaphoreGetCount( xTXDescriptorSemaphore );

        if( uxLowestSemCount > uxCurrentSemCount )
        {
            uxLowestSemCount = uxCurrentSemCount;
            FreeRTOS_printf( ( "TX DMA buffers: lowest %lu\n", uxLowestSemCount ) );
        }
    }
}
/*-----------------------------------------------------------*/

extern uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * NETWORK_BUFFER_SIZE ];
void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    uint8_t * ucRAMBuffer = ucNetworkPackets;
    uint32_t ulIndex;

    for( ulIndex = 0; ulIndex < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ulIndex++ )
    {
        pxNetworkBuffers[ ulIndex ].pucEthernetBuffer = ucRAMBuffer + ipBUFFER_PADDING;
        *( ( unsigned * ) ucRAMBuffer ) = ( unsigned ) ( &( pxNetworkBuffers[ ulIndex ] ) );
        ucRAMBuffer += NETWORK_BUFFER_SIZE;
    }

    cache_clean_invalidate();
}
/*-----------------------------------------------------------*/

static void prvEMACHandlerTask( void * pvParameters )
{
    UBaseType_t uxCount;

    uxLowestSemCount = GMAC_TX_BUFFERS + 1;

    #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
        NetworkBufferDescriptor_t * pxBuffer;
    #endif
    uint8_t * pucBuffer;
    BaseType_t xResult = 0;
    const TickType_t ulMaxBlockTime = pdMS_TO_TICKS( EMAC_MAX_BLOCK_TIME_MS );
    uint32_t ulISREvents = 0U;

    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;

    configASSERT( xEMACTaskHandle );

    for( ; ; )
    {
        xResult = 0;
        vCheckBuffersAndQueue();

        /* Wait for a new event or a time-out. */
        xTaskNotifyWait( 0U,                /* ulBitsToClearOnEntry */
                         EMAC_IF_ALL_EVENT, /* ulBitsToClearOnExit */
                         &( ulISREvents ),  /* pulNotificationValue */
                         ulMaxBlockTime );

        if( ( ulISREvents & EMAC_IF_RX_EVENT ) != 0 )
        {
            /* Wait for the EMAC interrupt to indicate that another packet has been
             * received. */
            xResult = prvEMACRxPoll();
        }

        if( ( ulISREvents & EMAC_IF_TX_EVENT ) != 0 )
        {
            while( xQueueReceive( xTxBufferQueue, &pucBuffer, 0 ) != pdFALSE )
            {
                #if ( ipconfigZERO_COPY_TX_DRIVER != 0 )
                {
                    pxBuffer = pxPacketBuffer_to_NetworkBuffer( pucBuffer );

                    if( pxBuffer != NULL )
                    {
                        vReleaseNetworkBufferAndDescriptor( pxBuffer );
                        TX_STAT_INCREMENT( tx_release_ok );
                    }
                    else
                    {
                        TX_STAT_INCREMENT( tx_release_bad );
                    }
                }
                #else /* if ( ipconfigZERO_COPY_TX_DRIVER != 0 ) */
                {
                    TX_STAT_INCREMENT( tx_release_ok );
                }
                #endif /* if ( ipconfigZERO_COPY_TX_DRIVER != 0 ) */
                uxCount = uxQueueMessagesWaiting( ( QueueHandle_t ) xTXDescriptorSemaphore );

                if( uxCount < ( GMAC_TX_BUFFERS - 1 ) )
                {
                    /* Tell the counting semaphore that one more TX descriptor is available. */
                    xSemaphoreGive( xTXDescriptorSemaphore );
                }
            }
        }

        if( ( ulISREvents & EMAC_IF_ERR_EVENT ) != 0 )
        {
            /* Future extension: logging about errors that occurred. */
        }

        gmac_enable_management( GMAC, true );

        if( xPhyCheckLinkStatus( &xPhyObject, xResult ) != 0 )
        {
            /* Something has changed to a Link Status, need re-check. */
            prvEthernetUpdateConfig( pdFALSE );
        }

        gmac_enable_management( GMAC, false );
    }
}
/*-----------------------------------------------------------*/
