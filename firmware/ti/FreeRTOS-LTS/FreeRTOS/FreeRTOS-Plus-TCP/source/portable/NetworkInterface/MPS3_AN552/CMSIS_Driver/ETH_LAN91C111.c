/* *INDENT-OFF* */

/*
 * Copyright (c) 2013-2021 Arm Limited. All rights reserved.
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the License); you may
 * not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an AS IS BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * -----------------------------------------------------------------------
 *
 * $Date:        2. September 2021
 * $Revision:    V1.0
 *
 * Driver:       Driver_ETH_MACn (default: Driver_ETH_MAC0),
 *               Driver_ETH_PHYn (default: Driver_ETH_PHY0)
 * Project:      Ethernet Media Access (MAC) Driver and
 *               Ethernet Physical Layer Transceiver (PHY) Driver
 *               for LAN91C111 on MPS2 platform
 * -----------------------------------------------------------------------
 * Use the following configuration settings in the middleware component
 * to connect to this driver.
 *
 *   Configuration Setting                     Value
 *   ---------------------                     -----
 *   Connect to hardware via Driver_ETH_MAC# = n (default: 0)
 *                           Driver_ETH_PHY# = n (default: 0)
 * -------------------------------------------------------------------- */

/* History:
 *  Version 1.0
 *    Initial release
 */

/* This file is based on
 * https://github.com/ARM-software/CMSIS-Driver/blob/b91908d907b647bd212920e30b383b03809d68e0/ETH/ETH_LAN91C111.c
*/

#include <string.h>

#include <string.h>

#include "SSE300MPS3.h"
#include "Driver_ETH_MAC.h"
#include "Driver_ETH_PHY.h"
#include "ETH_LAN91C111.h"

#include "FreeRTOS.h"

#define ARM_ETH_MAC_DRV_VERSION ARM_DRIVER_VERSION_MAJOR_MINOR(1,0) /* driver version */
#define ARM_ETH_PHY_DRV_VERSION ARM_DRIVER_VERSION_MAJOR_MINOR(1,0) /* driver version */


/* Ethernet MAC driver number (default) */
#ifndef ETH_MAC_NUM
#define ETH_MAC_NUM             0
#endif

/* Ethernet PHY driver number (default) */
#ifndef ETH_PHY_NUM
#define ETH_PHY_NUM             0
#endif

/* Ethernet base address */
#if __CORTEX_M > 7U
/* MPS3 platform */
#define CMSDK_ETH_BASE          ETHERNET_BASE_NS
#else
/* MPS2 platform */
#ifndef CMSDK_ETH_BASE
#define CMSDK_ETH_BASE          (0x40200000UL)
#endif
#endif

/* LAN91C111 Register Access */
#define LREG(object, reg)       (*((object volatile *)(CMSDK_ETH_BASE+reg)))

#ifdef __clang__
    #define __rbit( v )        __builtin_arm_rbit( v )
#elif defined( __GNUC__ )
    #define __rbit( v )        __RBIT( v )
#endif

/* Memory Buffer configuration */
#define ETH_BUF_SIZE        1536        /* Packet Transmit buffer size   */

/* Driver Version */
static const ARM_DRIVER_VERSION MAC_DriverVersion = {
  ARM_ETH_MAC_API_VERSION,
  ARM_ETH_MAC_DRV_VERSION
};

/* Driver Capabilities */
static const ARM_ETH_MAC_CAPABILITIES MAC_DriverCapabilities = {
  0,                                /* checksum_offload_rx_ip4  */
  0,                                /* checksum_offload_rx_ip6  */
  0,                                /* checksum_offload_rx_udp  */
  0,                                /* checksum_offload_rx_tcp  */
  0,                                /* checksum_offload_rx_icmp */
  0,                                /* checksum_offload_tx_ip4  */
  0,                                /* checksum_offload_tx_ip6  */
  0,                                /* checksum_offload_tx_udp  */
  0,                                /* checksum_offload_tx_tcp  */
  0,                                /* checksum_offload_tx_icmp */
  0,                                /* media_interface          */
  1,                                /* mac_address              */
  1,                                /* event_rx_frame           */
  0,                                /* event_tx_frame           */
  0,                                /* event_wakeup             */
  0,                                /* precision_timer          */
  0                                 /* reserved                 */
};

/* Local variables */
static ETH_CTRL  ETH = { 0, 0, 0, 0, 0 };
static uint8_t   tx_buf[ETH_BUF_SIZE];

/* Local functions */
static void MAC_SelectBank (uint8_t bank);
static uint32_t crc32_8bit_rev (uint32_t crc32, uint8_t val);
static uint32_t crc32_data (const uint8_t *data, uint32_t len);
static void output_MDO (uint32_t val, uint32_t num);
static void turnaround_MDO (void);
static uint32_t input_MDI (void);

/**
  \fn          void MAC_SelectBank (uint8_t bank)
  \brief       Select IO register bank.
  \param[in]   bank  register bank
  \return      none.
*/
static void MAC_SelectBank (uint8_t bank) {
  LREG(uint16_t, BSR) = BSR_UPPER | (bank & BSR_MASK);
}

/**
  \fn          uint32_t crc32_8bit_rev (uint32_t crc32, uint8_t val)
  \brief       Calculate 32-bit CRC (Polynom: 0x04C11DB7, data bit-reversed).
  \param[in]   crc32  CRC initial value
  \param[in]   val    Input value
  \return      Calculated CRC value
*/
static uint32_t crc32_8bit_rev (uint32_t crc32, uint8_t val) {
  uint32_t n;

  crc32 ^= __rbit (val);
  for (n = 8; n; n--) {
    if (crc32 & 0x80000000) {
      crc32 <<= 1;
      crc32  ^= 0x04C11DB7;
    } else {
      crc32 <<= 1;
    }
  }
  return (crc32);
}

/**
  \fn          uint32_t crc32_data (const uint8_t *data, uint32_t len)
  \brief       Calculate standard 32-bit Ethernet CRC.
  \param[in]   data  Pointer to buffer containing the data
  \param[in]   len   Data length in bytes
  \return      Calculated CRC value
*/
static uint32_t crc32_data (const uint8_t *data, uint32_t len) {
  uint32_t crc;

  for (crc = 0xFFFFFFFF; len; len--) {
    crc = crc32_8bit_rev (crc, *data++);
  }
  return (crc);
}

/**
  \fn          void output_MDO (uint32_t val, uint32_t n)
  \brief       Output a value to the MII PHY management interface.
  \param[in]   val  Pointer to buffer containing the data
  \param[in]   num  Data length in bytes
  \return      none.
*/
static void output_MDO (uint32_t val, uint32_t num) {
  uint16_t rval;

  for (val <<= (32U - num); num; val <<= 1, num--) {
    rval = MGMT_DEFAULT | MGMT_MDOE;
    if (val & 0x80000000U) {
      rval |= MGMT_MDO;
    }
    LREG(uint16_t, B3_MGMT) = rval;
    LREG(uint16_t, B3_MGMT) = rval | MGMT_MCLK;
    LREG(uint16_t, B3_MGMT) = rval;
  }
}

/**
  \fn          void turnaround_MDO (void)
  \brief       Turnaround MDO is tristated.
  \return      none.
*/
static void turnaround_MDO (void) {
  uint16_t rval = MGMT_DEFAULT;

  LREG(uint16_t, B3_MGMT) = rval;
  LREG(uint16_t, B3_MGMT) = rval | MGMT_MCLK;
  LREG(uint16_t, B3_MGMT) = rval;
}

/**
  \fn          uint32_t input_MDI (void)
  \brief       Input a value from the MII PHY management interface.
  \return      none.
*/
static uint32_t input_MDI (void) {
  uint16_t rval = MGMT_DEFAULT;
  uint32_t i,val = 0U;

  for (i = 0U; i < 16U; i++) {
    LREG(uint16_t, B3_MGMT) = rval;
    LREG(uint16_t, B3_MGMT) = rval | MGMT_MCLK;
    LREG(uint16_t, B3_MGMT) = rval;
    val <<= 1;
    if (LREG(uint16_t, B3_MGMT) & MGMT_MDI) {
      val |= 1U;
    }
  }
  return (val);
}


/* Ethernet Driver functions */

/**
  \fn          ARM_DRIVER_VERSION GetVersion (void)
  \brief       Get driver version.
  \return      \ref ARM_DRIVER_VERSION
*/
static ARM_DRIVER_VERSION MAC_GetVersion (void) {
  return MAC_DriverVersion;
}

/**
  \fn          ARM_ETH_MAC_CAPABILITIES GetCapabilities (void)
  \brief       Get driver capabilities.
  \return      \ref ARM_ETH_MAC_CAPABILITIES
*/
static ARM_ETH_MAC_CAPABILITIES MAC_GetCapabilities (void) {
  return MAC_DriverCapabilities;
}

/**
  \fn          int32_t Initialize (ARM_ETH_MAC_SignalEvent_t cb_event)
  \brief       Initialize Ethernet MAC Device.
  \param[in]   cb_event  Pointer to \ref ARM_ETH_MAC_SignalEvent
  \return      \ref execution_status
*/
static int32_t MAC_Initialize (ARM_ETH_MAC_SignalEvent_t cb_event) {

  if (ETH.flags & ETH_FLAG_INIT) {
    return ARM_DRIVER_OK;
  }

  /* Clear control structure */
  memset (&ETH, 0, sizeof (ETH_CTRL));

  ETH.cb_event = cb_event;
  ETH.flags    = ETH_FLAG_INIT;

  return ARM_DRIVER_OK;
}

/**
  \fn          int32_t Uninitialize (void)
  \brief       De-initialize Ethernet MAC Device.
  \return      \ref execution_status
*/
static int32_t MAC_Uninitialize (void) {

  ETH.flags = 0U;

  return ARM_DRIVER_OK;
}

/**
  \fn          int32_t PowerControl (ARM_POWER_STATE state)
  \brief       Control Ethernet MAC Device Power.
  \param[in]   state  Power state
  \return      \ref execution_status
*/
static int32_t MAC_PowerControl (ARM_POWER_STATE state) {
  uint32_t val;

  switch ((int32_t)state) {
    case ARM_POWER_OFF:
      /* Disable interrupts */
      NVIC_DisableIRQ(ETHERNET_IRQn);

      /* Power down */
      MAC_SelectBank (1);
      LREG(uint16_t, B1_CR) = CR_DEFAULT;

      ETH.flags &= ~ETH_FLAG_POWER;
      break;

    case ARM_POWER_LOW:
      return ARM_DRIVER_ERROR_UNSUPPORTED;

    case ARM_POWER_FULL:
      if ((ETH.flags & ETH_FLAG_INIT) == 0) {
        return ARM_DRIVER_ERROR;
      }
      if (ETH.flags & ETH_FLAG_POWER) {
        return ARM_DRIVER_OK;
      }

      /* Check device ID */
      MAC_SelectBank (3);
      val = LREG(uint16_t, B3_REV);
      if ((val & 0xFFF0) != REV_CHIP_ID) {
        /* Invalid ID */
        return ARM_DRIVER_ERROR;
      }

      /* Clear Interrupt Mask */
      MAC_SelectBank (2);
      LREG(uint8_t, B2_MSK) = 0;

      /* Reset receiver */
      MAC_SelectBank (0);
      LREG(uint16_t, B0_RCR) = RCR_SOFT_RST;

      /* Configure LEDs */
      LREG(uint16_t, B0_RPCR)= LEDA_10M_100M | LEDB_TX_RX;

      /* Clear control registers */
      LREG(uint16_t, B0_RCR) = 0;
      LREG(uint16_t, B0_TCR) = 0;

      /* Write Configuration */
      MAC_SelectBank (1);
      LREG(uint16_t, B1_CR)  = CR_EPH_POW_EN | CR_DEFAULT;
      LREG(uint16_t, B1_CTR) = CTR_LE_ENABLE | CTR_CR_ENABLE | CTR_TE_ENABLE | CTR_AUTO_REL | CTR_DEFAULT;

      /* Reset MMU */
      MAC_SelectBank(2);
      LREG(uint16_t, B2_MMUCR) = MMU_RESET;
      while (LREG(uint16_t, B2_MMUCR) & MMUCR_BUSY);

      /* Configure Interrupt Mask */
      MAC_SelectBank (2);
      LREG(uint8_t, B2_MSK) = MSK_RCV;

      /* Enable interrupts */
      NVIC_ClearPendingIRQ(ETHERNET_IRQn);
      NVIC_SetPriority( ETHERNET_IRQn, configMAC_INTERRUPT_PRIORITY );
      NVIC_EnableIRQ(ETHERNET_IRQn);

      ETH.flags |= ETH_FLAG_POWER;
      break;

    default:
      return ARM_DRIVER_ERROR_UNSUPPORTED;
  }

  return ARM_DRIVER_OK;
}

/**
  \fn          int32_t GetMacAddress (ARM_ETH_MAC_ADDR *ptr_addr)
  \brief       Get Ethernet MAC Address.
  \param[in]   ptr_addr  Pointer to address
  \return      \ref execution_status
*/
static int32_t MAC_GetMacAddress (ARM_ETH_MAC_ADDR *ptr_addr) {
  uint16_t val;

  if (ptr_addr == NULL) {
    return ARM_DRIVER_ERROR_PARAMETER;
  }

  if ((ETH.flags & ETH_FLAG_POWER) == 0U) {
    return ARM_DRIVER_ERROR;
  }

  MAC_SelectBank (1);

  val = LREG(uint16_t, B1_IAR0);
  ptr_addr->b[0] = (uint8_t)val;
  ptr_addr->b[1] = (uint8_t)(val >> 8);

  val = LREG(uint16_t, B1_IAR2);
  ptr_addr->b[2] = (uint8_t)val;
  ptr_addr->b[3] = (uint8_t)(val >> 8);

  val = LREG(uint16_t, B1_IAR4);
  ptr_addr->b[4] = (uint8_t)val;
  ptr_addr->b[5] = (uint8_t)(val >> 8);

  return ARM_DRIVER_OK;
}

/**
  \fn          int32_t SetMacAddress (const ARM_ETH_MAC_ADDR *ptr_addr)
  \brief       Set Ethernet MAC Address.
  \param[in]   ptr_addr  Pointer to address
  \return      \ref execution_status
*/
static int32_t MAC_SetMacAddress (const ARM_ETH_MAC_ADDR *ptr_addr) {
  uint16_t val;

  if (ptr_addr == NULL) {
    return ARM_DRIVER_ERROR_PARAMETER;
  }

  if ((ETH.flags & ETH_FLAG_POWER) == 0U) {
    return ARM_DRIVER_ERROR;
  }

  MAC_SelectBank (1);

  val  = (uint16_t) ptr_addr->b[0];
  val |= (uint16_t)(ptr_addr->b[1] << 8);
  LREG(uint16_t, B1_IAR0) = val;

  val  = (uint16_t) ptr_addr->b[2];
  val |= (uint16_t)(ptr_addr->b[3] << 8);
  LREG(uint16_t, B1_IAR2) = val;

  val  = (uint16_t) ptr_addr->b[4];
  val |= (uint16_t)(ptr_addr->b[5] << 8);
  LREG(uint16_t, B1_IAR4) = val;

  return ARM_DRIVER_OK;
}

/**
  \fn          int32_t SetAddressFilter (const ARM_ETH_MAC_ADDR *ptr_addr,
                                               uint32_t          num_addr)
  \brief       Configure Address Filter.
  \param[in]   ptr_addr  Pointer to addresses
  \param[in]   num_addr  Number of addresses to configure
  \return      \ref execution_status
*/
static int32_t MAC_SetAddressFilter (const ARM_ETH_MAC_ADDR *ptr_addr, uint32_t num_addr) {
  uint32_t crc, hi, lo;

  if ((ptr_addr == NULL) && (num_addr != 0U)) {
    return ARM_DRIVER_ERROR_PARAMETER;
  }

  if ((ETH.flags & ETH_FLAG_POWER) == 0U) {
    return ARM_DRIVER_ERROR;
  }

  hi = 0U;
  lo = 0U;

  if (num_addr != 0U) {
    /* Calculate 64-bit Hash table for MAC addresses */
    while (num_addr > 0U) {
      crc = crc32_data (&ptr_addr->b[0], 6) >> 26;
      if (crc & 0x20) {
        hi |= (1 << (crc & 0x1F));
      } else {
        lo |= (1 << crc);
      }

      ptr_addr++;
      num_addr--;
    }
  }

  /* Set hash registers */
  MAC_SelectBank (3);
  LREG(uint16_t, B3_MT0) = (uint16_t)lo;
  LREG(uint16_t, B3_MT2) = (uint16_t)(lo >> 16);
  LREG(uint16_t, B3_MT4) = (uint16_t)hi;
  LREG(uint16_t, B3_MT6) = (uint16_t)(hi >> 16);

  return ARM_DRIVER_OK;
}

/**
  \fn          int32_t SendFrame (const uint8_t *frame, uint32_t len, uint32_t flags)
  \brief       Send Ethernet frame.
  \param[in]   frame  Pointer to frame buffer with data to send
  \param[in]   len    Frame buffer length in bytes
  \param[in]   flags  Frame transmit flags (see ARM_ETH_MAC_TX_FRAME_...)
  \return      \ref execution_status
*/
static int32_t MAC_SendFrame (const uint8_t *frame, uint32_t len, uint32_t flags) {
  uint8_t packnr;
  uint32_t i,sz;

  if ((frame == NULL) || (len == 0U)) {
    return ARM_DRIVER_ERROR_PARAMETER;
  }

  if ((ETH.flags & ETH_FLAG_POWER) == 0U) {
    return ARM_DRIVER_ERROR;
  }

  if ((ETH.tx_len + len) > ETH_BUF_SIZE) {
    /* Frame size invalid */
    return ARM_DRIVER_ERROR;
  }

  if (flags & ARM_ETH_MAC_TX_FRAME_FRAGMENT) {
    memcpy (&tx_buf[ETH.tx_len], frame, len);
    ETH.tx_len += len;
    return ARM_DRIVER_OK;
  }

  /* Last fragment, send frame */
  MAC_SelectBank(2);

  /* MMU allocate memory for transmitting */
  LREG(uint16_t, B2_MMUCR) = MMU_ALLOC_TX;

  if ((LREG(uint8_t, B2_IST) & IST_ALLOC_INT) == 0U) {
    /* Not enough space, FIFO is busy transmitting */
    return ARM_DRIVER_ERROR_BUSY;
  }

  memcpy (&tx_buf[ETH.tx_len], frame, len);
  ETH.tx_len += len;

  /* Set TX packet number */
  packnr = LREG(uint8_t, B2_ARR);
  LREG(uint8_t, B2_PNR)  = packnr;
  LREG(uint16_t, B2_PTR) = PTR_AUTO_INCR;

  /* Reserve space for Status Word */
  LREG(uint16_t, B2_DATA0) = 0x0000;
  /* Set Total Size */
  LREG(uint16_t, B2_DATA0) = ETH.tx_len + 6;

  /* Send content from the intermediate buffer */
  for (i = 0U, sz = ETH.tx_len; sz > 1; i += 2U, sz -= 2U) {
    LREG(uint16_t, B2_DATA0) = __UNALIGNED_UINT16_READ(&tx_buf[i]);
  }

  /* Add control word and odd data byte */
  if (sz > 0U) {
    LREG(uint16_t, B2_DATA0) = RFC_CRC | RFC_ODD | tx_buf[i];
  } else {
    LREG(uint16_t, B2_DATA0) = RFC_CRC;
  }

  /* Enable transmitter */
  MAC_SelectBank (0);
  LREG(uint16_t, B0_TCR)   = TCR_TXENA | TCR_PAD_EN;

  /* Enqueue the packet */
  MAC_SelectBank (2);
  LREG(uint16_t, B2_MMUCR) = MMU_ENQ_TX;

  ETH.tx_len = 0U;
  return ARM_DRIVER_OK;
}

/**
  \fn          int32_t ReadFrame (uint8_t *frame, uint32_t len)
  \brief       Read data of received Ethernet frame.
  \param[in]   frame  Pointer to frame buffer for data to read into
  \param[in]   len    Frame buffer length in bytes
  \return      number of data bytes read or execution status
                 - value >= 0: number of data bytes read
                 - value < 0: error occurred, value is execution status as defined with \ref execution_status
*/
static int32_t MAC_ReadFrame (uint8_t *frame, uint32_t len) {
  uint32_t stat,sz,data;

  if ((frame == NULL) && (len != 0U)) {
    return ARM_DRIVER_ERROR_PARAMETER;
  }

  if ((ETH.flags & ETH_FLAG_POWER) == 0U) {
    return ARM_DRIVER_ERROR;
  }

  MAC_SelectBank (2);

  if ((frame == NULL) && (len == 0U)) {
    /* Discard received frame */
    LREG(uint16_t, B2_MMUCR) = MMU_REMV_REL_RX;

    /* Re-enable RCV interrupts */
    stat = LREG(uint16_t, B2_FIFO);
    if (stat & FIFO_REMPTY) {
      LREG(uint8_t, B2_MSK) = MSK_RCV;
    }
    return (0);
  }

  /* Pointer Register set to RCV + Auto Increase + Read access */
  LREG(uint16_t, B2_PTR) = PTR_RCV | PTR_AUTO_INCR | PTR_READ;

  /* Read status word and packet length */
  stat = LREG(uint32_t, B2_DATA);
  sz   = (stat >> 16) - ((stat & RFS_ODDFRM) ? 5 : 6);

  if (sz != len) {
    return ARM_DRIVER_ERROR;
  }

  /* Copy aligned bytes */
  for ( ; sz > 3U; frame += 4U, sz -= 4U) {
    __UNALIGNED_UINT32_WRITE(&frame[0], LREG(uint32_t, B2_DATA));
  }

  /* Copy remaining bytes */
  if (sz > 0U) {
    data = LREG(uint32_t, B2_DATA);
    for ( ; sz > 0U; frame++, sz--) {
      frame[0] = (uint8_t)data;
      data >>= 8U;
    }
  }

  /* MMU free packet */
  LREG(uint16_t, B2_MMUCR) = MMU_REMV_REL_RX;

  /* Re-enable RCV interrupts */
  stat = LREG(uint16_t, B2_FIFO);
  if (stat & FIFO_REMPTY) {
    LREG(uint8_t, B2_MSK) = MSK_RCV;
  }

  return ((int32_t)len);
}

/**
  \fn          uint32_t GetRxFrameSize (void)
  \brief       Get size of received Ethernet frame.
  \return      number of bytes in received frame
*/
static uint32_t MAC_GetRxFrameSize (void) {
  uint32_t stat;

  if ((ETH.flags & ETH_FLAG_POWER) == 0U) {
    return (0U);
  }

  MAC_SelectBank (2);
  stat = LREG(uint16_t, B2_FIFO);
  if (stat & FIFO_REMPTY) {
    /* RX Status FIFO empty */
    return (0U);
  }

  /* Pointer Register set to RCV + Auto Increase + Read access */
  LREG(uint16_t, B2_PTR) = PTR_RCV | PTR_AUTO_INCR | PTR_READ;

  /* Read frame status and length */
  stat = LREG(uint32_t, B2_DATA);
  if (stat & (RFS_ALGNERR | RFS_BADCRC | RFS_TOOLNG | RFS_TOOSHORT)) {
    /* Error, this frame is invalid */
    return (0xFFFFFFFF);
  }
  if ((stat >> 16) < 22U) {
    /* Error, this frame is too short */
    return (0xFFFFFFFF);
  }

  /* Return data length */
  return ((stat >> 16) - ((stat & RFS_ODDFRM) ? 5 : 6));
}

/**
  \fn          int32_t GetRxFrameTime (ARM_ETH_MAC_TIME *time)
  \brief       Get time of received Ethernet frame.
  \param[in]   time  Pointer to time structure for data to read into
  \return      \ref execution_status
*/
static int32_t MAC_GetRxFrameTime (ARM_ETH_MAC_TIME *time) {
  (void)time;
  return ARM_DRIVER_ERROR_UNSUPPORTED;
}

/**
  \fn          int32_t GetTxFrameTime (ARM_ETH_MAC_TIME *time)
  \brief       Get time of transmitted Ethernet frame.
  \param[in]   time  Pointer to time structure for data to read into
  \return      \ref execution_status
*/
static int32_t MAC_GetTxFrameTime (ARM_ETH_MAC_TIME *time) {
  (void)time;
  return ARM_DRIVER_ERROR_UNSUPPORTED;
}

/**
  \fn          int32_t ControlTimer (uint32_t control, ARM_ETH_MAC_TIME *time)
  \brief       Control Precision Timer.
  \param[in]   control  Operation
  \param[in]   time     Pointer to time structure
  \return      \ref execution_status
*/
static int32_t MAC_ControlTimer (uint32_t control, ARM_ETH_MAC_TIME *time) {
  (void)control;
  (void)time;
  return ARM_DRIVER_ERROR_UNSUPPORTED;
}

/**
  \fn          int32_t Control (uint32_t control, uint32_t arg)
  \brief       Control Ethernet Interface.
  \param[in]   control  Operation
  \param[in]   arg      Argument of operation (optional)
  \return      \ref execution_status
*/
static int32_t MAC_Control (uint32_t control, uint32_t arg) {
  uint16_t mac_tcr, mac_rcr, mac_rpcr;

  if ((ETH.flags & ETH_FLAG_POWER) == 0U) {
    return ARM_DRIVER_ERROR;
  }

  switch (control) {
    case ARM_ETH_MAC_CONFIGURE:
      if ((arg & ARM_ETH_MAC_SPEED_Msk) == ARM_ETH_MAC_SPEED_1G) {
        /* 1Gbit is not supported */
        return ARM_DRIVER_ERROR_UNSUPPORTED;
      }

      MAC_SelectBank (0);
      mac_tcr  = LREG(uint16_t, B0_TCR);
      mac_rcr  = LREG(uint16_t, B0_RCR);
      mac_rpcr = LREG(uint16_t, B0_RPCR);

      if ((arg & ARM_ETH_MAC_DUPLEX_Msk) == ARM_ETH_MAC_DUPLEX_FULL) {
        /* Enable full duplex mode */
        mac_rpcr |=  RPCR_DPLX;
      } else {
        /* Enable half duplex mode */
        mac_rpcr &= ~RPCR_DPLX;
      }

      if ((arg & ARM_ETH_MAC_LOOPBACK) != 0) {
        /* Enable loopback mode */
        mac_tcr |=  TCR_EPH_LOOP;
      } else {
        mac_tcr &= ~TCR_EPH_LOOP;
      }

      if ((arg & ARM_ETH_MAC_CHECKSUM_OFFLOAD_RX) ||
          (arg & ARM_ETH_MAC_CHECKSUM_OFFLOAD_TX)) {
        /* Checksum offload is not supported */
        return ARM_DRIVER_ERROR_UNSUPPORTED;
      }

      if ((arg & ARM_ETH_MAC_ADDRESS_BROADCAST) != 0) {
        /* Enable broadcast frame receive */
        /* Not used, always enabled       */
      }

      if ((arg & ARM_ETH_MAC_ADDRESS_MULTICAST) != 0) {
        /* Enable all multicast frame receive */
        mac_rcr |=  RCR_ALMUL;
      } else {
        mac_rcr &= ~RCR_ALMUL;
      }

      if ((arg & ARM_ETH_MAC_ADDRESS_ALL) != 0) {
        /* Enable all frame receive (Promiscuous mode) */
        mac_rcr |=  RCR_PRMS;
      } else {
        mac_rcr &= ~RCR_PRMS;
      }

      /* Set configuration */
      LREG(uint16_t, B0_TCR)  = mac_tcr;
      LREG(uint16_t, B0_RCR)  = mac_rcr;
      LREG(uint16_t, B0_RPCR) = mac_rpcr;
      break;

    case ARM_ETH_MAC_CONTROL_TX:
      /* Enable/disable MAC transmitter */
      MAC_SelectBank (0);
      mac_tcr  = LREG(uint16_t, B0_TCR);

      if (arg != 0) {
        mac_tcr |=  TCR_TXENA;
      } else {
        mac_tcr &= ~TCR_TXENA;
      }

      LREG(uint16_t, B0_TCR)  = mac_tcr;
      break;

    case ARM_ETH_MAC_CONTROL_RX:
      /* Enable/disable MAC receiver */
      MAC_SelectBank (0);
      mac_rcr  = LREG(uint16_t, B0_RCR);

      if (arg != 0) {
        mac_rcr |=  RCR_RXEN;
      } else {
        mac_rcr &= ~RCR_RXEN;
      }

      LREG(uint16_t, B0_RCR)  = mac_rcr;
      break;

    case ARM_ETH_MAC_FLUSH:
      /* Flush Tx and Rx buffers */
      if ((arg & ARM_ETH_MAC_FLUSH_RX) != 0) {
        MAC_SelectBank (0);
        mac_rcr  = LREG(uint16_t, B0_RCR);

        /* Disable Rx */
        LREG(uint16_t, B0_RCR) = (mac_rcr | RCR_SOFT_RST) & ~RCR_RXEN;

        MAC_SelectBank (2);
        while ((LREG(uint16_t, B2_FIFO) & FIFO_REMPTY) == 0U) {
          /* Force MMU Rx Discard */
          LREG(uint16_t, B2_MMUCR) = MMU_REMV_REL_RX;
          while (LREG(uint16_t, B2_MMUCR) & MMUCR_BUSY);
        }

        MAC_SelectBank (0);
        LREG(uint16_t, B0_RCR) = mac_rcr;
      }

      if ((arg & ARM_ETH_MAC_FLUSH_TX) != 0) {
        MAC_SelectBank (0);
        mac_tcr  = LREG(uint16_t, B0_TCR);

        /* Disable Tx */
        LREG(uint16_t, B0_TCR) = mac_tcr & ~TCR_TXENA;

        MAC_SelectBank (2);
        LREG(uint16_t, B2_MMUCR) = MMU_RESET_TX;
        while (LREG(uint16_t, B2_MMUCR) & MMUCR_BUSY);

        MAC_SelectBank (0);
        LREG(uint16_t, B0_TCR) = mac_tcr;
      }
      break;

    default:
      return ARM_DRIVER_ERROR_UNSUPPORTED;
  }
  return ARM_DRIVER_OK;
}

/**
  \fn          void ETHERNET_Handler (void)
  \brief       Ethernet Interrupt handler.
*/
extern void ETHERNET_Handler(void);
void ETHERNET_Handler(void) {
  uint32_t event = 0U;
  uint16_t bank;
  uint8_t  stat;

  /* Preserve current bank selection */
  bank = LREG(uint16_t, BSR);
  MAC_SelectBank (2);
  stat = LREG(uint8_t, B2_IST);
  if ((stat & IST_RCV_INT) != 0) {
    /* Receive interrupt */
    event |= ARM_ETH_MAC_EVENT_RX_FRAME;
    /* Clear Interrupt Mask */
    LREG(uint8_t, B2_MSK) = 0;
  }
  MAC_SelectBank ((uint8_t)bank);

  /* Callback event notification */
  if (event && ETH.cb_event) {
    ETH.cb_event (event);
  }
}

/**
  \fn          int32_t PHY_Read (uint8_t phy_addr, uint8_t reg_addr, uint16_t *data)
  \brief       Read Ethernet PHY Register through Management Interface.
  \param[in]   phy_addr  5-bit device address
  \param[in]   reg_addr  5-bit register address
  \param[out]  data      Pointer where the result is written to
  \return      \ref execution_status
*/
static int32_t PHY_Read (uint8_t phy_addr, uint8_t reg_addr, uint16_t *data) {

  MAC_SelectBank(3);

  /* 32 consecutive ones on MDO to establish sync */
  output_MDO (0xFFFFFFFFU, 32U);

  /* start code (01), read command (10) */
  output_MDO (0x06U, 4U);

  /* write PHY address */
  output_MDO (phy_addr, 5U);

  /* write the PHY register to write */
  output_MDO (reg_addr, 5U);

  /* turnaround MDO is tristated */
  turnaround_MDO ();

  /* read the data value */
  *data = (uint16_t)input_MDI ();

  /* turnaround MDO is tristated */
  turnaround_MDO ();

  return ARM_DRIVER_OK;
}

/**
  \fn          int32_t PHY_Write (uint8_t phy_addr, uint8_t reg_addr, uint16_t data)
  \brief       Write Ethernet PHY Register through Management Interface.
  \param[in]   phy_addr  5-bit device address
  \param[in]   reg_addr  5-bit register address
  \param[in]   data      16-bit data to write
  \return      \ref execution_status
*/
static int32_t PHY_Write (uint8_t phy_addr, uint8_t reg_addr, uint16_t data) {

  MAC_SelectBank(3);

  /* 32 consecutive ones on MDO to establish sync */
  output_MDO (0xFFFFFFFFU, 32U);

  /* start code (01), write command (01) */
  output_MDO (0x05U, 4U);

  /* write PHY address */
  output_MDO (phy_addr, 5U);

  /* write the PHY register to write */
  output_MDO (reg_addr, 5U);

  /* turnaround MDO (1,0)*/
  output_MDO (0x02U, 2U);

  /* write the data value */
  output_MDO (data, 16U);

  /* turnaround MDO is tristated */
  turnaround_MDO ();

  return ARM_DRIVER_OK;
}


/* MAC Driver Control Block */
extern
ARM_DRIVER_ETH_MAC ARM_Driver_ETH_MAC_(ETH_MAC_NUM);
ARM_DRIVER_ETH_MAC ARM_Driver_ETH_MAC_(ETH_MAC_NUM) = {
  MAC_GetVersion,
  MAC_GetCapabilities,
  MAC_Initialize,
  MAC_Uninitialize,
  MAC_PowerControl,
  MAC_GetMacAddress,
  MAC_SetMacAddress,
  MAC_SetAddressFilter,
  MAC_SendFrame,
  MAC_ReadFrame,
  MAC_GetRxFrameSize,
  MAC_GetRxFrameTime,
  MAC_GetTxFrameTime,
  MAC_ControlTimer,
  MAC_Control,
  PHY_Read,
  PHY_Write
};


/* Driver Version */
static const ARM_DRIVER_VERSION PHY_DriverVersion = {
  ARM_ETH_PHY_API_VERSION,
  ARM_ETH_PHY_DRV_VERSION
};

/**
  \fn          ARM_DRV_VERSION GetVersion (void)
  \brief       Get driver version.
  \return      \ref ARM_DRV_VERSION
*/
static ARM_DRIVER_VERSION PHY_GetVersion (void) {
  return PHY_DriverVersion;
}

/**
  \fn          int32_t Initialize (ARM_ETH_PHY_Read_t  fn_read,
                                   ARM_ETH_PHY_Write_t fn_write)
  \brief       Initialize Ethernet PHY Device.
  \param[in]   fn_read   Pointer to \ref ARM_ETH_MAC_PHY_Read
  \param[in]   fn_write  Pointer to \ref ARM_ETH_MAC_PHY_Write
  \return      \ref execution_status
*/
static int32_t PHY_Initialize (ARM_ETH_PHY_Read_t fn_read, ARM_ETH_PHY_Write_t fn_write) {
  /* PHY_Read and PHY_Write will be re-used, no need to register them again */
  uint16_t val;
  (void)fn_read;
  (void)fn_write;

  /* Reset PHY */
  PHY_Write (ETH_PHY_ADDR, PHY_CR, PHY_CR_RST);

  /* Clear PHY status */
  PHY_Read (ETH_PHY_ADDR, PHY_SO, &val);

  ETH.phy_cr = 0U;

  return ARM_DRIVER_OK;
}

/**
  \fn          int32_t Uninitialize (void)
  \brief       De-initialize Ethernet PHY Device.
  \return      \ref execution_status
*/
static int32_t PHY_Uninitialize (void) {

  ETH.phy_cr = 0U;

  return ARM_DRIVER_OK;
}

/**
  \fn          int32_t PowerControl (ARM_POWER_STATE state)
  \brief       Control Ethernet PHY Device Power.
  \param[in]   state  Power state
  \return      \ref execution_status
*/
static int32_t PHY_PowerControl (ARM_POWER_STATE state) {
  uint16_t val;

  switch ((int32_t)state) {
    case ARM_POWER_OFF:
      /* Select Power Saving Mode */
      if ((ETH.flags & ETH_FLAG_POWER) == 0U) {
        return ARM_DRIVER_ERROR;
      }
      ETH.phy_cr = PHY_CR_PDN;
      break;
    case ARM_POWER_FULL:
      /* Select Normal Operation Mode */
      if ((ETH.flags & ETH_FLAG_POWER) == 0U) {
        return ARM_DRIVER_ERROR;
      }

      /* Check Device Identification. */
      PHY_Read (ETH_PHY_ADDR, PHY_ID1, &val);
      if (val != PHY_CHIP_ID1) {
        /* Invalid PHY ID1 */
        return ARM_DRIVER_ERROR_UNSUPPORTED;
      }
      PHY_Read (ETH_PHY_ADDR, PHY_ID2, &val);
      if ((val & 0xFFF0) != PHY_CHIP_ID2) {
        /* Invalid PHY ID2 */
        return ARM_DRIVER_ERROR_UNSUPPORTED;
      }

      ETH.phy_cr = 0U;
      break;
    case ARM_POWER_LOW:
    default:
      return ARM_DRIVER_ERROR_UNSUPPORTED;
  }

  return PHY_Write (ETH_PHY_ADDR, PHY_CR, ETH.phy_cr);
}

/**
  \fn          int32_t SetInterface (uint32_t interface)
  \brief       Set Ethernet Media Interface.
  \param[in]   interface  Media Interface type
  \return      \ref execution_status
*/
static int32_t PHY_SetInterface (uint32_t interface) {
  /* Not used in this driver */
  (void)interface;
  return ARM_DRIVER_OK;
}

/**
  \fn          int32_t SetMode (uint32_t mode)
  \brief       Set Ethernet PHY Device Operation mode.
  \param[in]   mode  Operation Mode
  \return      \ref execution_status
*/
static int32_t PHY_SetMode (uint32_t mode) {
  uint16_t val;

  if ((ETH.flags & ETH_FLAG_POWER) == 0U) {
    return ARM_DRIVER_ERROR;
  }

  val = ETH.phy_cr & PHY_CR_PDN;

  switch (mode & ARM_ETH_PHY_SPEED_Msk) {
    case ARM_ETH_PHY_SPEED_10M:
      break;
    case ARM_ETH_PHY_SPEED_100M:
      val |= PHY_CR_SPEED;
      break;
    default:
      return ARM_DRIVER_ERROR_UNSUPPORTED;
  }

  switch (mode & ARM_ETH_PHY_DUPLEX_Msk) {
    case ARM_ETH_PHY_DUPLEX_HALF:
      break;
    case ARM_ETH_PHY_DUPLEX_FULL:
      val |= PHY_CR_DPLX;
      break;
  }

  if (mode & ARM_ETH_PHY_AUTO_NEGOTIATE) {
    val |= PHY_CR_ANEG_EN;
  }
  if (mode & ARM_ETH_PHY_LOOPBACK) {
    val |= PHY_CR_LPBK;
  }
  if (mode & ARM_ETH_PHY_ISOLATE) {
    val |= PHY_CR_MII_DIS;
  }

  ETH.phy_cr = val;

  /* Apply configured mode */
  return PHY_Write (ETH_PHY_ADDR, PHY_CR, val);
}

/**
  \fn          ARM_ETH_LINK_STATE GetLinkState (void)
  \brief       Get Ethernet PHY Device Link state.
  \return      current link status \ref ARM_ETH_LINK_STATE
*/
static ARM_ETH_LINK_STATE PHY_GetLinkState (void) {
  ARM_ETH_LINK_STATE state = ARM_ETH_LINK_DOWN;
  uint16_t val = 0U;

  if (ETH.flags & ETH_FLAG_POWER) {
    PHY_Read (ETH_PHY_ADDR, PHY_SR, &val);
  }
  if (val & PHY_SR_LINK) {
    /* Link Status bit is set */
    state = ARM_ETH_LINK_UP;
  }
  return (state);
}

/**
  \fn          ARM_ETH_LINK_INFO GetLinkInfo (void)
  \brief       Get Ethernet PHY Device Link information.
  \return      current link parameters \ref ARM_ETH_LINK_INFO
*/
static ARM_ETH_LINK_INFO PHY_GetLinkInfo (void) {
  ARM_ETH_LINK_INFO info;
  uint32_t speed, duplex;
  uint16_t val = 0U;

  speed  = ARM_ETH_SPEED_10M;
  duplex = ARM_ETH_DUPLEX_HALF;

  if (ETH.flags & ETH_FLAG_POWER) {
    PHY_Read (ETH_PHY_ADDR, PHY_SO, &val);
  }
  if (val & PHY_SO_SPDDET) {
    speed  = ARM_ETH_SPEED_100M;
  }
  if (val & PHY_SO_DPLXDET) {
    duplex = ARM_ETH_DUPLEX_FULL;
  }

  /* Link must be up to get valid state */
  info.speed  = speed;
  info.duplex = duplex;

  return (info);
}

/* PHY Driver Control Block */
extern
ARM_DRIVER_ETH_PHY ARM_Driver_ETH_PHY_(ETH_PHY_NUM);
ARM_DRIVER_ETH_PHY ARM_Driver_ETH_PHY_(ETH_PHY_NUM) = {
  PHY_GetVersion,
  PHY_Initialize,
  PHY_Uninitialize,
  PHY_PowerControl,
  PHY_SetInterface,
  PHY_SetMode,
  PHY_GetLinkState,
  PHY_GetLinkInfo
};

/* *INDENT-ON* */
