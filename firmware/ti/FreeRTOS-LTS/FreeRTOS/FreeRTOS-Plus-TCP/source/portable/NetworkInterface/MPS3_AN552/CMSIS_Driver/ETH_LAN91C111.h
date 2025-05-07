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
 * Project:      Register Interface Definitions for LAN91C111
 * -------------------------------------------------------------------- */

/* This file is a copy of
 * https://github.com/ARM-software/CMSIS-Driver/blob/b91908d907b647bd212920e30b383b03809d68e0/ETH/ETH_LAN91C111.h
*/

#ifndef ETH_LAN91C111_H__
#define ETH_LAN91C111_H__

#include <stdint.h>
#include "Driver_ETH_MAC.h"

/* Bank Select Register */
#define BSR             0x0E        // Bank Select register common to all banks
#define BSR_MASK        0x03        // Mask constant part of bank register
#define BSR_UPPER       0x3300      // Constant value for upper byte of BSR

/* Bank 0 Registers */
#define B0_TCR          0x00        // Transmit Control Register
#define B0_EPHSR        0x02        // EPH Status Register
#define B0_RCR          0x04        // Receive Control Register
#define B0_ECR          0x06        // Counter Register
#define B0_MIR          0x08        // Memory Information Register
#define B0_RPCR         0x0A        // Receive/Phy Control Register
#define B0_RES          0x0C        // Reserved

/* Bank 1 Registers */
#define B1_CR           0x00        // Configuration Register
#define B1_BAR          0x02        // Base Address Register
#define B1_IAR          0x04        // Individual Address Registers
#define B1_IAR0         0x04        // Individual Address Bytes 0-1
#define B1_IAR2         0x06        // Individual Address Bytes 2-3
#define B1_IAR4         0x08        // Individual Address Bytes 4-5
#define B1_GPR          0x0A        // General Purpose Register
#define B1_CTR          0x0C        // Control Register

/* Bank 2 Registers */
#define B2_MMUCR        0x00        // MMU Command Register
#define B2_PNR          0x02        // Packet Number Register (8 bit)
#define B2_ARR          0x03        // Allocation Result Register (8 bit)
#define B2_FIFO         0x04        // FIFO Ports Register
#define B2_TX_FIFO      0x04        // Tx FIFO Packet Number (8 bit)
#define B2_RX_FIFO      0x05        // Rx FIFO Packet Number (8 bit)
#define B2_PTR          0x06        // Pointer Register
#define B2_DATA         0x08        // Data Register (8/16/32 bit)
#define B2_DATA0        0x08        // Data Register Word 0
#define B2_DATA1        0x0A        // Data Register Word 1
#define B2_IST          0x0C        // Interrupt Status Register (8 bit)
#define B2_ACK          0x0C        // Interrupt Ack Register (8 bit)
#define B2_MSK          0x0D        // Interrupt Mask Register (8 bit)

/* Bank 3 Registers */
#define B3_MT           0x00        // Multicast Hash Table
#define B3_MT0          0x00        // Multicast Hash Table 0-1
#define B3_MT2          0x02        // Multicast Hash Table 2-3
#define B3_MT4          0x04        // Multicast Hash Table 4-5
#define B3_MT6          0x06        // Multicast Hash Table 6-7
#define B3_MGMT         0x08        // Management Interface PHY
#define B3_REV          0x0A        // Revision Register (Chip Id/Revision)
#define B3_ERCV         0x0C        // Early Receive Register

/* Transmit Control Register */
#define TCR_SWFDUP      0x8000      // Switched Full Duplex Mode
#define TCR_EPH_LOOP    0x2000      // Internal Loopback at the EPH block
#define TCR_STP_SQET    0x1000      // Stop transmit on SQET error
#define TCR_FDUPLX      0x0800      // Full duplex mode (receive own frames)
#define TCR_MON_CSN     0x0400      // Monitor carrier while transmitting
#define TCR_NOCRC       0x0100      // Don't append CRC to tx frames
#define TCR_PAD_EN      0x0080      // Pad short frames
#define TCR_FORCOL      0x0004      // Force collision
#define TCR_LOOP        0x0002      // PHY Local loopback
#define TCR_TXENA       0x0001      // Enable transmitter

/* EPH Status Register */
#define EPHSR_TXUNRN    0x8000      // Transmit Underrun
#define EPHSR_LINK_OK   0x4000      // General purpose input driven by nLNK pin
#define EPHSR_CTR_ROL   0x1000      // Counter Roll Over
#define EPHSR_EXC_DEF   0x0800      // Excessive Deferral
#define EPHSR_LOST_CARR 0x0400      // Lost Carrier Sense
#define EPHSR_LATCOL    0x0200      // Late Collision Detected
#define EPHSR_TX_DEFR   0x0080      // Transmit Deferred
#define EPHSR_LTX_BRD   0x0040      // Last Tx Frame was a broadcast
#define EPHSR_SQET      0x0020      // Signal Quality Error Test
#define EPHSR_16COL     0x0010      // 16 collisions reached
#define EPHSR_LTX_MULT  0x0008      // Last transmit frame was a multicast
#define EPHSR_MULCOL    0x0004      // Multiple collision detected
#define EPHSR_SNGLCOL   0x0002      // Single collision detected
#define EPHSR_TX_SUC    0x0001      // Last transmit was successful

/* Receive Control Register */
#define RCR_SOFT_RST    0x8000      // Software Reset
#define RCR_FILT_CAR    0x4000      // Filter Carrier
#define RCR_ABORT_ENB   0x2000      // Enable Rx Abort when collision
#define RCR_STRIP_CRC   0x0200      // Strip CRC of received frames
#define RCR_RXEN        0x0100      // Enable Receiver
#define RCR_ALMUL       0x0004      // Accept all multicast (no filtering)
#define RCR_PRMS        0x0002      // Promiscuous mode
#define RCR_RX_ABORT    0x0001      // Receive frame aborted (too long)

/* Receive/Phy Control Register */
#define RPCR_SPEED      0x2000      // Speed select input (10/100 MBps)
#define RPCR_DPLX       0x1000      // Duplex Select (Full/Half Duplex)
#define RPCR_ANEG       0x0800      // Auto-Negotiation mode select
#define RPCR_LEDA_MASK  0x00E0      // LEDA signal mode select
#define RPCR_LEDB_MASK  0x001C      // LEDB signal mode select

/* RPCR LEDA mode */
#define LEDA_10M_100M   0x0000      // 10 MB or 100 MB link detected
#define LEDA_10M        0x0040      // 10 MB link detected
#define LEDA_FDUPLX     0x0060      // Full Duplex Mode enabled
#define LEDA_TX_RX      0x0080      // Transmit or Receive packet occurred
#define LEDA_100M       0x00A0      // 100 MB link detected
#define LEDA_RX         0x00C0      // Receive packet occurred
#define LEDA_TX         0x00E0      // Transmit packet occurred

/* RPCR LEDB mode */
#define LEDB_10M_100M   0x0000      // 10 MB or 100 MB link detected
#define LEDB_10M        0x0008      // 10 MB link detected
#define LEDB_FDUPLX     0x000C      // Full Duplex Mode enabled
#define LEDB_TX_RX      0x0010      // Transmit/Receive packet occurred
#define LEDB_100M       0x0014      // 100 MB link detected
#define LEDB_RX         0x0018      // Receive packet occurred
#define LEDB_TX         0x001C      // Transmit packet occurred

/* Configuration Register */
#define CR_EPH_POW_EN   0x8000      // EPH Power Enable  (0= power down PHY)
#define CR_NO_WAIT      0x1000      // No wait states
#define CR_GPCNTRL      0x0400      // General purpose Output drives nCNTRL pin
#define CR_EXT_PHY      0x0200      // External PHY enabled (0= internal PHY)
#define CR_DEFAULT      0x20B1      // Default bits set to 1 for write

/* Control Register */
#define CTR_RCV_BADCRC  0x4000      // Bad CRC packet receive
#define CTR_AUTO_REL    0x0800      // Auto-release Tx memory
#define CTR_LE_ENABLE   0x0080      // Link error enable (mux into EPH int)
#define CTR_CR_ENABLE   0x0040      // Counter rollover enable (mux into EPH int)
#define CTR_TE_ENABLE   0x0020      // Transmit error enable (mux into EPH int)
#define CTR_EEPROM_SEL  0x0004      // EEPROM select
#define CTR_RELOAD      0x0002      // Reload from EEPROM
#define CTR_STORE       0x0001      // Store to EEPROM
#define CTR_DEFAULT     0x1210      // Default bits set to 1 for write

/* MMU Command Register */
#define MMUCR_CMD_MASK  0x00E0      // MMU Command mask
#define MMUCR_BUSY      0x0001      // MMU processing a release command

/* MMUCR Commands */
#define MMU_NOOP        0x0000      // No operation
#define MMU_ALLOC_TX    0x0020      // Allocate memory for Tx
#define MMU_RESET       0x0040      // Reset MMU to initial state
#define MMU_REMV_RX     0x0060      // Remove frame from top of Rx FIFO
#define MMU_REMV_REL_RX 0x0080      // Remove and Release top of Rx FIFO
#define MMU_REL_PKT     0x00A0      // Release specific packet
#define MMU_ENQ_TX      0x00C0      // Enqueue packet number into Tx FIFO
#define MMU_RESET_TX    0x00E0      // Reset Tx FIFO

/* FIFO status */
#define FIFO_REMPTY     0x8000      // No receive packets queued in Rx FIFO
#define FIFO_TEMPTY     0x0080      // No transmit packets in completion queue

/* Pointer Register */
#define PTR_RCV         0x8000      // Address refers to Rx area (0= Tx area)
#define PTR_AUTO_INCR   0x4000      // Auto increment on access
#define PTR_READ        0x2000      // Read access (0= write access)
#define PTR_ETEN        0x1000      // Enable early transmit underrun detection
#define PTR_NOT_EMPTY   0x0800      // Data FIFO not empty yet (read only bit)
#define PTR_MASK        0x07FF      // Mask pointer value

/* Interrupt Status Register */
#define IST_MDINT       0x80        // PHY MI Register 18 change status interrupt
#define IST_ERCV_INT    0x40        // Early Receive interrupt
#define IST_EPH_INT     0x20        // EPH Type interrupt
#define IST_RX_OVRN     0x10        // Receive Overrun interrupt
#define IST_ALLOC_INT   0x08        // Tx ram Allocation interrupt
#define IST_TX_EMPTY    0x04        // Tx FIFO empty interrupt
#define IST_TX_INT      0x02        // Tx Complete interrupt
#define IST_RCV_INT     0x01        // Rx Complete intererupt

/* Interrupt Ack Register */
#define ACK_MDINT       0x80        // PHY MI Register 18 change int. ack
#define ACK_ERCV_INT    0x40        // Early Receive int. ack
#define ACK_RX_OVRN     0x10        // Receive Overrun int. ack
#define ACK_TX_EMPTY    0x04        // Tx FIFO empty int. ack
#define ACK_TX_INT      0x02        // Tx Complete int. ack

/* Interrupt Mask Register */
#define MSK_MDINT       0x80        // PHY MI Register 18 change int. mask
#define MSK_ERCV_INT    0x40        // Early Receive int. mask
#define MSK_EPH_INT     0x20        // EPH Type int. mask
#define MSK_RX_OVRN     0x10        // Receive Overrun int. mask
#define MSK_ALLOC_INT   0x08        // Tx ram Allocation int. mask
#define MSK_TX_EMPTY    0x04        // Tx FIFO empty int. mask
#define MSK_TX_INT      0x02        // Tx Complete int. mask
#define MSK_RCV         0x01        // Rx Complete int. mask

/* PHY Management Interface */
#define MGMT_MSK_CRS100 0x0040      // Disables CRS100 detection in Tx Half Dup.
#define MGMT_MDOE       0x0008      // MII - 1= MDO pin output, 0= MDO tristated
#define MGMT_MCLK       0x0004      // MII - Value drives MDCLK pin
#define MGMT_MDI        0x0002      // MII - Value of MDI pin when read
#define MGMT_MDO        0x0001      // MII - Value drives MDO pin
#define MGMT_DEFAULT    0x3330      // Default bits set to 1 for write

/* Receive Frame Status */
#define RFS_ALGNERR     0x8000      // Frame alignment error
#define RFS_BROADCAST   0x4000      // Broadcast frame received
#define RFS_BADCRC      0x2000      // Bad CRC error
#define RFS_ODDFRM      0x1000      // Frame with Odd number of bytes received
#define RFS_TOOLNG      0x0800      // Too long frame received (max. 1518 bytes)
#define RFS_TOOSHORT    0x0400      // Too short frame received (min. 64 bytes)
#define RFS_MULTCAST    0x0001      // Multicast frame received
#define RFS_HASH_MASK   0x007E      // Hash value index for multicast registers

/* Receive Frame Control */
#define RFC_ODD         0x2000      // Odd number of bytes in frame
#define RFC_CRC         0x1000      // Append CRC (valid when TCR_NOCRC = 1)

/* Revision Register */
#define REV_CHIP_ID     0x3390      // Chip identification

/* PHY Registers */
#define PHY_CR          0           // Control Register
#define PHY_SR          1           // Status Register
#define PHY_ID1         2           // PHY Identifier 1
#define PHY_ID2         3           // PHY Identifier 2
#define PHY_ANA         4           // Auto-Negotiation Advertisement
#define PHY_ANRC        5           // Auto-Neg. Remote Capability

/* Vendor-specific Registers */
#define PHY_CFG1        16          // Configuration 1
#define PHY_CFG2        17          // Configuration 2
#define PHY_SO          18          // Status Output
#define PHY_MASK        19          // Interrupt Mask

/* Control Register */
#define PHY_CR_RST      0x8000      // Software Reset
#define PHY_CR_LPBK     0x4000      // Loopback mode
#define PHY_CR_SPEED    0x2000      // Speed Select (1=100Mb/s)
#define PHY_CR_ANEG_EN  0x1000      // Auto Negotiation Enable
#define PHY_CR_PDN      0x0800      // Power Down (1=power down)
#define PHY_CR_MII_DIS  0x0400      // Isolate Media interface
#define PHY_CR_ANEG_RST 0x0200      // Restart Auto Negotiation
#define PHY_CR_DPLX     0x0100      // Duplex Mode (1=Full duplex)
#define PHY_CR_COLST    0x0080      // Enable Collision Test

/* Status Register */
#define PHY_SR_CAP_T4   0x8000      // 100BASE-T4 Capable
#define PHY_SR_CAP_TXF  0x4000      // 100BASE-TX Full Duplex Capable
#define PHY_SR_CAP_TXH  0x2000      // 100BASE-TX Half Duplex Capable
#define PHY_SR_CAP_TF   0x1000      // 10BASE-T Full Duplex Capable
#define PHY_SR_CAP_TH   0x0800      // 10BASE-T Half Duplex Capable
#define PHY_SR_CAP_SUPR 0x0040      // MI Preamble Suppression Capable
#define PHY_SR_ANEG_ACK 0x0020      // Auto Negotiation Acknowledgment
#define PHY_SR_REM_FLT  0x0010      // Remote Fault Detect
#define PHY_SR_CAP_ANEG 0x0008      // Auto Negotiation Capable
#define PHY_SR_LINK     0x0004      // Link Status (1=link up)
#define PHY_SR_JAB      0x0002      // Jabber Detect
#define PHY_SR_EXREG    0x0001      // Extended Capability Register

/* Status Output Register */
#define PHY_SO_INT      0x8000      // Interrupt Detect
#define PHY_SO_LNKFAIL  0x4000      // Link Fail Detect
#define PHY_SO_LOSSSYNC 0x2000      // Descrambler Loss of Sync Detect
#define PHY_SO_CWRD     0x1000      // Codeword Error Detect
#define PHY_SO_SSD      0x0800      // Start of Stream Error Detect
#define PHY_SO_ESD      0x0400      // End of Stream Error Detect
#define PHY_SO_RPOL     0x0200      // Reverse Polarity Detect
#define PHY_SO_JAB      0x0100      // Jabber Detect
#define PHY_SO_SPDDET   0x0080      // 100/10 Speed Detect
#define PHY_SO_DPLXDET  0x0040      // Duplex Detect

/* PHY address */
#define ETH_PHY_ADDR    0           // LAN91C111 PHY address

/* PHY Identifier */
#define PHY_CHIP_ID1    0x0016      // PHY Chip identifier 1
#define PHY_CHIP_ID2    0xF840      // PHY Chip identifier 2

/* ETH Driver state flags */
#define ETH_FLAG_INIT   0x01        // Driver initialized
#define ETH_FLAG_POWER  0x02        // Driver powered

/* ETH Driver Control Information */
typedef struct {
  ARM_ETH_MAC_SignalEvent_t cb_event;   // Event callback
  uint16_t flags;                       // Control and state flags
  uint16_t tx_len;                      // Transmit length of data
  uint16_t phy_cr;                      // PHY Control shadow register
  uint16_t reserved;
} ETH_CTRL;

#endif /* ETH_LAN91C111_H__ */

/* *INDENT-ON* */
