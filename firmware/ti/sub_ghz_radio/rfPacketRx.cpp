/*
 * Copyright (c) 2019, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/***** Includes *****/
/* Standard C Libraries */
#include <stdlib.h>

/* TI Drivers */
#include <ti/drivers/rf/RF.h>
#include <ti/drivers/GPIO.h>

/* Driverlib Header files */
/* clang-format off */
// Can't have the file path separated by spaces, so clang-format needs to be turned off for this macro.
#include DeviceFamily_constructPath(driverlib/rf_prop_mailbox.h)
/* clang-format on */

/* Board Header files */
#include "ti_drivers_config.h"

/* Application Header files */
#include "RFQueue.hh"
#include <ti_radio_config.h>
#include "bsp.hh"
#include "smartrf_settings.h"

/***** Defines *****/

/* Packet RX Configuration */
#define DATA_ENTRY_HEADER_SIZE 8 /* Constant header size of a Generic Data Entry */
#define MAX_LENGTH 30            /* Max length byte the radio will accept */
#define NUM_DATA_ENTRIES 2       /* NOTE: Only two data entries supported at the moment */
#define NUM_APPENDED_BYTES 2     /* The Data Entries data field will contain:             \
                                  * 1 Header byte (RF_cmdPropRx.rxConf.bIncludeHdr = 0x1) \
                                  * Max 30 payload bytes                                  \
                                  * 1 status byte (RF_cmdPropRx.rxConf.bAppendStatus = 0x1) */

/***** Prototypes *****/
static void callback(RF_Handle h, RF_CmdHandle ch, RF_EventMask e);

/***** Variable declarations *****/
static RF_Object rfObject;
static RF_Handle rfHandle;

/* Buffer which contains all Data Entries for receiving data.
 * Pragmas are needed to make sure this buffer is 4 byte aligned (requirement from the RF Core) */
#if defined(__TI_COMPILER_VERSION__)
#pragma DATA_ALIGN(rxDataEntryBuffer, 4);
static uint8_t
    rxDataEntryBuffer[RF_QUEUE_DATA_ENTRY_BUFFER_SIZE(NUM_DATA_ENTRIES,
                                                      MAX_LENGTH,
                                                      NUM_APPENDED_BYTES)];
#elif defined(__IAR_SYSTEMS_ICC__)
#pragma data_alignment = 4
static uint8_t
    rxDataEntryBuffer[RF_QUEUE_DATA_ENTRY_BUFFER_SIZE(NUM_DATA_ENTRIES,
                                                      MAX_LENGTH,
                                                      NUM_APPENDED_BYTES)];
#elif defined(__GNUC__)
static uint8_t
    rxDataEntryBuffer[RF_QUEUE_DATA_ENTRY_BUFFER_SIZE(NUM_DATA_ENTRIES,
                                                      MAX_LENGTH,
                                                      NUM_APPENDED_BYTES)]
    __attribute__((aligned(4)));
#else
#error This compiler is not supported.
#endif

/* Receive dataQueue for RF Core to fill in data */
static dataQueue_t dataQueue;
static rfc_dataEntryGeneral_t *currentDataEntry;
static uint8_t packetLength;
static uint8_t *packetDataPointer;

static uint8_t packet[MAX_LENGTH + NUM_APPENDED_BYTES - 1]; /* The length byte is stored in a separate variable */

/***** Function definitions *****/

void *mainThread(void *arg0)
{
    RF_Params rfParams;
    RF_Params_init(&rfParams);

    GPIO_setConfig(bsp.kSubGLEDPin, GPIO_CFG_OUT_STD | GPIO_CFG_OUT_LOW);
    GPIO_write(bsp.kSubGLEDPin, CONFIG_GPIO_LED_OFF);

    if (RFQueue_defineQueue(&dataQueue,
                            rxDataEntryBuffer,
                            sizeof(rxDataEntryBuffer),
                            NUM_DATA_ENTRIES,
                            MAX_LENGTH + NUM_APPENDED_BYTES))
    {
        /* Failed to allocate space for all data entries */
        while (1)
            ;
    }

    /* Modify CMD_PROP_RX command for application needs */
    /* Set the Data Entity queue for received data */
    RF_cmdPropRx.pQueue = &dataQueue;
    /* Discard ignored packets from Rx queue */
    RF_cmdPropRx.rxConf.bAutoFlushIgnored = 1;
    /* Discard packets with CRC error from Rx queue */
    RF_cmdPropRx.rxConf.bAutoFlushCrcErr = 1;
    /* Implement packet length filtering to avoid PROP_ERROR_RXBUF */
    RF_cmdPropRx.maxPktLen = MAX_LENGTH;
    RF_cmdPropRx.pktConf.bRepeatOk = 1;
    RF_cmdPropRx.pktConf.bRepeatNok = 1;

    /* Request access to the radio */
#if defined(DeviceFamily_CC26X0R2)
    rfHandle = RF_open(&rfObject, &RF_prop, (RF_RadioSetup *)&RF_cmdPropRadioSetup, &rfParams);
#else
    rfHandle = RF_open(&rfObject, &RF_prop, (RF_RadioSetup *)&RF_cmdPropRadioDivSetup, &rfParams);
#endif // DeviceFamily_CC26X0R2

    /* Set the frequency */
    RF_postCmd(rfHandle, (RF_Op *)&RF_cmdFs, RF_PriorityNormal, NULL, 0);

    RF_EventMask terminationReason = RF_EventCmdAborted | RF_EventCmdPreempted;
    while ((terminationReason & RF_EventCmdAborted) && (terminationReason & RF_EventCmdPreempted))
    {
        /* Enter RX mode and stay forever in RX */
        // Re-run if command was aborted due to SW TCXO compensation
        terminationReason = RF_runCmd(rfHandle, (RF_Op *)&RF_cmdPropRx,
                                      RF_PriorityNormal, &callback,
                                      RF_EventRxEntryDone);
    }

    switch (terminationReason)
    {
    case RF_EventLastCmdDone:
        // A stand-alone radio operation command or the last radio
        // operation command in a chain finished.
        break;
    case RF_EventCmdCancelled:
        // Command cancelled before it was started; it can be caused
        // by RF_cancelCmd() or RF_flushCmd().
        break;
    case RF_EventCmdAborted:
        // Abrupt command termination caused by RF_cancelCmd() or
        // RF_flushCmd().
        break;
    case RF_EventCmdStopped:
        // Graceful command termination caused by RF_cancelCmd() or
        // RF_flushCmd().
        break;
    default:
        // Uncaught error event
        while (1)
            ;
    }

    uint32_t cmdStatus = ((volatile RF_Op *)&RF_cmdPropRx)->status;
    switch (cmdStatus)
    {
    case PROP_DONE_OK:
        // Packet received with CRC OK
        break;
    case PROP_DONE_RXERR:
        // Packet received with CRC error
        break;
    case PROP_DONE_RXTIMEOUT:
        // Observed end trigger while in sync search
        break;
    case PROP_DONE_BREAK:
        // Observed end trigger while receiving packet when the command is
        // configured with endType set to 1
        break;
    case PROP_DONE_ENDED:
        // Received packet after having observed the end trigger; if the
        // command is configured with endType set to 0, the end trigger
        // will not terminate an ongoing reception
        break;
    case PROP_DONE_STOPPED:
        // received CMD_STOP after command started and, if sync found,
        // packet is received
        break;
    case PROP_DONE_ABORT:
        // Received CMD_ABORT after command started
        break;
    case PROP_ERROR_RXBUF:
        // No RX buffer large enough for the received data available at
        // the start of a packet
        break;
    case PROP_ERROR_RXFULL:
        // Out of RX buffer space during reception in a partial read
        break;
    case PROP_ERROR_PAR:
        // Observed illegal parameter
        break;
    case PROP_ERROR_NO_SETUP:
        // Command sent without setting up the radio in a supported
        // mode using CMD_PROP_RADIO_SETUP or CMD_RADIO_SETUP
        break;
    case PROP_ERROR_NO_FS:
        // Command sent without the synthesizer being programmed
        break;
    case PROP_ERROR_RXOVF:
        // RX overflow observed during operation
        break;
    default:
        // Uncaught error event - these could come from the
        // pool of states defined in rf_mailbox.h
        while (1)
            ;
    }

    while (1)
        ;
}

void callback(RF_Handle h, RF_CmdHandle ch, RF_EventMask e)
{
    if (e & RF_EventRxEntryDone)
    {
        /* Toggle pin to indicate RX */
        GPIO_toggle(bsp.kSubGLEDPin);

        /* Get current unhandled data entry */
        currentDataEntry = RFQueue_getDataEntry();

        /* Handle the packet data, located at &currentDataEntry->data:
         * - Length is the first byte with the current configuration
         * - Data starts from the second byte */
        packetLength = *(uint8_t *)(&currentDataEntry->data);
        packetDataPointer = (uint8_t *)(&currentDataEntry->data + 1);

        /* Copy the payload + the status byte to the packet variable */
        memcpy(packet, packetDataPointer, (packetLength + 1));

        RFQueue_nextEntry();
    }
}
