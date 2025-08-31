// Includes
// Standard C Libraries
#include <stdlib.h>

// TI Drivers
#include <ti/drivers/rf/RF.h>
#include <ti/drivers/GPIO.h>

// Driverlib Header files
#include DeviceFamily_constructPath(driverlib / rf_prop_mailbox.h)

// Board Header files
#include "ti_drivers_config.h"

// Application Header files
#include "RFQueue.h"
#include <ti_radio_config.h>

#include <ti/sysbios/BIOS.h>
#include <ti/sysbios/knl/Semaphore.h>

// CMD_PROP_SET_LEN
rfc_CMD_PROP_SET_LEN_t RF_cmdPropSetLen =
    {
        .commandNo = 0x3401,
        .rxLen = 0x0000,
};

// Defines

// Packet RX Configuration
//  ------------------------------------------------------------------------------------------------------------------------
//  | DATA_ENTRY_HEADER (12 bytes) | H0 | H1 | H2 | H3 | Length N (1 or 2 Bytes)| D0 | D1 | D2 | .. | .. | D(N-2) | D(N-1) |
//  ------------------------------------------------------------------------------------------------------------------------

// Optional appended bytes
//  -------------------------------------------------------
//  | CRC1 | CRC0 | RSSI | TS0 | TS1 | TS2 | TS3 | Status |
//  -------------------------------------------------------
#define DATA_ENTRY_HEADER_SIZE 12             // Constant header size of a Partial Data Entry
#define MAX_LENGTH 300                        // Max length byte the application will accept
#define PACKET_HEADER_SIZE 4                  // Bytes in packet before location of the length byte
#define LENGTH_FIELD_INDEX PACKET_HEADER_SIZE // Position of length byte (after sync)
#define LENGTH_FIELD_SIZE 2                   // Can be 1 or 2
#define NUM_APPENDED_BYTES 0                  // .rxConf.bIncludeCrc = 0x1;       // 2 bytes (if default CRC is used)
                                              // .rxConf.bAppendRssi = 0x1;       // 1 byte
                                              // .rxConf.bAppendTimestamp = 0x1;  // 4 bytes
                                              // .rxConf.bAppendStatus = 0x1;     // 1 byte
// Prototypes
static void callback(RF_Handle h, RF_CmdHandle ch, RF_EventMask e);

// Variable declarations
static RF_Object rfObject;
static RF_Handle rfHandle;
static RF_CmdHandle rxHandle;

// Receive dataQueue for RF Core to fill in data
static dataQueue_t dataQueue;

#if defined(__TI_COMPILER_VERSION__)
#pragma DATA_ALIGN(rxDataEntryBuf0, 4);
static uint8_t rxDataEntryBuf0[DATA_ENTRY_HEADER_SIZE + MAX_LENGTH + LENGTH_POSITION - +NUM_APPENDED_BYTES];
#pragma DATA_ALIGN(rxDataEntryBuf1, 4);
static uint8_t rxDataEntryBuf1[DATA_ENTRY_HEADER_SIZE + MAX_LENGTH + LENGTH_POSITION - +NUM_APPENDED_BYTES];

#elif defined(__IAR_SYSTEMS_ICC__)
#pragma data_alignment = 4
static uint8_t rxDataEntryBuf0[DATA_ENTRY_HEADER_SIZE + MAX_LENGTH + LENGTH_POSITION + NUM_APPENDED_BYTES];
#pragma data_alignment = 4
static uint8_t rxDataEntryBuf1[DATA_ENTRY_HEADER_SIZE + MAX_LENGTH + LENGTH_POSITION + NUM_APPENDED_BYTES];

#elif defined(__GNUC__)
static uint8_t rxDataEntryBuf0[DATA_ENTRY_HEADER_SIZE + PACKET_HEADER_SIZE + LENGTH_FIELD_SIZE + MAX_LENGTH + NUM_APPENDED_BYTES] __attribute__((aligned(4)));
static uint8_t rxDataEntryBuf1[DATA_ENTRY_HEADER_SIZE + PACKET_HEADER_SIZE + LENGTH_FIELD_SIZE + MAX_LENGTH + NUM_APPENDED_BYTES] __attribute__((aligned(4)));

#else
#error This compiler is not supported.
#endif

// Receive dataQueue for RF Core to fill in data
static dataQueue_t dataQueue;
static uint16_t payloadLength;

rfc_dataEntryPartial_t *partialReadEntry0 = (rfc_dataEntryPartial_t *)&rxDataEntryBuf0;
rfc_dataEntryPartial_t *partialReadEntry1 = (rfc_dataEntryPartial_t *)&rxDataEntryBuf1;
rfc_dataEntryPartial_t *currentReadEntry = (rfc_dataEntryPartial_t *)&rxDataEntryBuf0;

rfc_propRxOutput_t rxStatistics;
static uint8_t lengthWritten = false;
static uint8_t cancelRx = false;
RF_Stat status = 0xFF;

// RX Semaphore
static Semaphore_Struct rxSemaphore;
static Semaphore_Handle rxSemaphoreHandle;

uint8_t packetHeader[PACKET_HEADER_SIZE];
uint8_t packetPayload[LENGTH_FIELD_SIZE + MAX_LENGTH];
uint8_t packetStatusBytes[NUM_APPENDED_BYTES];

// Debug
uint8_t eventNDataWritten = 0;
uint8_t eventRxOk = 0;
uint8_t eventCmdAborted = 0;
uint8_t eventRxBufFull = 0;
uint8_t eventRxEntryDone = 0;
uint8_t eventDataWritten = 0;
uint8_t eventRxAborted = 0;
uint8_t eventMdmSoft = 0;
uint8_t eventLastCmdDone = 0;
uint8_t dummy = 0;

// Function definitions

void *mainThread(void *arg0)
{
    RF_Params rfParams;
    RF_Params_init(&rfParams);

    GPIO_setConfig(CONFIG_GPIO_RLED, GPIO_CFG_OUT_STD | GPIO_CFG_OUT_LOW);
    GPIO_write(CONFIG_GPIO_RLED, CONFIG_GPIO_LED_OFF);

    /* Initialize RX semaphore */
    Semaphore_construct(&rxSemaphore, 0, NULL);
    rxSemaphoreHandle = Semaphore_handle(&rxSemaphore);

    partialReadEntry0->length = PACKET_HEADER_SIZE + LENGTH_FIELD_SIZE + MAX_LENGTH + NUM_APPENDED_BYTES + 4; // Make sure there is enough room for a complete packet in one data entry.
                                                                                                              // Number of bytes following this length field
                                                                                                              // + 4 is to make room for the pktStatus (2 bytes) and nextIndex (2 bytes)
    partialReadEntry0->config.irqIntv = PACKET_HEADER_SIZE + LENGTH_FIELD_SIZE;
    partialReadEntry0->config.type = DATA_ENTRY_TYPE_PARTIAL;
    partialReadEntry0->status = DATA_ENTRY_PENDING;

    partialReadEntry1->length = PACKET_HEADER_SIZE + LENGTH_FIELD_SIZE + MAX_LENGTH + NUM_APPENDED_BYTES + 4; // Make sure there is enough room for a complete packet in one data entry.
                                                                                                              // Number of bytes following this length field
                                                                                                              // + 4 is to make room for the pktStatus (2 bytes) and nextIndex (2 bytes)
    partialReadEntry1->config.irqIntv = PACKET_HEADER_SIZE + LENGTH_FIELD_SIZE;
    partialReadEntry1->config.type = DATA_ENTRY_TYPE_PARTIAL;
    partialReadEntry1->status = DATA_ENTRY_PENDING;

    partialReadEntry0->pNextEntry = (uint8_t *)partialReadEntry1;
    partialReadEntry1->pNextEntry = (uint8_t *)partialReadEntry0;

    dataQueue.pCurrEntry = (uint8_t *)partialReadEntry0;
    dataQueue.pLastEntry = NULL;

    // Modify CMD_PROP_RX command for application needs
    RF_cmdPropRx.pQueue = &dataQueue;
    RF_cmdPropRx.pOutput = (uint8_t *)&rxStatistics;
    RF_cmdPropRx.rxConf.bIncludeHdr = 1; // Must be 1 to receive the first byte after sync in the data entry
    RF_cmdPropRx.maxPktLen = 0;          // Unlimited length

    RF_cmdPropRx.rxConf.bAutoFlushCrcErr = 1;
    RF_cmdPropRx.pktConf.bRepeatOk = 0;
    RF_cmdPropRx.pktConf.bRepeatNok = 0;

    // Optional status bytes appended AFTER the payload
    // If these are changed, NUM_APPENDED_BYTES must also be updated
    RF_cmdPropRx.rxConf.bIncludeCrc = 0x0;      // 2 byte (if default CRC is used)
    RF_cmdPropRx.rxConf.bAppendRssi = 0x0;      // 1 byte
    RF_cmdPropRx.rxConf.bAppendStatus = 0x0;    // 1 Byte
    RF_cmdPropRx.rxConf.bAppendTimestamp = 0x0; // 4 bytes

    // Request access to the radio
    rfHandle = RF_open(&rfObject, &RF_prop, (RF_RadioSetup *)&RF_cmdPropRadioDivSetup, &rfParams);

    // Set the frequency
    RF_postCmd(rfHandle, (RF_Op *)&RF_cmdFs, RF_PriorityNormal, NULL, 0);

    while (true)
    {
        lengthWritten = false;
        cancelRx = false;
        status = 0xFF;

        eventNDataWritten = 0;
        eventRxOk = 0;
        eventCmdAborted = 0;
        eventRxBufFull = 0;
        eventRxEntryDone = 0;
        eventDataWritten = 0;
        eventRxAborted = 0;
        eventMdmSoft = 0;
        eventLastCmdDone = 0;

        rxHandle = RF_postCmd(rfHandle, (RF_Op *)&RF_cmdPropRx, RF_PriorityNormal, &callback, RF_EventNDataWritten | RF_EventRxOk | RF_EventRxBufFull | RF_EventCmdAborted | RF_EventMdmSoft /*|
                                                                                                                                                                          RF_EventCmdCancelled*/
        );                                                                                                                                                                                   // Not necessary, since this only happens if you cancel something that is not started

        Semaphore_pend(rxSemaphoreHandle, BIOS_WAIT_FOREVER); // Wait for cancelRx = true or RF_EventLastCmdDone

        if (cancelRx)
        {
            status = RF_cancelCmd(rfHandle, rxHandle, 0);
            Semaphore_pend(rxSemaphoreHandle, BIOS_WAIT_FOREVER); // Semaphore set after RF_EventCmdAborted (RF_EventLastCmdDone will not happen for RF_cancel)
        }
    }
}

void callback(RF_Handle h, RF_CmdHandle ch, RF_EventMask e)
{
    if (e & RF_EventNDataWritten)
    {
        GPIO_toggle(CONFIG_GPIO_RLED);
        eventNDataWritten++;

        if (!lengthWritten)
        {
            lengthWritten = true;

            if (LENGTH_FIELD_SIZE == 2)
            {
                payloadLength = (uint16_t)(((*(uint8_t *)(&currentReadEntry->rxData + LENGTH_FIELD_INDEX)) << 8) +
                                           (*(uint8_t *)(&currentReadEntry->rxData + LENGTH_FIELD_INDEX + 1)));
            }
            else
            {
                payloadLength = *(uint8_t *)(&currentReadEntry->rxData + LENGTH_FIELD_INDEX);
            }

            if (payloadLength > MAX_LENGTH)
            {
                cancelRx = true;
                Semaphore_post(rxSemaphoreHandle); // This takes us to "if (cancelRx)
            }
            else
            {
                RF_cmdPropSetLen.rxLen = payloadLength + PACKET_HEADER_SIZE + LENGTH_FIELD_SIZE - 1; // Must subtract 1 due to rxConf.bIncludeHdr = 1
                status = RF_runImmediateCmd(rfHandle, (uint32_t *)&RF_cmdPropSetLen);
            }
        }
    }

    if (e & RF_EventMdmSoft)
    {
        eventMdmSoft++;
    }

    if (e & RF_EventRxOk)
    {
        eventRxOk++;
        memcpy(packetHeader, (uint8_t *)(&currentReadEntry->rxData + 0), PACKET_HEADER_SIZE);
        memcpy(packetPayload, (uint8_t *)(&currentReadEntry->rxData + LENGTH_FIELD_INDEX), LENGTH_FIELD_SIZE + payloadLength);
        memcpy(packetStatusBytes, (uint8_t *)(&currentReadEntry->rxData + LENGTH_FIELD_INDEX + LENGTH_FIELD_SIZE + payloadLength), NUM_APPENDED_BYTES);
    }

    if (e & RF_EventLastCmdDone) // When RX is done due to CMD_SET_LEN (not happening when doing RF_cancel())
    {
        eventLastCmdDone++;
        currentReadEntry->status = DATA_ENTRY_PENDING;
        currentReadEntry = (rfc_dataEntryPartial_t *)currentReadEntry->pNextEntry;
        dataQueue.pCurrEntry = (uint8_t *)currentReadEntry;

        Semaphore_post(rxSemaphoreHandle);
    }

    if (e & RF_EventCmdAborted) // happens due to RF_cancel()
    {
        eventCmdAborted++;
        currentReadEntry->status = DATA_ENTRY_PENDING;
        currentReadEntry = (rfc_dataEntryPartial_t *)currentReadEntry->pNextEntry;
        dataQueue.pCurrEntry = (uint8_t *)currentReadEntry;

        Semaphore_post(rxSemaphoreHandle);
    }

    if (e & RF_EventRxBufFull) // This will happen BEFORE the RF_EventLastCmdDone
    {
        currentReadEntry->status = DATA_ENTRY_PENDING;
        currentReadEntry = (rfc_dataEntryPartial_t *)currentReadEntry->pNextEntry;
        dataQueue.pCurrEntry = (uint8_t *)currentReadEntry;

        eventRxBufFull++;
    }
}