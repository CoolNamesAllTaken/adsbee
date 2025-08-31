#include "sub_ghz_radio.hh"
#include "pico.hh" // For LED blinks.
#include "uat_packet_decoder.hh"
#include "macros.hh"

static const uint16_t kNumPartialDataEntries = SubGHzRadio::kRxPacketQueueLen;
static const uint16_t kPartialDataEntryHeaderSizeBytes = 12;
static const uint16_t kPartialDataEntryNumAppendedBytes = 6; // Appended Bytes determined by the settings below.
// .rxConf.bIncludeCrc = 0x0;       // 2 bytes (if default CRC is used)
// .rxConf.bAppendRssi = 0x1;       // 1 byte
// .rxConf.bAppendTimestamp = 0x1;  // 4 bytes
// .rxConf.bAppendStatus = 0x1;     // 1 byte
static const uint16_t kPartialDataEntryPayloadSizeBytes = SubGHzRadio::kRxPacketMaxLenBytes;
static const uint16_t kPartialDataEntryPayloadLenSzBytes = 2; // Length field size in bytes.

static const uint16_t kPartialDataEntrySizeBytes = sizeof(rfc_dataEntryPartial_t) + kPartialDataEntryPayloadLenSzBytes + kPartialDataEntryPayloadSizeBytes + kPartialDataEntryNumAppendedBytes;
static_assert(kPartialDataEntryHeaderSizeBytes % 4 == 0, "Partial Data Entry Header Size must be word aligned.");

static const RF_EventMask kRxEventMask = RF_EventRxEntryDone | RF_EventNDataWritten | RF_EventRxOk | RF_EventRxBufFull | RF_EventCmdAborted | RF_EventMdmSoft;

static volatile uint16_t current_packet_len_bytes = 0;

// Bool used to indicate that receiving was cancelled and needs to be restarted.
volatile static bool rx_stopped = false;

// Packet RX Configuration
//  ------------------------------------------------------------------------------------------------------------------------
//  | Partial Data Entry Header | Payload Length (lenSz Bytes) | Payload Bytes | Optional Appended Bytes
//  ------------------------------------------------------------------------------------------------------------------------

// Optional appended bytes
//  -------------------------------------------------------
//  | CRC1 | CRC0 | RSSI | TS0 | TS1 | TS2 | TS3 | Status |
//  -------------------------------------------------------
static uint8_t rx_data_entry_buf[kNumPartialDataEntries * kPartialDataEntrySizeBytes] __attribute__((aligned(4)));
static rfc_dataEntryPartial_t *partial_data_entry_ptrs[kNumPartialDataEntries] = {0};

static dataQueue_t rx_data_queue;
static bool rx_data_length_written = false;

inline void RollDataQueue()
{
    // We read from pLastEntry, RF core writes to pCurrEntry.
    ((rfc_dataEntryPartial_t *)rx_data_queue.pCurrEntry)->status = DATA_ENTRY_PENDING;
    rx_data_queue.pLastEntry = rx_data_queue.pCurrEntry;
    rx_data_queue.pCurrEntry = ((rfc_dataEntryPartial_t *)rx_data_queue.pCurrEntry)->pNextEntry;
}

void rf_cmd_callback(RF_Handle h, RF_CmdHandle ch, RF_EventMask e)
{
    // CONSOLE_INFO("SubGHzRadio", "RF command completed with handle %p, command handle %d, event mask %u", h, ch, e);

    if (e & RF_EventMdmSoft)
    {
        // Preamble detected. Get ready to figure out packet length!
        rx_data_length_written = false;
    }

    if (e & RF_EventNDataWritten)
    {
        if (!rx_data_length_written)
        {
            // Only set the length once, after receiving the first two bytes of the packet.
            rx_data_length_written = true;

            // TODO: Set this value based on bytes received so far.
            current_packet_len_bytes = 34;

            rfc_CMD_PROP_SET_LEN_t RF_cmdPropSetLen = {
                .commandNo = 0x3401,
                .rxLen = (uint16_t)(current_packet_len_bytes - 1) // Subtract 1 Byte to account for last Byte of sync (header byte) being automatically included in entry due to bIncludeHdr=1
            };
            RF_runImmediateCmd(h, (uint32_t *)&RF_cmdPropSetLen);
        }
    }

    if (e & (RF_EventRxOk | RF_EventLastCmdDone | RF_EventCmdAborted | RF_EventRxBufFull))
    {
        RollDataQueue();
        subg_radio.HandlePacketRx();
        RF_postCmd(h, (RF_Op *)&RF_cmdPropRx, RF_PriorityNormal, rf_cmd_callback, kRxEventMask);
    }

    // if ((e & RF_EventRxOk) /*e & RF_EventRxEntryDone*/)
    // {
    //     RollDataQueue();
    //     subg_radio.HandlePacketRx();

    //     // Run it again!
    //     // rx_data_length_written = false;
    //     // RF_postCmd(h, (RF_Op *)&RF_cmdPropRx, RF_PriorityNormal, rf_cmd_callback, kRxEventMask);
    // }
    // if ((e & RF_EventLastCmdDone) || (e & RF_EventCmdAborted))
    // {
    //     // Command completed or aborted; we will need to re-launch.
    //     RollDataQueue();
    //     // rx_data_length_written = false;
    //     rx_stopped = true; // Trigger a restart from the main update loop.
    // }
    // if ((e & RF_EventRxBufFull))
    // {
    //     RollDataQueue();
    //     subg_radio.HandlePacketRx();

    //     // Run it again!
    //     // rx_data_length_written = false;
    //     // RF_postCmd(h, (RF_Op *)&RF_cmdPropRx, RF_PriorityNormal, rf_cmd_callback, kRxEventMask);
    // }
}

bool SubGHzRadio::Init()
{
    RF_Params rf_params;
    RF_Params_init(&rf_params);

    // Override cmdPropRxAdv settings.
    // All other RF_cmdPropRx settings are from smartrf/smartrf_settings.h.
    RF_cmdPropRx.pQueue = &rx_data_queue;
    RF_cmdPropRx.pOutput = (uint8_t *)&rx_statistics_;
    RF_cmdPropRx.rxConf.bIncludeHdr = 1; // Must be 1 to receive the first byte after sync in the data entry. For UAT this is the last byte of the full 36 bit sync word.
    RF_cmdPropRx.maxPktLen = 33;         // Unlimited length
    RF_cmdPropRx.rxConf.bAutoFlushCrcErr = 1;
    // RF_cmdPropRx.pktConf.bRepeatOk = 1;  // Go back to sync search after receiving a packet correctly.
    // RF_cmdPropRx.pktConf.bRepeatNok = 1; // Go back to sync search after receiving a packet incorrectly.
    // Sync on the most significant 28 bits of the 36 bit sync word. Save the last 8 bits of sync for discrimination between uplink and ADSB packets in the payload.
    RF_cmdPropRxAdv.syncWord0 = RawUATADSBPacket::kSyncWordMS28;
    RF_cmdPropRxAdv.syncWord1 = RawUATUplinkPacket::kSyncWordMS28;

    // Set up the data queue.
    for (uint16_t i = 0; i < kNumPartialDataEntries; i++)
    {
        // Fill out the addresses first so that our pNextEntry assignment works in the next loop.
        partial_data_entry_ptrs[i] = (rfc_dataEntryPartial_t *)&rx_data_entry_buf[i * kPartialDataEntrySizeBytes];
    }
    for (uint16_t i = 0; i < kNumPartialDataEntries; i++)
    {
        rfc_dataEntryPartial_t *entry = partial_data_entry_ptrs[i];
        entry->length = sizeof(rfc_dataEntryPartial_t::pktStatus) + sizeof(rfc_dataEntryPartial_t::nextIndex) + kPartialDataEntryPayloadSizeBytes + kPartialDataEntryNumAppendedBytes;
        entry->config.irqIntv = 2; // Set interrupt interval to 2 bytes.
        entry->config.type = DATA_ENTRY_TYPE_PARTIAL;
        entry->config.lenSz = kPartialDataEntryPayloadLenSzBytes;
        entry->status = DATA_ENTRY_PENDING;
        entry->pNextEntry = (uint8_t *)partial_data_entry_ptrs[(i + 1) % kNumPartialDataEntries]; // Circular queue.

        // Sentinel values for debuging.
        memset(&(entry->rxData) + kPartialDataEntryPayloadLenSzBytes, 0xAA + i, kPartialDataEntryPayloadSizeBytes + kPartialDataEntryNumAppendedBytes);
    }
    rx_data_queue.pCurrEntry = (uint8_t *)partial_data_entry_ptrs[0];

    rf_handle_ = RF_open(&rf_object_, &RF_prop, (RF_RadioSetup *)&RF_cmdPropRadioDivSetup, &rf_params);
    if (!rf_handle_)
    {
        CONSOLE_ERROR("SubGHzRadio::Init", "Failed to open RF device.");
        return false; // Failed to open RF handle.
    }

    RF_EventMask ret = RF_runCmd(rf_handle_, (RF_Op *)&RF_cmdFs, RF_PriorityNormal, nullptr, 0);
    if (ret != RF_EventLastCmdDone)
    {
        CONSOLE_ERROR("SubGHzRadio::Init", "Failed to set frequency.");
        RF_close(rf_handle_);
        return false; // Failed to run command FS.
    }

    RF_CmdHandle cmd = RF_runCmd(rf_handle_, (RF_Op *)&RF_cmdPropRx, RF_PriorityNormal, rf_cmd_callback, kRxEventMask);
    if (cmd < 0)
    {
        CONSOLE_ERROR("SubGHzRadio::Init", "Failed to post command PROP_RX: returned code %d.", cmd);
        RF_close(rf_handle_);
        return false; // Failed to post command PROP_RX.
    }
    return true;
}

bool SubGHzRadio::HandlePacketRx()
{
    // pico_ll.BlinkSubGLED();
    // RollDataQueue();

    /* Handle the packet data, located at &currentDataEntry->data:
     * - Length is the first two bytes with the current configuration
     * - Data starts from the second byte */
    rfc_dataEntryPartial_t *filled_entry = (rfc_dataEntryPartial_t *)rx_data_queue.pLastEntry;
    uint8_t *buf = (uint8_t *)(&filled_entry->rxData);
    uint16_t packet_len_bytes = (buf[0] << 8) | buf[1];
    uint8_t *packet_data = buf + kPartialDataEntryPayloadLenSzBytes;

    RawUATADSBPacket raw_packet = RawUATADSBPacket(packet_data, packet_len_bytes);
    uat_packet_decoder.raw_uat_adsb_packet_queue.Enqueue(raw_packet);

    return true;
}

bool SubGHzRadio::Update()
{
    // if (rx_stopped)
    // {
    //     rx_stopped = false;
    //     RF_postCmd(rf_handle_, (RF_Op *)&RF_cmdPropRx, RF_PriorityNormal, rf_cmd_callback, kRxEventMask);
    // }
    return true;
}