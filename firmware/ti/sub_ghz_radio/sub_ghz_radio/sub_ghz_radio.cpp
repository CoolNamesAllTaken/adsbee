#include "sub_ghz_radio.hh"
#include "pico.hh" // For LED blinks.
#include "uat_packet_decoder.hh"
#include "macros.hh"
#include "hal.hh"

extern "C"
{
#include "ti/devices/cc13x2_cc26x2/driverlib/rf_prop_mailbox.h" // For status codes.
}

static const uint32_t kRxRestartTimeoutMs = 5000;

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

static const RF_EventMask kRxEventMask = RF_EventMdmSoft | RF_EventNDataWritten | (RF_EventRxEntryDone | RF_EventRxOk | RF_EventRxNOk) | (RF_EventLastCmdDone | RF_EventCmdCancelled | RF_EventCmdAborted | RF_EventCmdStopped);

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

// This is the entry that we are currently allowed to read from (not being used by the RF core).
static rfc_dataEntryPartial_t *current_read_entry;

static dataQueue_t rx_data_queue;
static bool rx_data_length_written = false;

static bool rx_ended = false;

inline void RollDataQueue()
{
    current_read_entry->status = DATA_ENTRY_PENDING;
    current_read_entry = (rfc_dataEntryPartial_t *)(((rfc_dataEntryPartial_t *)current_read_entry)->pNextEntry);
}

// Technical Reference Manual Section 23.7.5.4: https://www.ti.com/lit/ug/swcu117i/swcu117i.pdf
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

    if (e & RF_EventRxOk)
    {
        RollDataQueue();
        subg_radio.HandlePacketRx((rfc_dataEntryPartial_t *)(current_read_entry));
        // last_rx_start_timestamp_ms_ = get_time_since_boot_ms();
        // RF_postCmd(h, (RF_Op *)&RF_cmdPropRxAdv, RF_PriorityNormal, rf_cmd_callback, kRxEventMask);
    }

    if (e & (RF_EventLastCmdDone | RF_EventCmdAborted))
    {
        // subg_radio.HandlePacketRx((rfc_dataEntryPartial_t *)(rx_data_queue.pLastEntry));
        RollDataQueue();
        rx_ended = true;
    }

    if (e & RF_EventRxBufFull)
    {
        RollDataQueue();
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

    // Overriding settings from smartrf/smartrf_settings.c.
    /* RF_cmdPropRxAdv  - Advanced Rx command settings. */
    RF_cmdPropRxAdv.pQueue = &rx_data_queue;
    RF_cmdPropRxAdv.pOutput = (uint8_t *)&rx_statistics_;
    RF_cmdPropRxAdv.rxConf = {
        .bAutoFlushIgnored = 0, // If 1, automatically discard ignored packets from RX queue.
        .bAutoFlushCrcErr = 0,  // If 1, automatically discard packets with CRC error from RX queue.
        // bIncludeHdr must be 1 to receive the first byte after sync in the data entry. For UAT this is the last byte of the full 36 bit sync word.
        .bIncludeHdr = 1,      // If 1, include the received header or length byte in the stored packet; otherwise discard it.
        .bIncludeCrc = 0,      // 2 bytes (if default CRC is used)
        .bAppendRssi = 1,      // 1 byte
        .bAppendTimestamp = 1, // 4 bytes
        .bAppendStatus = 1     // 1 Byte
    };
    // RF_cmdPropRxAdv.pktConf.bRepeatOk = 0;  // Go back to sync search after receiving a packet correctly.
    // RF_cmdPropRxAdv.pktConf.bRepeatNok = 0; // Go back to sync search after receiving a packet incorrectly.
    // Sync on the most significant 32 bits of the 36 bit sync word. Save the last 4 bits of sync for discrimination between uplink and ADSB packets in the payload.
    // RF_cmdPropRx.syncWord = RawUATADSBPacket::kSyncWordMS32;
    RF_cmdPropRxAdv.syncWord0 = RawUATADSBPacket::kSyncWordMS32;
    RF_cmdPropRxAdv.syncWord1 = RawUATUplinkPacket::kSyncWordMS32;
    RF_cmdPropRxAdv.maxPktLen = 0; // Unlimited length

    // The last 4 bits of the Sync word are interpreted as the header, so the rest of the packet stays byte-aligned.
    RF_cmdPropRxAdv.hdrConf = {
        .numHdrBits = 4,
        .lenPos = 0,
        .numLenBits = 0};

    // No address field.
    RF_cmdPropRxAdv.addrConf = {0};

    /* RF_cmdPropRadioDivSetup - Radio setup command settings. */
    RF_cmdPropRadioDivSetup.formatConf.nSwBits = 32; // Use a 32-bit sync word to allow the last 4 bits of the sync to be used for format discrimination.

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
    rx_data_queue.pLastEntry = nullptr;

    current_read_entry = (rfc_dataEntryPartial_t *)(rx_data_queue.pCurrEntry);

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

    return StartPacketRx();
}

bool SubGHzRadio::DeInit()
{
    RF_close(rf_handle_);
    return true;
}

bool SubGHzRadio::HandlePacketRx(rfc_dataEntryPartial_t *filled_entry)
{
    // pico_ll.BlinkSubGLED();
    // RollDataQueue();

    /* Handle the packet data, located at &currentDataEntry->data:
     * - Length is the first two bytes with the current configuration
     * - Data starts from the second byte */
    // rfc_dataEntryPartial_t *filled_entry = (rfc_dataEntryPartial_t *)rx_data_queue.pLastEntry;
    uint8_t *buf = (uint8_t *)(&filled_entry->rxData);
    uint16_t packet_len_bytes = buf[0];

    if (packet_len_bytes > kRxPacketMaxLenBytes || packet_len_bytes == 0)
    {
        return false;
    }
    uint8_t *packet_data = buf + kPartialDataEntryPayloadLenSzBytes;

    RawUATADSBPacket raw_packet = RawUATADSBPacket(packet_data, packet_len_bytes);
    uat_packet_decoder.raw_uat_adsb_packet_queue.Enqueue(raw_packet);

    return true;
}

bool SubGHzRadio::StartPacketRx()
{
    last_rx_start_timestamp_ms_ = get_time_since_boot_ms();
    rx_cmd_handle_ = RF_postCmd(rf_handle_, (RF_Op *)&RF_cmdPropRxAdv, RF_PriorityNormal, rf_cmd_callback, kRxEventMask);
    if (rx_cmd_handle_ < 0)
    {
        CONSOLE_ERROR("SubGHzRadio::Init", "Failed to post command PROP_RX: returned code %d.", rx_cmd_handle_);
        return false; // Failed to post command PROP_RX.
    }
    return true;
}

bool SubGHzRadio::Update()
{
    // if (rx_stopped)
    // {
    //     rx_stopped = false;
    //     RF_postCmd(rf_handle_, (RF_Op *)&RF_cmdPropRx, RF_PriorityNormal, rf_cmd_callback, kRxEventMask);
    // }

    // Start at the entry after the one currently being filled, traverse until we run into an entry that is still pending.
    // rfc_dataEntryPartial_t *entry = (rfc_dataEntryPartial_t *)(((rfc_dataEntryPartial_t *)rx_data_queue.pCurrEntry)->pNextEntry);
    // for (uint16_t i = 0; i < kNumPartialDataEntries; i++)
    // {
    //     if (entry->status < DATA_ENTRY_FINISHED)
    //     {
    //         continue;
    //     }
    //     HandlePacketRx(entry);
    //     entry->status = DATA_ENTRY_PENDING;
    //     entry = (rfc_dataEntryPartial_t *)(entry->pNextEntry);
    // }
    // if (rx_ended)
    // {
    //     rx_ended = false;
    //     StartPacketRx();
    // }

    volatile uint16_t rx_status = ((volatile RF_Op *)&RF_cmdPropRxAdv)->status;
    if ((rx_status & 0xFF00) & PROP_DONE_OK)
    {
        StartPacketRx();
    }
    else if ((rx_status & 0xFF00) & PROP_ERROR_PAR)
    {
        char *error_str;
        switch (rx_status)
        {
        case PROP_ERROR_PAR:
            error_str = (char *)"Illegal parameter";
            break;
        case PROP_ERROR_RXBUF:
            error_str = (char *)"No available Rx buffer at the start of a packet";
            break;
        case PROP_ERROR_RXFULL:
            error_str = (char *)"Out of Rx buffer during reception in a partial read buffer";
            break;
        case PROP_ERROR_NO_SETUP:
            error_str = (char *)"Radio was not set up in proprietary mode";
            break;
        case PROP_ERROR_NO_FS:
            error_str = (char *)"Synth was not programmed when running Rx or Tx";
            break;
        case PROP_ERROR_RXOVF:
            error_str = (char *)"Rx overflow observed during operation";
            break;
        case PROP_ERROR_TXUNF:
            error_str = (char *)"Tx underflow observed during operation";
            break;
        default:
            error_str = (char *)"Unknown error";
        }
        CONSOLE_ERROR("SubGHzRadio::Update", "PROP_RX threw error (0x%x): %s. Restarting.", rx_status, error_str);
        StartPacketRx();
    }

    if (get_time_since_boot_ms() - last_rx_start_timestamp_ms_ > kRxRestartTimeoutMs)
    {
        //     last_rx_start_timestamp_ms_ = get_time_since_boot_ms();
        //     RF_postCmd(rf_handle_, (RF_Op *)&RF_cmdPropRxAdv, RF_PriorityNormal, rf_cmd_callback, kRxEventMask);
    }
    return true;
}