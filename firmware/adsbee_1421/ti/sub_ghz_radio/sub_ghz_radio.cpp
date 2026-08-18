#include "sub_ghz_radio.hh"

#include <posix/unistd.h>  // For usleep.

#include "adsbee.hh"
#include "hal.hh"
#include "macros.hh"
#include "uat_packet_decoder.hh"
#include "unit_conversions.hh"  // for CeilBitsToBytes

extern "C" {
#include DeviceFamily_constructPath(driverlib/rf_prop_mailbox.h)  // For status codes.
}

static const uint32_t kRxRestartTimeoutMs = 5000;
// Max wait for CMD_TX_TEST (TRIG_NOW) to leave the PENDING state after being posted.
static const uint32_t kCWTestStartTimeoutMs = 100;

static const uint16_t kNumPartialDataEntries = SubGHzRadio::kRxPacketQueueLen;
static const uint16_t kPartialDataEntryHeaderSizeBytes = 12;
static const uint16_t kPartialDataEntryNumAppendedBytes = 6;  // Appended Bytes determined by the settings below.
static const uint16_t kPartialDataEntryPayloadSizeBytes = SubGHzRadio::kRxPacketMaxLenBytes;
static const uint16_t kPartialDataEntryPayloadLenSzBytes = 2;  // Length field size in bytes.

static const uint16_t kPacketHeaderSizeBytes = 1;  // Equivalent to CeilBitsToBytes(RF_cmdPropRxAdv.hdrConf.numHdrBits);

static const uint16_t kPartialDataEntrySizeBytes = sizeof(rfc_dataEntryPartial_t) + kPartialDataEntryPayloadLenSzBytes +
                                                   kPacketHeaderSizeBytes + kPartialDataEntryPayloadSizeBytes +
                                                   kPartialDataEntryNumAppendedBytes;
static_assert(kPartialDataEntryHeaderSizeBytes % 4 == 0, "Partial Data Entry Header Size must be word aligned.");

static const RF_EventMask kRxEventMask =
    RF_EventMdmSoft | RF_EventNDataWritten | (RF_EventRxEntryDone | RF_EventRxOk | RF_EventRxNOk) |
    (RF_EventLastCmdDone | RF_EventCmdCancelled | RF_EventCmdAborted | RF_EventCmdStopped);

static volatile int16_t current_packet_len_bytes = INT16_MIN;

// Packet RX Configuration
//  ------------------------------------------------------------------------------------------------------------------------
//  | Partial Data Entry Header | Payload Length (lenSz Bytes) | Payload Bytes | Optional Appended Bytes
//  ------------------------------------------------------------------------------------------------------------------------

// Optional appended bytes
//  -------------------------------------------------------
//  | CRC1 | CRC0 | RSSI | TS0 | TS1 | TS2 | TS3 | Status |
//  -------------------------------------------------------
static uint8_t rx_data_entry_buf[kNumPartialDataEntries * kPartialDataEntrySizeBytes] __attribute__((aligned(4)));
static rfc_dataEntryPartial_t* partial_data_entry_ptrs[kNumPartialDataEntries] = {0};

// This is the entry that we are currently allowed to read from (not being used by the RF core).
static rfc_dataEntryPartial_t* current_read_entry;

static dataQueue_t rx_data_queue;

inline void RollDataQueue() {
    current_read_entry->status = DATA_ENTRY_PENDING;
    current_read_entry = (rfc_dataEntryPartial_t*)(((rfc_dataEntryPartial_t*)current_read_entry)->pNextEntry);
    rx_data_queue.pCurrEntry = (uint8_t*)current_read_entry;
}

// Technical Reference Manual Section 23.7.5.4: https://www.ti.com/lit/ug/swcu117i/swcu117i.pdf
void rf_cmd_callback(RF_Handle h, RF_CmdHandle ch, RF_EventMask e) {
    // CONSOLE_INFO("SubGHzRadio", "RF command completed with handle %p, command handle %d, event mask %u", h, ch, e);

    if (e & RF_EventMdmSoft) {
        // Preamble detected. Get ready to figure out packet length!
        current_packet_len_bytes = INT16_MIN;
    }

    if (e & RF_EventNDataWritten) {
        if (current_packet_len_bytes < 0) {
            // Only set the length once per packet (irqIntv=0 fires at 16 bytes; rxData[2] and [3] are ready).
            uint8_t sync_word_ls4 = (&(current_read_entry->rxData))[kPartialDataEntryPayloadLenSzBytes] &
                                    0x0F;  // Last 4 bits of sync word are the first 4 bits of the payload.
            uint8_t mdb_type_code = (&(current_read_entry->rxData))[kPartialDataEntryPayloadLenSzBytes + 1] >> 3;
            current_packet_len_bytes =
                UATPacketDecoder::SyncWordLSBAndMDBTypeCodeToMessageLenBytes(sync_word_ls4, mdb_type_code);

            rfc_CMD_PROP_SET_LEN_t RF_cmdPropSetLen = {.commandNo = CMD_PROP_SET_LEN,
                                                       .rxLen = (uint16_t)(current_packet_len_bytes)};
            RF_runImmediateCmd(h, (uint32_t*)&RF_cmdPropSetLen);
        }
    }

    if (e & RF_EventRxOk) {
        // rx_enabled is false while a debug RSSI scan owns the RX command; drop anything that
        // happens to match a UAT sync word off-frequency instead of feeding it to the decoder.
        if (subg_radio.rx_enabled) {
            subg_radio.HandlePacketRx(current_read_entry);
        }
    }

    if (e & (RF_EventLastCmdDone | RF_EventCmdAborted | RF_EventRxBufFull)) {
        RollDataQueue();
    }
}

bool SubGHzRadio::Init() {
    RF_Params rf_params;
    RF_Params_init(&rf_params);

    // Overriding settings from smartrf/smartrf_settings.c.
    /* RF_cmdPropRxAdv  - Advanced Rx command settings. */
    RF_cmdPropRxAdv.pQueue = &rx_data_queue;
    RF_cmdPropRxAdv.pOutput = (uint8_t*)&rx_statistics_;
    RF_cmdPropRxAdv.rxConf = {
        .bAutoFlushIgnored = 0,  // If 1, automatically discard ignored packets from RX queue.
        .bAutoFlushCrcErr = 0,   // If 1, automatically discard packets with CRC error from RX queue.
        // bIncludeHdr must be 1 to receive the first byte after sync in the data entry. For UAT this is the last byte
        // of the full 36 bit sync word.
        .bIncludeHdr =
            1,  // If 1, include the received header or length byte in the stored packet; otherwise discard it.
        .bIncludeCrc = 0,       // 2 bytes (if default CRC is used)
        .bAppendRssi = 1,       // 1 byte
        .bAppendTimestamp = 1,  // 4 bytes
        .bAppendStatus = 1      // 1 Byte
    };
    // RF_cmdPropRxAdv.pktConf.bRepeatOk = 0;  // Go back to sync search after receiving a packet correctly.
    // RF_cmdPropRxAdv.pktConf.bRepeatNok = 0; // Go back to sync search after receiving a packet incorrectly.
    // Sync on the most significant 32 bits of the 36 bit sync word. Save the last 4 bits of sync for discrimination
    // between uplink and ADSB packets in the payload. syncWord1 is "alternative sync word if non-zero"
    // (rf_prop_cmd.h), so 0 disables uplink reception at the RF core entirely (AT+SUBG_MODE=UAT_RX_NO_UPLINK):
    // no 552-byte receptions and no FEC decode work for uplinks.
    RF_cmdPropRxAdv.syncWord0 = RawUATADSBPacket::kSyncWordMS32;
    RF_cmdPropRxAdv.syncWord1 = UplinkRxEnabled() ? RawUATUplinkPacket::kSyncWordMS32 : 0;

    // Must be 0 (unlimited) so that CMD_PROP_SET_LEN (called in RF_EventNDataWritten) can shorten reception for
    // ADSB packets instead of always receiving the full 552-byte uplink length. If the RF callback is preempted
    // before CMD_PROP_SET_LEN fires, the RF core keeps writing until the data entry is full (kRxPacketMaxLenBytes),
    // at which point PROP_ERROR_RXFULL fires — not a memory stomp. RF software interrupt priority must be higher
    // than SPI priority; 1 point higher works well, higher values cause instability.
    RF_cmdPropRxAdv.maxPktLen = 0;

    // The last 4 bits of the Sync word are interpreted as the header, so the rest of the packet stays byte-aligned.
    RF_cmdPropRxAdv.hdrConf = {.numHdrBits = 4, .lenPos = 0, .numLenBits = 0};

    // No address field.
    RF_cmdPropRxAdv.addrConf = {0};

    /* RF_cmdPropRadioDivSetup - Radio setup command settings. */
    RF_cmdPropRadioDivSetup.formatConf.nSwBits =
        32;  // Use a 32-bit sync word to allow the last 4 bits of the sync to be used for format discrimination.

    // Set up the data queue.
    for (uint16_t i = 0; i < kNumPartialDataEntries; i++) {
        // Fill out the addresses first so that our pNextEntry assignment works in the next loop.
        partial_data_entry_ptrs[i] = (rfc_dataEntryPartial_t*)&rx_data_entry_buf[i * kPartialDataEntrySizeBytes];
    }

    for (uint16_t i = 0; i < kNumPartialDataEntries; i++) {
        rfc_dataEntryPartial_t* entry = partial_data_entry_ptrs[i];
        entry->length = sizeof(rfc_dataEntryPartial_t::pktStatus) + sizeof(rfc_dataEntryPartial_t::nextIndex) +
                        kPacketHeaderSizeBytes + kPartialDataEntryPayloadLenSzBytes +
                        kPartialDataEntryPayloadSizeBytes + kPartialDataEntryNumAppendedBytes;
        entry->config.irqIntv = 0;  // Set interrupt interval. We only need 1 byte after the header, increase to reduce
                                    // interrupt frequency. 0=16
        entry->config.type = DATA_ENTRY_TYPE_PARTIAL;
        entry->config.lenSz = kPartialDataEntryPayloadLenSzBytes;
        entry->status = DATA_ENTRY_PENDING;
        entry->pNextEntry = (uint8_t*)partial_data_entry_ptrs[(i + 1) % kNumPartialDataEntries];  // Circular queue.

        // Sentinel values for debuging.
        memset(&(entry->rxData) + kPartialDataEntryPayloadLenSzBytes, 0xAA + i,
               kPartialDataEntryPayloadSizeBytes + kPartialDataEntryNumAppendedBytes);
    }
    rx_data_queue.pCurrEntry = (uint8_t*)partial_data_entry_ptrs[0];
    rx_data_queue.pLastEntry = nullptr;

    current_read_entry = (rfc_dataEntryPartial_t*)(rx_data_queue.pCurrEntry);

    rf_handle_ = RF_open(&rf_object_, &RF_prop, (RF_RadioSetup*)&RF_cmdPropRadioDivSetup, &rf_params);
    if (!rf_handle_) {
        CONSOLE_ERROR("SubGHzRadio::Init", "Failed to open RF device.");
        return false;  // Failed to open RF handle.
    }

    RF_EventMask ret = RF_runCmd(rf_handle_, (RF_Op*)&RF_cmdFs, RF_PriorityNormal, nullptr, 0);
    if (ret != RF_EventLastCmdDone) {
        CONSOLE_ERROR("SubGHzRadio::Init", "Failed to set frequency.");
        RF_close(rf_handle_);
        rf_handle_ = nullptr;
        return false;  // Failed to run command FS.
    }

    return StartPacketRx();
}

bool SubGHzRadio::DeInit() {
    if (rf_handle_ != nullptr) {
        RF_close(rf_handle_);
        rf_handle_ = nullptr;
    }
    return true;
}

bool SubGHzRadio::Suspend() {
    if (rf_handle_ == nullptr) {
        return true;  // Already closed (e.g. user-disabled via AT+RX_ENABLE): nothing holds the RF core.
    }
    // Release the RF core so the MCU can reach STANDBY: the RF core holds a
    // PowerCC26XX_DISALLOW_STANDBY constraint the entire time it is powered. Abort the continuous RX
    // command (abrupt mode 0 -- it has no graceful stopping boundary), then DeInit()'s RF_close pends
    // on the queue and powers the RF core down, releasing the constraint. Mirrors the CW-test restore.
    rx_enabled = false;
    RF_cancelCmd(rf_handle_, rx_cmd_handle_, 0);
    return DeInit();
}

bool SubGHzRadio::Resume() {
    // Re-open the RF core and restart UAT reception after a Suspend()/STANDBY cycle (unless the user has
    // the receiver disabled). Init() re-runs the full RF_open + CMD_FS + StartPacketRx sequence, the same
    // known-good path StopCWTest() uses.
    return RestoreRx();
}

bool SubGHzRadio::RestoreRx() {
    if (!rx_requested_) {
        rx_enabled = false;
        return true;  // User has the receiver disabled: leave the RF client closed.
    }
    rx_enabled = true;
    return Init();
}

bool SubGHzRadio::SetRxEnabled(bool enabled) {
    rx_requested_ = enabled;
    if (!enabled) {
        if (rf_handle_ == nullptr || !rx_enabled) {
            // Already closed, or a CW/RSSI test / Suspend() owns the RF core: its restore path (RestoreRx()) will
            // honor rx_requested_ and leave the radio closed.
            return true;
        }
        // Same teardown as Suspend(): abort the continuous RX command and close the RF client.
        rx_enabled = false;
        RF_cancelCmd(rf_handle_, rx_cmd_handle_, 0);
        return DeInit();
    }
    if (rf_handle_ != nullptr) {
        // Already receiving, or a CW/RSSI test owns the RF core and its Stop*() -> RestoreRx() will bring RX up.
        return true;
    }
    rx_enabled = true;
    return Init();
}

bool SubGHzRadio::SetMode(SettingsManager::SubGHzRadioMode mode) {
    if (mode >= SettingsManager::kNumSubGHzRadioModes) {
        // Guard against stale persisted settings holding a removed enum value (mirrors ADSBee::SetR1090PreambleMode).
        mode = SettingsManager::kSubGHzRadioModeUATRx;
    }
    if (mode == mode_) {
        return true;
    }
    mode_ = mode;

    // Nothing to restart if the RF client is closed (before Init(), Suspend()ed, user-disabled) or a CW/RSSI test
    // owns the RX command: Init()/RestoreRx() reads mode_ when reception next comes up.
    if (rf_handle_ == nullptr || !rx_enabled) {
        return true;
    }

    // syncWord1 is only read when CMD_PROP_RX_ADV starts, and re-posting the aborted RF_cmdPropRxAdv without an
    // RF_close/RF_open cycle is rejected with PROP_ERROR_PAR (see StartRssiScan()), so tear the client down and
    // rebuild it exactly like Suspend()/Resume(). Clear the stale DONE_ABORT status first so Update() can't
    // misread it as "RX ended" and double-post before the RF core marks the new command PENDING.
    RF_cancelCmd(rf_handle_, rx_cmd_handle_, 0);
    DeInit();
    ((RF_Op*)&RF_cmdPropRxAdv)->status = IDLE;
    if (!Init()) {
        CONSOLE_ERROR("SubGHzRadio::SetMode", "Failed to restart RX in mode %s.",
                      SettingsManager::kSubGHzModeStrs[mode_]);
        return false;
    }
    return true;
}

bool SubGHzRadio::HandlePacketRx(rfc_dataEntryPartial_t* filled_entry) {
    /* Handle the packet data, located at &currentDataEntry->data:
     * - Length is the first two bytes with the current configuration
     * - Data starts from the second byte */
    // rfc_dataEntryPartial_t *filled_entry = (rfc_dataEntryPartial_t *)rx_data_queue.pLastEntry;
    uint8_t* buf = (uint8_t*)(&filled_entry->rxData);
    uint16_t rx_data_bytes_after_len =
        buf[0] | (buf[1] << 8);  // 2-Byte length is packaged LSB first (little endian). Includes appended bytes.
    uint16_t packet_len_bytes = rx_data_bytes_after_len - kPartialDataEntryNumAppendedBytes - kPacketHeaderSizeBytes;
    // Note that filled_entry->nextIndex should == packet_len_bytes + kPartialDataEntryNumAppendedBytes.
    uint8_t packet_sync_ls4 = buf[2] & 0x0F;  // Last 4 bits of sync word are the first 4 bits of the payload.
    uint8_t* packet_data = buf + kPartialDataEntryPayloadLenSzBytes + kPacketHeaderSizeBytes;

    if (packet_len_bytes > kRxPacketMaxLenBytes || packet_len_bytes == 0) {
        return false;
    }

    // Appended Bytes (no CRC)
    //------------------------------------------
    // | RSSI | TS0 | TS1 | TS2 | TS3 | Status |
    //------------------------------------------
    int8_t rssi_dbm = static_cast<int8_t>(packet_data[packet_len_bytes]);
    uint32_t timestamp = packet_data[packet_len_bytes + 1] | (packet_data[packet_len_bytes + 2] << 8) |
                         (packet_data[packet_len_bytes + 3] << 16) | (packet_data[packet_len_bytes + 4] << 24);
    int8_t status = static_cast<int8_t>(packet_data[packet_len_bytes + kPartialDataEntryNumAppendedBytes - 1]);
    static_assert(kPartialDataEntryNumAppendedBytes == 6);  // This section is hardcoded to match the appended bytes.

    switch (current_packet_len_bytes) {
        case RawUATADSBPacket::kShortADSBMessageNumBytes:
        case RawUATADSBPacket::kLongADSBMessageNumBytes: {
            RawUATADSBPacket raw_packet = RawUATADSBPacket(packet_data, current_packet_len_bytes);
            raw_packet.sigs_dbm = rssi_dbm;
            raw_packet.mlat_48mhz_64bit_counts = timestamp;

            adsbee.aircraft_dictionary.RecordSubGHzMetrics(1, 0, 0, 0);
            uat_packet_decoder.raw_uat_adsb_packet_queue.Enqueue(raw_packet);
            break;
        }
        case RawUATUplinkPacket::kUplinkMessageNumBytes: {
            if (!UplinkRxEnabled()) {
                // Uplink RX is disabled at the RF core (syncWord1 = 0), but a corrupted sync LS4 nibble on an ADS-B
                // sync, or a packet already in flight during a mode switch, can still land here. Drop it.
                return false;
            }
            RawUATUplinkPacket raw_packet = RawUATUplinkPacket(packet_data, current_packet_len_bytes);
            raw_packet.sigs_dbm = rssi_dbm;
            raw_packet.mlat_48mhz_64bit_counts = timestamp;

            adsbee.aircraft_dictionary.RecordSubGHzMetrics(0, 0, 1, 0);
            uat_packet_decoder.raw_uat_uplink_packet_queue.Enqueue(raw_packet);
            break;
        }
        default: {
            // Unrecognized packet length, skip. Don't print here since it's in the interrupt context.
            return false;
        }
    }

    return true;
}

bool SubGHzRadio::StartPacketRx() {
    last_rx_start_timestamp_ms_ = get_time_since_boot_ms();
    rx_cmd_handle_ = RF_postCmd(rf_handle_, (RF_Op*)&RF_cmdPropRxAdv, RF_PriorityNormal, rf_cmd_callback, kRxEventMask);
    if (rx_cmd_handle_ < 0) {
        CONSOLE_ERROR("SubGHzRadio::Init", "Failed to post command PROP_RX: returned code %d.", rx_cmd_handle_);
        return false;  // Failed to post command PROP_RX.
    }
    return true;
}

#ifdef HARDWARE_UNIT_TESTS
// Handle for the CW test command so it can be cancelled by StopCWTest().
static RF_CmdHandle cw_test_cmd_handle = -1;
// CMD_FS frequency saved before the CW test retunes the synth, so RX can be restored to the UAT
// default (978 MHz) afterward. Initialized to the smartrf default in case Stop runs without Start.
static uint16_t saved_fs_frequency = 0x03D2;  // 978 MHz.
static uint16_t saved_fs_fract = 0;

bool SubGHzRadio::StartCWTest(uint32_t freq_mhz) {
    // CMD_FS / CMD_TX_TEST need an open RF client. If the receiver is user-disabled (RF client closed), open it
    // now; the RX command Init() posts is cancelled immediately below, and StopCWTest() -> RestoreRx() honors the
    // disabled state afterward.
    if (rf_handle_ == nullptr && !Init()) {
        CONSOLE_ERROR("SubGHzRadio::StartCWTest", "Failed to open the RF client.");
        return false;
    }
    // Stop normal reception and prevent Update() from restarting it while the carrier is on. Use an
    // abrupt abort (mode 0): a graceful abort waits for a stopping boundary that never comes for the
    // continuous RX command, leaving it stuck in the command queue.
    rx_enabled = false;
    RF_cancelCmd(rf_handle_, rx_cmd_handle_, 0);

    // Remember the current synth frequency so StopCWTest() can restore normal reception.
    saved_fs_frequency = RF_cmdFs.frequency;
    saved_fs_fract = RF_cmdFs.fractFreq;

    // Retune the synthesizer to the requested CW frequency (frequency field is in whole MHz).
    RF_cmdFs.frequency = (uint16_t)freq_mhz;
    RF_cmdFs.fractFreq = 0;
    RF_EventMask fs_ret = RF_runCmd(rf_handle_, (RF_Op*)&RF_cmdFs, RF_PriorityNormal, nullptr, 0);
    if (fs_ret != RF_EventLastCmdDone) {
        CONSOLE_ERROR("SubGHzRadio::StartCWTest", "Failed to set frequency to %lu MHz.", (unsigned long)freq_mhz);
        // Retune back to the saved frequency and restart normal reception so a failed start doesn't
        // leave the radio disabled until reboot. cw_test_cmd_handle is still -1, so StopCWTest() just
        // performs the synth-restore + RX-reinit path.
        StopCWTest();
        return false;
    }

    // CMD_TX_TEST with bUseCw=1 emits an unmodulated carrier; TRIG_NEVER end trigger keeps it on indefinitely.
    static rfc_CMD_TX_TEST_t cw_test_cmd;
    memset(&cw_test_cmd, 0, sizeof(cw_test_cmd));
    cw_test_cmd.commandNo = CMD_TX_TEST;
    cw_test_cmd.startTrigger.triggerType = TRIG_NOW;
    cw_test_cmd.condition.rule = COND_NEVER;  // No follow-on command.
    cw_test_cmd.config.bUseCw = 1;            // Unmodulated continuous wave.
    cw_test_cmd.config.bFsOff = 0;            // Leave the synth on after the command.
    cw_test_cmd.txWord = 0xAAAA;
    cw_test_cmd.endTrigger.triggerType = TRIG_NEVER;  // Run until cancelled.

    cw_test_cmd_handle = RF_postCmd(rf_handle_, (RF_Op*)&cw_test_cmd, RF_PriorityNormal, nullptr, 0);
    if (cw_test_cmd_handle < 0) {
        CONSOLE_ERROR("SubGHzRadio::StartCWTest", "Failed to post CMD_TX_TEST: returned code %d.", cw_test_cmd_handle);
        // Don't leave a negative error code masquerading as a valid handle, then retune back and
        // restart normal reception so the synth isn't left retuned with RX stopped.
        cw_test_cmd_handle = -1;
        StopCWTest();
        return false;
    }

    // A valid handle only proves the command was queued; poll until the RF core reports it ACTIVE
    // (carrier keyed) so a rejected CMD_TX_TEST fails loudly instead of silently not transmitting.
    // Mirrors the LR2021 StartCwTone() chip_mode == kTx verification.
    uint16_t cw_status = IDLE;
    for (uint32_t elapsed_ms = 0; elapsed_ms < kCWTestStartTimeoutMs; elapsed_ms++) {
        cw_status = ((volatile RF_Op*)&cw_test_cmd)->status;
        if (cw_status != IDLE && cw_status != PENDING) {
            break;
        }
        usleep(1000);
    }
    if (cw_status != ACTIVE) {
        CONSOLE_ERROR("SubGHzRadio::StartCWTest", "CMD_TX_TEST failed to key the carrier: status 0x%04X.", cw_status);
        StopCWTest();
        return false;
    }
    return true;
}

bool SubGHzRadio::StopCWTest() {
    if (cw_test_cmd_handle >= 0) {
        // Abrupt abort (mode 0): the endless CW (TRIG_NEVER) has no graceful stopping boundary, so a
        // graceful abort would never complete and would leave the command stuck in the queue.
        RF_cancelCmd(rf_handle_, cw_test_cmd_handle, 0);
        cw_test_cmd_handle = -1;
    }
    // Fully reset the RF client to guarantee an empty command queue before re-posting RX (RF_close
    // pends on all queued commands), mirroring the LR2021 DeInit()/Init() restore path.
    DeInit();
    RF_cmdFs.frequency = saved_fs_frequency;
    RF_cmdFs.fractFreq = saved_fs_fract;  // Restore the pre-test frequency before Init() re-runs CMD_FS.
    return RestoreRx();  // Leaves the RF client closed if the receiver is user-disabled.
}

bool SubGHzRadio::StartRssiScan(uint32_t freq_mhz) {
    // Stop normal reception and prevent Update() from restarting it while the scan owns the RX
    // command. Abrupt abort (mode 0) for the same reason as StartCWTest(). The RF client may already be
    // closed if the receiver is user-disabled; Init() below opens it either way.
    rx_enabled = false;
    if (rf_handle_ != nullptr) {
        RF_cancelCmd(rf_handle_, rx_cmd_handle_, 0);
    }
    // Fully reset the RF client before restarting RX at the scan frequency: reposting the aborted
    // RF_cmdPropRxAdv without the RF_close/RF_open cycle is rejected by the RF core with
    // PROP_ERROR_PAR. Init() rebuilds the data-entry queue and re-runs CMD_FS, mirroring the
    // StopCWTest()/Resume() restore paths.
    DeInit();

    // Remember the current synth frequency so StopRssiScan() can restore normal reception, then
    // retune to the requested frequency (frequency field is in whole MHz) for Init()'s CMD_FS run.
    saved_fs_frequency = RF_cmdFs.frequency;
    saved_fs_fract = RF_cmdFs.fractFreq;
    RF_cmdFs.frequency = (uint16_t)freq_mhz;
    RF_cmdFs.fractFreq = 0;

    // Clear stale status so the ACTIVE poll below can't misread a leftover DONE/ERROR value.
    ((RF_Op*)&RF_cmdPropRxAdv)->status = IDLE;

    // RF_getRssi() only returns valid data while the RF core is executing an RX command, so bring
    // the radio back up (RF_open + CMD_FS + packet RX) at the scan frequency.
    if (!Init()) {
        CONSOLE_ERROR("SubGHzRadio::StartRssiScan", "Failed to restart RX at %lu MHz.", (unsigned long)freq_mhz);
        // Best-effort restore at the original frequency. Don't use StopRssiScan() here: if Init()
        // failed at RF_open, rf_handle_ is null and StopRssiScan()'s RF_cancelCmd would misuse it.
        RF_cmdFs.frequency = saved_fs_frequency;
        RF_cmdFs.fractFreq = saved_fs_fract;
        RestoreRx();
        return false;
    }

    // A valid handle only proves the command was queued; poll until the RF core reports it ACTIVE
    // (receiver listening) so a rejected RX command fails loudly instead of silently returning
    // RF_GET_RSSI_ERROR_VAL forever.
    uint16_t rx_status = IDLE;
    for (uint32_t elapsed_ms = 0; elapsed_ms < kCWTestStartTimeoutMs; elapsed_ms++) {
        rx_status = ((volatile RF_Op*)&RF_cmdPropRxAdv)->status;
        if (rx_status != IDLE && rx_status != PENDING) {
            break;
        }
        usleep(1000);
    }
    if (rx_status != ACTIVE) {
        CONSOLE_ERROR("SubGHzRadio::StartRssiScan", "RX command failed to start: status 0x%04X.", rx_status);
        StopRssiScan();
        return false;
    }
    return true;
}

int8_t SubGHzRadio::ReadRssiDbm() { return RF_getRssi(rf_handle_); }

bool SubGHzRadio::StopRssiScan() {
    if (rf_handle_ != nullptr) {
        RF_cancelCmd(rf_handle_, rx_cmd_handle_, 0);
    }
    // Fully reset the RF client to guarantee an empty command queue before re-posting RX, mirroring
    // StopCWTest().
    DeInit();
    RF_cmdFs.frequency = saved_fs_frequency;
    RF_cmdFs.fractFreq = saved_fs_fract;  // Restore the pre-scan frequency before Init() re-runs CMD_FS.
    return RestoreRx();  // Leaves the RF client closed if the receiver is user-disabled.
}
#endif

bool SubGHzRadio::Update() {
    if (!rx_enabled || rf_handle_ == nullptr) {
        return true;  // Not receiving, or the RF client is closed (user-disabled / failed Init): nothing to restart.
    }

    volatile uint16_t rx_status = ((volatile RF_Op*)&RF_cmdPropRxAdv)->status;
    if ((rx_status & 0xFF00) & PROP_DONE_OK) {
        StartPacketRx();
    } else if ((rx_status & 0xFF00) & PROP_ERROR_PAR) {
        char* error_str;
        switch (rx_status) {
            case PROP_ERROR_PAR:
                error_str = (char*)"Illegal parameter";
                break;
            case PROP_ERROR_RXBUF:
                error_str = (char*)"No available Rx buffer at the start of a packet";
                break;
            case PROP_ERROR_RXFULL:
                error_str = (char*)"Out of Rx buffer during reception in a partial read buffer";
                break;
            case PROP_ERROR_NO_SETUP:
                error_str = (char*)"Radio was not set up in proprietary mode";
                break;
            case PROP_ERROR_NO_FS:
                error_str = (char*)"Synth was not programmed when running Rx or Tx";
                break;
            case PROP_ERROR_RXOVF:
                error_str = (char*)"Rx overflow observed during operation";
                break;
            case PROP_ERROR_TXUNF:
                error_str = (char*)"Tx underflow observed during operation";
                break;
            default:
                error_str = (char*)"Unknown error";
        }
        rx_error_restart_count++;
        CONSOLE_ERROR("SubGHzRadio::Update", "PROP_RX threw error (0x%x): %s. Restarting.", rx_status, error_str);
        StartPacketRx();
    }

    return true;
}