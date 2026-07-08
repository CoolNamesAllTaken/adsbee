#include "ublox_max_m10.hh"

#include "comms.hh"  // For comms_manager (UART I/O) and CONSOLE_* logging.
#include "hal.hh"    // For get_time_since_boot_ms().

namespace {

// Append a UBX-CFG-VALSET cfgData entry (4-byte key, little-endian, followed by value_size value
// bytes, little-endian) to buf at offset. Returns the new offset.
uint16_t AppendCfgKeyValue(uint8_t* buf, uint16_t offset, uint32_t key_id, uint64_t value,
                           uint8_t value_size_bytes) {
    buf[offset++] = key_id & 0xFF;
    buf[offset++] = (key_id >> 8) & 0xFF;
    buf[offset++] = (key_id >> 16) & 0xFF;
    buf[offset++] = (key_id >> 24) & 0xFF;
    for (uint8_t i = 0; i < value_size_bytes; i++) {
        buf[offset++] = (value >> (8 * i)) & 0xFF;
    }
    return offset;
}

}  // namespace

void UbloxMAXM10::SendUbxFrame(uint8_t msg_class, uint8_t msg_id, const uint8_t* payload,
                               uint16_t payload_len) {
    comms_manager.iface_putc(SettingsManager::kGNSSUART, static_cast<char>(kUbxSync1));
    comms_manager.iface_putc(SettingsManager::kGNSSUART, static_cast<char>(kUbxSync2));

    // 8-bit Fletcher checksum is computed over class, id, length, and payload.
    uint8_t ck_a = 0;
    uint8_t ck_b = 0;
    auto checksum_byte = [&](uint8_t b) {
        ck_a = static_cast<uint8_t>(ck_a + b);
        ck_b = static_cast<uint8_t>(ck_b + ck_a);
    };

    uint8_t header[4] = {msg_class, msg_id, static_cast<uint8_t>(payload_len & 0xFF),
                         static_cast<uint8_t>((payload_len >> 8) & 0xFF)};
    for (uint8_t i = 0; i < sizeof(header); i++) {
        comms_manager.iface_putc(SettingsManager::kGNSSUART, static_cast<char>(header[i]));
        checksum_byte(header[i]);
    }
    for (uint16_t i = 0; i < payload_len; i++) {
        comms_manager.iface_putc(SettingsManager::kGNSSUART, static_cast<char>(payload[i]));
        checksum_byte(payload[i]);
    }
    comms_manager.iface_putc(SettingsManager::kGNSSUART, static_cast<char>(ck_a));
    comms_manager.iface_putc(SettingsManager::kGNSSUART, static_cast<char>(ck_b));
}

bool UbloxMAXM10::ScanForUbxMessage(uint8_t want_class, uint8_t want_id, uint32_t timeout_ms, uint8_t* out_payload,
                                    uint16_t out_cap, uint16_t* out_len, bool* is_ack) {
    // Minimal UBX frame state machine that scans the incoming byte stream (which also carries NMEA)
    // for a complete, well-formed UBX frame whose class/id match want_class/want_id. Up to out_cap
    // payload bytes are copied into out_payload (if provided); out_len receives the full payload
    // length. For ACK/NAK frames, is_ack (if provided) distinguishes ACK-ACK from ACK-NAK.
    enum State : uint8_t { kSync1, kSync2, kClass, kId, kLen1, kLen2, kPayload, kCkA, kCkB } state = kSync1;
    uint8_t msg_class = 0, msg_id = 0;
    uint16_t payload_len = 0, payload_idx = 0;

    uint32_t start_ms = get_time_since_boot_ms();
    char c;
    while (get_time_since_boot_ms() - start_ms < timeout_ms) {
        if (!comms_manager.iface_getc(SettingsManager::kGNSSUART, c)) {
            continue;  // No byte available yet; keep polling until timeout.
        }
        uint8_t b = static_cast<uint8_t>(c);
        switch (state) {
            case kSync1:
                if (b == kUbxSync1) state = kSync2;
                break;
            case kSync2:
                state = (b == kUbxSync2) ? kClass : kSync1;
                break;
            case kClass:
                msg_class = b;
                state = kId;
                break;
            case kId:
                msg_id = b;
                state = kLen1;
                break;
            case kLen1:
                payload_len = b;
                state = kLen2;
                break;
            case kLen2:
                payload_len |= static_cast<uint16_t>(b) << 8;
                payload_idx = 0;
                state = (payload_len == 0) ? kCkA : kPayload;
                break;
            case kPayload:
                if (out_payload != nullptr && payload_idx < out_cap) out_payload[payload_idx] = b;
                if (++payload_idx >= payload_len) state = kCkA;
                break;
            case kCkA:
                state = kCkB;
                break;
            case kCkB:
                // Frame complete. (Checksum bytes are consumed but not verified here; a corrupted
                // frame simply won't match and we keep scanning until timeout.)
                // want_id == kUbxIdWildcard matches any id within want_class.
                if (msg_class == want_class && (want_id == kUbxIdWildcard || msg_id == want_id)) {
                    if (is_ack != nullptr) *is_ack = (msg_id == kUbxIdAckAck);
                    if (out_len != nullptr) *out_len = payload_len;
                    return true;
                }
                state = kSync1;  // Not the frame we're after; keep scanning.
                break;
        }
    }
    return false;  // Timed out.
}

bool UbloxMAXM10::WaitForUbxMessage(uint8_t want_class, uint8_t want_id, uint32_t timeout_ms, bool* is_ack) {
    return ScanForUbxMessage(want_class, want_id, timeout_ms, nullptr, 0, nullptr, is_ack);
}

bool UbloxMAXM10::WaitForAck(uint8_t acked_class, uint8_t acked_id) {
    // The module replies to a VALSET with UBX-ACK-ACK (class 0x05 id 0x01) on success or
    // UBX-ACK-NAK (id 0x00) on failure. Match any frame in the ACK class so a NAK is detected
    // immediately (rather than scanning until timeout), and distinguish ACK from NAK via is_ack.
    // (acked_class/acked_id are not separately verified against the payload because in our init flow
    // only one VALSET is outstanding at a time.)
    (void)acked_class;
    (void)acked_id;
    bool is_ack = false;
    if (!WaitForUbxMessage(kUbxClassAck, kUbxIdWildcard, kAckTimeoutMs, &is_ack)) {
        return false;  // No ACK/NAK before timeout.
    }
    return is_ack;
}

bool UbloxMAXM10::ProbeLiveness() {
    // Poll UBX-MON-VER (a zero-length payload is a poll request per interface description S3.5.2)
    // and wait briefly for the reply (class/id 0x0A 0x04). UBX in/out are enabled on UART1 in the
    // module's factory-default state, so a present module answers even before our config pass runs.
    SendUbxFrame(kUbxClassMon, kUbxIdMonVer, nullptr, 0);
    return WaitForUbxMessage(kUbxClassMon, kUbxIdMonVer, kProbeTimeoutMs);
}

bool UbloxMAXM10::CfgValSet(uint32_t key_id, uint64_t value, uint8_t value_size_bytes, uint8_t layers) {
    // Payload: version(0) + layers + reserved[2] + cfgData(key + value).
    uint8_t payload[4 + 4 + 8];
    payload[0] = 0x00;    // version 0 (transactionless)
    payload[1] = layers;  // RAM/BBR/Flash bitfield
    payload[2] = 0x00;    // reserved
    payload[3] = 0x00;    // reserved
    uint16_t len = AppendCfgKeyValue(payload, 4, key_id, value, value_size_bytes);

    SendUbxFrame(kUbxClassCfg, kUbxIdCfgValset, payload, len);
    return WaitForAck(kUbxClassCfg, kUbxIdCfgValset);
}

bool UbloxMAXM10::ApplyConfigDefaults() {
    // Write the full firmware default configuration table to RAM + BBR as a known-good baseline.
    // BBR persists because V_BCKP is on an always-on battery-derived rail.
    uint8_t layers = kCfgLayerRam | kCfgLayerBbr;
    uint16_t num_ok = 0;
    uint16_t num_fail = 0;
    for (uint32_t i = 0; i < kNumUbloxConfigDefaults; i++) {
        const UbloxCfgDefault& d = kUbloxConfigDefaults[i];
        if (CfgValSet(d.key_id, d.value, d.size_bytes, layers)) {
            num_ok++;
        } else {
            num_fail++;
        }
    }
    CONSOLE_INFO("UbloxMAXM10::ApplyConfigDefaults", "Applied %u/%u config defaults (%u failed).",
                 num_ok, static_cast<unsigned>(kNumUbloxConfigDefaults), num_fail);
    // Treat the run as successful if the bulk of defaults applied (i.e. the module is responding).
    return num_ok > 0;
}

bool UbloxMAXM10::SendInitCommands() {
    // Quick liveness probe first: if the module is absent/unresponsive, bail immediately so we
    // don't grind through the full default-config pass (390 VALSETs x ACK timeout) and stall boot.
    // Init() marks the receiver unhealthy on a false return so the app falls back gracefully.
    if (!ProbeLiveness()) {
        return false;
    }

    // Module is present: write the full firmware default configuration table to RAM + BBR as a
    // known-good baseline.
    if (!ApplyConfigDefaults()) {
        return false;
    }

    // Application-specific overrides on top of the factory defaults (also RAM + BBR):
    uint8_t layers = kCfgLayerRam | kCfgLayerBbr;
    // Factory default for NMEA message output rates is 0 (off); we need GGA + RMC at 1 Hz.
    CfgValSetU1(kCfgMsgoutNmeaGgaUart1, 1, layers);
    CfgValSetU1(kCfgMsgoutNmeaRmcUart1, 1, layers);
    // Silence the other NMEA sentences we don't consume, to reduce UART traffic.
    CfgValSetU1(kCfgMsgoutNmeaGsaUart1, 0, layers);
    CfgValSetU1(kCfgMsgoutNmeaGsvUart1, 0, layers);
    CfgValSetU1(kCfgMsgoutNmeaGllUart1, 0, layers);
    CfgValSetU1(kCfgMsgoutNmeaVtgUart1, 0, layers);

    // TEMPORARY diagnostic: enable periodic UBX-MON-RF (antenna/AGC/noise) and UBX-NAV-SAT
    // (per-satellite C/N0 + count) output so DebugDumpModuleStatus can report why no fix is acquired.
    // Remove with the rest of the GNSS debug instrumentation.
    CfgValSetU1(kCfgMsgoutUbxMonRfUart1, 1, layers);
    CfgValSetU1(kCfgMsgoutUbxNavSatUart1, 1, layers);

    return true;
}

void UbloxMAXM10::DebugIngestByte(char c) {
    // TEMPORARY non-blocking UBX sniffer (remove with the rest of the GNSS debug instrumentation).
    // Runs the same UBX framing as ScanForUbxMessage but one byte per call, keeping leading payload
    // bytes for MON-RF and computing numSvs / max-C/N0 on the fly for NAV-SAT (which can be large).
    uint8_t b = static_cast<uint8_t>(c);
    switch (sniff_state_) {
        case UbxSniffState::kSync1:
            if (b == kUbxSync1) sniff_state_ = UbxSniffState::kSync2;
            break;
        case UbxSniffState::kSync2:
            sniff_state_ = (b == kUbxSync2) ? UbxSniffState::kClass : UbxSniffState::kSync1;
            break;
        case UbxSniffState::kClass:
            sniff_class_ = b;
            sniff_state_ = UbxSniffState::kId;
            break;
        case UbxSniffState::kId:
            sniff_id_ = b;
            sniff_state_ = UbxSniffState::kLen1;
            break;
        case UbxSniffState::kLen1:
            sniff_payload_len_ = b;
            sniff_state_ = UbxSniffState::kLen2;
            break;
        case UbxSniffState::kLen2:
            sniff_payload_len_ |= static_cast<uint16_t>(b) << 8;
            sniff_payload_idx_ = 0;
            sniff_nav_sat_numsvs_ = 0;
            sniff_nav_sat_max_cno_ = 0;
            sniff_state_ = (sniff_payload_len_ == 0) ? UbxSniffState::kCkA : UbxSniffState::kPayload;
            break;
        case UbxSniffState::kPayload: {
            // Buffer leading bytes (for MON-RF block-0 fields).
            if (sniff_payload_idx_ < kSniffBufLen) sniff_buf_[sniff_payload_idx_] = b;
            // Streaming NAV-SAT decode: numSvs at off 5; per-SV (12 B from off 8): cno at +2.
            if (sniff_class_ == kUbxClassNav && sniff_id_ == kUbxIdNavSat) {
                if (sniff_payload_idx_ == 5) {
                    sniff_nav_sat_numsvs_ = b;
                } else if (sniff_payload_idx_ >= 8) {
                    uint16_t off = sniff_payload_idx_ - 8;
                    if (off % 12 == 2) {  // cno byte of an SV record.
                        if (b > sniff_nav_sat_max_cno_) sniff_nav_sat_max_cno_ = b;
                    }
                }
            }
            if (++sniff_payload_idx_ >= sniff_payload_len_) sniff_state_ = UbxSniffState::kCkA;
            break;
        }
        case UbxSniffState::kCkA:
            sniff_state_ = UbxSniffState::kCkB;
            break;
        case UbxSniffState::kCkB:
            DebugDecodeSniffedFrame();
            sniff_state_ = UbxSniffState::kSync1;
            break;
    }
}

void UbloxMAXM10::DebugDecodeSniffedFrame() {
    // TEMPORARY: store a snapshot from the just-completed sniffed frame.
    if (sniff_class_ == kUbxClassMon && sniff_id_ == kUbxIdMonRf && sniff_payload_len_ >= 4 + 24) {
        // Block 0 starts at payload offset 4; fields relative to block base: +1 flags(jam bits1..0),
        // +2 antStatus, +3 antPower, +12 noisePerMS(u2), +14 agcCnt(u2), +18 magI, +20 magQ.
        const uint8_t* blk = &sniff_buf_[4];
        mon_rf_jamming_ = blk[1] & 0x03;
        mon_rf_ant_status_ = blk[2];
        mon_rf_ant_power_ = blk[3];
        mon_rf_noise_ = static_cast<uint16_t>(blk[12] | (blk[13] << 8));
        mon_rf_agc_ = static_cast<uint16_t>(blk[14] | (blk[15] << 8));
        mon_rf_mag_i_ = blk[18];
        mon_rf_mag_q_ = blk[20];
        mon_rf_valid_ = true;
    } else if (sniff_class_ == kUbxClassNav && sniff_id_ == kUbxIdNavSat) {
        nav_sat_numsvs_ = sniff_nav_sat_numsvs_;
        nav_sat_max_cno_ = sniff_nav_sat_max_cno_;
        nav_sat_valid_ = true;
    }
}

void UbloxMAXM10::DebugDumpModuleStatus() {
    // TEMPORARY: print the latest sniffed MON-RF + NAV-SAT snapshot (remove with the rest of the
    // GNSS debug instrumentation).
    if (mon_rf_valid_) {
        static const char* kAntStatusStr[] = {"INIT", "DONTKNOW", "OK", "SHORT", "OPEN"};
        static const char* kAntPowerStr[] = {"OFF", "ON", "DONTKNOW"};
        const char* ant_status_s = mon_rf_ant_status_ < 5 ? kAntStatusStr[mon_rf_ant_status_] : "?";
        const char* ant_power_s = mon_rf_ant_power_ < 3 ? kAntPowerStr[mon_rf_ant_power_] : "?";
        CONSOLE_PRINTF("GNSS RF: jam=%u antStatus=%u(%s) antPower=%u(%s) noise=%u agc=%u(/8191) magI=%u magQ=%u\r\n",
                       mon_rf_jamming_, mon_rf_ant_status_, ant_status_s, mon_rf_ant_power_, ant_power_s, mon_rf_noise_,
                       mon_rf_agc_, mon_rf_mag_i_, mon_rf_mag_q_);
    } else {
        CONSOLE_PRINTF("GNSS RF: waiting for UBX-MON-RF frame...\r\n");
    }
    if (nav_sat_valid_) {
        CONSOLE_PRINTF("GNSS SAT: numSvs=%u maxCno=%u dBHz\r\n", nav_sat_numsvs_, nav_sat_max_cno_);
    } else {
        CONSOLE_PRINTF("GNSS SAT: waiting for UBX-NAV-SAT frame...\r\n");
    }
}
