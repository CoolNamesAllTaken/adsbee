#include "beast_utils.hh"

#include <ctype.h>
#include <stdarg.h>

#include "beast_tables.hh"
#include "comms.hh"
#include "macros.hh"
#include "math.h"
#include "stdio.h"
#include "string.h"

// Mode S Beast Protocol Spec: https://github.com/firestuff/adsb-tools/blob/master/protocols/beast.md

BeastReporter::BeastFrameType BeastReporter::GetBeastFrameType(RawModeSPacket packet) {
    DecodedModeSPacket::DownlinkFormat downlink_format =
        static_cast<DecodedModeSPacket::DownlinkFormat>(packet.buffer[0] >> 27);
    switch (downlink_format) {
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatShortRangeAirToAirSurveillance:
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatAltitudeReply:
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatIdentityReply:
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatAllCallReply:
            return kBeastFrameTypeModeSShort;
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatLongRangeAirToAirSurveillance:
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatExtendedSquitter:
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatExtendedSquitterNonTransponder:
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatMilitaryExtendedSquitter:
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatCommBAltitudeReply:
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatCommBIdentityReply:
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatCommDExtendedLengthMessage:
            return kBeastFrameTypeModeSLong;
        default:
            return kBeastFrameTypeInvalid;
            break;
    }
}

uint16_t BeastReporter::WriteBufferWithBeastEscapes(uint8_t to_buf[], const uint8_t from_buf[],
                                                    uint16_t from_buf_num_bytes) {
    uint16_t to_buf_num_bytes = 0;
    for (uint16_t i = 0; i < from_buf_num_bytes; i++) {
        to_buf[to_buf_num_bytes++] = from_buf[i];
        // Escape any occurrence of 0x1a.
        if (from_buf[i] == kBeastEscapeChar) {
            to_buf[to_buf_num_bytes++] = kBeastEscapeChar;
        }
    }
    return to_buf_num_bytes;
}

uint16_t BeastReporter::BuildFeedStartFrame(uint8_t *beast_frame_buf, uint8_t *receiver_id) {
    uint16_t bytes_written = 0;
    beast_frame_buf[bytes_written++] = kBeastEscapeChar;
    beast_frame_buf[bytes_written++] = BeastFrameType::kBeastFrameTypeFeedId;

    // Send UUID as ASCII (will not contain 0x1A, since it's just hex characters and dashes).
    // UUID must imitate the form that's output by `cat /proc/sys/kernel/random/uuid` on Linux (e.g.
    // 38366a5c-c54f-4256-bd0a-1557961f5ad0).
    // ADSBee UUID Format: MMMMMMMM-MMMM-MMMM-NNNN-NNNNNNNNNNNN, where M's and N's represent printed hex digits of the
    // internally stored 64-bit UUID (e.g. 0bee00038172d18c) Example ADSBee UUID: 0bee0003-8172-d18c-0bee-00038172d18c
    char uuid[kUuidNumChars + 1] = "eeeeeeee-eeee-eeee-ffff-ffffffffffff";  // Leave space for null terminator.
    sprintf(uuid, "%02x%02x%02x%02x-%02x%02x-%02x%02x-", receiver_id[0], receiver_id[1], receiver_id[2], receiver_id[3],
            receiver_id[4], receiver_id[5], receiver_id[6], receiver_id[7]);
    sprintf(uuid + (kUuidNumChars - 2 * kReceiverIDLenBytes - 1), "%02x%02x-%02x%02x%02x%02x%02x%02x", receiver_id[0],
            receiver_id[1], receiver_id[2], receiver_id[3], receiver_id[4], receiver_id[5], receiver_id[6],
            receiver_id[7]);

    // Write receiver ID string to buffer.
    strncpy((char *)(beast_frame_buf + bytes_written), uuid, kUuidNumChars);
    bytes_written += kUuidNumChars;
    return bytes_written;
}

/**
 * Write a 6 Byte MLAT timestamp (12MHz or 48MHz counts) to buffer.
 * @param[in] buf Pointer to output buffer.
 * @param[in] mlat_counter MLAT timestamp value.
 * @retval Number of bytes written to the output buffer, including escapes.
 */
uint16_t WriteMLATTimestamp(uint8_t *buf, uint64_t mlat_counter) {
    uint8_t mlat_counter_buf[6];
    for (uint16_t i = 0; i < BeastReporter::kBeastMLATTimestampNumBytes; i++) {
        mlat_counter_buf[i] =
            (mlat_counter >> (BeastReporter::kBeastMLATTimestampNumBytes - i - 1) * kBitsPerByte) & 0xFF;
    }
    return BeastReporter::WriteBufferWithBeastEscapes(buf, mlat_counter_buf,
                                                      BeastReporter::kBeastMLATTimestampNumBytes);
}

/**
 * Use lookup table to convert RSSI from dBm to Beast power level (sqrt of un-logged dBFS, mutliplied by 255).
 * @param[out] buf Pointer to output buffer.
 * @param[in] rssi_dbm RSSI value in dBm.
 * @retval Number of bytes written to the output buffer, including escapes.
 */
uint16_t WriteRSSIdBmAsBeastPowerLevel(uint8_t *buf, int16_t rssi_dbm) {
    // Convert RSSI from dBm to Beast power level (sqrt of un-logged dBFS, multiplied by 255).
    uint16_t rssi_lut_index = MIN(MAX(rssi_dbm - kMinRSSIdBm, 0), static_cast<int>(sizeof(kRSSIdBmToRSSIdBFS) - 1));
    uint8_t rssi_byte = static_cast<uint8_t>(kRSSIdBmToRSSIdBFS[rssi_lut_index]);
    return BeastReporter::WriteBufferWithBeastEscapes(buf, &rssi_byte, 1);
}

uint16_t BeastReporter::BuildModeSBeastFrame(uint8_t *beast_frame_buf, const DecodedModeSPacket &packet,
                                             bool timestamp_48mhz) {
    uint8_t packet_buf[DecodedModeSPacket::kMaxPacketLenWords32 * kBytesPerWord];
    uint16_t data_num_bytes = packet.DumpPacketBuffer(packet_buf);

    beast_frame_buf[0] = kBeastEscapeChar;
    // Determine and write frame type Byte.
    switch (data_num_bytes * kBitsPerByte) {
        case 56:
            // 56-bit data (squitter): Mode S short frame.
            beast_frame_buf[1] = kBeastFrameTypeModeSShort;
            break;
        case 112:
            // 112-bit data (extended squitter): Mode S long frame.
            beast_frame_buf[1] = kBeastFrameTypeModeSLong;
            break;
        default:
            return 0;
    }
    uint16_t bytes_written = 2;

    bytes_written += WriteMLATTimestamp(
        beast_frame_buf + bytes_written,
        timestamp_48mhz ? packet.raw.GetMLAT48MHzCounter() : packet.raw.GetMLAT12MHzCounter());
    bytes_written += WriteRSSIdBmAsBeastPowerLevel(beast_frame_buf + bytes_written, packet.raw.sigs_dbm);

    // Write packet buffer with escape characters.
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, packet_buf, data_num_bytes);
    return bytes_written;
}

namespace {

// Appends printf output to a receiver info payload. Sets ok to false once the payload no longer fits.
struct InfoPayloadWriter {
    char *buf;
    uint16_t buf_len;
    uint16_t len = 0;
    bool ok = true;

    void Append(const char *format, ...) __attribute__((format(printf, 2, 3))) {
        if (!ok) return;
        va_list args;
        va_start(args, format);
        int n = vsnprintf(buf + len, buf_len - len, format, args);
        va_end(args);
        if (n < 0 || n >= buf_len - len) {
            ok = false;
            return;
        }
        len += n;
    }

    // Writes value with a fixed number of decimals, rounded, without relying on printf float support.
    void AppendFixedPoint(const char *key, double value, uint16_t decimals) {
        uint64_t scale = 1;
        for (uint16_t i = 0; i < decimals; i++) scale *= 10;
        bool negative = value < 0.0;
        uint64_t scaled = static_cast<uint64_t>((negative ? -value : value) * static_cast<double>(scale) + 0.5);
        const char *sign = negative && scaled != 0 ? "-" : "";
        if (decimals == 0) {
            Append("%s=%s%llu;", key, sign, static_cast<unsigned long long>(scaled));
        } else {
            Append("%s=%s%llu.%0*llu;", key, sign, static_cast<unsigned long long>(scaled / scale), decimals,
                   static_cast<unsigned long long>(scaled % scale));
        }
    }

    // Appends key=value with characters the payload can't carry replaced by '_'.
    void AppendText(const char *key, const char *value, uint16_t max_len, bool id_chars_only) {
        Append("%s=", key);
        for (uint16_t i = 0; ok && i < max_len && value[i] != '\0'; i++) {
            char c = value[i];
            bool allowed = id_chars_only ? (isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '.' || c == '-')
                                         : (c >= 0x20 && c <= 0x7e && c != ';' && c != '=');
            Append("%c", allowed ? c : '_');
        }
        Append(";");
    }
};

}  // namespace

uint16_t BeastReporter::BuildReceiverInfoFrame(uint8_t *buf, uint16_t buf_len, const ReceiverInfo &info) {
    if (info.id[0] == '\0' || buf_len < 3) {
        return 0;
    }
    buf_len = MIN(buf_len, kReceiverInfoFrameMaxLenBytes);
    buf[0] = kBeastEscapeChar;
    buf[1] = kBeastFrameTypeReceiverInfo;
    // The payload is built in place; one byte is kept back for the terminating newline.
    InfoPayloadWriter w = {.buf = reinterpret_cast<char *>(buf + 2), .buf_len = static_cast<uint16_t>(buf_len - 3)};

    w.Append("v=1;");
    w.AppendText("id", info.id, kReceiverInfoIDMaxLen, true);
    w.Append("clk=%lu;ep=%lx;", static_cast<unsigned long>(info.clock_hz), static_cast<unsigned long>(info.epoch));
    const ReceiverPosition &position = info.position;
    if (position.IsValid()) {
        w.AppendFixedPoint("lat", position.latitude_deg, 7);
        w.AppendFixedPoint("lon", position.longitude_deg, 7);
        w.AppendFixedPoint("alt", position.height_m, 2);
        w.Append("src=%s;", ReceiverPosition::SourceToStr(position.source));
        if (position.horizontal_accuracy_m > 0.0f) w.AppendFixedPoint("hacc", position.horizontal_accuracy_m, 2);
        if (position.vertical_accuracy_m > 0.0f) w.AppendFixedPoint("vacc", position.vertical_accuracy_m, 2);
    }
    w.Append("mov=%d;", position.moving ? 1 : 0);
    if (info.pps.valid) {
        w.Append("pps=%llx@%lu;", static_cast<unsigned long long>(info.pps.mlat_48mhz_counts & 0xFFFFFFFFFFFF),
                 static_cast<unsigned long>(info.pps.unix_time_s));
    }
    if (info.name[0] != '\0') w.AppendText("name", info.name, kReceiverInfoNameMaxLen, false);
    if (info.firmware_version[0] != '\0') {
        w.AppendText("fw", info.firmware_version, kReceiverInfoFirmwareVersionMaxLen, false);
    }
    if (!w.ok) {
        return 0;
    }
    w.len--;  // Drop the trailing ';'.
    buf[2 + w.len] = '\n';
    return 2 + w.len + 1;
}

uint16_t BeastReporter::BuildModeSIngestBeastFrame(uint8_t *beast_frame_buf, const DecodedModeSPacket &packet,
                                                   const uint8_t *receiver_id) {
    uint16_t bytes_written = 0;
    beast_frame_buf[bytes_written++] = kBeastEscapeChar;
    beast_frame_buf[bytes_written++] = BeastFrameType::kBeastFrameTypeIngestId;
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, receiver_id, kReceiverIDLenBytes);
    bytes_written += BuildModeSBeastFrame(beast_frame_buf + bytes_written, packet);
    return bytes_written;
}

/**
 * @brief Writes a buffer as hexadecimal ASCII characters. Does not require beast escapes since no ASCII characters
 * overlap with the 0x1a beast escape character. Note that to_buf will need to be twice as long as from_buf, since each
 * byte takes two chars to be represented as hex ascii.
 *
 * This function is not currently used.
 *
 * @param[out] to_buf Pointer to output buffer.
 * @param[in] from_buf Pointer to input buffer.
 * @param[in] from_buf_num_bytes Number of bytes in the input buffer.
 * @retval Number of bytes written to the output buffer.
 */
uint16_t WriteBufferAsHexASCII(uint8_t *to_buf, const uint8_t *from_buf, uint16_t from_buf_num_bytes) {
    const char hex_chars[] = "0123456789abcdef";
    for (uint16_t i = 0; i < from_buf_num_bytes; i++) {
        to_buf[i * 2] = hex_chars[(from_buf[i] >> 4) & 0x0F];
        to_buf[i * 2 + 1] = hex_chars[from_buf[i] & 0x0F];
    }
    return from_buf_num_bytes * 2;
}

uint16_t BeastReporter::BuildUATADSBBeastFrame(uint8_t *beast_frame_buf, const RawUATADSBPacket &packet) {
    char uat_message_type_char = ' ';
    switch (packet.buffer_len_bytes) {
        case RawUATADSBPacket::kShortADSBMessageNumBytes:
            // Short UAT ADSB message.
            uat_message_type_char = kUATMessageTypeADSBShort;
            break;
        case RawUATADSBPacket::kLongADSBMessageNumBytes:
            // Long UAT ADSB message.
            uat_message_type_char = kUATMessageTypeADSBLong;
            break;
        default:
            CONSOLE_ERROR("BeastReporter::BuildUATADSBBeastFrame", "Invalid UAT ADSB message length %d bytes.",
                          packet.buffer_len_bytes);
            return 0;  // Invalid length.
    }

    uint16_t bytes_written = 0;
    beast_frame_buf[bytes_written++] = kBeastEscapeChar;
    beast_frame_buf[bytes_written++] = BeastFrameType::kBeastFrameTypeUAT;
    beast_frame_buf[bytes_written++] = uat_message_type_char;

    bytes_written += WriteMLATTimestamp(beast_frame_buf + bytes_written, packet.GetMLAT12MHzCounter());
    bytes_written += WriteRSSIdBmAsBeastPowerLevel(beast_frame_buf + bytes_written, packet.sigs_dbm);

    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, packet.buffer,
                                                 packet.buffer_len_bytes);

    return bytes_written;
}

uint16_t BeastReporter::BuildUATUplinkBeastFrame(uint8_t *beast_frame_buf, const RawUATUplinkPacket &packet) {
    if (packet.encoded_message_len_bytes != RawUATUplinkPacket::kUplinkMessageNumBytes) {
        CONSOLE_ERROR("BeastReporter::BuildUATUplinkBeastFrame", "Invalid UAT Uplink message length %d bytes.",
                      packet.encoded_message_len_bytes);
        return 0;  // Invalid length.
    }

    uint16_t bytes_written = 0;
    beast_frame_buf[bytes_written++] = kBeastEscapeChar;
    beast_frame_buf[bytes_written++] = BeastFrameType::kBeastFrameTypeUAT;
    beast_frame_buf[bytes_written++] = kUATMessageTypeUplink;

    bytes_written += WriteMLATTimestamp(beast_frame_buf + bytes_written, packet.GetMLAT12MHzCounter());
    bytes_written += WriteRSSIdBmAsBeastPowerLevel(beast_frame_buf + bytes_written, packet.sigs_dbm);

    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, packet.encoded_message,
                                                 packet.encoded_message_len_bytes);

    return bytes_written;
}
