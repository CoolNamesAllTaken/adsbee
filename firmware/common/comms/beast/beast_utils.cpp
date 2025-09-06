#include "beast_utils.hh"

#include "beast_tables.hh"
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

uint16_t BeastReporter::BuildModeSBeastFrame(const DecodedModeSPacket &packet, uint8_t *beast_frame_buf) {
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

    // Write 6-Byte MLAT timestamp.
    uint64_t mlat_12mhz_counter = packet.GetMLAT12MHzCounter();
    uint8_t mlat_12mhz_counter_buf[6];
    for (uint16_t i = 0; i < kBeastMLATTimestampNumBytes; i++) {
        mlat_12mhz_counter_buf[i] = (mlat_12mhz_counter >> (kBeastMLATTimestampNumBytes - i - 1) * kBitsPerByte) & 0xFF;
    }
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, mlat_12mhz_counter_buf, 6);

    // Use lookup table to convert RSSI from dBm to Beast power level (sqrt of un-logged dBFS, mutliplied by 255).
    uint16_t rssi_lut_index =
        MIN(MAX(packet.raw.sigs_dbm - kMinRSSIdBm, 0), static_cast<int>(sizeof(kRSSIdBmToRSSIdBFS) - 1));
    uint8_t rssi_byte = static_cast<uint8_t>(kRSSIdBmToRSSIdBFS[rssi_lut_index]);
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, &rssi_byte, 1);

    // Write packet buffer with escape characters.
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, packet_buf, data_num_bytes);
    return bytes_written;
}

uint16_t BeastReporter::BuildModeSIngestBeastFrame(const DecodedModeSPacket &packet, uint8_t *beast_frame_buf,
                                                   const uint8_t *receiver_id) {
    uint16_t bytes_written = 0;
    beast_frame_buf[bytes_written++] = kBeastEscapeChar;
    beast_frame_buf[bytes_written++] = BeastFrameType::kBeastFrameTypeIngestId;
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, receiver_id, kReceiverIDLenBytes);
    bytes_written += BuildModeSBeastFrame(packet, beast_frame_buf + bytes_written);
    return bytes_written;
}

/**
 * @brief Writes a buffer as hexadecimal ASCII characters. Does not require beast escapes since no ASCII characters
 * overlap with the 0x1a beast escape character. Note that to_buf will need to be twice as long as from_buf, since each
 * byte takes two chars to be represented as hex ascii.
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

/**
 * Write a UAT ADSB frame as an encapsulated UAT beast message. To buffer must be at least 2*34 + 5 = 73 Bytes long to
 * accommodate long UAT ADSB messages as hex ASCII.
 * @param[in] packet Reference to DecodedUATADSBPacket to write to the buffer.
 * @param[out] beast_frame_buf Pointer to byte buffer to fill with payload.
 * @retval Number of bytes written to beast_frame_buf.
 */
uint16_t BeastReporter::BuildUATADSBBeastFrame(const DecodedUATADSBPacket &packet, uint8_t *beast_frame_buf) {
    uint16_t bytes_written = 0;
    beast_frame_buf[bytes_written++] = kBeastEscapeChar;
    beast_frame_buf[bytes_written++] = BeastFrameType::kBeastFrameTypeUAT;
    beast_frame_buf[bytes_written++] = '-';  // Downlink message.
    bytes_written += WriteBufferAsHexASCII(beast_frame_buf + bytes_written, packet.raw.encoded_message,
                                           packet.raw.encoded_message_len_bytes);
    bytes_written += sprintf((char *)(beast_frame_buf + bytes_written), "rs=%d", packet.raw.encoded_message_len_bytes);

    return bytes_written;
}
