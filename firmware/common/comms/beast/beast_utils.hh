#ifndef BEAST_UTILS_HH_
#define BEAST_UTILS_HH_

#include "transponder_packet.hh"

// Mode S Beast Protocol Spec: https://github.com/firestuff/adsb-tools/blob/master/protocols/beast.md

const uint8_t kBeastEscapeChar = 0x1a;
const uint16_t kBeastMLATTimestampNumBytes = 6;

// Beast Frame Structure
// <preceded by 0x1a escape character>
// 1 Byte Frame type (does not need escape).
// 1-2 Byte RSSI (may need escape Byte).
// 6-12 Byte MLAT Timestamp (may need 6x escape Bytes).
// Mode-S data (2 bytes + escapes for Mode A/C, 7 bytes + escapes for squitter, 14 bytes + escapes for extended
// squitter)
uint16_t kBeastFrameMaxLenBytes = 1 /* Frame Type */ + 2 * 6 /* MLAT timestamp + escapes */ + 2 /* RSSI + escape */ +
                                  2 * 14 /* Longest Mode S data + escapes */;  // [Bytes]

enum BeastFrameType {
    kBeastFrameTypeInvalid = 0x0,
    kBeastFrameTypeId = 0xe3,
    kBeastFrameTypeModeAC = 0x31,  // Note: This is not used, since I'm assuming it does NOT refer to DF 4,5.
    kBeastFrameTypeModeSShort = 0x32,
    kBeastFrameTypeModeSLong = 0x33
};

/**
 * Returns the Beast frame type corresponding to a Raw1090Packet.
 * NOTE: kBeastFrameTypeModeAC is not used, since ADSBee only decodes Mode S.
 * @param[in] packet Raw1090Packet to get the downlink format from.
 * @retval BeastFrameType corresponding the packet, or kBeastFrameTypeInvalid if it wasn't recognized.
 */
BeastFrameType GetBeastFrameType(Raw1090Packet packet) {
    Decoded1090Packet::DownlinkFormat downlink_format =
        static_cast<Decoded1090Packet::DownlinkFormat>(packet.buffer[0] >> 27);
    switch (downlink_format) {
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatShortRangeAirToAirSurveillance:
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatAltitudeReply:
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatIdentityReply:
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatAllCallReply:
            return kBeastFrameTypeModeSShort;
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatLongRangeAirToAirSurveillance:
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatExtendedSquitter:
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatExtendedSquitterNonTransponder:
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatMilitaryExtendedSquitter:
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatCommBAltitudeReply:
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatCommBIdentityReply:
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatCommDExtendedLengthMessage:
            return kBeastFrameTypeModeSLong;
        default:
            return kBeastFrameTypeInvalid;
            break;
    }
}

/**
 * Writes the specified number of bytes from from_buf to to_buf, adding 0x1a escape characters as necessary.
 * @param[out] to_buf Buffer to write to.
 * @param[in] from_buf Buffer to read from.
 * @param[in] from_buf_num_bytes Number of Bytes to write, not including escape characters that will be added.
 * @retval Number of bytes (including escapes) that were written to to_buf.
 */
uint16_t WriteBufferWithBeastEscapes(uint8_t to_buf[], const uint8_t from_buf[], uint16_t from_buf_num_bytes) {
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

/**
 * Converts a Decoded1090Packet payload to a data buffer in Mode S Beast output format.
 * @param[in] packet Reference to Decoded1090Packet to convert.
 * @param[out] beast_frame_buf Pointer to byte buffer to fill with payload.
 * @retval Number of bytes written to beast_frame_buf.
 */
uint16_t TransponderPacketToBeastFrame(const Decoded1090Packet &packet, uint8_t *beast_frame_buf) {
    uint8_t packet_buf[Decoded1090Packet::kMaxPacketLenWords32 * kBytesPerWord];
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

    // Write RSSI Byte.
    uint8_t rssi_byte_dbm = static_cast<uint8_t>(255 + packet.GetRSSIdBm());
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, &rssi_byte_dbm, 1);

    // Write packet buffer with escape characters.
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, packet_buf, data_num_bytes);
    return bytes_written;
}

uint16_t TransponderPacketToBeastFramePrependReceiverID(const Decoded1090Packet &packet, uint8_t *beast_frame_buf,
                                                        const uint8_t *receiver_id, uint16_t receiver_id_len_bytes) {
    uint16_t bytes_written = 0;
    beast_frame_buf[bytes_written++] = kBeastEscapeChar;
    beast_frame_buf[bytes_written++] = 0xe3;  // Message Type Receiver ID
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, receiver_id, receiver_id_len_bytes);
    bytes_written += TransponderPacketToBeastFrame(packet, beast_frame_buf + bytes_written);
    return bytes_written;
}

#endif /* BEAST_UTILS_HH_ */