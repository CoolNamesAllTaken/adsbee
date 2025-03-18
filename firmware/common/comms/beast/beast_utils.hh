#ifndef BEAST_UTILS_HH_
#define BEAST_UTILS_HH_

#include "math.h"
#include "stdio.h"
#include "string.h"
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
const uint16_t kBeastFrameMaxLenBytes = 1 /* Frame Type */ + 2 * 6 /* MLAT timestamp + escapes */ +
                                        2 /* RSSI + escape */ + 2 * 14 /* Longest Mode S data + escapes */;  // [Bytes]

const uint16_t kUuidNumChars = 36;
const uint16_t kReceiverIDLenBytes = 8;

enum BeastFrameType {
    kBeastFrameTypeInvalid = 0x0,
    kBeastFrameTypeIngestId = 0xe3,  // Used by readsb for forwarding messages internally.
    kBeastFrameTypeFeedId = 0xe4,    // Used by readsb for establishing a feed with a UUID.
    kBeastFrameTypeModeAC = 0x31,    // Note: This is not used, since I'm assuming it does NOT refer to DF 4,5.
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

uint16_t BuildFeedStartFrame(uint8_t *beast_frame_buf, uint8_t *receiver_id) {
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
 * Converts a Decoded1090Packet payload to a data buffer in Mode S Beast output format.
 * @param[in] packet Reference to Decoded1090Packet to convert.
 * @param[out] beast_frame_buf Pointer to byte buffer to fill with payload.
 * @retval Number of bytes written to beast_frame_buf.
 */
uint16_t Build1090BeastFrame(const Decoded1090Packet &packet, uint8_t *beast_frame_buf) {
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

    // Write RSSI Byte as linear value that correlates with log power detector output voltage. 255 = 0dBm, 0 = -100dBm.
    uint8_t rssi_byte_dbfs = (255 + packet.GetRSSIdBm() * 255 / 100);
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, &rssi_byte_dbfs, 1);

    // Write packet buffer with escape characters.
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, packet_buf, data_num_bytes);
    return bytes_written;
}

/**
 * Sends an Ingest Beast frame (0xe3) with a 16-Byte receiver ID prepended. This type of frame is used by readsb when
 * forwarding messages internally. For feeding, see Build1090BeastFrame.
 * @param[in] packet Reference to Decoded1090Packet to convert.
 * @param[out] beast_frame_buf Pointer to byte buffer to fill with payload.
 * @param[in] receiver_id Pointer to 16-Byte receiver ID.
 * @retval Number of bytes written to beast_frame_buf.
 */
uint16_t Build1090IngestBeastFrame(const Decoded1090Packet &packet, uint8_t *beast_frame_buf,
                                   const uint8_t *receiver_id) {
    uint16_t bytes_written = 0;
    beast_frame_buf[bytes_written++] = kBeastEscapeChar;
    beast_frame_buf[bytes_written++] = BeastFrameType::kBeastFrameTypeIngestId;
    bytes_written += WriteBufferWithBeastEscapes(beast_frame_buf + bytes_written, receiver_id, kReceiverIDLenBytes);
    bytes_written += Build1090BeastFrame(packet, beast_frame_buf + bytes_written);
    return bytes_written;
}

#endif /* BEAST_UTILS_HH_ */