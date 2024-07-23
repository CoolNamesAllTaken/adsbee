#ifndef BEAST_UTILS_HH_
#define BEAST_UTILS_HH_

#include "adsb_packet.hh"

// Mode S Beast Protocol Spec: https://github.com/firestuff/adsb-tools/blob/master/protocols/beast.md

uint16_t kBeastFrameMaxLenBytes =
    2 + 2 * 14;  // [Bytes] Accounts for frame type Byte, RSSI Byte, data with space to escape all data Bytes if needed.

enum BeastFrameType { kBeastModeACFrame = 0x31, kBeastModeSShortFrame = 0x32, kBeastModeSLongFrame = 0x33 };

/**
 * Converts a TransponderPacket payload to a data buffer in Mode S Beast output format.
 * @param[in] packet Reference to TransponderPacket to convert.
 * @param[out] beast_frame_buf Pointer to byte buffer to fill with payload.
 * @retval Number of bytes written to beast_frame_buf.
 */
uint16_t TransponderPacketToBeastFrame(const TransponderPacket &packet, uint8_t *beast_frame_buf) {
    uint8_t packet_buf[TransponderPacket::kMaxPacketLenWords32 * kBytesPerWord];
    uint16_t data_num_bytes = packet.DumpPacketBuffer(packet_buf);

    // Determine and write frame type Byte.
    switch (data_num_bytes * kBitsPerByte) {
        case 56:
            // 56-bit data (squitter): Mode S short frame.
            beast_frame_buf[0] = 0x32;
            break;
        case 112:
            // 112-bit data (extended squitter): Mode S long frame.
            beast_frame_buf[0] = 0x33;
            break;
        default:
            return 0;
    }
    // Write RSSI Byte.
    beast_frame_buf[1] = static_cast<uint8_t>(255 + packet.GetRSSIdBm());  // 255 = 0dBm.

    // Write packet buffer with escape characters.
    uint16_t bytes_written = 2;
    for (uint16_t i = 0; i < data_num_bytes; i++) {
        beast_frame_buf[bytes_written++] = packet_buf[i];
        // Escape any occurrence of 0x1a.
        if (packet_buf[i] == 0x1a) {
            beast_frame_buf[bytes_written++] = 0x1a;
        }
    }
    return bytes_written;
}

#endif /* BEAST_UTILS_HH_ */