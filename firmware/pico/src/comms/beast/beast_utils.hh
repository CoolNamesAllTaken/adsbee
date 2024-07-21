#ifndef BEAST_UTILS_HH_
#define BEAST_UTILS_HH_

#include "adsb_packet.hh"

uint16_t kBeastFrameMaxLen = 15;  // [Bytes]

enum BeastFrameType { kBeastModeACFrame = 0x31, kBeastModeSShortFrame = 0x32, kBeastModeSLongFrame = 0x33 };

bool TransponderPacketToBeastFrame(TransponderPacket &packet, uint8_t *beast_frame_buf) {
    uint16_t data_num_bits = packet.GetPacketBufferLenBits();
    uint16_t data_num_bytes = 0;
    switch (data_num_bits) {
        case 56:
            // 56-bit data (squitter): Mode S short frame.
            beast_frame_buf[0] = 0x32;
            data_num_bytes = 7;
            break;
        case 112:
            // 112-bit data (extended squitter): Mode S long frame.
            beast_frame_buf[0] = 0x33;
            data_num_bytes = 14;
            break;
        default:
            return false;
    }
    beast_frame_buf[1] = packet.GetRSSIdBm();
    for (uint16_t i = 0; i < data_num_bits / 8; i++) {
    }
}

#endif /* BEAST_UTILS_HH_ */