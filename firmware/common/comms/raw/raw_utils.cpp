#include "raw_utils.hh"

#include "stdio.h"

uint16_t BuildRawFrame(const Raw1090Packet& packet, char* raw_frame_buf) {
    char byte_buf[Raw1090Packet::kExtendedSquitterPacketLenBits / kBitsPerByte + 1];
    packet.PrintBuffer(byte_buf, sizeof(byte_buf));
    return snprintf(raw_frame_buf, kRawFrameMaxNumChars, "*%s;(%d,%d,%llu)\r\n", byte_buf, packet.sigs_dbm,
                    packet.sigq_db, packet.mlat_48mhz_64bit_counts);
}