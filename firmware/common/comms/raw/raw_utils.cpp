#include "raw_utils.hh"

#include "stdio.h"

uint16_t BuildRaw1090Frame(const Raw1090Packet& packet, char* raw_frame_buf) {
    char data_buf[Raw1090Packet::kExtendedSquitterPacketLenBits / kBitsPerNibble + 1] = {'\0'};
    packet.PrintBuffer(data_buf, sizeof(data_buf));
    return snprintf(raw_frame_buf, kRaw1090FrameMaxNumChars, "#MDS*%s;(%d,%d,%d,%016llX)", data_buf, packet.source,
                    packet.sigs_dbm, packet.sigq_db, packet.mlat_48mhz_64bit_counts);
}