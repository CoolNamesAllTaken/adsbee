#pragma once

#include "mode_s_packet.hh"
#include "spi_coprocessor_packet.hh"
#include "stdint.h"
#include "uat_packet.hh"

class CompositeArray {
    // This header is used on the SPI bus to precede a packed buffer of packets.
    struct __attribute__((__packed__)) RawPacketsHeader {
        uint16_t num_mode_s_packets = 0;
        uint16_t num_uat_adsb_packets = 0;
        uint16_t num_uat_uplink_packets = 0;
    };

    // This struct is used internally, to shuffle sets of packets around between functions.
    struct RawPackets {
        static constexpr uint16_t kMaxLenBytes = SPICoprocessorPacket::SCResponsePacket::kDataMaxLenBytes;
        uint16_t len_bytes = 0;  // Total length of the entire array in bytes, including header.

        RawPacketsHeader* header;
        RawModeSPacket* mode_s_packets = nullptr;          // Array of RawModeSPacket structs.
        RawUATADSBPacket* uat_adsb_packets = nullptr;      // Array of RawUATADSBPacket structs.
        RawUATUplinkPacket* uat_uplink_packets = nullptr;  // Array of RawUATUplinkPacket structs.
    };

    RawPackets FillRawPacketsBuffer(uint8_t* buf, uint16_t buf_len, PFBQueue<RawModeSPacket>& mode_s_queue,
                                    PFBQueue<RawUATADSBPacket>& uat_adsb_queue,
                                    PFBQueue<RawUATUplinkPacket>& uat_uplink_queue);
};