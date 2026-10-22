#pragma once

#include "data_structures.hh"
#include "mode_s_packet.hh"

class PacketDecoder {
   public:
    static constexpr uint16_t kRawModeSPacketQueueDepth = 100;
    static constexpr uint16_t kDecodedModeSPacketQueueDepth = 100;
    // Raw packets waiting at which 2 bit searches are skipped, as on the ADSBee 1090.
    static constexpr uint16_t kMaxBacklogForTwoBitCorrection = 4;

    PacketDecoder();

    bool Update();

    PFBQueue<RawModeSPacket> raw_mode_s_packet_queue;

    PFBQueue<DecodedModeSPacket> decoded_mode_s_packet_out_queue;

    // Health / diagnostics counters, reported and reset via AT+RX_STATS.
    uint32_t raw_queue_overflow_count = 0;  // Raw packets overwritten because raw_mode_s_packet_queue was full.
    uint32_t bitflips_fixed_count = 0;      // Extended squitter frames recovered via single-bit CRC correction.
    uint32_t two_bit_fixed_count = 0;       // Same with two bits. Both before the aircraft dictionary's track check.
    uint32_t decode_max_cycles = 0;         // Longest decode of one raw packet, in CPU cycles (correction included).
    uint32_t two_bit_corrections_skipped = 0;  // 2 bit searches skipped under load, until the dictionary counts them.

    // Decodes one raw packet (with one and two bit correction) into decoded_mode_s_packet_out_queue. Called by
    // Update(); public for the host tests.
    void DecodeOne(RawModeSPacket& raw_packet, bool df17_mode);

   private:
    RawModeSPacket raw_mode_s_packet_queue_buffer_[kRawModeSPacketQueueDepth];
    DecodedModeSPacket decoded_mode_s_packet_out_queue_buffer_[kDecodedModeSPacketQueueDepth];
};

extern PacketDecoder packet_decoder;
