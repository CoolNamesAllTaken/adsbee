#pragma once

#include "uat_packet.hh"
#include "data_structures.hh"

class UATPacketDecoder
{
public:
    static constexpr uint16_t kRawUATADSBPacketQueueDepth = 50;

    UATPacketDecoder() = default;
    ~UATPacketDecoder() = default;

    PFBQueue<RawUATADSBPacket> raw_uat_adsb_packet_queue = PFBQueue<RawUATADSBPacket>({.buf_len_num_elements = kRawUATADSBPacketQueueDepth,
                                                                                       .buffer = raw_uat_adsb_packet_buffer_,
                                                                                       .overwrite_when_full = true});

    bool Update();

private:
    RawUATADSBPacket raw_uat_adsb_packet_buffer_[kRawUATADSBPacketQueueDepth] = {};
};

extern UATPacketDecoder uat_packet_decoder;