#ifndef PACKET_DECODER_HH_
#define PACKET_DECODER_HH_

#include "data_structures.hh"
#include "transponder_packet.hh"

class PacketDecoder {
   public:
    static constexpr uint16_t kPacketQueueLen = 100;

    struct PacketDecoderConfig {
        bool enable_1090_error_correction = true;
        bool max_1090_error_correction_num_bits = 1;
    };

    PacketDecoder(PacketDecoderConfig config_in) : config_(config_in) {};

    bool Init() { return true; }
    bool Update();

    // Input queues.
    PFBQueue<Raw1090Packet> raw_1090_packet_in_queue =
        PFBQueue<Raw1090Packet>({.buf_len_num_elements = kPacketQueueLen, .buffer = raw_1090_packet_in_queue_buffer_});

    // Output queues.
    PFBQueue<Decoded1090Packet> decoded_1090_packet_out_queue = PFBQueue<Decoded1090Packet>(
        {.buf_len_num_elements = kPacketQueueLen, .buffer = decoded_1090_packet_out_queue_buffer_});
    PFBQueue<uint16_t> decoded_1090_packet_bit_flip_locations_out_queue = PFBQueue<uint16_t>(
        {.buf_len_num_elements = kPacketQueueLen, .buffer = decoded_1090_packet_bit_flip_locations_out_queue_buffer_});

   private:
    PacketDecoderConfig config_;
    Raw1090Packet raw_1090_packet_in_queue_buffer_[kPacketQueueLen];
    Decoded1090Packet decoded_1090_packet_out_queue_buffer_[kPacketQueueLen];
    uint16_t decoded_1090_packet_bit_flip_locations_out_queue_buffer_[kPacketQueueLen];
};

#endif /* PACKET_DECODER_HH_ */