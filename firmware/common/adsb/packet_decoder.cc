#include "packet_decoder.hh"

#include "comms.hh"
#include "crc.hh"

bool PacketDecoder::UpdateLogLoop() {
    uint16_t num_messages = debug_message_out_queue.Length();
    for (uint16_t i = 0; i < num_messages; i++) {
        DebugMessage message;
        debug_message_out_queue.Pop(message);
        switch (message.log_level) {
            case SettingsManager::LogLevel::kInfo:
                CONSOLE_INFO("PacketDecoder::DecoderLoop", "%s", message.message);
                break;
            case SettingsManager::LogLevel::kWarnings:
                CONSOLE_WARNING("PacketDecoder::DecoderLoop", "%s", message.message);
                break;
            case SettingsManager::LogLevel::kErrors:
                CONSOLE_ERROR("PacketDecoder::DecoderLoop", "%s", message.message);
                break;
            default:
                break;  // Don't do anything when logs are silent.
        }
    }
    return true;
}

bool PacketDecoder::UpdateDecoderLoop() {
    uint16_t num_packets_to_process = raw_1090_packet_in_queue.Length();
    if (num_packets_to_process == 0) {
        return true;  // Nothing to do.
    }

    for (uint16_t i = 0; i < num_packets_to_process; i++) {
        Raw1090Packet raw_packet;
        if (!raw_1090_packet_in_queue.Pop(raw_packet)) {
            debug_message_out_queue.Push(DebugMessage{
                .message = "Failed to pop raw packet from input queue.",
                .log_level = SettingsManager::LogLevel::kErrors,
            });
            return false;
        }

        Decoded1090Packet decoded_packet = Decoded1090Packet(raw_packet);
        if (decoded_packet.IsValid()) {
            decoded_1090_packet_out_queue.Push(decoded_packet);
        } else if (config_.enable_1090_error_correction &&
                   decoded_packet.GetBufferLenBits() == Decoded1090Packet::kExtendedSquitterPacketLenBits) {
            // Checksum correction is enabled, and we have a packet worth correcting.
            Raw1090Packet* raw_packet_ptr = decoded_packet.GetRawPtr();
            uint16_t packet_len_bytes = raw_packet_ptr->buffer_len_bits / kBitsPerByte;
            uint8_t raw_buffer[packet_len_bytes];
            WordBufferToByteBuffer(raw_packet_ptr->buffer, raw_buffer, packet_len_bytes);
            int16_t bit_flip_index = crc24_find_single_bit_error(crc24_syndrome(raw_buffer, packet_len_bytes),
                                                                 raw_packet_ptr->buffer_len_bits);
            if (bit_flip_index > 0) {
                // Found a single bit error: flip it and push the corrected packet to the output queue.
                flip_bit(raw_packet_ptr->buffer, bit_flip_index);
                decoded_1090_packet_bit_flip_locations_out_queue.Push(bit_flip_index);
                decoded_1090_packet_out_queue.Push(Decoded1090Packet(*raw_packet_ptr));
            }  // Else: Don't make any noise if we can't fix it.
        }
    }

    return true;
}