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
    uint16_t bit_flip_index;
    while (decoded_1090_packet_bit_flip_locations_out_queue.Pop(bit_flip_index)) {
        CONSOLE_WARNING("PacketDecoder::DecoderLoop", "Corrected single bit error at bit index %d.", bit_flip_index);
    }
    return true;
}

bool PacketDecoder::UpdateDecoderLoop() {
    uint16_t num_packets_to_process = raw_1090_packet_in_queue.Length();
    if (num_packets_to_process == 0) {
        return true;  // Nothing to do.
    }

    for (uint16_t i = 0; i < num_packets_to_process; i++) {
        RawModeSPacket raw_packet;
        if (!raw_1090_packet_in_queue.Pop(raw_packet)) {
            debug_message_out_queue.Push(DebugMessage{
                .message = "Failed to pop raw packet from input queue.",
                .log_level = SettingsManager::LogLevel::kErrors,
            });
            return false;
        }

        DecodedModeSPacket decoded_packet = DecodedModeSPacket(raw_packet);
        DebugMessage decode_debug_message = DebugMessage{
            .message = "",
            .log_level = SettingsManager::LogLevel::kInfo,
        };
        if (decoded_packet.IsValid()) {
            PushPacketIfNotDuplicate(decoded_packet);

            snprintf(decode_debug_message.message, DebugMessage::kMessageMaxLen, "src=%d [VALID     ] ",
                     decoded_packet.GetRaw().source);
        } else if (config_.enable_1090_error_correction &&
                   decoded_packet.GetBufferLenBits() == RawModeSPacket::kExtendedSquitterPacketLenBits) {
            // Checksum correction is enabled, and we have a packet worth correcting.
            RawModeSPacket* raw_packet_ptr = decoded_packet.GetRawPtr();
            uint16_t packet_len_bytes = raw_packet_ptr->buffer_len_bits / kBitsPerByte;
            uint8_t raw_buffer[packet_len_bytes];
            WordBufferToByteBuffer(raw_packet_ptr->buffer, raw_buffer, packet_len_bytes);
            int16_t bit_flip_index = crc24_find_single_bit_error(crc24_syndrome(raw_buffer, packet_len_bytes),
                                                                 raw_packet_ptr->buffer_len_bits);
            if (bit_flip_index > 0) {
                // Found a single bit error: flip it and push the corrected packet to the output queue.
                flip_bit(raw_packet_ptr->buffer, bit_flip_index);
                decoded_1090_packet_bit_flip_locations_out_queue.Push(bit_flip_index);
                PushPacketIfNotDuplicate(DecodedModeSPacket(*raw_packet_ptr));

                snprintf(decode_debug_message.message, DebugMessage::kMessageMaxLen, "src=%d [1FIXD     ] ",
                         decoded_packet.GetRaw().source);
            } else {
                // Checksum correction failed.
                snprintf(decode_debug_message.message, DebugMessage::kMessageMaxLen, "src=%d [     NOFIX] ",
                         decoded_packet.GetRaw().source);
            }
        } else {
            // Invalid and not worth correcting.
            snprintf(decode_debug_message.message, DebugMessage::kMessageMaxLen, "src=%d [     INVLD] ",
                     decoded_packet.GetRaw().source);
        }

        // Append packet contents to debug message.
        uint16_t message_len = strlen(decode_debug_message.message);
        message_len +=
            snprintf(decode_debug_message.message + message_len, DebugMessage::kMessageMaxLen - message_len,
                     "df=%02d icao=0x%06x 0x", decoded_packet.GetDownlinkFormat(), decoded_packet.GetICAOAddress());
        // Append a print of the packet contents.
        raw_packet.PrintBuffer(decode_debug_message.message + message_len, DebugMessage::kMessageMaxLen - message_len);
        debug_message_out_queue.Push(decode_debug_message);
    }

    return true;
}

bool PacketDecoder::PushPacketIfNotDuplicate(const DecodedModeSPacket& decoded_packet) {
    uint32_t icao = decoded_packet.GetICAOAddress();
    uint32_t timestamp_ms = decoded_packet.GetTimestampMs();
    uint16_t packet_source = decoded_packet.GetRaw().source;

    // Check if we have already seen this packet from another source (got caught by multiple state machines
    // simultaneously).
    for (uint16_t i = 0; i < kMaxNumSources; i++) {
        if (last_demod_icao_[i] == icao &&
            (timestamp_ms - last_demod_timestamp_ms_[i]) < kMinSameAircraftMessageIntervalMs) {
            // Already seen this packet from the same aircraft within the minimum interval.
            DebugMessage debug_message = DebugMessage{
                .log_level = SettingsManager::LogLevel::kWarnings,
            };
            snprintf(debug_message.message, DebugMessage::kMessageMaxLen,
                     "PacketDecoder::PushPacketIfNotDuplicate: Skipped duplicate packet with icao=0x%x src=%d "
                     "timestamp_ms=%d.",
                     icao, packet_source, timestamp_ms);
            debug_message_out_queue.Push(debug_message);
            return false;
        }
    }

    decoded_1090_packet_out_queue.Push(decoded_packet);

    if (packet_source >= 0 && packet_source < kMaxNumSources) {
        // Only update packet cache if the source is valid.
        last_demod_icao_[packet_source] = icao;
        last_demod_timestamp_ms_[packet_source] = timestamp_ms;
    }

    return true;
}