#include "mode_s_packet_decoder.hh"

#include "comms.hh"
#include "crc.hh"

bool ModeSPacketDecoder::UpdateLogLoop() {
    uint16_t num_messages = debug_message_out_queue.Length();
    for (uint16_t i = 0; i < num_messages; i++) {
        DebugMessage message;
        debug_message_out_queue.Dequeue(message);
        switch (message.log_level) {
            case SettingsManager::LogLevel::kInfo:
                CONSOLE_INFO("ModeSPacketDecoder::DecoderLoop", "%s", message.message);
                break;
            case SettingsManager::LogLevel::kWarnings:
                CONSOLE_WARNING("ModeSPacketDecoder::DecoderLoop", "%s", message.message);
                break;
            case SettingsManager::LogLevel::kErrors:
                CONSOLE_ERROR("ModeSPacketDecoder::DecoderLoop", "%s", message.message);
                break;
            default:
                break;  // Don't do anything when logs are silent.
        }
    }
    uint16_t bit_flip_index;
    while (decoded_mode_s_packet_bit_flip_locations_out_queue.Dequeue(bit_flip_index)) {
        CONSOLE_INFO("ModeSPacketDecoder::DecoderLoop", "Corrected single bit error at bit index %d.", bit_flip_index);
    }
    return true;
}

bool ModeSPacketDecoder::UpdateDecoderLoop() {
    uint16_t num_packets_to_process = raw_mode_s_packet_in_queue.Length();
    if (num_packets_to_process == 0) {
        return true;  // Nothing to do.
    }

    for (uint16_t i = 0; i < num_packets_to_process; i++) {
        RawModeSPacket raw_packet;
        if (!raw_mode_s_packet_in_queue.Dequeue(raw_packet)) {
            debug_message_out_queue.Enqueue(DebugMessage{
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
        if (decoded_packet.is_valid) {
            PushPacketIfNotDuplicate(decoded_packet);

            snprintf(decode_debug_message.message, DebugMessage::kMessageMaxLen, "src=%d [VALID     ] ",
                     decoded_packet.raw.source);
        } else if (config_.enable_1090_error_correction &&
                   decoded_packet.raw.buffer_len_bytes == RawModeSPacket::kExtendedSquitterPacketLenBytes) {
            // Checksum correction is enabled, and we have a packet worth correcting.
            uint8_t raw_buffer[decoded_packet.raw.buffer_len_bytes];
            WordBufferToByteBuffer(decoded_packet.raw.buffer, raw_buffer, decoded_packet.raw.buffer_len_bytes);
            int16_t bit_flip_index =
                crc24_find_single_bit_error(crc24_syndrome(raw_buffer, decoded_packet.raw.buffer_len_bytes),
                                            decoded_packet.raw.buffer_len_bytes * kBitsPerByte);
            if (bit_flip_index > 0) {
                // Found a single bit error: flip it and push the corrected packet to the output queue.
                flip_bit(decoded_packet.raw.buffer, bit_flip_index);
                decoded_mode_s_packet_bit_flip_locations_out_queue.Enqueue(bit_flip_index);
                PushPacketIfNotDuplicate(DecodedModeSPacket(decoded_packet.raw));

                snprintf(decode_debug_message.message, DebugMessage::kMessageMaxLen, "src=%d [1FIXD     ] ",
                         decoded_packet.raw.source);
            } else {
                // Checksum correction failed.
                snprintf(decode_debug_message.message, DebugMessage::kMessageMaxLen, "src=%d [     NOFIX] ",
                         decoded_packet.raw.source);
            }
        } else {
            // Invalid and not worth correcting.
            snprintf(decode_debug_message.message, DebugMessage::kMessageMaxLen, "src=%d [     INVLD] ",
                     decoded_packet.raw.source);
        }

        // Append packet contents to debug message.
        uint16_t message_len = strnlen(decode_debug_message.messagem, DebugMessage::kMessageMaxLen);
        message_len += snprintf(decode_debug_message.message + message_len, DebugMessage::kMessageMaxLen - message_len,
                                "df=%02d icao=0x%06x", decoded_packet.downlink_format, decoded_packet.icao_address);
        // Append a print of the packet contents.
        raw_packet.PrintBuffer(decode_debug_message.message + message_len, DebugMessage::kMessageMaxLen - message_len);
        debug_message_out_queue.Enqueue(decode_debug_message);
    }

    return true;
}

bool ModeSPacketDecoder::PushPacketIfNotDuplicate(const DecodedModeSPacket& decoded_packet) {
    uint32_t timestamp_ms = decoded_packet.raw.GetTimestampMs();
    uint16_t packet_source = decoded_packet.raw.source;

    // Check if we have already seen this packet from another source (got caught by multiple state machines
    // simultaneously).
    for (uint16_t i = 0; i < kMaxNumSources; i++) {
        if (last_demod_icao_[i] == decoded_packet.icao_address &&
            (timestamp_ms - last_demod_timestamp_ms_[i]) < kMinSameAircraftMessageIntervalMs) {
            // Already seen this packet from the same aircraft within the minimum interval.
            DebugMessage debug_message = DebugMessage{
                .log_level = SettingsManager::LogLevel::kInfo,
            };
            snprintf(debug_message.message, DebugMessage::kMessageMaxLen,
                     "ModeSPacketDecoder::PushPacketIfNotDuplicate: Skipped duplicate packet with icao=0x%x src=%d "
                     "timestamp_ms=%d.",
                     decoded_packet.icao_address, packet_source, timestamp_ms);
            debug_message_out_queue.Enqueue(debug_message);
            return false;
        }
    }

    decoded_mode_s_packet_out_queue.Enqueue(decoded_packet);

    if (packet_source >= 0 && packet_source < kMaxNumSources) {
        // Only update packet cache if the source is valid.
        last_demod_icao_[packet_source] = decoded_packet.icao_address;
        last_demod_timestamp_ms_[packet_source] = timestamp_ms;
    }

    return true;
}