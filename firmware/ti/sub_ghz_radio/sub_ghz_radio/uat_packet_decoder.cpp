#include "uat_packet_decoder.hh"

#include "buffer_utils.hh"
#include "comms.hh"
#include "object_dictionary.hh"
#include "pico.hh"

bool UATPacketDecoder::Update() {
    // Process incoming UAT ADS-B packets.
    while (!raw_uat_adsb_packet_queue.IsEmpty()) {
        // pico_ll.BlinkSubGLED();

        RawUATADSBPacket packet;
        raw_uat_adsb_packet_queue.Dequeue(packet);
        uint16_t packet_len_bytes = packet.encoded_message_len_bytes;
        // Decode the packet and enqueue the result.
        DecodedUATADSBPacket decoded_packet = DecodedUATADSBPacket(packet);

        char raw_packet_buffer[2 * packet_len_bytes + 1];
        ByteBufferToHexString(raw_packet_buffer, packet.encoded_message, packet_len_bytes);

        if (decoded_packet.is_valid) {
            pico_ll.BlinkSubGLED();
            object_dictionary.metrics.num_valid_uat_adsb_packets++;
            CONSOLE_INFO(
                "UATPacketDecoder::Update", "-[%dFIXD     ] mdb_tc=%d icao=0x%06x len=%d buf=%s rssi=%d ts=%lu",
                decoded_packet.raw.sigq_bits, decoded_packet.header.mdb_type_code, decoded_packet.header.icao_address,
                packet_len_bytes, raw_packet_buffer, packet.sigs_dbm, packet.mlat_48mhz_64bit_counts);
            if (!object_dictionary.raw_uat_adsb_packet_queue.Enqueue(decoded_packet.raw)) {
                CONSOLE_ERROR("UATPacketDecoder::Update", "Failed to enqueue decoded UAT ADS-B packet.");
            }
        } else {
            CONSOLE_INFO("UATPacketDecoder::Update", "-[     INVLD] len=%d buf=%s rssi=%d ts=%lu", packet_len_bytes,
                         raw_packet_buffer, packet.sigs_dbm, packet.mlat_48mhz_64bit_counts);
        }
    }

    while (!raw_uat_uplink_packet_queue.IsEmpty()) {
        RawUATUplinkPacket packet;
        raw_uat_uplink_packet_queue.Dequeue(packet);
        // Decode the packet and enqueue the result.
        DecodedUATUplinkPacket decoded_packet = DecodedUATUplinkPacket(packet);

        if (decoded_packet.is_valid) {
            pico_ll.BlinkSubGLED();
            object_dictionary.metrics.num_valid_uat_uplink_packets++;
            CONSOLE_INFO("UATPacketDecoder::Update", "+[%02dFIXD     ] len=%d rssi=%d ts=%lu",
                         decoded_packet.raw.sigq_bits, RawUATUplinkPacket::kUplinkMessageNumBytes, packet.sigs_dbm,
                         packet.mlat_48mhz_64bit_counts);
            if (!object_dictionary.raw_uat_uplink_packet_queue.Enqueue(decoded_packet.raw)) {
                CONSOLE_ERROR("UATPacketDecoder::Update", "Failed to enqueue decoded UAT Uplink packet.");
            }
        } else {
            CONSOLE_INFO("UATPacketDecoder::Update", "+[     INVLD] len=%d rssi=%d ts=%lu",
                         RawUATUplinkPacket::kUplinkMessageNumBytes, packet.sigs_dbm, packet.mlat_48mhz_64bit_counts);
        }
    }
    return true;
}