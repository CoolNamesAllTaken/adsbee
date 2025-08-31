#include "uat_packet_decoder.hh"
#include "comms.hh"
#include "object_dictionary.hh"
#include "pico.hh"

bool UATPacketDecoder::Update()
{
    // Process incoming UAT ADS-B packets.
    while (!raw_uat_adsb_packet_queue.IsEmpty())
    {
        // pico_ll.BlinkSubGLED();

        RawUATADSBPacket packet;
        raw_uat_adsb_packet_queue.Dequeue(packet);
        uint16_t packet_len_bytes = packet.encoded_message_len_bits / kBitsPerByte;
        // Decode the packet and enqueue the result.
        DecodedUATADSBPacket decoded_packet = DecodedUATADSBPacket(packet);

        char raw_packet_buffer[2 * packet_len_bytes + 1];
        for (uint16_t i = 0; i < packet_len_bytes; i++)
        {
            sprintf(raw_packet_buffer + (2 * i), "%02X", packet.encoded_message[i]);
        }
        raw_packet_buffer[2 * packet_len_bytes] = '\0';

        if (decoded_packet.IsValid())
        {
            pico_ll.BlinkSubGLED();
            CONSOLE_INFO("UATPacketDecoder::Update", "[%dFIXD     ] mdb_tc=%d icao=0x%06x len=%d buf=%s", decoded_packet.GetRawPtr()->sigq_bits, decoded_packet.header.mdb_type_code, decoded_packet.header.icao_address, packet_len_bytes, raw_packet_buffer);
            if (!object_dictionary.decoded_uat_adsb_packet_queue.Enqueue(decoded_packet))
            {
                CONSOLE_ERROR("UATPacketDecoder::Update", "Failed to enqueue decoded UAT ADS-B packet.");
            }
        }
        else
        {
            CONSOLE_INFO("UATPacketDecoder::Update", "[     INVLD] len=%d buf=%s", packet_len_bytes, raw_packet_buffer);
        }
    }
    return true;
}