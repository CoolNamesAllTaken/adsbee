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
        // Decode the packet and enqueue the result.
        DecodedUATADSBPacket decoded_packet = DecodedUATADSBPacket(packet);
        if (decoded_packet.IsValid())
        {
            pico_ll.BlinkSubGLED();
            CONSOLE_INFO("UATPacketDecoder::Update", "[%dFIXD     ] mdb_tc=%d icao=0x%06x", decoded_packet.GetRawPtr()->sigq_bits, decoded_packet.header.mdb_type_code, decoded_packet.header.icao_address);
            if (!object_dictionary.decoded_uat_adsb_packet_queue.Enqueue(decoded_packet))
            {
                CONSOLE_ERROR("UATPacketDecoder::Update", "Failed to enqueue decoded UAT ADS-B packet.");
            }
        }
        else
        {
            CONSOLE_INFO("UATPacketDecoder::Update", "[     INVLD]");
        }
    }
    return true;
}