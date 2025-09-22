#include "composite_array.hh"

#include <cstring>  // For memcpy.

#include "comms.hh"

CompositeArray::RawPackets CompositeArray::PackRawPacketsBuffer(uint8_t* buf, uint16_t buf_len_bytes,
                                                                PFBQueue<RawModeSPacket>* mode_s_queue,
                                                                PFBQueue<RawUATADSBPacket>* uat_adsb_queue,
                                                                PFBQueue<RawUATUplinkPacket>* uat_uplink_queue) {
    RawPackets packets_to_report = {
        .len_bytes = sizeof(RawPackets::Header),
        .header = reinterpret_cast<RawPackets::Header*>(buf),
        .mode_s_packets = nullptr,
        .uat_adsb_packets = nullptr,
        .uat_uplink_packets = nullptr,
    };

    packets_to_report.header->num_mode_s_packets = 0;
    packets_to_report.header->num_uat_adsb_packets = 0;
    packets_to_report.header->num_uat_uplink_packets = 0;

    // Fill up the CompositeArray::RawPackets header and associated buffers with as many packets as we can report.
    if (mode_s_queue) {
        // Stuff with Mode S packets.
        RawModeSPacket mode_s_packet;
        packets_to_report.mode_s_packets = reinterpret_cast<RawModeSPacket*>(buf + packets_to_report.len_bytes);
        while (packets_to_report.len_bytes + sizeof(RawModeSPacket) < buf_len_bytes &&
               mode_s_queue->Dequeue(mode_s_packet)) {
            memcpy(&packets_to_report.mode_s_packets[packets_to_report.header->num_mode_s_packets], &mode_s_packet,
                   sizeof(RawModeSPacket));
            packets_to_report.header->num_mode_s_packets++;
            packets_to_report.len_bytes += sizeof(RawModeSPacket);
        }
    }
    if (uat_adsb_queue) {
        // Stuff with UAT ADS-B packets.
        RawUATADSBPacket uat_adsb_packet;
        packets_to_report.uat_adsb_packets = reinterpret_cast<RawUATADSBPacket*>(buf + packets_to_report.len_bytes);
        while (packets_to_report.len_bytes + sizeof(RawUATADSBPacket) < buf_len_bytes &&
               uat_adsb_queue->Dequeue(uat_adsb_packet)) {
            memcpy(&packets_to_report.uat_adsb_packets[packets_to_report.header->num_uat_adsb_packets],
                   &uat_adsb_packet, sizeof(RawUATADSBPacket));
            packets_to_report.header->num_uat_adsb_packets++;
            packets_to_report.len_bytes += sizeof(RawUATADSBPacket);
        }
    }
    if (uat_uplink_queue) {
        // Stuff with UAT Uplink packets.
        RawUATUplinkPacket uat_uplink_packet;
        packets_to_report.uat_uplink_packets = reinterpret_cast<RawUATUplinkPacket*>(buf + packets_to_report.len_bytes);
        while (packets_to_report.len_bytes + sizeof(RawUATUplinkPacket) < buf_len_bytes &&
               uat_uplink_queue->Dequeue(uat_uplink_packet)) {
            memcpy(&packets_to_report.uat_uplink_packets[packets_to_report.header->num_uat_uplink_packets],
                   &uat_uplink_packet, sizeof(RawUATUplinkPacket));
            packets_to_report.header->num_uat_uplink_packets++;
            packets_to_report.len_bytes += sizeof(RawUATUplinkPacket);
        }
    }

    return packets_to_report;
}

bool CompositeArray::UnpackRawPacketsBuffer(CompositeArray::RawPackets& packets, uint8_t* buf, uint16_t buf_len_bytes) {
#ifdef ON_PICO
    // Ensure that buf is word-aligned.
    if (reinterpret_cast<uintptr_t>(buf) % 4 != 0) {
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer", "Buffer is not word-aligned.");
        return false;  // Buffer must be word-aligned.
    }
#endif

    if (buf_len_bytes < sizeof(RawPackets::Header)) {
        // Buffer too small to contain header.
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer", "Buffer too small to contain header.");
        return false;
    }

    packets.header = reinterpret_cast<RawPackets::Header*>(buf);

    packets.mode_s_packets = reinterpret_cast<RawModeSPacket*>(buf + sizeof(RawPackets::Header));
    packets.uat_adsb_packets =
        reinterpret_cast<RawUATADSBPacket*>(packets.mode_s_packets + packets.header->num_mode_s_packets);
    packets.uat_uplink_packets =
        reinterpret_cast<RawUATUplinkPacket*>(packets.uat_adsb_packets + packets.header->num_uat_adsb_packets);

    // Extract the header and make sure buf is big enough to contain the claimed number of packets.
    packets.len_bytes = sizeof(RawPackets::Header) + packets.header->num_mode_s_packets * sizeof(RawModeSPacket) +
                        packets.header->num_uat_adsb_packets * sizeof(RawUATADSBPacket) +
                        packets.header->num_uat_uplink_packets * sizeof(RawUATUplinkPacket);

    if (buf_len_bytes < packets.len_bytes) {
        CONSOLE_ERROR(
            "CompositeArray::UnpackRawPacketsBuffer",
            "Buffer too small for claimed number of packets: expected %u bytes from header, buffer was %u bytes.",
            packets.len_bytes, buf_len_bytes);
        return false;  // Buffer is too short to contain the claimed number of packets.
    }

    return true;
}

bool CompositeArray::UnpackRawPacketsBufferToQueues(uint8_t* buf, uint16_t buf_len_bytes,
                                                    PFBQueue<RawModeSPacket>* mode_s_queue,
                                                    PFBQueue<RawUATADSBPacket>* uat_adsb_queue,
                                                    PFBQueue<RawUATUplinkPacket>* uat_uplink_queue) {
    CompositeArray::RawPackets packets;
    if (!UnpackRawPacketsBuffer(packets, buf, buf_len_bytes)) {
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBufferToQueues", "Failed to unpack buffer.");
        return false;
    }

    if (mode_s_queue == nullptr && packets.header->num_mode_s_packets > 0) {
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBufferToQueues",
                      "No Mode S queue provided but header claims %d packets.", packets.header->num_mode_s_packets);
        return false;  // No Mode S queue provided but header claims packets.
    }
    if (uat_adsb_queue == nullptr && packets.header->num_uat_adsb_packets > 0) {
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBufferToQueues",
                      "No UAT ADS-B queue provided but header claims %d packets.",
                      packets.header->num_uat_adsb_packets);
        return false;  // No UAT ADS-B queue provided but header claims packets.
    }
    if (uat_uplink_queue == nullptr && packets.header->num_uat_uplink_packets > 0) {
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBufferToQueues",
                      "No UAT Uplink queue provided but header claims %d packets.",
                      packets.header->num_uat_uplink_packets);
        return false;  // No UAT Uplink queue provided but header claims packets.
    }

    for (uint16_t i = 0; i < packets.header->num_mode_s_packets; i++) {
        if (!mode_s_queue->Enqueue(packets.mode_s_packets[i])) {
            CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer", "Mode S queue full, cannot enqueue packet %d / %d.",
                          i, packets.header->num_mode_s_packets);
            return false;  // Queue full, cannot enqueue packet.
        }
    }

    for (uint16_t i = 0; i < packets.header->num_uat_adsb_packets; i++) {
        if (!uat_adsb_queue->Enqueue(packets.uat_adsb_packets[i])) {
            CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer",
                          "UAT ADS-B queue full, cannot enqueue packet %d / %d.", i,
                          packets.header->num_uat_adsb_packets);
            return false;  // Queue full, cannot enqueue packet.
        }
    }

    for (uint16_t i = 0; i < packets.header->num_uat_uplink_packets; i++) {
        if (!uat_uplink_queue->Enqueue(packets.uat_uplink_packets[i])) {
            CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer",
                          "UAT Uplink queue full, cannot enqueue packet %d / %d.", i,
                          packets.header->num_uat_uplink_packets);
            return false;  // Queue full, cannot enqueue packet.
        }
    }

    return true;  // All packets successfully enqueued.
}