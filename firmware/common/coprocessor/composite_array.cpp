#include "composite_array.hh"

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

    // Fill up the CompositeArray::RawPackets header and associated buffers with as many packets as we can report.
    if (mode_s_queue) {
        // Stuff with Mode S packets.
        RawModeSPacket mode_s_packet;
        packets_to_report.mode_s_packets = reinterpret_cast<RawModeSPacket*>(buf + packets_to_report.len_bytes);
        while (packets_to_report.len_bytes < buf_len_bytes && mode_s_queue->Dequeue(mode_s_packet)) {
            packets_to_report.mode_s_packets[packets_to_report.header->num_mode_s_packets] = mode_s_packet;
            packets_to_report.header->num_mode_s_packets++;
            packets_to_report.len_bytes += sizeof(RawModeSPacket);
        }
    }
    if (uat_adsb_queue) {
        // Stuff with UAT ADS-B packets.
        RawUATADSBPacket uat_adsb_packet;
        packets_to_report.uat_adsb_packets = reinterpret_cast<RawUATADSBPacket*>(buf + packets_to_report.len_bytes);
        while (packets_to_report.len_bytes < buf_len_bytes && uat_adsb_queue->Dequeue(uat_adsb_packet)) {
            packets_to_report.uat_adsb_packets[packets_to_report.header->num_uat_adsb_packets] = uat_adsb_packet;
            packets_to_report.header->num_uat_adsb_packets++;
            packets_to_report.len_bytes += sizeof(RawUATADSBPacket);
        }
    }
    if (uat_uplink_queue) {
        // Stuff with UAT Uplink packets.
        RawUATUplinkPacket uat_uplink_packet;
        packets_to_report.uat_uplink_packets = reinterpret_cast<RawUATUplinkPacket*>(buf + packets_to_report.len_bytes);
        while (packets_to_report.len_bytes < buf_len_bytes && uat_uplink_queue->Dequeue(uat_uplink_packet)) {
            packets_to_report.uat_uplink_packets[packets_to_report.header->num_uat_uplink_packets] = uat_uplink_packet;
            packets_to_report.header->num_uat_uplink_packets++;
            packets_to_report.len_bytes += sizeof(RawUATUplinkPacket);
        }
    }

    return packets_to_report;
}

bool CompositeArray::UnpackRawPacketsBuffer(uint8_t* buf, uint16_t buf_len_bytes,
                                            PFBQueue<RawModeSPacket>* mode_s_queue,
                                            PFBQueue<RawUATADSBPacket>* uat_adsb_queue,
                                            PFBQueue<RawUATUplinkPacket>* uat_uplink_queue) {
    // Ensure that buf is word-aligned.
    if (reinterpret_cast<uintptr_t>(buf) % 4 != 0) {
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer", "Buffer is not word-aligned.");
        return false;  // Buffer must be word-aligned.
    }
    // Make sure buf is big enough to contain a header.
    if (buf_len_bytes < sizeof(RawPackets::Header)) {
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer", "Buffer too small to contain header.");
        return false;
    }
    // Extract the header and make sure buf is big enough to contain the claimed number of packets.
    RawPackets::Header* header = reinterpret_cast<RawPackets::Header*>(buf);
    uint16_t expected_len_bytes = sizeof(RawPackets::Header) + header->num_mode_s_packets * sizeof(RawModeSPacket) +
                                  header->num_uat_adsb_packets * sizeof(RawUATADSBPacket) +
                                  header->num_uat_uplink_packets * sizeof(RawUATUplinkPacket);
    if (buf_len_bytes < expected_len_bytes) {
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer", "Buffer too small for claimed number of packets.");
        return false;  // Buffer is too short to contain the claimed number of packets.
    }
    if (mode_s_queue == nullptr && header->num_mode_s_packets > 0) {
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer",
                      "No Mode S queue provided but header claims %d packets.", header->num_mode_s_packets);
        return false;  // No Mode S queue provided but header claims packets.
    }
    if (uat_adsb_queue == nullptr && header->num_uat_adsb_packets > 0) {
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer",
                      "No UAT ADS-B queue provided but header claims %d packets.", header->num_uat_adsb_packets);
        return false;  // No UAT ADS-B queue provided but header claims packets.
    }
    if (uat_uplink_queue == nullptr && header->num_uat_uplink_packets > 0) {
        CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer",
                      "No UAT Uplink queue provided but header claims %d packets.", header->num_uat_uplink_packets);
        return false;  // No UAT Uplink queue provided but header claims packets.
    }

    uint8_t* cursor = buf + sizeof(RawPackets::Header);
    RawModeSPacket* mode_s_packets = reinterpret_cast<RawModeSPacket*>(cursor);
    for (uint16_t i = 0; i < header->num_mode_s_packets; i++) {
        if (!mode_s_queue->Enqueue(mode_s_packets[i])) {
            CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer", "Mode S queue full, cannot enqueue packet %d / %d.",
                          i, header->num_mode_s_packets);
            return false;  // Queue full, cannot enqueue packet.
        }
        cursor += sizeof(RawModeSPacket);
    }

    RawUATADSBPacket* uat_adsb_packets = reinterpret_cast<RawUATADSBPacket*>(cursor);
    for (uint16_t i = 0; i < header->num_uat_adsb_packets; i++) {
        if (!uat_adsb_queue->Enqueue(uat_adsb_packets[i])) {
            CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer",
                          "UAT ADS-B queue full, cannot enqueue packet %d / %d.", i, header->num_uat_adsb_packets);
            return false;  // Queue full, cannot enqueue packet.
        }
        cursor += sizeof(RawUATADSBPacket);
    }

    RawUATUplinkPacket* uat_uplink_packets = reinterpret_cast<RawUATUplinkPacket*>(cursor);
    for (uint16_t i = 0; i < header->num_uat_uplink_packets; i++) {
        if (!uat_uplink_queue->Enqueue(uat_uplink_packets[i])) {
            CONSOLE_ERROR("CompositeArray::UnpackRawPacketsBuffer",
                          "UAT Uplink queue full, cannot enqueue packet %d / %d.", i, header->num_uat_uplink_packets);
            return false;  // Queue full, cannot enqueue packet.
        }
        cursor += sizeof(RawUATUplinkPacket);
    }

    return true;  // All packets successfully enqueued.
}