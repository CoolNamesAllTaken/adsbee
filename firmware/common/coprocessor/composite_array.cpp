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
        while (packets_to_report.len_bytes + sizeof(RawModeSPacket) <= buf_len_bytes &&
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
        while (packets_to_report.len_bytes + sizeof(RawUATADSBPacket) <= buf_len_bytes &&
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
        while (packets_to_report.len_bytes + sizeof(RawUATUplinkPacket) <= buf_len_bytes &&
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

bool CompositeArray::MergeRawPacketsBuffers(uint8_t* dst_buf, const uint8_t* src_buf) {
    auto* dst_hdr = reinterpret_cast<RawPackets::Header*>(dst_buf);
    auto* src_hdr = reinterpret_cast<const RawPackets::Header*>(src_buf);

    const uint16_t N = dst_hdr->num_mode_s_packets;
    const uint16_t M = dst_hdr->num_uat_adsb_packets;
    const uint16_t K = dst_hdr->num_uat_uplink_packets;
    const uint16_t P = src_hdr->num_mode_s_packets;
    const uint16_t Q = src_hdr->num_uat_adsb_packets;
    const uint16_t R = src_hdr->num_uat_uplink_packets;

    const uint32_t combined_size = sizeof(RawPackets::Header) + (uint32_t)(N + P) * sizeof(RawModeSPacket) +
                                   (uint32_t)(M + Q) * sizeof(RawUATADSBPacket) +
                                   (uint32_t)(K + R) * sizeof(RawUATUplinkPacket);
    if (combined_size > RawPackets::kMaxLenBytes) {
        return false;
    }

    // Offsets in dst before any modification.
    const uint16_t adsb_start = sizeof(RawPackets::Header) + N * sizeof(RawModeSPacket);
    const uint16_t upl_start = adsb_start + M * sizeof(RawUATADSBPacket);

    // Pointers into src sections.
    const uint8_t* src_ms_ptr = src_buf + sizeof(RawPackets::Header);
    const uint8_t* src_adsb_ptr = src_ms_ptr + P * sizeof(RawModeSPacket);
    const uint8_t* src_upl_ptr = src_adsb_ptr + Q * sizeof(RawUATADSBPacket);

    // Step 1: Insert src's Mode S after dst's Mode S by shifting ADS-B and Uplink forward.
    const uint16_t src_ms_size = P * sizeof(RawModeSPacket);
    const uint16_t adsb_upl_size = M * sizeof(RawUATADSBPacket) + K * sizeof(RawUATUplinkPacket);
    if (adsb_upl_size > 0) {
        memmove(dst_buf + adsb_start + src_ms_size, dst_buf + adsb_start, adsb_upl_size);
    }
    if (src_ms_size > 0) {
        memcpy(dst_buf + adsb_start, src_ms_ptr, src_ms_size);
    }
    dst_hdr->num_mode_s_packets = N + P;

    // Step 2: Insert src's ADS-B after dst's (now-shifted) ADS-B by shifting Uplink forward.
    // new_upl_start: position of UPL_a after step 1, before step 2's shift.
    const uint16_t new_upl_start = adsb_start + src_ms_size + M * sizeof(RawUATADSBPacket);
    const uint16_t src_adsb_size = Q * sizeof(RawUATADSBPacket);
    const uint16_t upl_size = K * sizeof(RawUATUplinkPacket);
    if (upl_size > 0) {
        memmove(dst_buf + new_upl_start + src_adsb_size, dst_buf + new_upl_start, upl_size);
    }
    if (src_adsb_size > 0) {
        memcpy(dst_buf + new_upl_start, src_adsb_ptr, src_adsb_size);
    }
    dst_hdr->num_uat_adsb_packets = M + Q;

    // Step 3: Append src's Uplink after UPL_a (which was shifted by src_adsb_size in step 2).
    const uint16_t src_upl_size = R * sizeof(RawUATUplinkPacket);
    if (src_upl_size > 0) {
        memcpy(dst_buf + new_upl_start + src_adsb_size + upl_size, src_upl_ptr, src_upl_size);
    }
    dst_hdr->num_uat_uplink_packets = K + R;

    return true;
}

uint16_t CompositeArray::CalculateRawPacketsBufferLength(PFBQueue<RawModeSPacket>* mode_s_queue,
                                                         PFBQueue<RawUATADSBPacket>* uat_adsb_queue,
                                                         PFBQueue<RawUATUplinkPacket>* uat_uplink_queue) {
    uint16_t total_len_bytes = sizeof(RawPackets::Header);

    if (mode_s_queue) {
        total_len_bytes += mode_s_queue->Length() * sizeof(RawModeSPacket);
    }
    if (uat_adsb_queue) {
        total_len_bytes += uat_adsb_queue->Length() * sizeof(RawUATADSBPacket);
    }
    if (uat_uplink_queue) {
        total_len_bytes += uat_uplink_queue->Length() * sizeof(RawUATUplinkPacket);
    }

    return total_len_bytes;
}