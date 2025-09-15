#pragma once

#include "data_structures.hh"
#include "mode_s_packet.hh"
#include "stdint.h"
#include "uat_packet.hh"

/**
 * CompositeArrays are used to shuffle packets around between internal functions and on the SPI bus. With multiple
 * coexisting packet types, it becomes inefficient to run multiple SPI transactions, one for each packet type, and
 * likewise it's inefficient to allocate multiple separate packet buffers internally, since not all of the buffer space
 * will get used, and the code becomes harder to change as we add more packet types.
 *
 * The CompositeArray class solves this problem by providing a nice way to pass around a single buffer that contains
 * zero or more packets of each kind. The buffer starts with a CompositeArray::RawPackets::Header, which describes how
 * many packets of each type are present, followed by arrays of raw packets of each type.
 */
class CompositeArray {
   public:
    struct RawPackets {
        // This header is used on the SPI bus to precede a packed buffer of packets.
        struct __attribute__((__packed__)) Header {
            uint16_t num_mode_s_packets = 0;
            uint16_t num_uat_adsb_packets = 0;
            uint16_t num_uat_uplink_packets = 0;
            uint16_t padding = 0;  // Padding to make struct word-aligned (8 bytes total)
        };

        uint16_t len_bytes = 0;  // Total length of the entire array in bytes, including header.

        Header* header;
        RawModeSPacket* mode_s_packets = nullptr;          // Array of RawModeSPacket structs.
        RawUATADSBPacket* uat_adsb_packets = nullptr;      // Array of RawUATADSBPacket structs.
        RawUATUplinkPacket* uat_uplink_packets = nullptr;  // Array of RawUATUplinkPacket structs.
    };

    // Ensure that things are nicely word-aliged so that we can do direct array access without memcpy.
    static_assert(sizeof(RawPackets::Header) % 4 == 0);  // Make sure it's word-aligned.
    static_assert(sizeof(RawModeSPacket) % 4 == 0);
    static_assert(sizeof(RawUATADSBPacket) % 4 == 0);
    static_assert(sizeof(RawUATUplinkPacket) % 4 == 0);

    /**
     * Fills a buffer as a CompositeArray (RawPackets::Header) followed by arrays of raw packets of each kind. Takes
     * pointers to queues to dequeue the packets from; any queues that are passed as a nullptr are skipped.
     * @param[out] buf Buffer to fill with header and packed packets.
     * @param[out] buf_len_bytes Length of the buffer, in bytes.
     * @param[in] mode_s_queue Pointer to a PFBQueue of RawModeSPacket to dequeue packets from, or nullptr to skip.
     * @param[in] uat_adsb_queue Pointer to a PFBQueue of RawUATADSBPacket to dequeue packets from, or nullptr to skip.
     * @param[in] uat_uplink_queue Pointer to a PFBQueue of RawUATUplinkPacket to dequeue packets from, or nullptr to
     * skip.
     * @retval CompositeArray::RawPackets struct that describes the contents of the buffer.
     */
    static RawPackets PackRawPacketsBuffer(uint8_t* buf, uint16_t buf_len_bytes, PFBQueue<RawModeSPacket>* mode_s_queue,
                                           PFBQueue<RawUATADSBPacket>* uat_adsb_queue,
                                           PFBQueue<RawUATUplinkPacket>* uat_uplink_queue);

    /**
     * Unpacks a buffer containing a CompositeArray (RawPackets::Header) followed by arrays of raw packets of each kind,
     * and enqueues the packets into the provided queues. Any queues that are passed as a nullptr are skipped. Returns
     * true if every packet that was passed in found a home, false otherwise.
     * @param[in] buf Buffer containing header and packed packets.
     * @param[in] buf_len_bytes Length of the buffer, in bytes.
     * @param[out] mode_s_queue Pointer to a PFBQueue of RawModeSPacket to enqueue packets into, or nullptr to skip.
     * @param[out] uat_adsb_queue Pointer to a PFBQueue of RawUATADSBPacket to enqueue packets into, or nullptr to skip.
     * @param[out] uat_uplink_queue Pointer to a PFBQueue of RawUATUplinkPacket to enqueue packets into, or nullptr to
     * skip.
     * @retval True if all packets were successfully enqueued, false otherwise.
     */
    static bool UnpackRawPacketsBuffer(uint8_t* buf, uint16_t buf_len_bytes, PFBQueue<RawModeSPacket>* mode_s_queue,
                                       PFBQueue<RawUATADSBPacket>* uat_adsb_queue,
                                       PFBQueue<RawUATUplinkPacket>* uat_uplink_queue);
};