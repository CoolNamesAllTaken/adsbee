#pragma once

#include "data_structures.hh"
#include "mode_s_packet.hh"
#include "stdint.h"
#include "stdio.h"
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
        static constexpr uint16_t kErrorMessageMaxLen = 256;

        // This header is used on the SPI bus to precede a packed buffer of packets.
        struct __attribute__((__packed__)) Header {
            uint16_t num_mode_s_packets = 0;
            uint16_t num_uat_adsb_packets = 0;
            uint16_t num_uat_uplink_packets = 0;
            uint16_t padding = 0;  // Padding to make struct word-aligned (8 bytes total)
        };

        /**
         * Validates the CompositeArray::RawPackets struct to ensure that the header is present and that the length
         * is sufficient to hold the declared number of packets. If an error_msg buffer is provided, it will be filled
         * with a description of the error if the struct is invalid.
         * @param[in,out] error_msg Optional buffer to fill with an error message if the struct is invalid.
         * @retval True if the struct is valid, false otherwise.
         */
        bool IsValid(char* error_msg = nullptr) const {
            if (header == nullptr) {
                if (error_msg) {
                    snprintf(error_msg, kErrorMessageMaxLen, "Invalid CompositeArray::RawPackets: null header.");
                }
                return false;
            }
            if (len_bytes < sizeof(Header)) {
                if (error_msg) {
                    snprintf(error_msg, kErrorMessageMaxLen,
                             "Invalid CompositeArray::RawPackets: insufficient length for header.");
                }
                return false;
            }
            uint16_t expected_len_bytes = sizeof(Header) + header->num_mode_s_packets * sizeof(RawModeSPacket) +
                                          header->num_uat_adsb_packets * sizeof(RawUATADSBPacket) +
                                          header->num_uat_uplink_packets * sizeof(RawUATUplinkPacket);
            if (len_bytes < expected_len_bytes) {
                if (error_msg) {
                    snprintf(error_msg, kErrorMessageMaxLen,
                             "Invalid CompositeArray::RawPackets: insufficient length for %u Mode S packet(s), %u UAT "
                             "ADSB packet(s), %u UAT Uplink packet(s) (expected %u bytes, got %u bytes).",
                             header->num_mode_s_packets, header->num_uat_adsb_packets, header->num_uat_uplink_packets,
                             expected_len_bytes, len_bytes);
                }
                return false;
            }
            return true;
        }

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
     * and returns a CompositeArray::RawPackets struct that describes the contents of the buffer.
     * @param[out] packets Struct to fill with pointers to the arrays in the buffer.
     * @param[in] buf Buffer containing header and packed packets.
     * @param[in] buf_len_bytes Length of the buffer, in bytes.
     * @retval CompositeArray::RawPackets struct that describes the contents of the buffer.
     */
    static bool UnpackRawPacketsBuffer(CompositeArray::RawPackets& packets, uint8_t* buf, uint16_t buf_len_bytes);

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
    static bool UnpackRawPacketsBufferToQueues(uint8_t* buf, uint16_t buf_len_bytes,
                                               PFBQueue<RawModeSPacket>* mode_s_queue,
                                               PFBQueue<RawUATADSBPacket>* uat_adsb_queue,
                                               PFBQueue<RawUATUplinkPacket>* uat_uplink_queue);
};