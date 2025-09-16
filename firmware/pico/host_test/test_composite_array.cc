#include "composite_array.hh"
#include "gtest/gtest.h"

TEST(CompositeArray, PackRawPacketsBufferNoQueues) {
    uint8_t buffer[100] = {0};
    CompositeArray::RawPackets packets =
        CompositeArray::PackRawPacketsBuffer(buffer, sizeof(buffer), nullptr, nullptr, nullptr);

    // Expect only the header to be present with zero counts
    EXPECT_EQ(packets.len_bytes, sizeof(CompositeArray::RawPackets::Header));
    EXPECT_EQ(packets.header->num_mode_s_packets, 0);
    EXPECT_EQ(packets.header->num_uat_adsb_packets, 0);
    EXPECT_EQ(packets.header->num_uat_uplink_packets, 0);
    EXPECT_EQ(packets.mode_s_packets, nullptr);
    EXPECT_EQ(packets.uat_adsb_packets, nullptr);
    EXPECT_EQ(packets.uat_uplink_packets, nullptr);
}

TEST(CompositeArray, PackRawPacketsBufferTooManyPackets) {
    uint8_t buffer[sizeof(CompositeArray::RawPackets::Header) + 5 * sizeof(RawModeSPacket)] = {0};

    PFBQueue<RawModeSPacket>::PFBQueueConfig queue_config = {
        .buf_len_num_elements = 10, .buffer = nullptr, .overwrite_when_full = false};
    PFBQueue<RawModeSPacket> mode_s_queue = PFBQueue<RawModeSPacket>(queue_config);

    RawModeSPacket dummy_packet;
    for (int i = 0; i < queue_config.buf_len_num_elements; i++) {
        dummy_packet.buffer[0] = i;  // Differentiate packets by first word
        mode_s_queue.Enqueue(dummy_packet);
    }
    CompositeArray::RawPackets packets =
        CompositeArray::PackRawPacketsBuffer(buffer, sizeof(buffer), &mode_s_queue, nullptr, nullptr);

    // Expect only 5 packets to be packed due to buffer size
    EXPECT_EQ(packets.len_bytes, sizeof(CompositeArray::RawPackets::Header) + 5 * sizeof(RawModeSPacket));
    EXPECT_EQ(packets.header->num_mode_s_packets, 5);
    EXPECT_EQ(packets.header->num_uat_adsb_packets, 0);
    EXPECT_EQ(packets.header->num_uat_uplink_packets, 0);
    EXPECT_NE(packets.mode_s_packets, nullptr);
    EXPECT_EQ(packets.uat_adsb_packets, nullptr);
    EXPECT_EQ(packets.uat_uplink_packets, nullptr);

    for (uint16_t i = 0; i < packets.header->num_mode_s_packets; i++) {
        EXPECT_EQ(packets.mode_s_packets[i].buffer[0], i);
    }
}

TEST(CompositeArray, PackRawPacketsBufferTooManyMixedPackets) {
    const uint16_t num_mode_s_packets_to_enqueue = 4;
    const uint16_t num_uat_adsb_packets_to_enqueue = 3;
    const uint16_t num_uat_uplink_packets_to_enqueue = 6;

    uint8_t buffer[sizeof(CompositeArray::RawPackets::Header) + num_mode_s_packets_to_enqueue * sizeof(RawModeSPacket) +
                   num_uat_adsb_packets_to_enqueue * sizeof(RawUATADSBPacket) +
                   (num_uat_uplink_packets_to_enqueue - 1) * sizeof(RawUATUplinkPacket)] = {0};

    PFBQueue<RawModeSPacket>::PFBQueueConfig mode_s_queue_config = {
        .buf_len_num_elements = 10, .buffer = nullptr, .overwrite_when_full = false};
    PFBQueue<RawModeSPacket> mode_s_queue = PFBQueue<RawModeSPacket>(mode_s_queue_config);
    PFBQueue<RawUATADSBPacket>::PFBQueueConfig uat_adsb_queue_config = {
        .buf_len_num_elements = 10, .buffer = nullptr, .overwrite_when_full = false};
    PFBQueue<RawUATADSBPacket> uat_adsb_queue = PFBQueue<RawUATADSBPacket>(uat_adsb_queue_config);
    PFBQueue<RawUATUplinkPacket>::PFBQueueConfig uat_uplink_queue_config = {
        .buf_len_num_elements = 10, .buffer = nullptr, .overwrite_when_full = false};
    PFBQueue<RawUATUplinkPacket> uat_uplink_queue = PFBQueue<RawUATUplinkPacket>(uat_uplink_queue_config);

    RawModeSPacket dummy_mode_s_packet;
    for (int i = 0; i < num_mode_s_packets_to_enqueue; i++) {
        dummy_mode_s_packet.buffer[0] = i;  // Differentiate packets by first word
        mode_s_queue.Enqueue(dummy_mode_s_packet);
    }
    RawUATADSBPacket dummy_uat_adsb_packet;
    for (int i = 0; i < num_uat_adsb_packets_to_enqueue; i++) {
        dummy_uat_adsb_packet.encoded_message[0] = i;  // Differentiate packets by first word
        uat_adsb_queue.Enqueue(dummy_uat_adsb_packet);
    }
    RawUATUplinkPacket dummy_uat_uplink_packet;
    for (int i = 0; i < num_uat_uplink_packets_to_enqueue; i++) {
        dummy_uat_uplink_packet.encoded_message[0] = i;  // Differentiate packets by first word
        uat_uplink_queue.Enqueue(dummy_uat_uplink_packet);
    }
    CompositeArray::RawPackets packets =
        CompositeArray::PackRawPacketsBuffer(buffer, sizeof(buffer), &mode_s_queue, &uat_adsb_queue, &uat_uplink_queue);

    // Expect only 3 packets to be packed due to buffer size
    EXPECT_EQ(packets.len_bytes, sizeof(CompositeArray::RawPackets::Header) +
                                     num_mode_s_packets_to_enqueue * sizeof(RawModeSPacket) +
                                     num_uat_adsb_packets_to_enqueue * sizeof(RawUATADSBPacket) +
                                     (num_uat_uplink_packets_to_enqueue - 1) * sizeof(RawUATUplinkPacket));
    EXPECT_EQ(packets.header->num_mode_s_packets, num_mode_s_packets_to_enqueue);
    EXPECT_EQ(packets.header->num_uat_adsb_packets, num_uat_adsb_packets_to_enqueue);
    EXPECT_EQ(packets.header->num_uat_uplink_packets, num_uat_uplink_packets_to_enqueue - 1);
    EXPECT_NE(packets.mode_s_packets, nullptr);
    EXPECT_NE(packets.uat_adsb_packets, nullptr);
    EXPECT_NE(packets.uat_uplink_packets, nullptr);

    for (uint16_t i = 0; i < packets.header->num_mode_s_packets; i++) {
        EXPECT_EQ(packets.mode_s_packets[i].buffer[0], i);
    }
    for (uint16_t i = 0; i < packets.header->num_uat_adsb_packets; i++) {
        EXPECT_EQ(packets.uat_adsb_packets[i].encoded_message[0], i);
    }
    for (uint16_t i = 0; i < packets.header->num_uat_uplink_packets; i++) {
        EXPECT_EQ(packets.uat_uplink_packets[i].encoded_message[0], i);
    }
}

TEST(CompositeArray, PackUnpackRawPacketsBufferMixedPackets) {
    const uint16_t num_mode_s_packets_to_enqueue = 4;
    const uint16_t num_uat_adsb_packets_to_enqueue = 3;
    const uint16_t num_uat_uplink_packets_to_enqueue = 6;

    uint8_t buffer[sizeof(CompositeArray::RawPackets::Header) + num_mode_s_packets_to_enqueue * sizeof(RawModeSPacket) +
                   num_uat_adsb_packets_to_enqueue * sizeof(RawUATADSBPacket) +
                   (num_uat_uplink_packets_to_enqueue) * sizeof(RawUATUplinkPacket)] = {0};

    SCOPED_TRACE("PackUnpackRawPacketsBufferMixedPackets");

    PFBQueue<RawModeSPacket>::PFBQueueConfig mode_s_queue_config = {
        .buf_len_num_elements = 10, .buffer = nullptr, .overwrite_when_full = false};
    PFBQueue<RawModeSPacket> mode_s_queue = PFBQueue<RawModeSPacket>(mode_s_queue_config);
    PFBQueue<RawUATADSBPacket>::PFBQueueConfig uat_adsb_queue_config = {
        .buf_len_num_elements = 10, .buffer = nullptr, .overwrite_when_full = false};
    PFBQueue<RawUATADSBPacket> uat_adsb_queue = PFBQueue<RawUATADSBPacket>(uat_adsb_queue_config);
    PFBQueue<RawUATUplinkPacket>::PFBQueueConfig uat_uplink_queue_config = {
        .buf_len_num_elements = 10, .buffer = nullptr, .overwrite_when_full = false};
    PFBQueue<RawUATUplinkPacket> uat_uplink_queue = PFBQueue<RawUATUplinkPacket>(uat_uplink_queue_config);

    RawModeSPacket dummy_mode_s_packet;
    for (int i = 0; i < num_mode_s_packets_to_enqueue; i++) {
        dummy_mode_s_packet.buffer[0] = i;  // Differentiate packets by first word
        mode_s_queue.Enqueue(dummy_mode_s_packet);
    }
    RawUATADSBPacket dummy_uat_adsb_packet;
    for (int i = 0; i < num_uat_adsb_packets_to_enqueue; i++) {
        dummy_uat_adsb_packet.encoded_message[0] = i;  // Differentiate packets by first word
        uat_adsb_queue.Enqueue(dummy_uat_adsb_packet);
    }
    RawUATUplinkPacket dummy_uat_uplink_packet;
    for (int i = 0; i < num_uat_uplink_packets_to_enqueue; i++) {
        dummy_uat_uplink_packet.encoded_message[0] = i;  // Differentiate packets by first word
        uat_uplink_queue.Enqueue(dummy_uat_uplink_packet);
    }
    CompositeArray::RawPackets packets =
        CompositeArray::PackRawPacketsBuffer(buffer, sizeof(buffer), &mode_s_queue, &uat_adsb_queue, &uat_uplink_queue);

    EXPECT_TRUE(mode_s_queue.IsEmpty());
    EXPECT_TRUE(uat_adsb_queue.IsEmpty());
    EXPECT_TRUE(uat_uplink_queue.IsEmpty());

    // Make sure we get an error if we try to unpack without providing all queues.
    EXPECT_FALSE(CompositeArray::UnpackRawPacketsBufferToQueues(buffer, packets.len_bytes, &mode_s_queue,
                                                                &uat_adsb_queue, nullptr));
    EXPECT_FALSE(CompositeArray::UnpackRawPacketsBufferToQueues(buffer, packets.len_bytes, nullptr, &uat_adsb_queue,
                                                                &uat_uplink_queue));
    EXPECT_FALSE(CompositeArray::UnpackRawPacketsBufferToQueues(buffer, packets.len_bytes, &mode_s_queue, nullptr,
                                                                &uat_uplink_queue));

    EXPECT_TRUE(CompositeArray::UnpackRawPacketsBufferToQueues(buffer, packets.len_bytes, &mode_s_queue,
                                                               &uat_adsb_queue, &uat_uplink_queue));
    EXPECT_EQ(mode_s_queue.Length(), num_mode_s_packets_to_enqueue);
    EXPECT_EQ(uat_adsb_queue.Length(), num_uat_adsb_packets_to_enqueue);
    EXPECT_EQ(uat_uplink_queue.Length(), num_uat_uplink_packets_to_enqueue);

    RawModeSPacket dequeued_mode_s_packet;
    for (uint16_t i = 0; i < num_mode_s_packets_to_enqueue; i++) {
        EXPECT_TRUE(mode_s_queue.Dequeue(dequeued_mode_s_packet));
        EXPECT_EQ(dequeued_mode_s_packet.buffer[0], i);
    }
    RawUATADSBPacket dequeued_uat_adsb_packet;
    for (uint16_t i = 0; i < num_uat_adsb_packets_to_enqueue; i++) {
        EXPECT_TRUE(uat_adsb_queue.Dequeue(dequeued_uat_adsb_packet));
        EXPECT_EQ(dequeued_uat_adsb_packet.encoded_message[0], i);
    }
    RawUATUplinkPacket dequeued_uat_uplink_packet;
    for (uint16_t i = 0; i < num_uat_uplink_packets_to_enqueue; i++) {
        EXPECT_TRUE(uat_uplink_queue.Dequeue(dequeued_uat_uplink_packet));
        EXPECT_EQ(dequeued_uat_uplink_packet.encoded_message[0], i);
    }
}

TEST(CompositeArray, RawPacketsHeaderIsValid) {
    CompositeArray::RawPackets packets;
    char error_msg[CompositeArray::RawPackets::kErrorMessageMaxLen];

    // Null header
    packets.header = nullptr;
    EXPECT_FALSE(packets.IsValid(error_msg));
    EXPECT_STREQ(error_msg, "Invalid CompositeArray::RawPackets: null header.");

    // Insufficient length for header
    CompositeArray::RawPackets::Header header = {};
    packets.header = &header;
    EXPECT_FALSE(packets.IsValid(error_msg));
    EXPECT_STREQ(error_msg, "Invalid CompositeArray::RawPackets: insufficient length for header.");

    // Insufficient length for packets
    packets.header->num_mode_s_packets = 2;
    packets.header->num_uat_adsb_packets = 1;
    packets.header->num_uat_uplink_packets = 1;
    packets.len_bytes = 8;  // Too small to hold the packets
    // uint16_t expected_len_bytes = sizeof(CompositeArray::RawPackets::Header) +
    //                               packets.header->num_mode_s_packets * sizeof(RawModeSPacket) +
    //                               packets.header->num_uat_adsb_packets * sizeof(RawUATADSBPacket) +
    //                               packets.header->num_uat_uplink_packets * sizeof(RawUATUplinkPacket);
    EXPECT_FALSE(packets.IsValid(error_msg));
    EXPECT_STREQ(
        error_msg,
        "Invalid CompositeArray::RawPackets: insufficient length for 2 Mode S packet(s), 1 UAT ADSB packet(s), 1 "
        "UAT Uplink packet(s) (expected 704 bytes, got 8 bytes).");

    // Valid case
    packets.len_bytes = sizeof(CompositeArray::RawPackets::Header) + 2 * sizeof(RawModeSPacket) +
                        1 * sizeof(RawUATADSBPacket) + 1 * sizeof(RawUATUplinkPacket);
    EXPECT_TRUE(packets.IsValid());
}