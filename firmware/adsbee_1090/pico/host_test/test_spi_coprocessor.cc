#include "gtest/gtest.h"
#include "spi_coprocessor.hh"
#include "spi_coprocessor_packet.hh"

TEST(SPICoprocessor, SCWritePacket) {
    SPICoprocessorPacket::SCWritePacket packet;
    packet.cmd = ObjectDictionary::SCCommand::kCmdWriteToSlave;
    packet.addr = ObjectDictionary::Address::kAddrRawModeSPacket;
    RawModeSPacket tpacket = RawModeSPacket((const char*)"8D7C1BE8581B66E9BD8CEEDC1C9F");
    packet.len = sizeof(RawModeSPacket);
    memcpy(packet.data, &tpacket, packet.len);
    // Calculate CRC and add it to the data buffer.
    uint16_t crc =
        CalculateCRC16(packet.GetBuf(), packet.GetBufLenBytes() - SPICoprocessorPacket::SCWritePacket::kCRCLenBytes);
    memcpy(packet.data + packet.len, &crc, sizeof(uint16_t));
    EXPECT_TRUE(packet.IsValid());

    packet.PopulateCRC();
    EXPECT_TRUE(packet.IsValid());

    EXPECT_EQ(packet.GetBufLenBytes(), sizeof(RawModeSPacket) + sizeof(ObjectDictionary::SCCommand) +
                                           sizeof(ObjectDictionary::Address) + 2 * sizeof(uint16_t) +
                                           SPICoprocessorPacket::SCWritePacket::kCRCLenBytes);

    SPICoprocessorPacket::SCWritePacket packet_copy =
        SPICoprocessorPacket::SCWritePacket(packet.GetBuf(), packet.GetBufLenBytes());
    EXPECT_EQ(packet.cmd, packet_copy.cmd);
    EXPECT_EQ(packet.addr, packet_copy.addr);
    EXPECT_EQ(packet.IsValid(), packet_copy.IsValid());
    RawModeSPacket* tpacket_copy = (RawModeSPacket*)packet_copy.data;
    EXPECT_EQ(tpacket.buffer_len_bytes, tpacket_copy->buffer_len_bytes);
    EXPECT_EQ(tpacket.buffer[0], tpacket_copy->buffer[0]);
    EXPECT_EQ(tpacket.buffer[1], tpacket_copy->buffer[1]);
    EXPECT_EQ(tpacket.buffer[2], tpacket_copy->buffer[2]);
    EXPECT_EQ(tpacket.buffer[3], tpacket_copy->buffer[3]);

    // Poke packet and make checksum fail.
    packet.data[0] = ~packet.data[0];
    EXPECT_FALSE(packet.IsValid());
}

// TEST(SPICoprocessor, SCReadRequestPacket) {
//     // Test packet creation.
//     SPICoprocessorPacket::SCReadRequestPacket packet;
//     packet.cmd = ObjectDictionary::SCCommand::kCmdReadFromMaster;
//     packet.addr = ObjectDictionary::Address::kAddrSettingsData;
//     packet.offset = 0xFEBC;
//     packet.len = 40;
//     // Make sure that CRC generation works as expected.
//     packet.PopulateCRC();
//     EXPECT_TRUE(packet.IsValid());
//     EXPECT_EQ(CalculateCRC16(packet.GetBuf(),
//                              packet.GetBufLenBytes() - SPICoprocessorPacket::SCReadRequestPacket::kCRCLenBytes),
//               packet.crc);

//     // Test packet ingestion.
//     SPICoprocessorPacket::SCReadRequestPacket packet_copy =
//         SPICoprocessorPacket::SCReadRequestPacket(packet.GetBuf(), packet.GetBufLenBytes());
//     EXPECT_EQ(packet_copy.cmd, packet.cmd);
//     EXPECT_EQ(packet_copy.addr, packet.addr);
//     EXPECT_EQ(packet_copy.offset, packet.offset);
//     EXPECT_EQ(packet_copy.len, packet.len);
//     EXPECT_TRUE(packet_copy.IsValid());
//     // Changes to packet should not affect packet_copy.
//     packet.GetBuf()[0] = ~packet.GetBuf()[0];
//     EXPECT_FALSE(packet.IsValid());
//     EXPECT_TRUE(packet_copy.IsValid());
// }

TEST(SPICoprocessor, SCResponsePacket) {
    // Test packet creation.
    SPICoprocessorPacket::SCResponsePacket packet;
    packet.cmd = ObjectDictionary::SCCommand::kCmdDataBlock;
    EXPECT_EQ(packet.GetBuf()[0], ObjectDictionary::SCCommand::kCmdDataBlock);
    RawModeSPacket tpacket = RawModeSPacket((const char*)"8D7C1BE8581B66E9BD8CEEDC1C9F");
    packet.data_len_bytes = sizeof(RawModeSPacket);
    memcpy(packet.data, &tpacket, packet.data_len_bytes);
    EXPECT_FALSE(packet.IsValid());
    packet.PopulateCRC();
    EXPECT_TRUE(packet.IsValid());

    // Test packet ingestion.
    SPICoprocessorPacket::SCResponsePacket packet_copy =
        SPICoprocessorPacket::SCResponsePacket(packet.GetBuf(), packet.GetBufLenBytes());
    EXPECT_TRUE(packet_copy.IsValid());
    EXPECT_EQ(packet_copy.cmd, packet.cmd);
    RawModeSPacket* tpacket_copy = (RawModeSPacket*)packet_copy.data;
    EXPECT_EQ(tpacket_copy->buffer[0], 0x8D7C1BE8u);
    EXPECT_EQ(tpacket_copy->buffer[1], 0x581B66E9u);
    EXPECT_EQ(tpacket_copy->buffer[2], 0xBD8CEEDCu);
    EXPECT_EQ(tpacket_copy->buffer[3], 0x1C9Fu << 16);
    // Poke the checksum and see it fail.
    tpacket_copy->buffer[0] = tpacket_copy->buffer[0] << 1;
    EXPECT_FALSE(packet_copy.IsValid());
    // Make sure original packet was not affected.
    EXPECT_TRUE(packet.IsValid());
}

void BuildAckPacket(SPICoprocessorPacket::SCAckPacket& packet, bool success) {
    packet.ack = success ? 1 : 0;
    packet.PopulateCRC();
}

TEST(SPICoprocessor, SCAckPacket) {
    // Basic send/receive round-trip.
    SPICoprocessorPacket::SCAckPacket packet;
    EXPECT_EQ(packet.cmd, ObjectDictionary::SCCommand::kCmdAck);  // Default must be kCmdAck.
    EXPECT_EQ(packet.GetBufLenBytes(), SPICoprocessorPacket::SCAckPacket::kBufLenBytes);
    BuildAckPacket(packet, true);
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.ack, 1);

    // NACK.
    SPICoprocessorPacket::SCAckPacket nack_packet;
    BuildAckPacket(nack_packet, false);
    EXPECT_TRUE(nack_packet.IsValid());
    EXPECT_EQ(nack_packet.ack, 0);

    // Poking any field must invalidate the CRC.
    nack_packet.ack = ~nack_packet.ack;
    EXPECT_FALSE(nack_packet.IsValid());
}

TEST(SPICoprocessor, SCResponsePacketScrambleBuf) {
    // Regression: pre-scrambling the data buffer must not corrupt the CRC when only a subset of bytes is populated.
    // GetCRCPtr() uses data_len_bytes to locate the CRC, so bytes beyond data_len_bytes are irrelevant.
    SCOPED_TRACE("SCResponsePacketScrambleBuf");

    SPICoprocessorPacket::SCResponsePacket packet;
    memset(packet.data, 0xFF, SPICoprocessorPacket::SCResponsePacket::kDataMaxLenBytes);
    packet.cmd = ObjectDictionary::SCCommand::kCmdDataBlock;
    packet.data_len_bytes = 1;
    packet.data[0] = 1;
    packet.PopulateCRC();
    EXPECT_TRUE(packet.IsValid());
}