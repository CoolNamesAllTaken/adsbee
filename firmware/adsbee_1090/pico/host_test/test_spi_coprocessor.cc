#include "gtest/gtest.h"
#include "spi_coprocessor.hh"
#include "spi_coprocessor_packet.hh"

TEST(SPICoprocessor, SCWritePacket) {
    SPICoprocessorPacket::SCWritePacket packet;
    packet.cmd = ObjectDictionary::SCCommand::kCmdWriteToSlave;
    packet.addr = ObjectDictionary::Address::kAddrRawModeSPacket;
    RawModeSPacket tpacket = RawModeSPacket((char *)"8D7C1BE8581B66E9BD8CEEDC1C9F");
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
    RawModeSPacket *tpacket_copy = (RawModeSPacket *)packet_copy.data;
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
    RawModeSPacket tpacket = RawModeSPacket((char *)"8D7C1BE8581B66E9BD8CEEDC1C9F");
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
    RawModeSPacket *tpacket_copy = (RawModeSPacket *)packet_copy.data;
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

void BuildAckPacket(SPICoprocessorPacket::SCResponsePacket &packet, bool success) {
    packet.cmd = ObjectDictionary::SCCommand::kCmdAck;
    packet.data_len_bytes = 1;
    packet.data[0] = success ? 1 : 0;
    packet.PopulateCRC();

    // Break up CRC calculation for debugging (is usually inlined).
    // uint16_t buf_len_bytes = packet.GetBufLenBytes();
    // uint8_t *buf = packet.GetBuf();
    // uint16_t crc = CalculateCRC16(buf, buf_len_bytes - SPICoprocessorPacket::SCResponsePacket::kCRCLenBytes);
    // packet.SetCRC(crc);
}

TEST(SPICoprocessor, SCResponsePacketScrambleBuf) {
    // This test case addresses an issue that was discovered while removing the memset command that sets the data buffer
    // of the SCResponsePacket to all zeros. The issue was that if the data buffer was not set to 0's, the CRC would be
    // calculated as invalid.

    SCOPED_TRACE("SCResponsePacketScrambleBuf");

    SPICoprocessorPacket::SCResponsePacket packet;
    BuildAckPacket(packet, true);
    EXPECT_TRUE(packet.IsValid());

    SPICoprocessorPacket::SCResponsePacket response_packet;
    memset((uint8_t *)&response_packet.data, 0xFF, SPICoprocessorPacket::SCResponsePacket::kDataMaxLenBytes);
    BuildAckPacket(response_packet, true);
    EXPECT_TRUE(response_packet.IsValid());
}