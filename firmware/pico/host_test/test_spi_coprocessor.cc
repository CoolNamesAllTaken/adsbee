#include "gtest/gtest.h"
#include "spi_coprocessor.hh"

TEST(SPICoprocessor, SCWritePacket) {
    SPICoprocessor::SCWritePacket packet;
    packet.cmd = SPICoprocessor::SCCommand::kCmdWriteToSlave;
    packet.addr = ObjectDictionary::Address::kAddrRawTransponderPacket;
    RawTransponderPacket tpacket = RawTransponderPacket((char *)"8D7C1BE8581B66E9BD8CEEDC1C9F");
    packet.len = sizeof(RawTransponderPacket);
    memcpy(packet.data, &tpacket, packet.len);
    // Calculate CRC and add it to the data buffer.
    uint16_t crc =
        CalculateCRC16(packet.GetBuf(), packet.GetBufLenBytes() - SPICoprocessor::SCWritePacket::kCRCLenBytes);
    memcpy(packet.data + packet.len, &crc, sizeof(uint16_t));
    EXPECT_TRUE(packet.IsValid());

    packet.PopulateCRC();
    EXPECT_TRUE(packet.IsValid());

    EXPECT_EQ(packet.GetBufLenBytes(), sizeof(RawTransponderPacket) + sizeof(SPICoprocessor::SCCommand) +
                                           sizeof(ObjectDictionary::Address) + 2 * sizeof(uint16_t) +
                                           SPICoprocessor::SCWritePacket::kCRCLenBytes);

    SPICoprocessor::SCWritePacket packet_copy = SPICoprocessor::SCWritePacket(packet.GetBuf(), packet.GetBufLenBytes());
    EXPECT_EQ(packet.cmd, packet_copy.cmd);
    EXPECT_EQ(packet.addr, packet_copy.addr);
    EXPECT_EQ(packet.IsValid(), packet_copy.IsValid());
    RawTransponderPacket *tpacket_copy = (RawTransponderPacket *)packet_copy.data;
    EXPECT_EQ(tpacket.buffer_len_bits, tpacket_copy->buffer_len_bits);
    EXPECT_EQ(tpacket.buffer[0], tpacket_copy->buffer[0]);
    EXPECT_EQ(tpacket.buffer[1], tpacket_copy->buffer[1]);
    EXPECT_EQ(tpacket.buffer[2], tpacket_copy->buffer[2]);
    EXPECT_EQ(tpacket.buffer[3], tpacket_copy->buffer[3]);

    // Poke packet and make checksum fail.
    packet.data[0] = ~packet.data[0];
    EXPECT_FALSE(packet.IsValid());
}

TEST(SPICoprocessor, SCReadRequestPacket) {
    // Test packet creation.
    SPICoprocessor::SCReadRequestPacket packet;
    packet.cmd = SPICoprocessor::SCCommand::kCmdReadFromMaster;
    packet.addr = ObjectDictionary::Address::kAddrSettingsData;
    packet.offset = 0xFEBC;
    packet.len = 40;
    // Make sure that CRC generation works as expected.
    packet.PopulateCRC();
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(
        CalculateCRC16(packet.GetBuf(), packet.GetBufLenBytes() - SPICoprocessor::SCReadRequestPacket::kCRCLenBytes),
        packet.crc);

    // Test packet ingestion.
    SPICoprocessor::SCReadRequestPacket packet_copy =
        SPICoprocessor::SCReadRequestPacket(packet.GetBuf(), packet.GetBufLenBytes());
    EXPECT_EQ(packet_copy.cmd, packet.cmd);
    EXPECT_EQ(packet_copy.addr, packet.addr);
    EXPECT_EQ(packet_copy.offset, packet.offset);
    EXPECT_EQ(packet_copy.len, packet.len);
    EXPECT_TRUE(packet_copy.IsValid());
    // Changes to packet should not affect packet_copy.
    packet.GetBuf()[0] = ~packet.GetBuf()[0];
    EXPECT_FALSE(packet.IsValid());
    EXPECT_TRUE(packet_copy.IsValid());
}

TEST(SPICoprocessor, SCResponsePacket) {
    // Test packet creation.
    SPICoprocessor::SCResponsePacket packet;
    packet.cmd = SPICoprocessor::SCCommand::kCmdDataBlock;
    EXPECT_EQ(packet.GetBuf()[0], SPICoprocessor::SCCommand::kCmdDataBlock);
    RawTransponderPacket tpacket = RawTransponderPacket((char *)"8D7C1BE8581B66E9BD8CEEDC1C9F");
    packet.data_len_bytes = sizeof(RawTransponderPacket);
    memcpy(packet.data, &tpacket, packet.data_len_bytes);
    EXPECT_FALSE(packet.IsValid());
    packet.PopulateCRC();
    EXPECT_TRUE(packet.IsValid());

    // Test packet ingestion.
    SPICoprocessor::SCResponsePacket packet_copy =
        SPICoprocessor::SCResponsePacket(packet.GetBuf(), packet.GetBufLenBytes());
    EXPECT_TRUE(packet_copy.IsValid());
    EXPECT_EQ(packet_copy.cmd, packet.cmd);
    RawTransponderPacket *tpacket_copy = (RawTransponderPacket *)packet_copy.data;
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