#include "gtest/gtest.h"
#include "ads_b_packet.hh"

TEST(ADSBPacket, GetNBitWordFromBuffer) {
    uint32_t packet_buffer[ADSBPacket::kMaxPacketLenWords32];
    packet_buffer[0] = 0x8D76CE88;
    packet_buffer[1] = 0x204C9072;
    packet_buffer[2] = 0xCB48209A;
    packet_buffer[3] = 0x0000504D;

    ADSBPacket packet = ADSBPacket(packet_buffer, 4);

    EXPECT_EQ(packet.GetNBitWordFromBuffer(1, 0, packet_buffer), 0b1);
    EXPECT_EQ(packet.GetNBitWordFromBuffer(1, 1, packet_buffer), 0b0);

    EXPECT_EQ(packet.GetNBitWordFromBuffer(8, 0, packet_buffer), 0x8D);
    EXPECT_EQ(packet.GetNBitWordFromBuffer(16, 0, packet_buffer), 0x8D76);
    EXPECT_EQ(packet.GetNBitWordFromBuffer(24, 0, packet_buffer), 0x8D76CE);
    EXPECT_EQ(packet.GetNBitWordFromBuffer(32, 0, packet_buffer), 0x8D76CE88);

    // first bit index = 4
    EXPECT_EQ(packet.GetNBitWordFromBuffer(32, 4, packet_buffer), 0xD76CE882);
    EXPECT_EQ(packet.GetNBitWordFromBuffer(24, 4, packet_buffer), 0xD76CE8);
    EXPECT_EQ(packet.GetNBitWordFromBuffer(16, 4, packet_buffer), 0xD76C);
    EXPECT_EQ(packet.GetNBitWordFromBuffer(8, 4, packet_buffer), 0xD7);

    // first bit index = 8
    EXPECT_EQ(packet.GetNBitWordFromBuffer(32, 8, packet_buffer), 0x76CE8820);
    EXPECT_EQ(packet.GetNBitWordFromBuffer(24, 8, packet_buffer), 0x76CE88);
    EXPECT_EQ(packet.GetNBitWordFromBuffer(16, 8, packet_buffer), 0x76CE);
    EXPECT_EQ(packet.GetNBitWordFromBuffer(8, 8, packet_buffer), 0x76);

    // first bit index = 12
    EXPECT_EQ(packet.GetNBitWordFromBuffer(32, 12, packet_buffer), 0x6CE88204);

    // first bit index = 16
    EXPECT_EQ(packet.GetNBitWordFromBuffer(32, 16, packet_buffer), 0xCE88204C);

    // make sure it doesn't fall off the end; can use some printfs to double check this
    EXPECT_EQ(packet.GetNBitWordFromBuffer(16, 32*3+16, packet_buffer), 0x504D);
}

// Example packets taken from http://jasonplayne.com:8080/. Thanks, Jason!

TEST(ADSBPacket, PacketBuffer) {
    uint32_t packet_buffer[ADSBPacket::kMaxPacketLenWords32];

    // Nominal packet.
    packet_buffer[0] = 0x8D76CE88;
    packet_buffer[1] = 0x204C9072;
    packet_buffer[2] = 0xCB48209A;
    packet_buffer[3] = 0x0000504D;

    ADSBPacket packet = ADSBPacket(packet_buffer, 4);

    // Check that packet was ingested and conditioned properly.
    uint32_t check_buffer[ADSBPacket::kMaxPacketLenWords32];
    EXPECT_EQ(112/8, packet.DumpPacketBuffer(check_buffer));
    EXPECT_EQ(check_buffer[0], 0x8D76CE88);
    EXPECT_EQ(check_buffer[1], 0x204C9072);
    EXPECT_EQ(check_buffer[2], 0xCB48209A);
    EXPECT_EQ(check_buffer[3], 0x504D0000);

    EXPECT_EQ(packet.Get24BitWordFromPacketBuffer(0*24), 0x8D76CE);
    EXPECT_EQ(packet.Get24BitWordFromPacketBuffer(1*24), 0x88204C);
    EXPECT_EQ(packet.Get24BitWordFromPacketBuffer(2*24), 0x9072CB);
    EXPECT_EQ(packet.Get24BitWordFromPacketBuffer(3*24), 0x48209A);
    EXPECT_EQ(packet.Get24BitWordFromPacketBuffer(4*24), 0x504D00);

    // Nominal packet with extra bit ingested.
    packet_buffer[0] = 0x8D76CE88;
    packet_buffer[1] = 0x204C9072;
    packet_buffer[2] = 0xCB48209A;
    packet_buffer[3] = (0x0000504D << 1) | 0b1;
    // TODO: make this test!
}

TEST(ADSBPacket, CRC24Checksum) {
    uint32_t packet_buffer[ADSBPacket::kMaxPacketLenWords32];

    // Test packet from https://mode-s.org/decode/book-the_1090mhz_riddle-junzi_sun.pdf pg. 91.
    // 0x8D406B902015A678D4D220[000000] (stripped off parity and replaced with 0's for testing)
    packet_buffer[0] = 0x8D406B90;
    packet_buffer[1] = 0x2015A678;
    packet_buffer[2] = 0xD4D22000;
    packet_buffer[3] = 0x00000000;

    ADSBPacket packet = ADSBPacket(packet_buffer, 4);

    EXPECT_EQ(packet.CalculateCRC24(), 0xAA4BDA);

    // EXPECT_TRUE(packet.IsValid());
    // EXPECT_EQ(packet.GetDownlinkFormat(), 17);
    // EXPECT_EQ(packet.GetCapability(), 5);
    // EXPECT_EQ(packet.GetICAOAddress(), 0x76CE88);
    // EXPECT_EQ(packet.GetTypeCode(), 4);

    



    // Check CRC performance with error injection.
}