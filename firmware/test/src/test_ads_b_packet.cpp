#include "gtest/gtest.h"
#include "ads_b_packet.hh"

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
    ASSERT_EQ(112/8, packet.DumpPacketBuffer(check_buffer));
    ASSERT_EQ(check_buffer[0], 0x8D76CE88);
    ASSERT_EQ(check_buffer[1], 0x204C9072);
    ASSERT_EQ(check_buffer[2], 0xCB48209A);
    ASSERT_EQ(check_buffer[3], 0x504D0000);

    ASSERT_TRUE(packet.IsValid());
    ASSERT_EQ(packet.GetDownlinkFormat(), 17);
    ASSERT_EQ(packet.GetCapability(), 5);
    ASSERT_EQ(packet.GetICAOAddress(), 0x76CE88);
    ASSERT_EQ(packet.GetTypeCode(), 4);

    ASSERT_EQ(packet.Get24BitWordFromPacketBuffer(0*24), 0x8D76CE);
    ASSERT_EQ(packet.Get24BitWordFromPacketBuffer(1*24), 0x88204C);
    ASSERT_EQ(packet.Get24BitWordFromPacketBuffer(2*24), 0x9072CB);
    ASSERT_EQ(packet.Get24BitWordFromPacketBuffer(3*24), 0x48209A);

    ASSERT_EQ(packet.CalculateCRC24(), 0x9A504D);

    // Nominal packet with extra bit ingested.
    packet_buffer[0] = 0x8D76CE88;
    packet_buffer[1] = 0x204C9072;
    packet_buffer[2] = 0xCB48209A;
    packet_buffer[3] = (0x0000504D << 1) | 0b1;

    // Check CRC performance with error injection.
}