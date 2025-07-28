#include "gtest/gtest.h"
#include "uat_packet.hh"

TEST(RawUATPacket, StringConstructor) {
    const char *buf_str = "00a66ef135445d525a0c0519119021204800";
    RawUATPacket packet = RawUATPacket(buf_str);
    ASSERT_EQ(packet.buffer_len_bits, 144);
    ASSERT_EQ(packet.buffer[0], 0x00);
    ASSERT_EQ(packet.buffer[1], 0xa6);
    ASSERT_EQ(packet.buffer[2], 0x6e);
    ASSERT_EQ(packet.buffer[3], 0xf1);
    ASSERT_EQ(packet.buffer[4], 0x35);
    ASSERT_EQ(packet.buffer[5], 0x44);
    ASSERT_EQ(packet.buffer[6], 0x5d);
    ASSERT_EQ(packet.buffer[7], 0x52);
    ASSERT_EQ(packet.buffer[8], 0x5a);
    ASSERT_EQ(packet.buffer[9], 0x0c);
    ASSERT_EQ(packet.buffer[10], 0x05);
    ASSERT_EQ(packet.buffer[11], 0x19);
    ASSERT_EQ(packet.buffer[12], 0x11);
    ASSERT_EQ(packet.buffer[13], 0x90);
    ASSERT_EQ(packet.buffer[14], 0x21);
    ASSERT_EQ(packet.buffer[15], 0x20);
    ASSERT_EQ(packet.buffer[16], 0x48);
    ASSERT_EQ(packet.buffer[17], 0x00);
}

TEST(DecodedUATPacket, IsValid) {
    const char *buf_str = "00a974f13536e352301a0899123219814f00";
    DecodedUATPacket packet = DecodedUATPacket(buf_str);
    ASSERT_TRUE(packet.IsValid());

    const char *invalid_buf_str = "00a974f13536e352301a0899123219814f01";  // Invalid CRC.
    DecodedUATPacket invalid_packet = DecodedUATPacket(invalid_buf_str);
    ASSERT_FALSE(invalid_packet.IsValid());
}

TEST(DecodedUATPacket, AltitudeEncodedToAltitudeFt) {
    ASSERT_EQ(DecodedUATPacket::AltitudeEncodedToAltitudeFt(0), INT32_MIN);  // Invalid altitude.
    ASSERT_EQ(DecodedUATPacket::AltitudeEncodedToAltitudeFt(1), -1000);
    ASSERT_EQ(DecodedUATPacket::AltitudeEncodedToAltitudeFt(2), -975);
    ASSERT_EQ(DecodedUATPacket::AltitudeEncodedToAltitudeFt(40), -25);
    ASSERT_EQ(DecodedUATPacket::AltitudeEncodedToAltitudeFt(41), 0);
    ASSERT_EQ(DecodedUATPacket::AltitudeEncodedToAltitudeFt(42), 25);
    ASSERT_EQ(DecodedUATPacket::AltitudeEncodedToAltitudeFt(4094), 101325);
    ASSERT_EQ(DecodedUATPacket::AltitudeEncodedToAltitudeFt(4095), INT32_MAX);
}