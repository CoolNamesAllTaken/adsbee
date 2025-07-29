#include "buffer_utils.hh"
#include "gtest/gtest.h"
#include "uat_packet.hh"

// Initialize global Reed-Solomon decoder instances.
RS::ReedSolomon<RawUATADSBPacket::kShortADSBMessagePayloadNumBytes,
                RawUATADSBPacket::kShortADSBMessageFECParityNumBytes>
    uat_short_adsb_rs;
RS::ReedSolomon<RawUATADSBPacket::kLongADSBMessagePayloadNumBytes, RawUATADSBPacket::kLongADSBMessageFECParityNumBytes>
    uat_long_adsb_rs;

TEST(RawUATADSBPacket, StringConstructor) {
    const char *buf_str = "00a66ef135445d525a0c0519119021204800";
    RawUATADSBPacket packet = RawUATADSBPacket(buf_str);
    ASSERT_EQ(packet.encoded_message_len_bits, 144);
    ASSERT_EQ(packet.encoded_message[0], 0x00);
    ASSERT_EQ(packet.encoded_message[1], 0xa6);
    ASSERT_EQ(packet.encoded_message[2], 0x6e);
    ASSERT_EQ(packet.encoded_message[3], 0xf1);
    ASSERT_EQ(packet.encoded_message[4], 0x35);
    ASSERT_EQ(packet.encoded_message[5], 0x44);
    ASSERT_EQ(packet.encoded_message[6], 0x5d);
    ASSERT_EQ(packet.encoded_message[7], 0x52);
    ASSERT_EQ(packet.encoded_message[8], 0x5a);
    ASSERT_EQ(packet.encoded_message[9], 0x0c);
    ASSERT_EQ(packet.encoded_message[10], 0x05);
    ASSERT_EQ(packet.encoded_message[11], 0x19);
    ASSERT_EQ(packet.encoded_message[12], 0x11);
    ASSERT_EQ(packet.encoded_message[13], 0x90);
    ASSERT_EQ(packet.encoded_message[14], 0x21);
    ASSERT_EQ(packet.encoded_message[15], 0x20);
    ASSERT_EQ(packet.encoded_message[16], 0x48);
    ASSERT_EQ(packet.encoded_message[17], 0x00);
}

TEST(DecodedUATADSBPacket, IsValid) {
    const char *buf_str = "00a974f13536e352301a0899123219814f00";
    DecodedUATADSBPacket packet = DecodedUATADSBPacket(buf_str);
    ASSERT_TRUE(packet.IsValid());

    const char *invalid_buf_str = "00a974f13536e352301a0899123219814f01";  // Invalid CRC.
    DecodedUATADSBPacket invalid_packet = DecodedUATADSBPacket(invalid_buf_str);
    ASSERT_FALSE(invalid_packet.IsValid());
}

TEST(DecodedUATADSBPacket, AltitudeEncodedToAltitudeFt) {
    ASSERT_EQ(DecodedUATADSBPacket::AltitudeEncodedToAltitudeFt(0), INT32_MIN);  // Invalid altitude.
    ASSERT_EQ(DecodedUATADSBPacket::AltitudeEncodedToAltitudeFt(1), -1000);
    ASSERT_EQ(DecodedUATADSBPacket::AltitudeEncodedToAltitudeFt(2), -975);
    ASSERT_EQ(DecodedUATADSBPacket::AltitudeEncodedToAltitudeFt(40), -25);
    ASSERT_EQ(DecodedUATADSBPacket::AltitudeEncodedToAltitudeFt(41), 0);
    ASSERT_EQ(DecodedUATADSBPacket::AltitudeEncodedToAltitudeFt(42), 25);
    ASSERT_EQ(DecodedUATADSBPacket::AltitudeEncodedToAltitudeFt(4094), 101325);
    ASSERT_EQ(DecodedUATADSBPacket::AltitudeEncodedToAltitudeFt(4095), INT32_MAX);
}