#include "adsb_packet.hh"
#include "beast_utils.hh"
#include "gtest/gtest.h"

TEST(BeastUtils, TransponderPacketToBeastFrame) {
    // Create packet with a single 0x1a that must be escaped.
    TransponderPacket tpacket = TransponderPacket((char *)"8d495066587f469bb826d21ad767", -80);

    uint8_t beast_frame_buf[kBeastFrameMaxLenBytes];
    ASSERT_EQ(TransponderPacketToBeastFrame(tpacket, beast_frame_buf), 17);  // 14 bytes + 1x escape byte
    EXPECT_EQ(beast_frame_buf[0], 0x33);                                     // Packet type is Mode S long frame.
    EXPECT_EQ(beast_frame_buf[1], 255 - 80);                                 // RSSI is -80dBm.
    EXPECT_EQ(beast_frame_buf[2], 0x8D);
    EXPECT_EQ(beast_frame_buf[3], 0x49);
    EXPECT_EQ(beast_frame_buf[4], 0x50);
    EXPECT_EQ(beast_frame_buf[5], 0x66);
    EXPECT_EQ(beast_frame_buf[6], 0x58);
    EXPECT_EQ(beast_frame_buf[7], 0x7f);
    EXPECT_EQ(beast_frame_buf[8], 0x46);
    EXPECT_EQ(beast_frame_buf[9], 0x9B);
    EXPECT_EQ(beast_frame_buf[10], 0xB8);
    EXPECT_EQ(beast_frame_buf[11], 0x26);
    EXPECT_EQ(beast_frame_buf[12], 0xD2);
    EXPECT_EQ(beast_frame_buf[13], 0x1A);
    EXPECT_EQ(beast_frame_buf[14], 0x1A);  // Escape
    EXPECT_EQ(beast_frame_buf[15], 0xD7);
    EXPECT_EQ(beast_frame_buf[16], 0x67);
}