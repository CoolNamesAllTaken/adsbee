#include "beast_utils.hh"
#include "gtest/gtest.h"
#include "transponder_packet.hh"

TEST(BeastUtils, TransponderPacketToBeastFrame) {
    // Create packet with a single 0x1a that must be escaped in data, a typical RSSI value, and an unmasked MLAT
    // counter. Note: MLAT counter is shifted left by 2 bits to simulate multiplying a 48MHz counter with a 12MHz
    // desired result.
    DecodedTransponderPacket tpacket =
        DecodedTransponderPacket((char *)"8d495066587f469bb826d21ad767", -80, 0xABABFF1AFFFFFF1A << 2);

    uint8_t beast_frame_buf[kBeastFrameMaxLenBytes];
    // 1 (frame) + 6 (mlat) + 2 (mlat escape) + 1 (rssi) + 14 (data) + 1 (data escape) = 25 Bytes.
    EXPECT_EQ(TransponderPacketToBeastFrame(tpacket, beast_frame_buf), 25);
    EXPECT_EQ(beast_frame_buf[0], 0x33);  // Packet type is Mode S long frame.
    EXPECT_EQ(beast_frame_buf[1], 0xFF);  // MLAT Counter Begin
    EXPECT_EQ(beast_frame_buf[2], 0x1A);
    EXPECT_EQ(beast_frame_buf[3], 0x1A);  // escape
    EXPECT_EQ(beast_frame_buf[4], 0xFF);
    EXPECT_EQ(beast_frame_buf[5], 0xFF);
    EXPECT_EQ(beast_frame_buf[6], 0xFF);
    EXPECT_EQ(beast_frame_buf[7], 0x1A);
    EXPECT_EQ(beast_frame_buf[8], 0x1A);      // escape
    EXPECT_EQ(beast_frame_buf[9], 255 - 80);  // RSSI is -80dBm.
    EXPECT_EQ(beast_frame_buf[10], 0x8D);     // Mode S Data Begin
    EXPECT_EQ(beast_frame_buf[11], 0x49);
    EXPECT_EQ(beast_frame_buf[12], 0x50);
    EXPECT_EQ(beast_frame_buf[13], 0x66);
    EXPECT_EQ(beast_frame_buf[14], 0x58);
    EXPECT_EQ(beast_frame_buf[15], 0x7f);
    EXPECT_EQ(beast_frame_buf[16], 0x46);
    EXPECT_EQ(beast_frame_buf[17], 0x9B);
    EXPECT_EQ(beast_frame_buf[18], 0xB8);
    EXPECT_EQ(beast_frame_buf[19], 0x26);
    EXPECT_EQ(beast_frame_buf[20], 0xD2);
    EXPECT_EQ(beast_frame_buf[21], 0x1A);
    EXPECT_EQ(beast_frame_buf[22], 0x1A);  // Escape
    EXPECT_EQ(beast_frame_buf[23], 0xD7);
    EXPECT_EQ(beast_frame_buf[24], 0x67);
}