#include "beast_utils.hh"
#include "gtest/gtest.h"
#include "transponder_packet.hh"

TEST(BeastUtils, Build1090BeastFrame) {
    // Create packet with a single 0x1a that must be escaped in data, a typical RSSI value, and an unmasked MLAT
    // counter. Note: MLAT counter is shifted left by 2 bits to simulate multiplying a 48MHz counter with a 12MHz
    // desired result.
    Decoded1090Packet tpacket = Decoded1090Packet((char *)"8d495066587f469bb826d21ad767",  // string
                                                  0,                                       // source
                                                  -80,                                     // sigs
                                                  50,                                      // sigq
                                                  0xABABFF1AFFFFFF1A << 2                  // mlat
    );

    uint8_t beast_frame_buf[kBeastFrameMaxLenBytes];
    // 1 (frame) + 6 (mlat) + 2 (mlat escape) + 1 (rssi) + 14 (data) + 1 (data escape) = 25 Bytes.
    EXPECT_EQ(Build1090BeastFrame(tpacket, beast_frame_buf), 26);
    EXPECT_EQ(beast_frame_buf[0], kBeastEscapeChar);  // Packet begins with escape char.
    EXPECT_EQ(beast_frame_buf[1], 0x33);              // Packet type is Mode S long frame.
    EXPECT_EQ(beast_frame_buf[2], 0xFF);              // MLAT Counter Begin
    EXPECT_EQ(beast_frame_buf[3], 0x1A);
    EXPECT_EQ(beast_frame_buf[4], 0x1A);  // escape
    EXPECT_EQ(beast_frame_buf[5], 0xFF);
    EXPECT_EQ(beast_frame_buf[6], 0xFF);
    EXPECT_EQ(beast_frame_buf[7], 0xFF);
    EXPECT_EQ(beast_frame_buf[8], 0x1A);
    EXPECT_EQ(beast_frame_buf[9], 0x1A);   // escape
    EXPECT_EQ(beast_frame_buf[10], 14);    // RSSI is -80dBm.
    EXPECT_EQ(beast_frame_buf[11], 0x8D);  // Mode S Data Begin
    EXPECT_EQ(beast_frame_buf[12], 0x49);
    EXPECT_EQ(beast_frame_buf[13], 0x50);
    EXPECT_EQ(beast_frame_buf[14], 0x66);
    EXPECT_EQ(beast_frame_buf[15], 0x58);
    EXPECT_EQ(beast_frame_buf[16], 0x7f);
    EXPECT_EQ(beast_frame_buf[17], 0x46);
    EXPECT_EQ(beast_frame_buf[18], 0x9B);
    EXPECT_EQ(beast_frame_buf[19], 0xB8);
    EXPECT_EQ(beast_frame_buf[20], 0x26);
    EXPECT_EQ(beast_frame_buf[21], 0xD2);
    EXPECT_EQ(beast_frame_buf[22], 0x1A);
    EXPECT_EQ(beast_frame_buf[23], 0x1A);  // escape
    EXPECT_EQ(beast_frame_buf[24], 0xD7);
    EXPECT_EQ(beast_frame_buf[25], 0x67);
}

TEST(BeastUtils, Build1090IngestBeastFrame) {
    // Create packet with a single 0x1a that must be escaped in data, a typical RSSI value, and an unmasked MLAT
    // counter. Note: MLAT counter is shifted left by 2 bits to simulate multiplying a 48MHz counter with a 12MHz
    // desired result.
    Decoded1090Packet tpacket = Decoded1090Packet((char *)"8d495066587f469bb826d21ad767",  // string
                                                  0,                                       // source
                                                  0,                                       // sigs
                                                  50,                                      // sigq
                                                  0xABABFF1AFFFFFF1A << 2);

    uint8_t beast_frame_buf[kBeastFrameMaxLenBytes];
    // 1 (frame) + 6 (mlat) + 2 (mlat escape) + 1 (rssi) + 14 (data) + 1 (data escape) = 25 Bytes.
    uint8_t uid[kReceiverIDLenBytes] = {0xde, 0xad, 0xbe, 0x1a, 0xef, 0x1a, 0xaa, 0xbb};
    uint uid_num_chars_to_escape = 2;
    uint uid_escaped_length = kReceiverIDLenBytes + uid_num_chars_to_escape;

    EXPECT_EQ(Build1090IngestBeastFrame(tpacket, beast_frame_buf, uid), uid_escaped_length + 2 + 26);
    uint bytes_compared = 0;
    EXPECT_EQ(beast_frame_buf[bytes_compared++], kBeastEscapeChar);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], BeastFrameType::kBeastFrameTypeIngestId);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xde);  // uid[0]
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xad);  // uid[1]
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xbe);  // uid[2]
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x1a);  // uid[3] escape
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x1a);  // uid[3]
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xef);  // uid[4]
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x1a);  // uid[5] escape
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x1a);  // uid[5]
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xaa);  // uid[6]
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xbb);  // uid[7]
    EXPECT_EQ(beast_frame_buf[bytes_compared++], kBeastEscapeChar);
    EXPECT_EQ(beast_frame_buf[bytes_compared++],
              BeastFrameType::kBeastFrameTypeModeSLong);  // Packet type is Mode S long frame.
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xFF);   // MLAT Counter Begin
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x1A);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x1A);  // escape
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xFF);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xFF);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xFF);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x1A);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x1A);  // escape
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 255);   // RSSI is 0dBm.
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x8D);  // Mode S Data Begin
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x49);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x50);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x66);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x58);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x7f);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x46);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x9B);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xB8);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x26);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xD2);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x1A);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x1A);  // Escape
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xD7);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0x67);
}

TEST(BeastUtils, BuildFeedStartFrame) {
    uint8_t beast_frame_buf[kBeastFrameMaxLenBytes];

    uint8_t uid[kReceiverIDLenBytes] = {0xde, 0xad, 0xbe, 0x1a, 0xef, 0x1a, 0xaa, 0xbb};
    EXPECT_EQ(BuildFeedStartFrame(beast_frame_buf, uid), 38);
    uint16_t bytes_compared = 0;

    EXPECT_EQ(beast_frame_buf[bytes_compared++], kBeastEscapeChar);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], BeastFrameType::kBeastFrameTypeFeedId);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'd');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'e');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'a');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'd');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'b');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'e');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], '1');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'a');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], '-');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'e');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'f');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], '1');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'a');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], '-');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'a');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'a');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'b');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'b');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], '-');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'd');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'e');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'a');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'd');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], '-');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'b');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'e');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], '1');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'a');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'e');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'f');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], '1');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'a');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'a');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'a');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'b');
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 'b');
}
