#include <cstring>
#include <string>

#include "beast_utils.hh"
#include "gtest/gtest.h"
#include "mode_s_packet.hh"

TEST(BeastUtils, BuildModeSBeastFrame) {
    // Create packet with a single 0x1a that must be escaped in data, a typical RSSI value, and an unmasked MLAT
    // counter. Note: MLAT counter is shifted left by 2 bits to simulate multiplying a 48MHz counter with a 12MHz
    // desired result.
    DecodedModeSPacket tpacket = DecodedModeSPacket((const char*)"8d495066587f469bb826d21ad767",  // string
                                                    0,                                            // source
                                                    -80,                                          // sigs
                                                    50,                                           // sigq
                                                    0xABABFF1AFFFFFF1A << 2                       // mlat
    );

    uint8_t beast_frame_buf[BeastReporter::kModeSBeastFrameMaxLenBytes];
    // 1 (frame) + 6 (mlat) + 2 (mlat escape) + 1 (rssi) + 14 (data) + 1 (data escape) = 25 Bytes.
    EXPECT_EQ(BeastReporter::BuildModeSBeastFrame(beast_frame_buf, tpacket), 26);
    EXPECT_EQ(beast_frame_buf[0], BeastReporter::kBeastEscapeChar);  // Packet begins with escape char.
    EXPECT_EQ(beast_frame_buf[1], 0x33);                             // Packet type is Mode S long frame.
    EXPECT_EQ(beast_frame_buf[2], 0xFF);                             // MLAT Counter Begin
    EXPECT_EQ(beast_frame_buf[3], 0x1A);
    EXPECT_EQ(beast_frame_buf[4], 0x1A);  // escape
    EXPECT_EQ(beast_frame_buf[5], 0xFF);
    EXPECT_EQ(beast_frame_buf[6], 0xFF);
    EXPECT_EQ(beast_frame_buf[7], 0xFF);
    EXPECT_EQ(beast_frame_buf[8], 0x1A);
    EXPECT_EQ(beast_frame_buf[9], 0x1A);   // escape
    EXPECT_EQ(beast_frame_buf[10], 8);     // RSSI is -80dBm.
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

TEST(BeastUtils, BuildModeSIngestBeastFrame) {
    // Create packet with a single 0x1a that must be escaped in data, a typical RSSI value, and an unmasked MLAT
    // counter. Note: MLAT counter is shifted left by 2 bits to simulate multiplying a 48MHz counter with a 12MHz
    // desired result.
    DecodedModeSPacket tpacket = DecodedModeSPacket((const char*)"8d495066587f469bb826d21ad767",  // string
                                                    0,                                            // source
                                                    0,                                            // sigs
                                                    50,                                           // sigq
                                                    0xABABFF1AFFFFFF1A << 2);

    uint8_t beast_frame_buf[BeastReporter::kModeSBeastFrameMaxLenBytes];
    // 1 (frame) + 6 (mlat) + 2 (mlat escape) + 1 (rssi) + 14 (data) + 1 (data escape) = 25 Bytes.
    uint8_t uid[BeastReporter::kReceiverIDLenBytes] = {0xde, 0xad, 0xbe, 0x1a, 0xef, 0x1a, 0xaa, 0xbb};
    uint uid_num_chars_to_escape = 2;
    uint uid_escaped_length = BeastReporter::kReceiverIDLenBytes + uid_num_chars_to_escape;

    EXPECT_EQ(BeastReporter::BuildModeSIngestBeastFrame(beast_frame_buf, tpacket, uid), uid_escaped_length + 2 + 26);
    uint bytes_compared = 0;
    EXPECT_EQ(beast_frame_buf[bytes_compared++], BeastReporter::kBeastEscapeChar);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], BeastReporter::kBeastFrameTypeIngestId);
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
    EXPECT_EQ(beast_frame_buf[bytes_compared++], BeastReporter::kBeastEscapeChar);
    EXPECT_EQ(beast_frame_buf[bytes_compared++],
              BeastReporter::kBeastFrameTypeModeSLong);  // Packet type is Mode S long frame.
    EXPECT_EQ(beast_frame_buf[bytes_compared++], 0xFF);  // MLAT Counter Begin
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
    uint8_t beast_frame_buf[BeastReporter::kModeSBeastFrameMaxLenBytes];

    uint8_t uid[BeastReporter::kReceiverIDLenBytes] = {0xde, 0xad, 0xbe, 0x1a, 0xef, 0x1a, 0xaa, 0xbb};
    EXPECT_EQ(BeastReporter::BuildFeedStartFrame(beast_frame_buf, uid), 38);
    uint16_t bytes_compared = 0;

    EXPECT_EQ(beast_frame_buf[bytes_compared++], BeastReporter::kBeastEscapeChar);
    EXPECT_EQ(beast_frame_buf[bytes_compared++], BeastReporter::kBeastFrameTypeFeedId);
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

struct UATADSBPacketBeastTest {
    RawUATADSBPacket packet;
    char beast_frame_buf[2 * BeastReporter::kUATADSBBeastFrameMaxLenBytes];
};

UATADSBPacketBeastTest uat_adsb_tests[] = {
    {.packet = RawUATADSBPacket("00a66ef135445d525a0c05191190212048006cb82bc4d53a5b2bb0a8ec6e", -60, 0, 0x123456 << 2),
     .beast_frame_buf =
         "1aec730000001234562d"  // Prefix: escape | frame type | uat message type | mlat timestamp | rssi
         "00a66ef135445d525a0c05191190212048006cb82bc4d53a5b2bb0a8ec6e"}};

TEST(BeastUtils, BuildUATADSBFrame) {
    for (const auto& test : uat_adsb_tests) {
        uint8_t beast_frame_buf[BeastReporter::kUATADSBBeastFrameMaxLenBytes];
        uint16_t bytes_written = BeastReporter::BuildUATADSBBeastFrame(beast_frame_buf, test.packet);
        EXPECT_EQ(bytes_written, strlen(test.beast_frame_buf) / 2);
        // Convert beast_frame_buf binary buffer to string buffer.
        char beast_frame_buf_str[2 * BeastReporter::kUATADSBBeastFrameMaxLenBytes + 1];
        ByteBufferToHexString(beast_frame_buf_str, beast_frame_buf, bytes_written);
        EXPECT_STREQ(beast_frame_buf_str, test.beast_frame_buf);
    }
}

struct UATUplinkPacketBeastTest {
    RawUATUplinkPacket packet;
    char beast_frame_buf[2 * BeastReporter::kUATUplinkBeastFrameMaxLenBytes];
};

UATUplinkPacketBeastTest uat_uplink_tests[] = {
    {.packet = RawUATUplinkPacket(
         "352d30000000147058000000c9c70d000000523c3c000000d61f170000005cc7f1000000b60cd7000000b01f0c0000002ec7720000000"
         "08cd3000000001f1e0000003505330000000ef6c10000001d5ffc000000687c7500000022f5c300000010d91c0000000020b400000000"
         "51cb00000000600c000000ff4cf000000000f57f00000051541c00000091227000000054037f0000007c4f1e0000004d053000000050f"
         "77c00000060de17000000cb00d90000004c337d0000007400f5000000d30015000000583549000000330e43000000d724050000005df0"
         "80000000b922d3000000c710c100000077007c000000f300d3000000c700c10000002dff810000003400540000007d5be00000000747c"
         "3000000cdc02c0000007c7c78000000f54dd5000000d950f500000020601500000051cb49000000604c430000004c7805000000f5cf80"
         "0000005408d30000002233c100000003d7b20000004f5e0000000005725a000000fccf78000000756700000000c3f6000000001cc3000"
         "00000b47c00000000c71f000000004d5d0000000035f3000000007f5f000000001d5100000000705400000000c7940000000028c30700"
         "00006495b5000000b5a39a000000d06df300000066d54d00000015e4e2000000fd19ca0000001534a70000007153d3000000ac0ea0000"
         "000c86953000000472843000000779764000000706f3b000000b006f30000009b356d0000000b0ee7000000ffc3ce00000049013f0000"
         "00964ddb000000",
         -60, 0, 0x00431a123456 << 2),
     .beast_frame_buf =
         "1aec7500431a1a1234562d"  // Prefix: escape | frame type | uat message type | mlat timestamp | rssi
         "352d30000000147058000000c9c70d000000523c3c000000d61f170000005cc7f1000000b60cd7000000b01f0c0000002ec7720000000"
         "08cd3000000001f1e0000003505330000000ef6c10000001d5ffc000000687c7500000022f5c300000010d91c0000000020b400000000"
         "51cb00000000600c000000ff4cf000000000f57f00000051541c00000091227000000054037f0000007c4f1e0000004d053000000050f"
         "77c00000060de17000000cb00d90000004c337d0000007400f5000000d30015000000583549000000330e43000000d724050000005df0"
         "80000000b922d3000000c710c100000077007c000000f300d3000000c700c10000002dff810000003400540000007d5be00000000747c"
         "3000000cdc02c0000007c7c78000000f54dd5000000d950f500000020601500000051cb49000000604c430000004c7805000000f5cf80"
         "0000005408d30000002233c100000003d7b20000004f5e0000000005725a000000fccf78000000756700000000c3f6000000001cc3000"
         "00000b47c00000000c71f000000004d5d0000000035f3000000007f5f000000001d5100000000705400000000c7940000000028c30700"
         "00006495b5000000b5a39a000000d06df300000066d54d00000015e4e2000000fd19ca0000001534a70000007153d3000000ac0ea0000"
         "000c86953000000472843000000779764000000706f3b000000b006f30000009b356d0000000b0ee7000000ffc3ce00000049013f0000"
         "00964ddb000000"}};

TEST(BeastUtils, BuildUATUplinkFrame) {
    for (const auto& test : uat_uplink_tests) {
        uint8_t beast_frame_buf[BeastReporter::kUATUplinkBeastFrameMaxLenBytes];
        uint16_t bytes_written = BeastReporter::BuildUATUplinkBeastFrame(beast_frame_buf, test.packet);
        EXPECT_EQ(bytes_written, strlen(test.beast_frame_buf) / 2);
        // Convert beast_frame_buf binary buffer to string buffer.
        char beast_frame_buf_str[2 * BeastReporter::kUATUplinkBeastFrameMaxLenBytes + 1];
        ByteBufferToHexString(beast_frame_buf_str, beast_frame_buf, bytes_written);
        EXPECT_STREQ(beast_frame_buf_str, test.beast_frame_buf);
    }
}
TEST(BeastUtils, BuildModeSBeastFrameWith48MHzTimestamp) {
    // Same packet as BuildModeSBeastFrame: the 48MHz field is the full count mod 2^48, 4x the 12MHz one.
    uint64_t mlat_48mhz = 0x00ABFF1AFFFFFF1AULL;
    DecodedModeSPacket tpacket = DecodedModeSPacket((const char*)"8d495066587f469bb826d21ad767", 0, -80, 50, mlat_48mhz);
    uint8_t frame_12mhz[BeastReporter::kModeSBeastFrameMaxLenBytes];
    uint8_t frame_48mhz[BeastReporter::kModeSBeastFrameMaxLenBytes];
    uint16_t len_12mhz = BeastReporter::BuildModeSBeastFrame(frame_12mhz, tpacket);
    uint16_t len_48mhz = BeastReporter::BuildModeSBeastFrame(frame_48mhz, tpacket, true);

    // Unescape the 6 timestamp bytes that follow the frame type.
    auto timestamp = [](const uint8_t* frame) {
        uint64_t value = 0;
        uint16_t i = 2;
        for (uint16_t n = 0; n < 6; n++, i++) {
            value = (value << 8) | frame[i];
            if (frame[i] == BeastReporter::kBeastEscapeChar) i++;
        }
        return value;
    };
    EXPECT_EQ(timestamp(frame_48mhz), 0xFF1AFFFFFF1AULL);
    EXPECT_EQ(timestamp(frame_12mhz), (mlat_48mhz >> 2) & 0xFFFFFFFFFFFFULL);
    EXPECT_EQ(frame_48mhz[0], BeastReporter::kBeastEscapeChar);
    EXPECT_EQ(frame_48mhz[1], BeastReporter::kBeastFrameTypeModeSLong);
    // Two escaped 0x1a in the 48MHz timestamp, none in the 12MHz one.
    EXPECT_EQ(len_48mhz, len_12mhz + 2);
    EXPECT_EQ(memcmp(frame_48mhz + len_48mhz - 16, frame_12mhz + len_12mhz - 16, 16), 0);  // Same RSSI and data.
}

TEST(BeastUtils, PacketWithoutMLATTimestampHasZeroTimestamps) {
    // An m1421 packet the receiver could not time carries only a coarse receive time.
    RawModeSPacket packet((const char*)"8d495066587f469bb826d21ad767", 0, -80, 50, 0x00ABFF1AFFFFFF1AULL);
    EXPECT_EQ(packet.GetMLAT48MHzCounter(), 0xFF1AFFFFFF1AULL);
    packet.no_mlat_timestamp = true;
    EXPECT_EQ(packet.GetMLAT48MHzCounter(), 0u);
    EXPECT_EQ(packet.GetMLAT12MHzCounter(), 0u);
}

TEST(BeastUtils, BuildReceiverInfoFrame) {
    BeastReporter::ReceiverInfo info;
    strcpy(info.id, "0bee00038172d18c");
    info.epoch = 0x3fa2;
    info.position.source = ReceiverPosition::kSourceGNSS;
    info.position.latitude_deg = 37.4219983;
    info.position.longitude_deg = -122.0840575;
    info.position.height_m = 31.42f;
    info.position.horizontal_accuracy_m = 2.5f;
    info.position.vertical_accuracy_m = 4.0f;
    info.pps.valid = true;
    info.pps.mlat_48mhz_counts = 0x12f1c0a39b100ULL;  // Wider than 48 bits: sent mod 2^48.
    info.pps.unix_time_s = 1791936000;
    strcpy(info.name, "Hilltop");
    strcpy(info.firmware_version, "adsbee_1090-0.9.1");

    uint8_t buf[BeastReporter::kReceiverInfoFrameMaxLenBytes];
    uint16_t len = BeastReporter::BuildReceiverInfoFrame(buf, sizeof(buf), info);
    ASSERT_GT(len, 3);
    EXPECT_EQ(buf[0], 0x1a);
    EXPECT_EQ(buf[1], 0xe9);
    EXPECT_EQ(buf[len - 1], '\n');
    std::string payload(reinterpret_cast<char*>(buf + 2), len - 3);
    EXPECT_EQ(payload,
              "v=1;id=0bee00038172d18c;clk=48000000;ep=3fa2;lat=37.4219983;lon=-122.0840575;alt=31.42;src=gnss;"
              "hacc=2.50;vacc=4.00;mov=0;pps=2f1c0a39b100@1791936000;name=Hilltop;fw=adsbee_1090-0.9.1");
    // Printable ASCII only: never the Beast escape Byte.
    for (char c : payload) {
        EXPECT_GE(c, 0x20);
        EXPECT_LE(c, 0x7e);
    }
}

TEST(BeastUtils, ReceiverInfoFrameEscapesAndOmissions) {
    BeastReporter::ReceiverInfo info;
    strcpy(info.id, "bad id;=\x1a");
    info.epoch = 1;
    info.position.moving = true;  // No position source: no lat/lon/alt/src, but mov is sent.
    strcpy(info.name, "a;b=c\x1a\x7f");
    uint8_t buf[BeastReporter::kReceiverInfoFrameMaxLenBytes];
    uint16_t len = BeastReporter::BuildReceiverInfoFrame(buf, sizeof(buf), info);
    ASSERT_GT(len, 3);
    std::string payload(reinterpret_cast<char*>(buf + 2), len - 3);
    EXPECT_EQ(payload, "v=1;id=bad_id___;clk=48000000;ep=1;mov=1;name=a_b_c__");

    // Negative coordinates that round to zero have no sign; unknown accuracies are left out.
    info.position.source = ReceiverPosition::kSourceFixed;
    info.position.latitude_deg = -0.00000001;
    info.position.longitude_deg = 179.99999996;
    info.position.height_m = -12.345f;
    info.name[0] = '\0';
    len = BeastReporter::BuildReceiverInfoFrame(buf, sizeof(buf), info);
    payload.assign(reinterpret_cast<char*>(buf + 2), len - 3);
    EXPECT_EQ(payload, "v=1;id=bad_id___;clk=48000000;ep=1;lat=0.0000000;lon=180.0000000;alt=-12.35;src=fixed;mov=1");

    // No ID or no room: no frame.
    EXPECT_EQ(BeastReporter::BuildReceiverInfoFrame(buf, 20, info), 0);
    info.id[0] = '\0';
    EXPECT_EQ(BeastReporter::BuildReceiverInfoFrame(buf, sizeof(buf), info), 0);
}

TEST(BeastUtils, ReceiverInfoSchedule) {
    BeastReporter::ReceiverInfoSchedule schedule;
    BeastReporter::ReceiverInfo info;
    info.epoch = 7;
    info.position.source = ReceiverPosition::kSourceFixed;
    EXPECT_TRUE(schedule.Due(0, info));  // First frame of a connection.
    schedule.MarkSent(1000, info);
    EXPECT_FALSE(schedule.Due(1000, info));
    EXPECT_FALSE(schedule.Due(10999, info));
    EXPECT_TRUE(schedule.Due(11000, info));  // Every 10 s.

    BeastReporter::ReceiverInfo changed = info;
    changed.epoch = 8;
    EXPECT_TRUE(schedule.Due(1001, changed));  // Right away on a new epoch,
    changed = info;
    changed.position.source = ReceiverPosition::kSourceGNSS;
    EXPECT_TRUE(schedule.Due(1001, changed));  // a new position source,
    changed = info;
    changed.position.moving = true;
    EXPECT_TRUE(schedule.Due(1001, changed));  // or a change of the moving flag.
    schedule.MarkSent(1001, changed);
    EXPECT_FALSE(schedule.Due(1500, changed));
    EXPECT_TRUE(schedule.Due(2001, changed));  // Every second while moving.
    EXPECT_TRUE(schedule.Due(1500, info));     // Stopped moving: tell the server now.

    schedule.MarkSent(1501, info);
    schedule.Restart();
    EXPECT_TRUE(schedule.Due(1502, info));  // New connection.
    // Works across the millisecond counter wrapping.
    schedule.MarkSent(0xFFFFF000u, info);
    EXPECT_FALSE(schedule.Due(0x00000100u, info));
    EXPECT_TRUE(schedule.Due(0xFFFFF000u + 10000u, info));
}
