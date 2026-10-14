#include <vector>

#include "feed_datagram.hh"
#include "gtest/gtest.h"

// Splits buf into datagrams the way a UDP feed sends it.
static std::vector<std::vector<uint8_t>> Split(SettingsManager::ReportingProtocol protocol,
                                               const std::vector<uint8_t>& buf, uint16_t max_len) {
    std::vector<std::vector<uint8_t>> datagrams;
    uint16_t offset = 0;
    while (offset < buf.size()) {
        uint16_t len = FeedDatagram::NextLen(protocol, buf.data() + offset, buf.size() - offset, max_len);
        EXPECT_GT(len, 0);
        datagrams.emplace_back(buf.begin() + offset, buf.begin() + offset + len);
        offset += len;
    }
    return datagrams;
}

TEST(FeedDatagram, BatchThatFitsIsOneDatagram) {
    std::vector<uint8_t> buf(FeedDatagram::kMaxPayloadBytes, 'x');
    EXPECT_EQ(Split(SettingsManager::kRaw, buf, FeedDatagram::kMaxPayloadBytes).size(), 1u);
    EXPECT_EQ(Split(SettingsManager::kBeast, buf, FeedDatagram::kMaxPayloadBytes).size(), 1u);
}

TEST(FeedDatagram, BeastSplitsBeforeFrameStartsOnly) {
    // Three 8 byte frames; the second carries escaped 0x1A data bytes, including one right before the next frame.
    std::vector<uint8_t> f1 = {0x1A, 0x31, 1, 2, 3, 4, 5, 6};
    std::vector<uint8_t> f2 = {0x1A, 0x32, 0x1A, 0x1A, 3, 4, 0x1A, 0x1A};
    std::vector<uint8_t> f3 = {0x1A, 0x33, 1, 2, 3, 4, 5, 6};
    std::vector<uint8_t> buf;
    for (auto* f : {&f1, &f2, &f3}) buf.insert(buf.end(), f->begin(), f->end());

    auto datagrams = Split(SettingsManager::kBeast, buf, 17);
    ASSERT_EQ(datagrams.size(), 2u);
    EXPECT_EQ(datagrams[0].size(), 16u);  // f1 + f2
    EXPECT_EQ(datagrams[1], f3);

    datagrams = Split(SettingsManager::kBeastNoUAT, buf, 8);
    ASSERT_EQ(datagrams.size(), 3u);
    EXPECT_EQ(datagrams[1], f2);
}

TEST(FeedDatagram, FrameLongerThanTheLimitGoesAlone) {
    std::vector<uint8_t> buf = {'a', 'b', 'c', 'd', 'e', '\n', 'f', '\n', 'g', '\n'};
    auto datagrams = Split(SettingsManager::kAircraftJSON, buf, 4);
    ASSERT_EQ(datagrams.size(), 2u);
    EXPECT_EQ(datagrams[0].size(), 6u);
    EXPECT_EQ(datagrams[1].size(), 4u);
}

TEST(FeedDatagram, TextSplitsAfterNewlines) {
    std::string text = "*8D4840D6202CC371C32CE0576098;\n*5D4840D6;\n*8D4840D6202CC371C32CE0576098;\n";
    std::vector<uint8_t> buf(text.begin(), text.end());
    auto datagrams = Split(SettingsManager::kRaw, buf, 45);
    ASSERT_EQ(datagrams.size(), 2u);
    EXPECT_EQ(std::string(datagrams[0].begin(), datagrams[0].end()), "*8D4840D6202CC371C32CE0576098;\n*5D4840D6;\n");
}

TEST(FeedDatagram, GDL90SplitsAfterClosingFlags) {
    std::vector<uint8_t> buf = {0x7E, 0x00, 0x81, 0x7E, 0x7E, 0x14, 1, 2, 3, 0x7E};
    auto datagrams = Split(SettingsManager::kGDL90, buf, 6);
    ASSERT_EQ(datagrams.size(), 2u);
    EXPECT_EQ(datagrams[0].size(), 4u);
    EXPECT_EQ(datagrams[1].size(), 6u);
}

TEST(FeedDatagram, MAVLinkUsesTheLengthField) {
    std::vector<uint8_t> v1(3 + 8, 0);  // Payload length 3.
    v1[0] = 0xFE;
    v1[1] = 3;
    std::vector<uint8_t> v2_signed(2 + 12 + 13, 0);  // Payload length 2, signed.
    v2_signed[0] = 0xFD;
    v2_signed[1] = 2;
    v2_signed[2] = 0x01;
    std::vector<uint8_t> buf = v1;
    buf.insert(buf.end(), v2_signed.begin(), v2_signed.end());
    buf.insert(buf.end(), v1.begin(), v1.end());
    auto datagrams = Split(SettingsManager::kMAVLINK2, buf, 30);
    ASSERT_EQ(datagrams.size(), 3u);
    EXPECT_EQ(datagrams[0], v1);
    EXPECT_EQ(datagrams[1], v2_signed);
    EXPECT_EQ(datagrams[2], v1);
}
