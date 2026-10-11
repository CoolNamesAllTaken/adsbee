#include "gtest/gtest.h"
#include "comms/uplink_tx_budget.hh"

TEST(UplinkTxBudget, LineMaxMatchesWriter) {
    uint8_t payload[kUATUplinkPayloadNumBytes] = {0};
    char line[kUATUplinkJSONLineMaxNumChars];
    EXPECT_EQ(WriteUATUplinkJSONLine(line, payload, -127, UINT32_MAX), UplinkTxBudget::kLineMaxNumBytes);
}

TEST(UplinkTxBudget, JSONLine) {
    uint8_t payload[kUATUplinkPayloadNumBytes];
    memset(payload, 0xFF, sizeof(payload));
    char line[kUATUplinkJSONLineMaxNumChars];
    uint16_t len = WriteUATUplinkJSONLine(line, payload, -80, 123456);

    std::string expected = "{\"uat_uplink\":\"" + std::string(576, '/') + "\",\"rssi\":-80,\"t\":123456}\n";
    EXPECT_EQ(len, expected.length());
    EXPECT_STREQ(line, expected.c_str());
}

TEST(UplinkTxBudget, HalfOfRingStaysFreeForAircraftLines) {
    const uint16_t kRingBytes = 8192;
    EXPECT_EQ(UplinkTxBudget::ReservedBytes(kRingBytes), 4096);
    EXPECT_TRUE(UplinkTxBudget::HasRoomForLine(kRingBytes - 1, kRingBytes));
    EXPECT_TRUE(UplinkTxBudget::HasRoomForLine(4096 + 621, kRingBytes));
    EXPECT_FALSE(UplinkTxBudget::HasRoomForLine(4096 + 620, kRingBytes));
    EXPECT_FALSE(UplinkTxBudget::HasRoomForLine(0, kRingBytes));
}

TEST(UplinkTxBudget, FullStreamNeeds230400Baud) {
    EXPECT_EQ(UplinkTxBudget::kFullStreamMinBaud, 198720u);
    EXPECT_LT(UplinkTxBudget::LinesPerSecond(115200), UplinkTxBudget::kMaxLinesPerSecond);
    EXPECT_EQ(UplinkTxBudget::LinesPerSecond(115200), 18u);
    EXPECT_GE(UplinkTxBudget::LinesPerSecond(230400), UplinkTxBudget::kMaxLinesPerSecond);
    EXPECT_GE(UplinkTxBudget::LinesPerSecond(1000000), UplinkTxBudget::kMaxLinesPerSecond);
}
