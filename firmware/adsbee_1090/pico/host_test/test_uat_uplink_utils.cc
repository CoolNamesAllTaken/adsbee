#include <string>

#include "gtest/gtest.h"
#include "uat_uplink_utils.hh"

// Base64 of payload[i] = 7 * i + 3.
static const char kTestPayloadBase64[] =
    "AwoRGB8mLTQ7QklQV15lbHN6gYiPlp2kq7K5wMfO1dzj6vH4/wYNFBsiKTA3PkVMU1phaG92fYSLkpmgp661vMPK0djf5u30"
    "+wIJEBceJSwzOkFIT1ZdZGtyeYCHjpWco6qxuL/GzdTb4unw9/4FDBMaISgvNj1ES1JZYGdudXyDipGYn6attLvCydDX3uXs"
    "8/oBCA8WHSQrMjlAR05VXGNqcXh/ho2Um6KpsLe+xczT2uHo7/b9BAsSGSAnLjU8Q0pRWF9mbXR7gomQl56lrLO6wcjP1t3k"
    "6/L5AAcOFRwjKjE4P0ZNVFtiaXB3foWMk5qhqK+2vcTL0tng5+71/AMKERgfJi00O0JJUFdeZWxzeoGIj5adpKuyucDHztXc"
    "4+rx+P8GDRQbIikwNz5FTFNaYWhvdn2Ei5KZoKeutbzDytHY3+bt9PsCCRAXHiUsMzpBSE9WXWRrcnmAh46VnKOqsbi/xs3U"
    "2+Lp8Pf+BQwTGiEoLzY9REtSWWBnbnV8g4qRmJ+mrbS7wsnQ197l7PP6AQgPFh0kKzI5QEdOVVxjanF4f4aNlJuiqbC3vsXM";

static void FillTestPayload(uint8_t payload[kUATUplinkPayloadNumBytes]) {
    for (uint16_t i = 0; i < kUATUplinkPayloadNumBytes; i++) {
        payload[i] = static_cast<uint8_t>(7 * i + 3);
    }
}

TEST(UATUplinkUtils, MessageLayout) {
    uint8_t payload[kUATUplinkPayloadNumBytes];
    FillTestPayload(payload);
    uint8_t message[kUATUplinkMessageNumBytes];
    memset(message, 0xFF, sizeof(message));

    EXPECT_EQ(BuildUATUplinkMessage(message, payload, -80, 0x12345678), 440);
    EXPECT_EQ(memcmp(message, payload, kUATUplinkPayloadNumBytes), 0);
    EXPECT_EQ(static_cast<int8_t>(message[432]), -80);
    EXPECT_EQ(message[433], 0);
    EXPECT_EQ(message[434], 0);
    EXPECT_EQ(message[435], 0);
    // Little endian timestamp.
    EXPECT_EQ(message[436], 0x78);
    EXPECT_EQ(message[437], 0x56);
    EXPECT_EQ(message[438], 0x34);
    EXPECT_EQ(message[439], 0x12);
}

TEST(UATUplinkUtils, MessageRSSILimits) {
    uint8_t payload[kUATUplinkPayloadNumBytes] = {0};
    uint8_t message[kUATUplinkMessageNumBytes];

    BuildUATUplinkMessage(message, payload, INT16_MIN, 0);
    EXPECT_EQ(static_cast<int8_t>(message[432]), -128);  // Unknown.
    BuildUATUplinkMessage(message, payload, -200, 0);
    EXPECT_EQ(static_cast<int8_t>(message[432]), -127);
    BuildUATUplinkMessage(message, payload, 300, 0);
    EXPECT_EQ(static_cast<int8_t>(message[432]), 127);
}

TEST(UATUplinkUtils, JSONLine) {
    uint8_t payload[kUATUplinkPayloadNumBytes];
    FillTestPayload(payload);
    char line[kUATUplinkJSONLineMaxNumChars];

    std::string expected = std::string("{\"uat_uplink\":\"") + kTestPayloadBase64 + "\",\"rssi\":-80,\"t\":123456}\n";
    EXPECT_EQ(WriteUATUplinkJSONLine(line, payload, -80, 123456), expected.length());
    EXPECT_STREQ(line, expected.c_str());
}

TEST(UATUplinkUtils, JSONLineUnknownRSSI) {
    uint8_t payload[kUATUplinkPayloadNumBytes];
    FillTestPayload(payload);
    char line[kUATUplinkJSONLineMaxNumChars];

    std::string expected = std::string("{\"uat_uplink\":\"") + kTestPayloadBase64 + "\",\"t\":7}\n";
    EXPECT_EQ(WriteUATUplinkJSONLine(line, payload, INT16_MIN, 7), expected.length());
    EXPECT_STREQ(line, expected.c_str());
}

TEST(UATUplinkUtils, JSONLineLongestFitsBuffer) {
    uint8_t payload[kUATUplinkPayloadNumBytes] = {0};
    char line[kUATUplinkJSONLineMaxNumChars];

    uint16_t len = WriteUATUplinkJSONLine(line, payload, -127, UINT32_MAX);
    EXPECT_EQ(len, 621);
    EXPECT_LT(len, kUATUplinkJSONLineMaxNumChars);
    EXPECT_EQ(line[len - 1], '\n');
    EXPECT_EQ(line[len], '\0');
}
