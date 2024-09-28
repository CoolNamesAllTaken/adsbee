#include "gtest/gtest.h"
#include "settings.hh"

TEST(Settings, DeviceInfoGetDefaultSSIDAndUID) {
    SettingsManager::DeviceInfo device_info;
    strncpy(device_info.part_code, (char *)"010240002F-20240907-986541", SettingsManager::DeviceInfo::kPartCodeLen + 1);

    char ssid_buf[SettingsManager::Settings::kWiFiSSIDMaxLen];
    device_info.GetDefaultSSID(ssid_buf);
    EXPECT_STREQ(ssid_buf, (char *)"ADSBee1090-0240907986541");

    uint8_t uid_buf[SettingsManager::Settings::kFeedReceiverIDNumBytes];
    device_info.GetDefaultFeedReceiverID(uid_buf);
    EXPECT_EQ(uid_buf[0], 0xBE);
    EXPECT_EQ(uid_buf[1], 0xE0);

    uint64_t uid_val = 240907986541;
    EXPECT_EQ(uid_buf[2], (uid_val >> (8 * 5)) & 0xFF);
    EXPECT_EQ(uid_buf[3], (uid_val >> (8 * 4)) & 0xFF);
    EXPECT_EQ(uid_buf[4], (uid_val >> (8 * 3)) & 0xFF);
    EXPECT_EQ(uid_buf[5], (uid_val >> (8 * 2)) & 0xFF);
    EXPECT_EQ(uid_buf[6], (uid_val >> (8 * 1)) & 0xFF);
    EXPECT_EQ(uid_buf[7], uid_val & 0xFF);
}