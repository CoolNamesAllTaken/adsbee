#include <cstring>

#include "gtest/gtest.h"
#include "settings.hh"
#include "settings_migration.hh"
#include "settings_versions.hh"

TEST(Settings, DeviceInfoGetDefaultSSIDAndUID) {
    SettingsManager::DeviceInfo device_info;
    strncpy(device_info.part_code, (const char*)"010240002F-20240907-986541",
            SettingsManager::DeviceInfo::kPartCodeLen + 1);

    char ssid_buf[SettingsManager::Settings::kWiFiSSIDMaxLen];
    device_info.GetDefaultSSID(ssid_buf);
    EXPECT_STREQ(ssid_buf, (const char*)"ADSBee1090-0240907986541");

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

TEST(Settings, CoreNetworkSettings) {
    SettingsManager::Settings test_settings;
    EXPECT_FALSE(test_settings.core_network_settings.IsValid());
    test_settings.core_network_settings.UpdateCRC32();
    EXPECT_EQ(test_settings.core_network_settings.crc32, test_settings.core_network_settings.CalculateCRC32());
    EXPECT_TRUE(test_settings.core_network_settings.IsValid());

    test_settings.core_network_settings.wifi_ap_enabled = !test_settings.core_network_settings.wifi_ap_enabled;
    EXPECT_FALSE(test_settings.core_network_settings.IsValid());
    test_settings.core_network_settings.UpdateCRC32();
    EXPECT_TRUE(test_settings.core_network_settings.IsValid());
}

TEST(SettingsMigration, LayoutLockedSizes) {
    // Belt-and-suspenders alongside the static_asserts in settings_versions.hh.
    EXPECT_EQ(sizeof(settings_v12::Settings), 1088u);
    EXPECT_EQ(sizeof(settings_v12::CoreNetworkSettings),
              sizeof(SettingsManager::Settings::CoreNetworkSettings));
    EXPECT_EQ(sizeof(settings_v12::RxPosition), sizeof(SettingsManager::RxPosition));
}

TEST(SettingsMigration, UnmigratableVersionReturnsFalse) {
    uint8_t blob[sizeof(settings_v12::Settings)] = {0};
    SettingsManager::Settings out;
    // Pre-v12, unknown-future, and current version are all not migratable by this utility.
    EXPECT_FALSE(SettingsMigrator::Migrate(blob, sizeof(blob), 11, out));
    EXPECT_FALSE(SettingsMigrator::Migrate(blob, sizeof(blob), 999, out));
    EXPECT_FALSE(SettingsMigrator::Migrate(blob, sizeof(blob), kSettingsVersion, out));
    // A v12 version tag but a too-short blob must also be rejected.
    EXPECT_FALSE(SettingsMigrator::Migrate(blob, sizeof(settings_v12::Settings) - 1, 12, out));
}

TEST(SettingsMigration, V12ToV13PreservesAllFields) {
    // Build a v12 settings blob with distinctive, non-default values across every field.
    settings_v12::Settings v12 = {};
    v12.settings_version = 12;

    // Core network settings: build a valid-CRC block using the live struct (which also proves byte compatibility),
    // then copy it into the frozen v12 layout.
    {
        SettingsManager::Settings::CoreNetworkSettings cns;  // Zero-fills strings in its constructor.
        cns.esp32_enabled = true;
        strncpy(cns.wifi_ap_ssid, "MigrateNet", sizeof(cns.wifi_ap_ssid));
        strncpy(cns.wifi_ap_password, "supersecret", sizeof(cns.wifi_ap_password));
        cns.wifi_ap_channel = 6;
        cns.ethernet_enabled = true;
        cns.UpdateCRC32();
        ASSERT_EQ(sizeof(cns), sizeof(v12.core_network_settings));
        memcpy(&v12.core_network_settings, &cns, sizeof(cns));
    }

    v12.r1090_rx_enabled = false;
    v12.tl_offset_mv = 123;
    v12.r1090_bias_tee_enabled = true;
    v12.watchdog_timeout_sec = 42;
    v12.log_level = SettingsManager::LogLevel::kInfo;  // 3
    v12.reporting_protocols[0] = SettingsManager::ReportingProtocol::kCSBee;
    v12.reporting_protocols[1] = SettingsManager::ReportingProtocol::kGDL90;
    v12.reporting_protocols[2] = SettingsManager::ReportingProtocol::kAircraftJSON;
    v12.baud_rates[0] = 1200;
    v12.baud_rates[1] = 57600;
    v12.baud_rates[2] = 4800;
    v12.subg_enabled = SettingsManager::EnableState::kEnableStateDisabled;
    v12.subg_rx_enabled = false;
    v12.subg_bias_tee_enabled = true;
    v12.subg_mode = SettingsManager::SubGHzRadioMode::kSubGHzRadioModeUATRx;

    strncpy(v12.feed_uris[0], "myfeed.example.com", sizeof(v12.feed_uris[0]));
    strncpy(v12.feed_uris[9], "feed.adsb.fi", sizeof(v12.feed_uris[9]));
    v12.feed_ports[0] = 30005;
    v12.feed_ports[9] = 30004;
    v12.feed_is_active[0] = true;
    v12.feed_is_active[9] = true;
    v12.feed_protocols[0] = SettingsManager::ReportingProtocol::kBeast;
    v12.feed_protocols[9] = SettingsManager::ReportingProtocol::kBeast;
    v12.feed_receiver_ids[0][0] = 0xDE;
    v12.feed_receiver_ids[0][7] = 0xAD;

    v12.mavlink_system_id = 7;
    v12.mavlink_component_id = 42;

    v12.rx_position.source = 1;  // kPositionSourceFixed
    v12.rx_position.latitude_deg = 37.5f;
    v12.rx_position.longitude_deg = -122.3f;
    v12.rx_position.gnss_altitude_ft = 111;
    v12.rx_position.baro_altitude_ft = 222;
    v12.rx_position.heading_deg = 90.0f;
    v12.rx_position.speed_kts = 33;
    v12.rx_position.icao_address = 0xABCDEF;

    // Serialize to a raw blob and migrate.
    uint8_t blob[sizeof(settings_v12::Settings)];
    memcpy(blob, &v12, sizeof(v12));

    SettingsManager::Settings out;
    ASSERT_TRUE(SettingsMigrator::Migrate(blob, sizeof(blob), 12, out));

    // Version updated to current.
    EXPECT_EQ(out.settings_version, kSettingsVersion);

    // Network settings preserved and still CRC-valid.
    EXPECT_TRUE(out.core_network_settings.IsValid());
    EXPECT_STREQ(out.core_network_settings.wifi_ap_ssid, "MigrateNet");
    EXPECT_STREQ(out.core_network_settings.wifi_ap_password, "supersecret");
    EXPECT_EQ(out.core_network_settings.wifi_ap_channel, 6);
    EXPECT_TRUE(out.core_network_settings.ethernet_enabled);

    // System / 1090 settings preserved.
    EXPECT_FALSE(out.r1090_rx_enabled);
    EXPECT_EQ(out.tl_offset_mv, 123);
    EXPECT_TRUE(out.r1090_bias_tee_enabled);
    EXPECT_EQ(out.watchdog_timeout_sec, 42u);

    // Comms settings preserved.
    EXPECT_EQ(out.log_level, SettingsManager::LogLevel::kInfo);
    EXPECT_EQ(out.reporting_protocols[0], SettingsManager::ReportingProtocol::kCSBee);
    EXPECT_EQ(out.reporting_protocols[1], SettingsManager::ReportingProtocol::kGDL90);
    EXPECT_EQ(out.reporting_protocols[2], SettingsManager::ReportingProtocol::kAircraftJSON);
    EXPECT_EQ(out.baud_rates[0], 1200u);
    EXPECT_EQ(out.baud_rates[1], 57600u);
    EXPECT_EQ(out.baud_rates[2], 4800u);

    // Sub-GHz settings preserved.
    EXPECT_EQ(out.subg_enabled, SettingsManager::EnableState::kEnableStateDisabled);
    EXPECT_FALSE(out.subg_rx_enabled);
    EXPECT_TRUE(out.subg_bias_tee_enabled);

    // New v13 fields take their defaults.
    EXPECT_FALSE(out.remote_id_rx_enabled);
    EXPECT_EQ(out.remote_id_transports, (uint8_t)(SettingsManager::kRemoteIDTransportBLE4 |
                                                  SettingsManager::kRemoteIDTransportBLE5Long |
                                                  SettingsManager::kRemoteIDTransportWiFiBeacon));

    // Feed settings preserved.
    EXPECT_STREQ(out.feed_uris[0], "myfeed.example.com");
    EXPECT_STREQ(out.feed_uris[9], "feed.adsb.fi");
    EXPECT_EQ(out.feed_ports[0], 30005);
    EXPECT_EQ(out.feed_ports[9], 30004);
    EXPECT_TRUE(out.feed_is_active[0]);
    EXPECT_TRUE(out.feed_is_active[9]);
    EXPECT_EQ(out.feed_protocols[0], SettingsManager::ReportingProtocol::kBeast);
    EXPECT_EQ(out.feed_receiver_ids[0][0], 0xDE);
    EXPECT_EQ(out.feed_receiver_ids[0][7], 0xAD);

    // MAVLINK settings preserved.
    EXPECT_EQ(out.mavlink_system_id, 7);
    EXPECT_EQ(out.mavlink_component_id, 42);

    // Receiver position preserved.
    EXPECT_EQ(out.rx_position.source, SettingsManager::RxPosition::kPositionSourceFixed);
    EXPECT_FLOAT_EQ(out.rx_position.latitude_deg, 37.5f);
    EXPECT_FLOAT_EQ(out.rx_position.longitude_deg, -122.3f);
    EXPECT_EQ(out.rx_position.gnss_altitude_ft, 111);
    EXPECT_EQ(out.rx_position.baro_altitude_ft, 222);
    EXPECT_FLOAT_EQ(out.rx_position.heading_deg, 90.0f);
    EXPECT_EQ(out.rx_position.speed_kts, 33);
    EXPECT_EQ(out.rx_position.icao_address, 0xABCDEFu);
}