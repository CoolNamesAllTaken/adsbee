// 1090 MHz receiver mode values stored in flash, and the settings version that guards their numbering.
#include <cstring>

#include "gtest/gtest.h"
#include "settings.hh"

using SM = SettingsManager;

// Same lookup as CommsManager::ATR1090PreambleCallback; -1 if the name is rejected.
static int ModeForName(const char* name) {
    for (uint16_t i = 0; i < SM::kNumR1090PreambleModes; i++) {
        if (strcmp(name, SM::kR1090PreambleModeStrs[i]) == 0) {
            return i;
        }
    }
    return -1;
}

TEST(Settings, R1090PreambleModesAreNumberedContiguously) {
    static_assert(SM::kR1090PreambleModeModeS == 0, "0 is MODE_S.");
    static_assert(SM::kR1090PreambleModeDF17 == 1, "1 is DF17.");
    EXPECT_EQ(SM::kNumR1090PreambleModes, 2);
    for (uint16_t i = 0; i < SM::kNumR1090PreambleModes; i++) {
        EXPECT_STRNE(SM::kR1090PreambleModeStrs[i], "") << "mode " << i << " has a name";
    }
}

TEST(Settings, R1090PreambleModeFactoryDefaultIsModeS) {
    EXPECT_EQ(SM::Settings().r1090_preamble_mode, SM::kR1090PreambleModeModeS);
}

TEST(Settings, R1090PreambleModeNamesSelectTheirModes) {
    EXPECT_EQ(ModeForName("MODE_S"), SM::kR1090PreambleModeModeS);
    EXPECT_EQ(ModeForName("DF17"), SM::kR1090PreambleModeDF17);
    EXPECT_EQ(ModeForName("mode_s"), -1);
    EXPECT_EQ(ModeForName(""), -1);
}

TEST(Settings, VersionNumberingModesIsCurrent) {
    // Version 5 numbers R1090PreambleMode as above; versions 6 to 8 keep that numbering.
    EXPECT_EQ(kSettingsVersion, 8u);
    SM::Settings settings;
    settings.Stamp();
    EXPECT_TRUE(settings.IsValid());
}

TEST(Settings, BlobFromAnOlderVersionIsRejected) {
    // Load() migrates or resets a blob of another version.
    SM::Settings settings;
    settings.Stamp();
    settings.settings_version = 6;
    settings.crc = settings.ComputeCRC();
    EXPECT_FALSE(settings.IsValid());
}

TEST(Settings, TornOrChangedBlobIsRejected) {
    SM::Settings settings;
    settings.Stamp();
    settings.r1090_preamble_mode = SM::kR1090PreambleModeDF17;  // Changed after stamping: stale CRC.
    EXPECT_FALSE(settings.IsValid());
}

TEST(Settings, Version5BlobMigratesWithDistanceFilterOff) {
    // A version 5 blob is today's struct up to rx_position, then its CRC.
    SM::Settings current;
    current.mavlink_system_id = 42;
    current.r1090_preamble_mode = SM::kR1090PreambleModeDF17;
    current.rx_position.icao_address = 0xBEE001;
    uint8_t blob[sizeof(SM::Settings)];
    memset(blob, 0xFF, sizeof(blob));  // Erased flash past the version 5 struct.
    memcpy(blob, static_cast<const void*>(&current), SM::kVersion5SettingsSize - sizeof(uint32_t));
    uint32_t version = 5;
    memcpy(blob + offsetof(SM::Settings, settings_version), &version, sizeof(version));
    uint32_t crc = crc32_ieee_802_3(blob, SM::kVersion5SettingsSize - sizeof(uint32_t));
    memcpy(blob + SM::kVersion5SettingsSize - sizeof(uint32_t), &crc, sizeof(crc));

    SM::Settings out;
    out.filter_distance_enabled = true;
    out.filter_distance_deci_nm = 777;
    out.asterix_sac = 9;
    ASSERT_TRUE(SM::MigrateFromOlderVersion(blob, out));
    EXPECT_TRUE(out.IsValid());
    EXPECT_EQ(out.settings_version, kSettingsVersion);
    EXPECT_EQ(out.mavlink_system_id, 42);
    EXPECT_EQ(out.r1090_preamble_mode, SM::kR1090PreambleModeDF17);
    EXPECT_EQ(out.rx_position.icao_address, 0xBEE001u);
    EXPECT_FALSE(out.filter_distance_enabled);
    EXPECT_EQ(out.filter_distance_deci_nm, SM::Settings::kDefaultFilterDistanceDeciNm);
    EXPECT_EQ(out.FilterDistanceMeters(), 0u);
    EXPECT_EQ(out.asterix_sac, 0);

    // A torn version 5 blob, or a blob of another version, is left to the reset path.
    blob[10] ^= 1;
    SM::Settings untouched;
    EXPECT_FALSE(SM::MigrateFromOlderVersion(blob, untouched));
    blob[10] ^= 1;
    version = 4;
    memcpy(blob + offsetof(SM::Settings, settings_version), &version, sizeof(version));
    EXPECT_FALSE(SM::MigrateFromOlderVersion(blob, untouched));
}

TEST(Settings, Version6BlobMigratesWithASTERIXDataSourceZero) {
    // A version 6 blob is today's struct up to the distance filter, then its CRC.
    SM::Settings current;
    current.mavlink_system_id = 42;
    current.filter_distance_enabled = true;
    current.filter_distance_deci_nm = 355;
    uint8_t blob[sizeof(SM::Settings)];
    memset(blob, 0xFF, sizeof(blob));  // Erased flash past the version 6 struct.
    memcpy(blob, static_cast<const void*>(&current), SM::kVersion6SettingsSize - sizeof(uint32_t));
    uint32_t version = 6;
    memcpy(blob + offsetof(SM::Settings, settings_version), &version, sizeof(version));
    uint32_t crc = crc32_ieee_802_3(blob, SM::kVersion6SettingsSize - sizeof(uint32_t));
    memcpy(blob + SM::kVersion6SettingsSize - sizeof(uint32_t), &crc, sizeof(crc));

    SM::Settings out;
    out.asterix_sac = 9;
    out.asterix_sic = 10;
    ASSERT_TRUE(SM::MigrateFromOlderVersion(blob, out));
    EXPECT_TRUE(out.IsValid());
    EXPECT_EQ(out.settings_version, kSettingsVersion);
    EXPECT_EQ(out.mavlink_system_id, 42);
    EXPECT_TRUE(out.filter_distance_enabled);
    EXPECT_EQ(out.filter_distance_deci_nm, 355u);
    EXPECT_EQ(out.asterix_sac, 0);
    EXPECT_EQ(out.asterix_sic, 0);

    EXPECT_TRUE(out.rx_position_details == RxPositionDetails());
}

TEST(Settings, Version7BlobMigratesWithRxPositionDetailsEmpty) {
    // A version 7 blob is today's struct up to the ASTERIX SAC/SIC, then its CRC.
    SM::Settings current;
    current.filter_distance_enabled = true;
    current.asterix_sac = 25;
    current.asterix_sic = 7;
    uint8_t blob[sizeof(SM::Settings)];
    memset(blob, 0xFF, sizeof(blob));  // Erased flash past the version 7 struct: it must not become RX_POSITION details.
    memcpy(blob, static_cast<const void*>(&current), SM::kVersion7SettingsSize - sizeof(uint32_t));
    uint32_t version = 7;
    memcpy(blob + offsetof(SM::Settings, settings_version), &version, sizeof(version));
    uint32_t crc = crc32_ieee_802_3(blob, SM::kVersion7SettingsSize - sizeof(uint32_t));
    memcpy(blob + SM::kVersion7SettingsSize - sizeof(uint32_t), &crc, sizeof(crc));

    SM::Settings out;
    out.rx_position_details.ellipsoid_height_set = true;
    out.rx_position_details.moving = true;
    ASSERT_TRUE(SM::MigrateFromOlderVersion(blob, out));
    EXPECT_TRUE(out.IsValid());
    EXPECT_TRUE(out.filter_distance_enabled);
    EXPECT_EQ(out.asterix_sac, 25);
    EXPECT_EQ(out.asterix_sic, 7);
    EXPECT_TRUE(out.rx_position_details == RxPositionDetails());

    // A version 8 blob is not migrated.
    version = 8;
    memcpy(blob + offsetof(SM::Settings, settings_version), &version, sizeof(version));
    SM::Settings untouched;
    EXPECT_FALSE(SM::MigrateFromOlderVersion(blob, untouched));
}

TEST(Settings, ASTERIXDataSourceDefaultsToZero) {
    SM::Settings settings;
    EXPECT_EQ(settings.asterix_sac, 0);
    EXPECT_EQ(settings.asterix_sic, 0);
    EXPECT_EQ(sizeof(SM::Settings), 83u);
}
