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
    // Version 5 numbers R1090PreambleMode as above; version 6 keeps that numbering.
    EXPECT_EQ(kSettingsVersion, 6u);
    SM::Settings settings;
    settings.Stamp();
    EXPECT_TRUE(settings.IsValid());
}

TEST(Settings, BlobFromAnOlderVersionIsRejected) {
    // A valid version 4 blob (0.3.11-rc4) fails the check, so Load() resets to factory defaults.
    SM::Settings settings;
    settings.Stamp();
    settings.settings_version = 4;
    settings.crc = settings.ComputeCRC();
    EXPECT_FALSE(settings.IsValid());
}

TEST(Settings, TornOrChangedBlobIsRejected) {
    SM::Settings settings;
    settings.Stamp();
    settings.r1090_preamble_mode = SM::kR1090PreambleModeDF17;  // Changed after stamping: stale CRC.
    EXPECT_FALSE(settings.IsValid());
}

TEST(Settings, Version5BlobMigratesWithMaxDistanceOff) {
    // A version 5 blob is today's struct up to rx_position, then its CRC.
    SM::Settings v6;
    v6.mavlink_system_id = 42;
    v6.r1090_preamble_mode = SM::kR1090PreambleModeDF17;
    v6.rx_position.icao_address = 0xBEE001;
    uint8_t blob[sizeof(SM::Settings)];
    memset(blob, 0xFF, sizeof(blob));  // Erased flash past the version 5 struct.
    memcpy(blob, static_cast<const void*>(&v6), SM::kVersion5SettingsSize - sizeof(uint32_t));
    uint32_t version = 5;
    memcpy(blob + offsetof(SM::Settings, settings_version), &version, sizeof(version));
    uint32_t crc = crc32_ieee_802_3(blob, SM::kVersion5SettingsSize - sizeof(uint32_t));
    memcpy(blob + SM::kVersion5SettingsSize - sizeof(uint32_t), &crc, sizeof(crc));

    SM::Settings out;
    out.max_distance_m = 777;
    ASSERT_TRUE(SM::MigrateFromVersion5(blob, out));
    EXPECT_TRUE(out.IsValid());
    EXPECT_EQ(out.settings_version, kSettingsVersion);
    EXPECT_EQ(out.mavlink_system_id, 42);
    EXPECT_EQ(out.r1090_preamble_mode, SM::kR1090PreambleModeDF17);
    EXPECT_EQ(out.rx_position.icao_address, 0xBEE001u);
    EXPECT_EQ(out.max_distance_m, 0u);

    // A torn version 5 blob, or a blob of another version, is left to the reset path.
    blob[10] ^= 1;
    SM::Settings untouched;
    EXPECT_FALSE(SM::MigrateFromVersion5(blob, untouched));
    blob[10] ^= 1;
    version = 4;
    memcpy(blob + offsetof(SM::Settings, settings_version), &version, sizeof(version));
    EXPECT_FALSE(SM::MigrateFromVersion5(blob, untouched));
}
