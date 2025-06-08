#include "hardware_unit_tests.hh"
#include "spi_coprocessor.hh"

#define NO_ESP32_EXIT_GUARD                                                                       \
    if (!bsp.has_esp32 || !esp32.IsEnabled()) {                                                   \
        CONSOLE_ERROR("test_spi_coprocessor", "ESP32 not installed or disabled, skipping test."); \
        return;                                                                                   \
    }

UTEST(SpiCoprocessor, WriteReadScratchNoAck) {
    NO_ESP32_EXIT_GUARD
    uint32_t scratch_out = 0xDEADBEEF;
    ASSERT_TRUE(esp32.Write(ObjectDictionary::Address::kAddrScratch, scratch_out));
    uint32_t scratch_in = 0x0;
    ASSERT_TRUE(esp32.Read(ObjectDictionary::Address::kAddrScratch, scratch_in));
    EXPECT_EQ(scratch_out, scratch_in);
}

UTEST(SpiCoprocessor, WriteReadScratchWithAck) {
    NO_ESP32_EXIT_GUARD
    uint32_t scratch_out = 0xDEADBEEF;
    // Write requires an ack.
    ASSERT_TRUE(esp32.Write(ObjectDictionary::Address::kAddrScratch, scratch_out, true));
    uint32_t scratch_in = 0x0;
    ASSERT_TRUE(esp32.Read(ObjectDictionary::Address::kAddrScratch, scratch_in));
    EXPECT_EQ(scratch_out, scratch_in);
}

UTEST(SPICoprocessor, ReadWriteReadRewriteRereadBigNoAck) {
    NO_ESP32_EXIT_GUARD
    SettingsManager::Settings settings_in_original;
    memset(&settings_in_original, 0x0, sizeof(settings_in_original));
    ASSERT_TRUE(esp32.Read(ObjectDictionary::Address::kAddrSettingsData, settings_in_original));
    SettingsManager::Settings settings_out;
    for (uint16_t i = 0; i < sizeof(settings_out); i++) {
        ((uint8_t *)&settings_out)[i] = i % UINT8_MAX;
    }
    // Don't require ACK, don't write last Byte of Settings in order to avoid triggering a reboot.
    ASSERT_TRUE(esp32.Write(ObjectDictionary::Address::kAddrSettingsData, settings_out, false,
                            sizeof(SettingsManager::Settings) - 1));
    SettingsManager::Settings settings_in_modified;
    ASSERT_TRUE(esp32.Read(ObjectDictionary::Address::kAddrSettingsData, settings_in_modified));
    // Fake the last Byte.
    memcpy((uint8_t *)&settings_in_modified + sizeof(SettingsManager::Settings) - 1,
           (uint8_t *)&settings_out + sizeof(SettingsManager::Settings) - 1, 1);
    for (uint16_t i = 0; i < sizeof(settings_out); i++) {
        EXPECT_EQ(i % UINT8_MAX, ((uint8_t *)&settings_in_modified)[i]);
    }
    ASSERT_TRUE(esp32.Write(ObjectDictionary::Address::kAddrSettingsData, settings_in_original));
}

UTEST(SPICoprocessor, ReadWriteReadRewriteRereadBigWithAck) {
    NO_ESP32_EXIT_GUARD
    SettingsManager::Settings settings_in_original;
    memset(&settings_in_original, 0x0, sizeof(settings_in_original));
    ASSERT_TRUE(esp32.Read(ObjectDictionary::Address::kAddrSettingsData, settings_in_original));
    SettingsManager::Settings settings_out;
    for (uint16_t i = 0; i < sizeof(settings_out); i++) {
        ((uint8_t *)&settings_out)[i] = i % UINT8_MAX;
    }
    // Don't require ACK, don't write last Byte of Settings in order to avoid triggering a reboot.
    ASSERT_TRUE(esp32.Write(ObjectDictionary::Address::kAddrSettingsData, settings_out, true,
                            sizeof(SettingsManager::Settings) - 1));
    SettingsManager::Settings settings_in_modified;
    ASSERT_TRUE(esp32.Read(ObjectDictionary::Address::kAddrSettingsData, settings_in_modified));
    // Fake the last Byte.
    memcpy((uint8_t *)&settings_in_modified + sizeof(SettingsManager::Settings) - 1,
           (uint8_t *)&settings_out + sizeof(SettingsManager::Settings) - 1, 1);
    for (uint16_t i = 0; i < sizeof(settings_out); i++) {
        EXPECT_EQ(i % UINT8_MAX, ((uint8_t *)&settings_in_modified)[i]);
    }
    ASSERT_TRUE(esp32.Write(ObjectDictionary::Address::kAddrSettingsData, settings_in_original, true));
}