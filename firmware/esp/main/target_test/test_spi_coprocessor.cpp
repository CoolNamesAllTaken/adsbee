#include "hardware_unit_tests.hh"
#include "spi_coprocessor.hh"

UTEST(SPICoprocessor, WriteReadScratchNoAck) {
    uint32_t scratch_out = 0xDEADBEEF;
    EXPECT_TRUE(pico.Write(ObjectDictionary::Address::kAddrScratch, scratch_out));
    uint32_t scratch_in = 0x0;
    EXPECT_TRUE(pico.Read(ObjectDictionary::Address::kAddrScratch, scratch_in));
    EXPECT_EQ(scratch_out, scratch_in);
}

UTEST(SPICoprocessor, WriteReadScratchWithAck) {
    uint32_t scratch_out = 0xDEADBEEF;
    // Write requires an ack.
    EXPECT_TRUE(pico.Write(ObjectDictionary::Address::kAddrScratch, scratch_out, true));
    uint32_t scratch_in = 0x0;
    EXPECT_TRUE(pico.Read(ObjectDictionary::Address::kAddrScratch, scratch_in));
    EXPECT_EQ(scratch_out, scratch_in);
}

UTEST(SPICoprocessor, ReadWriteReadRewriteRereadBigNoAck) {
    SettingsManager::Settings settings_in_original;
    memset(&settings_in_original, 0x0, sizeof(settings_in_original));
    EXPECT_TRUE(pico.Read(ObjectDictionary::Address::kAddrSettingsStruct, settings_in_original));
    SettingsManager::Settings settings_out;
    for (uint16_t i = 0; i < sizeof(settings_out); i++) {
        ((uint8_t *)&settings_out)[i] = i % UINT8_MAX;
    }
    EXPECT_TRUE(pico.Write(ObjectDictionary::Address::kAddrSettingsStruct, settings_out));
    SettingsManager::Settings settings_in_modified;
    EXPECT_TRUE(pico.Read(ObjectDictionary::Address::kAddrSettingsStruct, settings_in_modified));
    for (uint16_t i = 0; i < sizeof(settings_out); i++) {
        EXPECT_EQ(i % UINT8_MAX, ((uint8_t *)&settings_in_modified)[i]);
    }
    EXPECT_TRUE(pico.Write(ObjectDictionary::Address::kAddrSettingsStruct, settings_in_original));
}