#include "adsbee.hh"
#include "hardware_unit_tests.hh"
#include "unit_conversions.hh"

UTEST(CC1312, EnterBootloader) { EXPECT_TRUE(adsbee.subg_radio.EnterBootloader()); }

UTEST(CC1312, BootloaderCommandReset) {
    EXPECT_TRUE(adsbee.subg_radio.BootloaderCommandPing());
    EXPECT_TRUE(adsbee.subg_radio.BootloaderCommandReset());
    EXPECT_FALSE(adsbee.subg_radio.BootloaderCommandPing());
    sleep_ms(100);
    EXPECT_TRUE(adsbee.subg_radio.EnterBootloader());
}

UTEST(CC1312, BootloaderCommandMemoryReadSingleWord) {
    uint32_t read_buf_32[1] = {0};
    EXPECT_TRUE(adsbee.subg_radio.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + CC1312::kFCFG1RegOffUserID,
                                                              read_buf_32, 1));
    printf("User ID (32 bit read): 0x%08X\n", read_buf_32[0]);
    uint8_t read_buf_8[4] = {0};
    EXPECT_TRUE(adsbee.subg_radio.BootloaderCommandMemoryRead(CC1312::kBaseAddrFCFG1 + CC1312::kFCFG1RegOffUserID,
                                                              read_buf_8, 4));
    printf("User ID (8 bit read): 0x%02X%02X%02X%02X\n", read_buf_8[0], read_buf_8[1], read_buf_8[2], read_buf_8[3]);
    EXPECT_EQ(read_buf_32[0], read_buf_8[0] << 24 | read_buf_8[1] << 16 | read_buf_8[2] << 8 | read_buf_8[3]);
}