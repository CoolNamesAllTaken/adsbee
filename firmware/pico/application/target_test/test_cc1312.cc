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
    static const uint32_t kRegOffsetUserID = 0x294;
    uint32_t read_buf_32[1] = {0};
    EXPECT_TRUE(adsbee.subg_radio.BootloaderCommandMemoryRead(kRegOffsetUserID, read_buf_32, 1));
    uint32_t read_buf_8[4] = {0};
    EXPECT_TRUE(adsbee.subg_radio.BootloaderCommandMemoryRead(kRegOffsetUserID, read_buf_8, 4));
    EXPECT_EQ(read_buf_32[0], read_buf_8[0] << 24 | read_buf_8[1] << 16 | read_buf_8[2] << 8 | read_buf_8[3]);
}