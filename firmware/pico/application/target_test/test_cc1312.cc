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