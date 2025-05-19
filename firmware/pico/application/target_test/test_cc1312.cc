#include "adsbee.hh"
#include "hardware_unit_tests.hh"
#include "unit_conversions.hh"

UTEST(CC1312, EnterBootloader) { EXPECT_TRUE(adsbee.subg_radio.EnterBootloader()); }