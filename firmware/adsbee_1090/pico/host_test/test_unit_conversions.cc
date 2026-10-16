#include <cstring>

#include "gtest/gtest.h"
#include "unit_conversions.hh"

TEST(UnitConversions, MetersToFeet)
{
    ASSERT_NEAR(MetersToFeet(123456), 405039, 0.001 * 123456);
}

TEST(UnitConversions, FeetToMeters)
{
    ASSERT_NEAR(FeetToMeters(405039), 123456, 0.001 * 405039);
}
static bool Parse(const char* str, uint32_t& deci_nm, uint32_t max = 100000) {
    return ParseDeciNm(str, strlen(str), deci_nm, max);
}

TEST(UnitConversions, ParseDeciNm) {
    uint32_t d = 7;
    EXPECT_TRUE(Parse("50", d));
    EXPECT_EQ(d, 500u);
    EXPECT_TRUE(Parse("12.5", d));
    EXPECT_EQ(d, 125u);
    EXPECT_TRUE(Parse("0.1", d));
    EXPECT_EQ(d, 1u);
    EXPECT_TRUE(Parse(".3", d));
    EXPECT_EQ(d, 3u);
    EXPECT_TRUE(Parse("7.", d));
    EXPECT_EQ(d, 70u);
    EXPECT_TRUE(Parse("0.25", d));  // Rounds to the nearest tenth.
    EXPECT_EQ(d, 3u);
    EXPECT_TRUE(Parse("0.249", d));
    EXPECT_EQ(d, 2u);
    EXPECT_TRUE(Parse("9.96", d));
    EXPECT_EQ(d, 100u);
    EXPECT_TRUE(Parse("10000.0", d));
    EXPECT_EQ(d, 100000u);

    d = 7;
    for (const char* bad : {"", ".", "-1", "+1", "1e3", "1.2.3", " 5", "5 ", "abc", "10000.1", "99999999999999"}) {
        EXPECT_FALSE(Parse(bad, d)) << bad;
        EXPECT_EQ(d, 7u) << bad;
    }
}

TEST(UnitConversions, DeciNmToMeters) {
    EXPECT_EQ(DeciNmToMeters(0), 0u);
    EXPECT_EQ(DeciNmToMeters(1), 185u);  // 185.2 m.
    EXPECT_EQ(DeciNmToMeters(10), 1852u);
    EXPECT_EQ(DeciNmToMeters(1000), 185200u);
    EXPECT_EQ(DeciNmToMeters(100000), 18520000u);
}
