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