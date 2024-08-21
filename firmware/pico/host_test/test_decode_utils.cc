#include "decode_utils.hh"  // for location calculation utility functions
#include "gtest/gtest.h"

TEST(DecodeUtils, GrayCodeConversion) {
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b0000), 0u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b0001), 1u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b0011), 2u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b0010), 3u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b0110), 4u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b0111), 5u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b0101), 6u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b0100), 7u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b1100), 8u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b1101), 9u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b1111), 10u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b1110), 11u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b1010), 12u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b1011), 13u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b1001), 14u);
    EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b1000), 15u);
}