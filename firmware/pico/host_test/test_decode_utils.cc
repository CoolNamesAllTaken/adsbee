#include "decode_utils.hh"  // for location calculation utility functions
#include "gtest/gtest.h"

TEST(DecodeUtils, GrayCodeConversion) { EXPECT_EQ(GrayCodeNibbleToBinaryNibble(0b0000), 0b0000); }