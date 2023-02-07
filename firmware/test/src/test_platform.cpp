#include "gtest/gtest.h"

TEST(PlatformTest, TestPointerSize) {
	// Check pointer size is 64 bit
	ASSERT_EQ(sizeof(void*)*8, 64U);
}