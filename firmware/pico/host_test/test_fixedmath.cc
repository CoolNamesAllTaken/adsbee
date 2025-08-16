#include "fixedmath/fixed_math.hpp"
#include "gtest/gtest.h"

using fixedmath::fixed_t;
using fixedmath::operator""_fix;

static constexpr float kAtanDegCloseEnough = 0.0001f;

TEST(FixedMath, ATan) {
    fixed_t result = fixedmath::func::atan(fixedmath::fixed_t(1.0f));
    EXPECT_NEAR(static_cast<float>(result), 45.0f, kAtanDegCloseEnough);
}