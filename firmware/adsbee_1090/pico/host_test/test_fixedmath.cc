#include "fixedmath/fixed_math.hpp"
#include "gtest/gtest.h"

using fixedmath::fixed_t;
using fixedmath::operator""_fix;

static constexpr float kAtanDegCloseEnough = 0.001f;
static constexpr fixedmath::fixed_t kDegToRad = fixedmath::fixed_t(M_PI / 180.0f);

TEST(FixedMath, ATan) {
    fixed_t result = fixedmath::func::atan(fixedmath::fixed_t(1.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(45.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test atan(0) = 0
    result = fixedmath::func::atan(fixedmath::fixed_t(0.0f));
    EXPECT_NEAR(static_cast<float>(result), 0.0f, kAtanDegCloseEnough);

    // Test atan(-1) = -45 degrees
    result = fixedmath::func::atan(fixedmath::fixed_t(-1.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(-45.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test atan(sqrt(3)) = 60 degrees
    result = fixedmath::func::atan(fixedmath::fixed_t(1.732050808f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(60.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test atan(1/sqrt(3)) = 30 degrees
    result = fixedmath::func::atan(fixedmath::fixed_t(0.577350269f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(30.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test large positive value approaches 90 degrees
    result = fixedmath::func::atan(fixedmath::fixed_t(100.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(89.4f) * kDegToRad), 0.1f);

    // Test large negative value approaches -90 degrees
    result = fixedmath::func::atan(fixedmath::fixed_t(-100.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(-89.4f) * kDegToRad), 0.1f);
}

TEST(FixedMath, ATan2) {
    fixed_t result = fixedmath::func::atan2(fixedmath::fixed_t(1.0f), fixedmath::fixed_t(1.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(45.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test atan2(0, 1) = 0
    result = fixedmath::func::atan2(fixedmath::fixed_t(0.0f), fixedmath::fixed_t(1.0f));
    EXPECT_NEAR(static_cast<float>(result), 0.0f, kAtanDegCloseEnough);

    // Test atan2(-1, 1) = -45 degrees
    result = fixedmath::func::atan2(fixedmath::fixed_t(-1.0f), fixedmath::fixed_t(1.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(-45.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test atan2(sqrt(3), 1) = 60 degrees
    result = fixedmath::func::atan2(fixedmath::fixed_t(1.732050808f), fixedmath::fixed_t(1.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(60.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test atan2(1/sqrt(3), 1) = 30 degrees
    result = fixedmath::func::atan2(fixedmath::fixed_t(0.577350269f), fixedmath::fixed_t(1.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(30.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test atan2(100, 1) approaches 90 degrees
    result = fixedmath::func::atan2(fixedmath::fixed_t(100.0f), fixedmath::fixed_t(1.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(89.4f) * kDegToRad), 0.1f);

    // Test atan2(-100, 1) approaches -90 degrees
    result = fixedmath::func::atan2(fixedmath::fixed_t(-100.0f), fixedmath::fixed_t(1.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(-89.4f) * kDegToRad), 0.1f);

    // Test atan2(1, 0) = 90 degrees
    result = fixedmath::func::atan2(fixedmath::fixed_t(1.0f), fixedmath::fixed_t(0.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(90.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test atan2(-1, 0) = -90 degrees
    result = fixedmath::func::atan2(fixedmath::fixed_t(-1.0f), fixedmath::fixed_t(0.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(-90.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test atan2(0, -1) = 180 degrees
    result = fixedmath::func::atan2(fixedmath::fixed_t(0.0f), fixedmath::fixed_t(-1.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(180.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test atan2(1, -1) = 135 degrees
    result = fixedmath::func::atan2(fixedmath::fixed_t(1.0f), fixedmath::fixed_t(-1.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(135.0f) * kDegToRad),
                kAtanDegCloseEnough);

    // Test atan2(-1, -1) = -135 degrees
    result = fixedmath::func::atan2(fixedmath::fixed_t(-1.0f), fixedmath::fixed_t(-1.0f));
    EXPECT_NEAR(static_cast<float>(result), static_cast<float>(fixedmath::fixed_t(-135.0f) * kDegToRad),
                kAtanDegCloseEnough);
}