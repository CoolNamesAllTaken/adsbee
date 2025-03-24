#include "awb_utils.h"
#include "geo_utils.hh"
#include "gtest/gtest.h"
#include "math.h"

// Earth radius is 3963.1 mi. Not counting non-spherical shape, distance tolerance is 3963.1 mi * kHaversineTolerance.
// 3963.1 mi * 0.00005 = 0.20 mi.
static const float kHaversineTolerance = 0.00005f;

#define SQ(x) ((x) * (x))
#define EXPECT_NEAR_HAV(theta_deg)                                                                   \
    EXPECT_NEAR(slow_hav_deg(theta_deg), hav_awb(static_cast<uint32_t>(theta_deg * INV_RESOLUTION)), \
                kHaversineTolerance)                                                                 \
        << "Failed with theta_deg=" << theta_deg

float slow_hav_deg(float theta_deg) { return SQ(sin(theta_deg * M_PI / 360.0)); }

TEST(GeoUtils, HaversineAWB) {
    for (float theta_deg = 0.0f; theta_deg < 360.0f; theta_deg += 0.5f) {
        EXPECT_NEAR_HAV(theta_deg);
    }
}