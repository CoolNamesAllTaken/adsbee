#include "awb_utils.h"
#include "geo_utils.hh"
#include "gtest/gtest.h"
#include "macros.hh"
#include "math.h"

static const float kHaversineToleranceFloor =
    0.00002f;  // Minimum value for haversine tolerance to avoid floating point precision issues.
static const float kHaversineToleranceFrac = 0.0001f;

static const float kHavDiffToMetersToleranceFrac = 0.001f;
static const float kEarthMeanRadiusMeters = 6372797.560856f;  // Mean radius of the Earth in meters.

static const float kGeoDistanceToleranceFrac = 0.01f;

#define SQ(x) ((x) * (x))

/** Test the haversine lookup table function. **/
void expect_near_hav(float theta_deg) {
    float slow_hav_result = SQ(sin(theta_deg * M_PI / 360.0));
    EXPECT_NEAR(slow_hav_result, hav_awb(static_cast<uint32_t>(theta_deg * INV_RESOLUTION)),
                MAX(kHaversineToleranceFrac * slow_hav_result, kHaversineToleranceFloor))
        << "Failed with theta_deg=" << theta_deg;
}

TEST(GeoUtils, HaversineAWB) {
    for (float theta_deg = 0.0f; theta_deg < 360.0f; theta_deg += 0.001f) {
        expect_near_hav(theta_deg);
    }
}

/** Test the havdiff to meters lookup table function. **/
TEST(GeoUtils, HavDiffToMeters) {
    for (float x = 0.0f; x < 1.0f; x += 0.001f) {
        uint32_t slow_havdiff_result_m = asin(sqrt(x)) * (2.0f * kEarthMeanRadiusMeters);
        EXPECT_NEAR(slow_havdiff_result_m, havdiff_to_m(x), kHavDiffToMetersToleranceFrac * slow_havdiff_result_m)
            << "Failed with x=" << x;
    }
}

/** Test the geoidal distance function. **/
TEST(GeoUtils, CalculateGeoidalDistance) {
    // Cross checking against this haversine calcualtor: https://www.movable-type.co.uk/scripts/latlong.html
    // Start with small hops
    EXPECT_NEAR(CalculateGeoidalDistanceMetersDeg(20.35f, -13.78f, 19.35f, -13.78f), 111200,
                111200 * kGeoDistanceToleranceFrac);  // -lat only
    EXPECT_NEAR(CalculateGeoidalDistanceMetersDeg(19.35f, -13.78f, 20.35f, -13.78f), 111200,
                111200 * kGeoDistanceToleranceFrac);  // +lat only
    EXPECT_NEAR(CalculateGeoidalDistanceMetersDeg(19.35f, -13.78f, 19.35f, -14.78f), 104900,
                104900 * kGeoDistanceToleranceFrac);  // -long only
    EXPECT_NEAR(CalculateGeoidalDistanceMetersDeg(19.35f, -13.78f, 19.35f, -12.78f), 104900,
                104900 * kGeoDistanceToleranceFrac);  // +long only

    // Bigger hop
    EXPECT_NEAR(CalculateGeoidalDistanceMetersDeg(20.35f, -13.78f, 320.2f, -50.99f), 7722e3f,
                7722e3f * kGeoDistanceToleranceFrac);
}