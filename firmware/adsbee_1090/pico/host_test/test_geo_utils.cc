#include <cmath>
#include <random>

#include "awb_utils.h"
#include "geo_utils.hh"
#include "gtest/gtest.h"
#include "macros.hh"

static const float kTrackToleranceDeg = 0.1f;
static const int32_t kSpeedToleranceKts = 1;

static uint32_t DegToAWB(double deg) { return static_cast<uint32_t>(static_cast<int64_t>(llround(deg / 360.0 * 4294967296.0))); }

/**
 * Reference geodesic distances (m) and initial azimuths (deg) on WGS-84 from GeographicLib (Karney's algorithm, accurate
 * to nanometers). Cases cover the equator, mid latitudes, near the poles, across the antimeridian and up to 600 km.
 */
struct GeodesicCase {
    double lat_a, lon_a, lat_b, lon_b, distance_m, azimuth_deg;
};
static const GeodesicCase kGeodesicCases[] = {
    // lat_a, lon_a, lat_b, lon_b, s12 (m), azi1 (deg)
    {0, 0, 1, 0, 110574.389, 0.000},
    {0, 0, 0, 1, 111319.491, 90.000},
    {37.4, -122, 37.5, -122, 11098.610, 0.000},
    {37.4, -122, 38.4, -121, 141614.458, 38.087},
    {37.4, -122, 32, -117.5, 726986.975, 144.157},
    {52, 4.5, 51, 6, 152400.157, 136.298},
    {-33.9, 151.2, -34.9, 148.9, 238801.501, 241.675},
    {60, 179.5, 60.5, -179, 100014.545, 55.503},    // Across the antimeridian.
    {-10, -179.9, -11, 179, 163505.459, 227.331},
    {85, 0, 86, 90, 714820.065, 38.741},            // Near the north pole.
    {89.5, 10, 89.5, -170, 111693.951, 0.000},      // Across the north pole.
    {-88, 45, -86, -135, 670155.630, 180.000},      // Across the south pole.
    {12.34, 56.78, 12.341, 56.781, 155.137, 44.514},  // Short hop.
};

TEST(GeoUtils, DistanceAndBearingMatchGeodesic) {
    for (const auto &c : kGeodesicCases) {
        GeoReference ref(DegToAWB(c.lat_a), DegToAWB(c.lon_a));
        uint32_t distance_m;
        uint16_t bearing_bam16;
        CalculateDistanceAndBearing(ref, DegToAWB(c.lat_b), DegToAWB(c.lon_b), distance_m, bearing_bam16);
        // 0.015% + 1 m up to 600 km, 0.15% beyond.
        double tolerance_m = c.distance_m < 600e3 ? 0.00015 * c.distance_m + 1.0 : 0.0015 * c.distance_m;
        EXPECT_NEAR(distance_m, c.distance_m, tolerance_m) << c.lat_a << "," << c.lon_a << " -> " << c.lat_b << ","
                                                           << c.lon_b;
        double bearing_error_deg = fmod(Bam16ToDeg(bearing_bam16) - c.azimuth_deg + 540.0, 360.0) - 180.0;
        EXPECT_LT(fabs(bearing_error_deg), 0.2) << c.lat_a << "," << c.lon_a << " -> " << c.lat_b << "," << c.lon_b;
        EXPECT_EQ(distance_m, CalculateGeoidalDistanceMetersAWB(DegToAWB(c.lat_a), DegToAWB(c.lon_a), DegToAWB(c.lat_b),
                                                                DegToAWB(c.lon_b)));
    }
}

TEST(GeoUtils, DistanceEdgeCases) {
    // Same point, anywhere.
    for (double lat : {-90.0, -45.0, 0.0, 45.0, 90.0}) {
        EXPECT_EQ(CalculateGeoidalDistanceMetersAWB(DegToAWB(lat), DegToAWB(10.0), DegToAWB(lat), DegToAWB(10.0)), 0u);
    }
    // The poles are one point whatever the longitude.
    EXPECT_LE(CalculateGeoidalDistanceMetersAWB(DegToAWB(90.0), 0, DegToAWB(90.0), DegToAWB(123.0)), 1u);
    // Antipodes: half the meridian (20003931 m).
    EXPECT_NEAR(CalculateGeoidalDistanceMetersAWB(0, 0, 0, DegToAWB(180.0)), 20003931, 1);
    EXPECT_NEAR(CalculateGeoidalDistanceMetersAWB(DegToAWB(90.0), 0, DegToAWB(-90.0), 0), 20003931, 1);
    // Symmetric within the error bound (the radius of curvature follows the bearing at the start point).
    EXPECT_NEAR(CalculateGeoidalDistanceMetersAWB(DegToAWB(40.0), DegToAWB(-100.0), DegToAWB(42.0), DegToAWB(-97.0)),
                CalculateGeoidalDistanceMetersAWB(DegToAWB(42.0), DegToAWB(-97.0), DegToAWB(40.0), DegToAWB(-100.0)),
                0.0003 * 336000);
}

TEST(GeoUtils, CalculateGeoidalDistanceDeg) {
    EXPECT_NEAR(CalculateGeoidalDistanceMetersDeg(20.35f, -13.78f, 19.35f, -13.78f), 110702, 20);
    EXPECT_NEAR(CalculateGeoidalDistanceMetersDeg(19.35f, -13.78f, 19.35f, -14.78f), 105070, 20);
}

TEST(GeoUtils, SinCosQ30) {
    for (double deg = -360.0; deg <= 360.0; deg += 0.0137) {
        int32_t s, c;
        SinCosQ30(DegToAWB(deg), s, c);
        double rad = deg * M_PI / 180.0;
        EXPECT_NEAR(s / 1073741824.0, sin(rad), 5e-9) << deg;
        EXPECT_NEAR(c / 1073741824.0, cos(rad), 5e-9) << deg;
    }
}

TEST(GeoUtils, BearingCardinalDirections) {
    GeoReference ref(DegToAWB(10.0), DegToAWB(20.0));
    uint32_t d;
    uint16_t b;
    CalculateDistanceAndBearing(ref, DegToAWB(10.5), DegToAWB(20.0), d, b);
    EXPECT_NEAR(Bam16ToDeg(b), 0.0f, 0.01f);
    CalculateDistanceAndBearing(ref, DegToAWB(10.0), DegToAWB(20.5), d, b);
    EXPECT_NEAR(Bam16ToDeg(b), 89.957f, 0.01f);  // A parallel is not a great circle: slightly north of east.
    CalculateDistanceAndBearing(ref, DegToAWB(9.5), DegToAWB(20.0), d, b);
    EXPECT_NEAR(Bam16ToDeg(b), 180.0f, 0.01f);
    CalculateDistanceAndBearing(ref, DegToAWB(10.0), DegToAWB(19.5), d, b);
    EXPECT_NEAR(Bam16ToDeg(b), 270.043f, 0.01f);
}

TEST(GeoUtils, IsDistanceGreaterThanAgreesWithDistance) {
    // Random pairs around thresholds: the integer bounds must never contradict the full calculation by more than its
    // error, and must agree exactly away from the threshold.
    std::mt19937 rng(455);
    std::uniform_real_distribution<double> lat_dist(-89.9, 89.9), lon_dist(-180.0, 180.0), off(-3.0, 3.0);
    for (int i = 0; i < 20000; i++) {
        double lat = lat_dist(rng), lon = lon_dist(rng);
        uint32_t a_lat = DegToAWB(lat), a_lon = DegToAWB(lon);
        uint32_t b_lat = DegToAWB(fmax(-90.0, fmin(90.0, lat + off(rng)))), b_lon = DegToAWB(lon + 2 * off(rng));
        uint32_t d = CalculateGeoidalDistanceMetersAWB(a_lat, a_lon, b_lat, b_lon);
        for (uint32_t threshold_m : {20000u, 50000u, 200000u}) {
            bool greater = IsDistanceGreaterThan(a_lat, a_lon, b_lat, b_lon, threshold_m);
            if (d > threshold_m * 1.0002 + 1) {
                EXPECT_TRUE(greater) << d << " vs " << threshold_m;
            } else if (d < threshold_m * 0.9998 - 1) {
                EXPECT_FALSE(greater) << d << " vs " << threshold_m;
            }
        }
    }
}

/** Test track and speed calculation from NE velocity components. **/
void expect_track_and_speed(int32_t n_vel_kts, int32_t e_vel_kts, float expected_track_deg,
                            int32_t expected_speed_kts) {
    float track_deg = 0.0f;
    int32_t speed_kts = 0;
    CalculateTrackAndSpeedFromNEVelocities(n_vel_kts, e_vel_kts, track_deg, speed_kts);
    EXPECT_NEAR(expected_track_deg, track_deg, kTrackToleranceDeg)
        << "Track failed for n=" << n_vel_kts << " e=" << e_vel_kts;
    EXPECT_NEAR(expected_speed_kts, speed_kts, kSpeedToleranceKts)
        << "Speed failed for n=" << n_vel_kts << " e=" << e_vel_kts;
}

TEST(GeoUtils, CalculateTrackAndSpeed_Table) {
    expect_track_and_speed(100, 0, 0.0f, 100);     // Due north
    expect_track_and_speed(0, 100, 90.0f, 100);    // Due east
    expect_track_and_speed(-100, 0, 180.0f, 100);  // Due south
    expect_track_and_speed(0, -100, 270.0f, 100);  // Due west
    expect_track_and_speed(100, 100, 45.0f, 141);  // NE diagonal: speed = sqrt(2)*100 ≈ 141
}
