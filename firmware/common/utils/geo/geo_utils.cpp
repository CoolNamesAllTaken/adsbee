#include "geo_utils.hh"

#include "awb_utils.h"
#include "comms.hh"
#include "fixedmath/fixed_math.hpp"
#include "geo_tables.hh"
#include "macros.hh"

// Interpolation increases execution time but decreases the size of the tables required to be stored in flash to achieve
// a given precision.
#define INTERPOLATE_HAV_AWB
#define INTERPOLATE_HAVDIFF_TO_M

static const uint32_t kEarthMeanRadiusMeters = 6372798;  // Quadratic mean radius for WS-84.
// 2 * PI * kEarthMeanRadiusMeters * kBoundingBoxDeltaLatAWB / UINT32_MAX = kBoundingBoxDimensionMeters
static const uint32_t kBoundingBoxDeltaAWB =
    kBoundingBoxDimensionMeters * (UINT32_MAX / static_cast<uint32_t>(2 * kEarthMeanRadiusMeters * M_PI));

static const uint32_t kAWBPerHavSteps =
    (UINT32_MAX / 2) / (kDeg180ToHavNumSteps - 1);  // Number of AWB values per haversine table step

const fixedmath::fixed_t kDegPerRadian =
    fixedmath::fixed_t{180.0f / M_PI};  // Conversion factor from radians to degrees.

float hav_awb(uint32_t theta_awb) {
    // Function: hav(theta) = (sin(theta * 0.5f))^2

    // Haversine function is symmetric about 180 degrees, so we map angles from 0-360 degrees to 0-180 degrees.
    if (theta_awb > UINT32_MAX / 2) {
        theta_awb = UINT32_MAX - theta_awb;
    }

#ifndef INTERPOLATE_HAV_AWB
    // Simple lookup to floored index, no interpolation.
    uint32_t hav_index = theta_awb / kAWBPerHavSteps;
    return kDeg180ToHav[hav_index];
#else
    // Interpolate between the two closest values in the lookup table.
    uint32_t hav_index = theta_awb / kAWBPerHavSteps;
    uint32_t hav_overshoot_awb = theta_awb % kAWBPerHavSteps;
    return kDeg180ToHav[hav_index] * (kAWBPerHavSteps - hav_overshoot_awb) / kAWBPerHavSteps +
           kDeg180ToHav[hav_index + 1] * hav_overshoot_awb / kAWBPerHavSteps;
#endif
}

float havdiff_to_m(float x) {
    if (x < 0.0f) {
        CONSOLE_ERROR("geo_utils::havdiff_to_m", "x must be >= 0.0f, but got %f.", x);
        return 0.0f;
    }
#ifndef INTERPOLATE_HAVDIFF_TO_M
    // Simple lookup to floored index, no interpolation.
    return kHavdiffToMeters[static_cast<uint32_t>(x * (kHavdiffToMetersNumSteps - 1))];
#else
    // Interpolate between the two closest values in the lookup table.
    float havdiff_index_float = x * (kHavdiffToMetersNumSteps - 1);
    // Casting float to unsigned int is safe here because havdiff_index_float is always >= 0.0f.
    uint32_t havdiff_index_rounded = static_cast<uint32_t>(havdiff_index_float);
    float havdiff_overshoot_frac = fmodf(havdiff_index_float, 1.0f);
    return kHavdiffToMeters[havdiff_index_rounded] * (1.0f - havdiff_overshoot_frac) +
           kHavdiffToMeters[havdiff_index_rounded + 1] * havdiff_overshoot_frac;
#endif
}

uint32_t CalculateGeoidalDistanceMetersAWB(uint32_t lat_a_awb, uint32_t lon_a_awb, uint32_t lat_b_awb,
                                           uint32_t lon_b_awb) {
    // The only floating point operations here are the additions and a single multiply within the havdiff_to_m call,
    // since I didn't want to deal with fixed point multiplication with the need for high resolution.
    return havdiff_to_m(hav_awb(lat_b_awb - lat_a_awb) +
                        (1 - hav_awb(lat_a_awb - lat_b_awb) - hav_awb(lat_a_awb + lat_b_awb)) *
                            hav_awb(lon_b_awb - lon_a_awb));
}

uint32_t CalculateGeoidalDistanceMetersDeg(float lat_a_deg, float lon_a_deg, float lat_b_deg, float lon_b_deg) {
    // Convert degrees to Angular Weighted Binary format.
    // Cast floats to signed ints, then to unsigned ints, to avoid undefined behavior with negative floats.
    uint32_t lat_a_awb = safe_cast_float_to_uint32(INV_RESOLUTION * lat_a_deg);
    uint32_t lon_a_awb = safe_cast_float_to_uint32(INV_RESOLUTION * lon_a_deg);
    uint32_t lat_b_awb = safe_cast_float_to_uint32(INV_RESOLUTION * lat_b_deg);
    uint32_t lon_b_awb = safe_cast_float_to_uint32(INV_RESOLUTION * lon_b_deg);

    return CalculateGeoidalDistanceMetersAWB(lat_a_awb, lon_a_awb, lat_b_awb, lon_b_awb);
}

inline fixedmath::fixed_t wrapped_atan2(fixedmath::fixed_t y, fixedmath::fixed_t x) {
    fixedmath::fixed_t val = fixedmath::func::atan2(y, x);
    return val < fixedmath::fixed_t(0) ? (val + fixedmath::fixed_t(2.0f * M_PI)) : val;
}

void CalculateTrackAndSpeedFromNEVelocities(int n_vel_kts, int e_vel_kts, float &track_deg, int &speed_kts) {
    track_deg = static_cast<float>(
        wrapped_atan2(static_cast<fixedmath::fixed_t>(e_vel_kts), static_cast<fixedmath::fixed_t>(n_vel_kts)) *
        kDegPerRadian);
    fixedmath::fixed_t speed_kts_fixed =
        fixedmath::func::sqrt(static_cast<fixedmath::fixed_t>(n_vel_kts * n_vel_kts + e_vel_kts * e_vel_kts));
    // Round speed_kts_fixed.
    if (speed_kts_fixed % fixedmath::fixed_t(1) >= fixedmath::fixed_t(0.5f)) {
        speed_kts_fixed += fixedmath::fixed_t(1);
    }
    speed_kts = static_cast<int16_t>(speed_kts_fixed);
}
