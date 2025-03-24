#pragma once

#include "stdint.h"

static const uint32_t kBoundingBoxDimensionMeters = 50'000;

bool IsWithinBoundingBox(uint32_t lat_a_awb, uint32_t lon_a_awb, uint32_t lat_b_awb, uint32_t lon_b_awb);

/**
 * @brief Calculates the great circle distance along the surface of the earth between two lat/long coordinate sets.
 * @param[in] lat_a_awb Latitude of coordinate A, in Alternative Weighted Binary format.
 * @param[in] lon_a_awb Longitude of coordinate A, in Alternative Weighted Binary format.
 * @param[in] lat_b_awb Latitude of coordinate B, in Alternative Weighted Binary format.
 * @param[in] lon_b_awb Longitude of coordinate B, in Alternative Weighted Binary format.
 * @retval Great circle distance between points A and B, in meters.
 */
uint32_t CalculateGeoidalDistanceMetersAWB(uint32_t lat_a_awb, uint32_t lon_a_awb, uint32_t lat_b_awb,
                                           uint32_t lon_b_awb);

uint32_t CalculateGeoidalDistanceMetersDeg(float lat_a_deg, float lon_a_deg, float lat_b_deg, float lon_b_deg);

/**
 * @brief Calculates the haversine of an angle, in radians. Exposed for testing.
 * @param[in] theta_awb Angle from 0-360 degrees in Alternative Weighted Binary format, where 0 is 0 degrees and
 * UINT32_MAX is 360 degrees.
 * @retval Haversine of theta.
 */
float hav_awb(uint32_t theta_awb);

/**
 * @brief Calculates distance between to points on Earth given a float as an input that is equivalent to the
 * following expression:
 *      hav(lat_b_rad - lat_a_rad)
 *      + (1 - hav(lat_a_rad - lat_b_rad) - hav(lat_a_rad + lat_b_rad)) * hav(lon_b_rad - lon_a_rad)
 *
 * This function uses a lookup table to calculate 2 * kEarthMeanRadius * asin(sqrt(x)), where x is an input float
 * between 0.0f and 1.0f.
 * @param[in] x Result of the haversine expression
 */
float havdiff_to_m(float x);