#pragma once

#include "stdint.h"

/**
 * @brief Calculates the great circle distance along the surface of the earth between two lat/long coordinate sets.
 * @param[in] lat_a Latitude of coordinate A, in degrees. + for N, - for S.
 * @param[in] lon_a Longitude of coordinate A, in degrees. + for E, - for W.
 * @param[in] lat_b Latitude of coordinate B, in degrees. + for N, - for S.
 * @param[in] lon_b Longitude of coordinate B, in degrees. + for E, - for W.
 * @retval Great circle distance between points A and B.
 */
float CalculateGeoidalDistance(float lat_a_deg, float lon_a_deg, float lat_b_deg, float lon_b_deg);

/**
 * @brief Calculates the haversine of an angle, in radians. Exposed for testing.
 * @param[in] theta_awb Angle from 0-360 degrees in Alternative Weighted Binary format, where 0 is 0 degrees and
 * UINT32_MAX is 360 degrees.
 * @retval Haversine of theta.
 */
float hav_awb(uint32_t theta_awb);