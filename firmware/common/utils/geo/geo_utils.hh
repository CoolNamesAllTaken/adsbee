#pragma once

/**
 * @brief Calculates the great circle distance along the surface of the earth between two lat/long coordinate sets.
 * @param[in] lat_a Latitude of coordinate A, in degrees. + for N, - for S.
 * @param[in] lon_a Longitude of coordinate A, in degrees. + for E, - for W.
 * @param[in] lat_b Latitude of coordinate B, in degrees. + for N, - for S.
 * @param[in] lon_b Longitude of coordinate B, in degrees. + for E, - for W.
 * @retval Great circle distance between points A and B.
 */
float CalculateGeoidalDistance(float lat_a_deg, float lon_a_deg, float lat_b_deg, float lon_b_deg);