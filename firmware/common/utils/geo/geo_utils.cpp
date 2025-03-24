#include "geo_utils.hh"

#include "awb_utils.h"
#include "geo_tables.hh"

float hav_awb(uint32_t theta_awb) {
    // Function: hav(theta) = (sin(theta * 0.5f))^2

    // Haversine function is symmetric about 180 degrees, so we map angles from 0-360 degrees to 0-180 degrees.
    if (theta_awb > UINT32_MAX / 2) {
        theta_awb = UINT32_MAX - theta_awb;
    }
    // TODO: wrap the end case
    // Simple lookup to floored index, no interpolation.
    uint32_t hav_index = theta_awb / ((UINT32_MAX / 2) / (kDeg180ToHavNumSteps - 1));
    return kDeg180ToHav[hav_index];
}

// /**
//  * @brief Calculates the great circle distance along the surface of the earth between two lat/long coordinate sets.
//  * @param[in] lat_a Latitude of coordinate A, in degrees. + for N, - for S.
//  * @param[in] lon_a Longitude of coordinate A, in degrees. + for E, - for W.
//  * @param[in] lat_b Latitude of coordinate B, in degrees. + for N, - for S.
//  * @param[in] lon_b Longitude of coordinate B, in degrees. + for E, - for W.
//  * @retval Great circle distance between points A and B.
//  */
// float CalculateGeoidalDistance(float lat_a, float lon_a, float lat_b, float lon_b) {
//     float lat_a_rad = DegreesToRadians(lat_a);
//     float lon_a_rad = DegreesToRadians(lon_a);
//     float lat_b_rad = DegreesToRadians(lat_b);
//     float lon_b_rad = DegreesToRadians(lon_b);

//     return 2 * kEarthMeanRadius *
//            asin(sqrt(hav(lat_b_rad - lat_a_rad) +
//                      (1 - hav(lat_a_rad - lat_b_rad) - hav(lat_a_rad + lat_b_rad)) * hav(lon_b_rad - lon_a_rad)));
// }