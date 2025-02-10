#pragma once

/**
 * Utilities ripped from the NASA CPR verification code in otder to allow conversion from floating point representation
 * of postiions to Alternative Weighted Binary, the fixed point representation used by the CPR decoder library.
 */

#include "math.h"
#include "stdint.h"

#define RESOLUTION        360.0f / 4294967296.0f  // = 360/2^32
#define INV_RESOLUTION    4294967296.0f / 360.0f  // = 2^32/360
// simple in-line abs(X-Y)
#define __diffabs__(X, Y) (X >= Y ? X - Y : Y - X)
// simple modulus operation (correct for X in [-359,(2*360-1)])
#define __mod360__(X)     (X >= 360 ? X - 360 : (X < 0 ? 360 + X : X))

/**
 * Convert an Alternative Weighted Binary latitude to a floating point representation.
 * @param[in] awb_lat The Alternative Weighted Binary latitude to convert.
 * @return The floating point representation of the latitude, in degrees.
 */
inline float awb2lat(uint32_t awb_lat) {
    if (awb_lat <= 107374182u)  // 2^30
        return awb_lat * RESOLUTION;
    else
        return awb_lat * RESOLUTION - 360.0f;
}

/**
 * Convert an Alternative Weighted Binary longitude to a floating point representation.
 * @param[in] awb_lon The Alternative Weighted Binary longitude to convert.
 * @return The floating point representation of the longitude, in degrees.
 */
inline float awb2lon(int_type awb_lon) { return __mod360__(awb_lon * RESOLUTION); }

/**
 * Convert a floating point latitude to an Alternative Weighted Binary representation.
 * @param[in] lat The latitude to convert.
 * @return The Alternative Weighted Binary representation of the latitude.
 */
inline uint32_t lat2awb(float lat) { return (uint32_t)floor(INV_RESOLUTION * __mod360__(lat) + 0.5f); }

/**
 * Convert an Alternative Weighted Binary longitude to a floating point representation.
 * @param[in] awb_lon The Alternative Weighted Binary longitude to convert.
 * @return The floating point representation of the longitude.
 */
inline uint32_t lon2awb(float lon) { return (uint32_t)floor(lon * INV_RESOLUTION + 0.5f); }