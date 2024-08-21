#ifndef DECODE_UTILS_HH_
#define DECODE_UTILS_HH_

#include <cstdint>

const uint16_t kCPRNz = 15;                           // number of latitude zones between equator and a pole
const float kCPRdLatEven = 360.0f / (4 * kCPRNz);     // size of latitude zone for even message
const float kCPRdLatOdd = 360.0f / (4 * kCPRNz - 1);  // size of latitude zone for odd message
const uint32_t kCPRLatLonMaxCount = (2 << 16) - 1;    // 2^17

/**
 * Converts a numeric value into an ASCII character for use in decoding callsigns.
 * @param[in] value 6-bit value to lookup.
 * @retval Character that matches the input value. If the input value is invalid or unused, returns '#'.
 */
char LookupCallsignChar(uint8_t value);

inline uint8_t GrayCodeNibbleToBinaryNibble(uint8_t gray_code_nibble) {
    switch (gray_code_nibble) {
        case 0b0000:
            return 0;
        case 0b0001:
            return 1;
        case 0b0011:
            return 2;
        case 0b0010:
            return 3;
        case 0b0110:
            return 4;
        case 0b0111:
            return 5;
        case 0b0101:
            return 6;
        case 0b0100:
            return 7;
        case 0b1100:
            return 8;
        case 0b1101:
            return 9;
        case 0b1111:
            return 10;
        case 0b1110:
            return 11;
        case 0b1010:
            return 12;
        case 0b1011:
            return 13;
        case 0b1001:
            return 14;
        case 0b1000:
            return 15;
    }
    return 0;
}

/**
 * Calculate the number of longituide zones (between 1 and 59) at a given latitude.
 * @param[in] lat Latitude to calculate NL (number of longitude zones) at.
 * @retval NL (number of longitude zones) in the Compact Position Reporting (CPR) representation at the given latitude.
 */
uint16_t CalcNLCPRFromLat(float lat);

/**
 * Wrap southern hemisphere latitudes resulting from CPR decode. Transforms latitude from [270, 360] to [-90, 90].
 * @param[in] latitude Latitude in degrees.
 * @retval Wrapped latitude.
 */
inline float WrapCPRDecodeLatitude(float latitude) { return latitude >= 270.0f ? latitude - 360.0f : latitude; }

/**
 * Wrap longitude floating point value to conventional values. Transforms longitude from [0, 360] to [-180, 180].
 * @param[in] longitude Longitude in degrees.
 * @retval Wrapped longitude.
 */
inline float WrapCPRDecodeLongitude(float longitude) { return longitude >= 180.0f ? longitude - 360.0f : longitude; }

#endif /* DECODE_UTILS_HH_ */