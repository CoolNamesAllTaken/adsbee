#include "decode_utils.hh"

#include <cmath>

const uint16_t callsign_char_array_len = 64;
char callsign_char_array[] = "#ABCDEFGHIJKLMNOPQRSTUVWXYZ##### ###############0123456789######";

/**
 * Converts a numeric value into an ASCII character for use in decoding callsigns.
 * @param[in] value 6-bit value to lookup.
 * @retval Character that matches the input value. If the input value is invalid or unused, returns '#'.
 */
char lookup_callsign_char(uint8_t value) {
    if (value >= callsign_char_array_len) {
        return '#';
    }
    return callsign_char_array[value];
}

/**
 * Calculate the number of longituide zones (between 1 and 59) at a given latitude.
 * @param[in] lat Latitude to calculate NL (number of longitude zones) at.
 * @retval NL (number of longitude zones) in the Compact Position Reporting (CPR) representation at the given latitude.
 */
uint16_t calc_nl_cpr_from_lat(float lat) {
    lat = floorf(lat);

    // Special cases.
    if (lat == 0) {
        return 59;  // On the equator.
    } else if (lat == 87) {
        return 2;  // Near the north pole.
    } else if (lat == -87) {
        return 2;  // Near the south pole.
    } else if (lat > 87) {
        return 1;  // In the north pole bin.
    } else if (lat < -87) {
        return 1;  // In the south pole bin.
    }

    // Equation 5.3
    return floorf(2.0f * (float)M_PI /
                  acosf(1 - (1 - cosf((float)M_PI / (2.0f * kCPRNz))) / powf(cosf((float)M_PI / 180.0f * lat), 2)));
}

float wrap_latitude(float latitude) { return latitude >= 270.0f ? latitude - 360.0f : latitude; }

float wrap_longitude(float longitude) { return longitude >= 180.0f ? longitude - 360.0f : longitude; }

// bool calc_lat_from_cpr(uint32_t n_lat_cpr_even, uint32_t n_lat_cpr_odd, float &lat, uint16_t &nl) {
//     // Equation 5.5
//     float lat_cpr_even = n_lat_cpr_even / kCPRMaxCount;
//     float lat_cpr_odd = n_lat_cpr_odd / kCPRMaxCount;

//     // Equation 5.6
//     int32_t lat_zone_index = floorf(59.0f * lat_cpr_even - 60.0f * lat_cpr_odd + 0.5f);

//     // Equation 5.7
//     float lat_even = kCPRdLatEven * ((lat_zone_index % 60) + lat_cpr_even);
//     float lat_odd = kCPRdLatOdd * ((lat_zone_index % 59) + lat_cpr_odd);

//     // Equation 5.8
//     lat_even = lat_even >= 270 ? lat_even : lat_even - 360.0f;
//     lat_odd = lat_odd >= 270 ? lat_odd : lat_odd - 360.0f;
// }
