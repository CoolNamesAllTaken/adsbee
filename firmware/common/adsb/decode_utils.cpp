#include "decode_utils.hh"

#include <cmath>

const uint16_t callsign_char_array_len = 64;
char callsign_char_array[] = "#ABCDEFGHIJKLMNOPQRSTUVWXYZ##### ###############0123456789######";

char LookupCallsignChar(uint8_t value) {
    if (value >= callsign_char_array_len) {
        return '#';
    }
    return callsign_char_array[value];
}

uint16_t CalcNLCPRFromLat(float lat) {
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