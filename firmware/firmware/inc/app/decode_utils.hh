#ifndef _DECODE_UTILS_HH_
#define _DECODE_UTILS_HH_

#include <cstdint>

const uint16_t kCPRNz = 15; // number of latitude zones between equator and a pole
const float kCPRdLatEven = 360.0f / (4 * kCPRNz); // size of latitude zone for even message
const float kCPRdLatOdd = 360.0f / (4 * kCPRNz - 1); // size of latitude zone for odd message
const uint32_t kCPRMaxCount = 2 << 16; // 2^17

char lookup_callsign_char(uint8_t value);
uint16_t calc_nl_cpr_from_lat(float lat);
// int32_t calc_cpr_lat_zone_index(uint32_t n_lat_cpr_even, uint32_t n_lat_cpr_odd);

#endif /* _DECODE_UTILS_HH_ */