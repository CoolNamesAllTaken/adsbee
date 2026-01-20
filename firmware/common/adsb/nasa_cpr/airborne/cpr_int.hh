/*
 * cpr_int.hh
 *
 * Contact: Cesar Munoz
 * Organization: NASA/Langley Research Center
 *
 * This software may be used, reproduced, and provided to others only as
 * permitted under the terms of the agreement under which it was acquired from
 * the U.S. Government. Neither title to, nor ownership of, the software is
 * hereby transferred. This notice shall remain on all copies of the software.
 *
 * Copyright 2019 United States Government as represented by the Administrator
 * of the National Aeronautics and Space Administration. All Rights Reserved.
 *
 * Converted to C++ with namespace by Claude 2025-01-20.
 */
#pragma once

#include <cstdint>
#include <cstdlib>

namespace nasa_cpr::airborne {

#define MAX(X, Y)       ((X) > (Y) ? (X) : (Y))
using int_type = uint32_t;

inline int_type times(int_type X, int_type Y) { return (X) * (Y); }
inline int_type plus(int_type X, int_type Y) { return (X) + (Y); }
inline int_type minus(int_type X, int_type Y) { return (X) - (Y); }
inline int_type div_shift(int_type X, int_type Y) { return (X) >> (Y); }
inline int_type mod_uint(int_type X, int_type Y) { return (X) % (Y); }
inline int_type div(int_type X, int_type Y) { return (X) / (Y); }

constexpr int_type pow206 = 64;
constexpr int_type pow216 = 65536;
constexpr int_type pow217 = 131072;
constexpr int_type pow218 = 262144;
constexpr int_type pow230 = 1073741824;
constexpr uint64_t pow231 = 2147483648ULL;
constexpr uint64_t pow232 = 4294967296ULL;

constexpr int NB = 17;  // Airborne

// Precalculated Constants for NB == 17 (Airborne)
constexpr int_type pow232nb1 = 65536;   // = 2^(32-(NB-1))
constexpr int_type pow232nb = 32768;    // = 2^(32-NB)
constexpr int_type pow2nb1 = 65536;     // = 2^(NB-1)
constexpr int_type pow2nb = 131072;     // = 2^NB
constexpr int sub32nb = 15;             // = 32-NB
constexpr int minNB17 = 17;             // = min(NB,17)
constexpr int_type pow2mnb116 = 65536;  // = min(2^(NB-1),2^16)
constexpr int_type pow2c31mb = 16384;

/* ======================================================== */
/* ================= Logic Operations ===================== */
/* ======================================================== */

inline int_type closest_div_mult(int_type num, int_type den) {
    return (den == 1 ? times(pow232nb, num)
                     : plus(times(pow232nb, div(num, den)),
                            div(plus(div(times(pow232nb1, mod_uint(num, den)), den), 1), 2)));
}

/* ======================================================== */
/* ============== Function Declarations =================== */
/* ======================================================== */

int_type nl_awb(int_type awb);
int_type encoding(int_type nz, int_type awb_lat);
int_type rlat_int(int_type i, int_type awb_lat);
int_type local_decode(int_type nz, int_type ref, int_type mes);
int_type global_decode(int_type nz, int_type mes0, int_type mes1, int_type i);
bool north_lat(int_type i, int_type mes0, int_type mes1, int_type own);

}  // namespace nasa_cpr::airborne
