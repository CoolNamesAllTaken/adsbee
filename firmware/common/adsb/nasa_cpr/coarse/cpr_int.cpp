/*
 * cpr_int.cc
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
#include "cpr_int.hh"

namespace nasa_cpr::coarse {

/* ======================================================== */
/* ==================== Util ============================== */
/* ======================================================== */

static int_type closest_mult_div_shift(int_type a, int_type x) {
    int_type q = times(x, div_shift(a, sub32nb));
    int_type r = div_shift(plus(div_shift(times(times(2, x), mod_uint(a, pow232nb)), sub32nb), 1), 1);
    return plus(q, r);
}

/* ======================================================== */
/* ================== Encoding ============================ */
/* ======================================================== */

int_type encoding(int_type nz, int_type awb_lat) {
    int_type mul = times(nz, awb_lat);
    int_type num = mul + pow2c31mb;
    int_type ans = div_shift(num, sub32nb);
    return (NB == 19 ? mod_uint(ans, 131072) : ans);
}

int_type rlat_int(int_type i, int_type awb_lat) {
    int_type ii = (i == 0 ? 60 : 59);  // = minus(60,i)
    int_type num = closest_mult_div_shift(awb_lat, ii);
    int_type ans = closest_div_mult(num, ii);
    return ans;
}

/* ======================================================== */
/* ==================== Local Decoding ==================== */
/* ======================================================== */

static int_type local_zone(int_type nz, int_type ref, int_type mes) {
    int_type y = (NB == 19 ? times(4, mes) : mes);
    int_type nzz = (NB == 19 ? times(4, nz) : nz);
    int_type a = pow2nb1;
    int_type b = times(nzz, div_shift(ref, sub32nb));
    int_type c = div_shift(times(nzz, mod_uint(ref, pow232nb)), sub32nb);
    int_type d = plus(a, plus(b, c));
    return (d < y ? minus(nzz, 1) : div_shift(minus(d, y), NB));
}

int_type local_decode(int_type nz, int_type ref, int_type mes) {
    int_type y = (NB == 19 ? times(4, mes) : mes);
    int_type nnz = (NB == 19 ? times(4, nz) : nz);
    int_type num = plus(times(pow2nb, local_zone(nz, ref, mes)), y);
    return closest_div_mult(num, nnz);
}

/* ======================================================== */
/* =================== Global Decoding ==================== */
/* ======================================================== */

static int_type global_zone(int_type nz, int_type mes0, int_type mes1, bool i) {
    int_type result = 0;
    if (nz > 1) {
        int_type a = plus(times(minus(nz, 1), mes0), pow2mnb116);
        int_type b = times(nz, mes1);
        int_type num = minus(plus(a, times(minus(nz, i), pow218)), b);
        result = mod_uint(div_shift(num, minNB17), minus(nz, i));
    }
    return result;
}

int_type global_decode(int_type nz, int_type mes0, int_type mes1, int_type i) {
    int_type mes = (i == 0 ? mes0 : mes1);
    int_type mmes = (NB == 19 ? 4 * mes : mes);
    int_type nzi = (1 <= minus(nz, i) ? minus(nz, i) : 1);
    int_type nnz = (NB == 19 ? 4 * nzi : nzi);
    int_type num = plus(times(pow2nb, global_zone(nz, mes0, mes1, i)), mmes);
    return closest_div_mult(num, nnz);
}

bool north_lat(int_type i, int_type mes0, int_type mes1, int_type own) {
    int_type diff = minus(global_decode(60, mes0, mes1, i), own);
    return diff <= 357913941 || 3937053355 <= diff;
}

}  // namespace nasa_cpr::coarse
