/*
 * cpr_int.c
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
 */
#include "airborne/cpr_int.h"

/* ======================================================== */
/* ==================== Util ============================== */
/* ======================================================== */

// closest_mult_div_shift(a,x) = CPR@uint32.closest_mult_div_shift(a,x,32-NB)

/*@
axiomatic utils {
  logic integer closest_mult_div_shift(integer a, integer x)
  = \let q = mul_u32(x, div_shift(a,sub32nb));
    \let r = div_shift(add_u32(div_shift(mul_u32(mul_u32(2,x),mod_u32(a,pow232nb)),sub32nb),1),1);
    add_u32(q, r);
}
*/

/*@
  ensures \result == closest_mult_div_shift(a,x);
*/
int_type closest_mult_div_shift(int_type a, int_type x) {
    int_type q = times(x, div_shift(a, sub32nb));
    int_type r = div_shift(plus(div_shift(times(times(2, x), mod_uint(a, pow232nb)), sub32nb), 1), 1);
    return plus(q, r);
}

/* ======================================================== */
/* ================== Encoding ============================ */
/* ======================================================== */

/*@
axiomatic encode {
  logic integer encoding(integer nz, integer awb_lat, integer b)
  = \let pow231b_ = (b==12? 524288
                  :(b==14? pow217
                  :(b==17?  16384
                  :(b==19?   4096 : -1)))); // = \pow(2,(32-(b+1)))
    \let mul = mul_u32(nz,awb_lat);
    \let num = add_u32(mul,pow231b_);
    \let ans = shr_u32(num,(32-b));
    (b==19 ? mod_u32(ans,pow217) : ans);

  // b in cpr_int.rlat_int is assumed to be equal to NB (defined in cpr_int.h)
  logic integer rlat_int(integer i, integer awb_lat)
  = \let ii = (i==0 ? 60 : 59); // = sub_u32(60,i)
    \let num = closest_mult_div_shift(awb_lat, ii);
    \let ans = l_closest_div_mult(num, ii);
    ans;
}
*/

/* requires b==12 || b==14 || b==17 || b==19;
    ensures \result == encoding(nz,awb_lat,b);

int_type encoding(int_type nz, int_type awb_lat, int_type b){
  int_type pow2c31mb = (b==12? 524288
                     : (b==14? pow217
                     : (b==17?  16384
                     : (b==19?   4096 : -1 )))); // = \pow(2,(32-(b+1)))
  int_type mul = times(nz,awb_lat);
  int_type num = mul + pow2c31mb;
  int_type ans = div_shift(num, (32-b));
  return ( b==19 ? mod_uint(ans, 131072) : ans );
}
 */
/*@ ensures \result == encoding(nz,awb_lat,nb);
 */
int_type encoding(int_type nz, int_type awb_lat) {
    int_type mul = times(nz, awb_lat);
    int_type num = mul + pow2c31mb;
    int_type ans = div_shift(num, sub32nb);
    return (NB == 19 ? mod_uint(ans, 131072) : ans);
}

/*@ requires i==0 || i==1;
    ensures \result == rlat_int(i,awb_lat);
 */
int_type rlat_int(int_type i, int_type awb_lat) {
    int_type ii = (i == 0 ? 60 : 59);  // = minus(60,i)
    int_type num = closest_mult_div_shift(awb_lat, ii);
    int_type ans = closest_div_mult(num, ii);
    return ans;
}

/* ======================================================== */
/* ==================== Local Decoding ==================== */
/* ======================================================== */

/*@
axiomatic local_decoding {
  logic integer local_zone(integer nz, integer ref, integer mes)
  = \let y   = ( NB == 19 ? mul_u32(4,mes) : mes );
    \let nzz = ( NB == 19 ? mul_u32(4,nz) : nz );
    \let a   = pow2nb1;
    \let b   = mul_u32(nzz, div_shift(ref, sub32nb));
    \let c   = div_shift(mul_u32(nzz, mod_u32(ref, pow232nb)), sub32nb);
    \let d   = add_u32(a, add_u32(b, c));
    (d < y ? sub_u32(nzz,1) : div_shift(sub_u32(d, y), NB));

  logic integer local_decode(integer nz, integer ref, integer mes)
  = \let y   = ( NB == 19 ? mul_u32(4,mes) : mes );
    \let nnz = ( NB == 19 ? mul_u32(4,nz) : nz );
    \let num = add_u32(mul_u32(pow2nb, local_zone(nz, ref, mes)), y);
    (nz==0? 0 : l_closest_div_mult(num, nnz));
} */

/*@ requires nz < pow206;
    requires mes < pow217;
    ensures \result == local_zone(nz,ref,mes);
 */
int_type local_zone(int_type nz, int_type ref, int_type mes) {
    int_type y = (NB == 19 ? times(4, mes) : mes);
    int_type nzz = (NB == 19 ? times(4, nz) : nz);
    int_type a = pow2nb1;
    int_type b = times(nzz, div_shift(ref, sub32nb));
    int_type c = div_shift(times(nzz, mod_uint(ref, pow232nb)), sub32nb);
    int_type d = plus(a, plus(b, c));
    return (d < y ? minus(nzz, 1) : div_shift(minus(d, y), NB));
}

/*@ requires 0 < nz < pow206;
    requires mes < pow217;
    ensures \result == local_decode(nz,ref,mes);
 */
int_type local_decode(int_type nz, int_type ref, int_type mes) {
    int_type y = (NB == 19 ? times(4, mes) : mes);
    int_type nnz = (NB == 19 ? times(4, nz) : nz);
    int_type num = plus(times(pow2nb, local_zone(nz, ref, mes)), y);
    return closest_div_mult(num, nnz);
}

/* ======================================================== */
/* =================== Global Decoding ==================== */
/* ======================================================== */

/*@
axiomatic global_decoding {
  logic integer global_zone(integer nz, integer mes0, integer mes1, integer i);

  axiom global_zone__def_0 :
    \forall integer nz, integer mes0, integer mes1, integer i;
    0 <= i <= 1 ==> global_zone(1,mes0,mes1,i) == 0;

  axiom global_zone__def_1 :
    \forall integer nz, integer mes0, integer mes1, integer i;
    0 <= i <= 1 &&
    1 < nz < pow206
    ==> global_zone(nz,mes0,mes1,i)
        == \let a   = add_u32(mul_u32(sub_u32(nz,1),mes0),pow2mnb116);
           \let b   = mul_u32(nz,mes1);
           \let num = sub_u32(add_u32(a,mul_u32(sub_u32(nz,i),pow218)), b);
           mod_u32(div_shift(num, minNB17), sub_u32(nz,i));

  logic integer global_decode(integer nz, integer mes0, integer mes1, integer i)
  = \let mes  = ( i  == 0  ? mes0 : mes1 );
    \let mmes = ( NB == 19 ? mul_u32(4,mes) : mes );
    \let nzi  = \max(sub_u32(nz,i), 1);
    \let nnz  = ( NB == 19 ? mul_u32(4,nzi) : nzi );
    \let num  = add_u32(mul_u32(pow2nb, global_zone(nz, mes0, mes1, i)), mmes);
    l_closest_div_mult(num, nnz);

  predicate north_lat(integer i, integer mes0, integer mes1, integer own)
  = \let diff = sub_u32(global_decode(60,mes0,mes1,i), own);
    diff<=357913941      // ~ 2^30/3 = 30 degrees.
    || 3937053355<=diff; // ~ 2^32-2^30/3 = -30 degrees.

}
 */

/*@ requires 0 < nz < pow206;
    requires mes0 < \min(pow217,pow2nb);
    requires mes1 < \min(pow217,pow2nb);
    requires 0 <= i <= 1;
    ensures \result == global_zone(nz,mes0,mes1,i);
 */
int_type global_zone(int_type nz, int_type mes0, int_type mes1, bool i) {
    int_type result = 0;
    if (nz > 1) {
        int_type a = plus(times(minus(nz, 1), mes0), pow2mnb116);
        int_type b = times(nz, mes1);
        int_type num = minus(plus(a, times(minus(nz, i), pow218)), b);
        result = mod_uint(div_shift(num, minNB17), minus(nz, i));
    }
    return result;
}

/*@ requires 0 < nz < pow206;
    requires mes0 < \min(pow217,pow2nb);
    requires mes1 < \min(pow217,pow2nb);
    requires 0 <= i <= 1;
    ensures \result == global_decode(nz,mes0,mes1,i);
 */
int_type global_decode(int_type nz, int_type mes0, int_type mes1, int_type i) {
    int_type mes = (i == 0 ? mes0 : mes1);
    int_type mmes = (NB == 19 ? 4 * mes : mes);
    int_type nzi = (1 <= minus(nz, i) ? minus(nz, i) : 1);
    int_type nnz = (NB == 19 ? 4 * nzi : nzi);
    int_type num = plus(times(pow2nb, global_zone(nz, mes0, mes1, i)), mmes);
    return closest_div_mult(num, nnz);
}

/*@
    requires mes0 < \min(pow217,pow2nb);
    requires mes1 < \min(pow217,pow2nb);
    requires 0 <= i <= 1;
    requires own<=pow230 || (3*pow230<=own && own<pow232);
    ensures \result <==> north_lat(i,mes0,mes1,own);
  */
bool north_lat(int_type i, int_type mes0, int_type mes1, int_type own) {
    int_type diff = minus(global_decode(60, mes0, mes1, i), own);
    return diff <= 357913941 || 3937053355 <= diff;
}