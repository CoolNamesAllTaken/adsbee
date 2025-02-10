/*
 * cpr_int.h
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
#ifndef CPR_INT__H
#define CPR_INT__H

#include <stdbool.h>
#include <stdlib.h>

// Changed to uppercase to avoid breaking stdlib stuff. John 2025-02-10.
#define MAX(X, Y)       (X > Y ? X : Y)

#define int_type        unsigned int

#define times(X, Y)     ((X) * (Y))
#define plus(X, Y)      ((X) + (Y))
#define minus(X, Y)     ((X) - (Y))
#define div_shift(X, Y) ((X) >> (Y))
#define mod_uint(X, Y)  ((X) % (Y))
#define div(X, Y)       ((X) / (Y))

#define pow206          64
#define pow216          65536
#define pow217          131072
#define pow218          262144
#define pow230          1073741824
#define pow231          2147483648
#define pow232          4294967296

#define NB              17  // Airborne

// Precalculated Constants
#if NB == 12                // Coarse
#define pow232nb1  2097152  // = 2^(32-(NB-1))
#define pow232nb   1048576  // = 2^(32-NB)
#define pow2nb1    2048     // = 2^(NB-1)
#define pow2nb     4096     // = 2^NB
#define sub32nb    20       // = 32-NB
#define minNB17    12       // = min(NB,17)
#define pow2mnb116 2048     // = min(2^(NB-1),2^16)
#define pow2c31mb  524288
#elif NB == 14             // Intent
#define pow232nb1  524288  // = 2^(32-(NB-1))
#define pow232nb   262144  // = 2^(32-NB)
#define pow2nb1    8192    // = 2^(NB-1)
#define pow2nb     16384   // = 2^NB
#define sub32nb    18      // = 32-NB
#define minNB17    14      // = min(NB,17)
#define pow2mnb116 8192    // = min(2^(NB-1),2^16)
#define pow2c31mb  pow217
#elif NB == 17             // Airborne
#define pow232nb1  65536   // = 2^(32-(NB-1))
#define pow232nb   32768   // = 2^(32-NB)
#define pow2nb1    65536   // = 2^(NB-1)
#define pow2nb     131072  // = 2^NB
#define sub32nb    15      // = 32-NB
#define minNB17    17      // = min(NB,17)
#define pow2mnb116 65536   // = min(2^(NB-1),2^16)
#define pow2c31mb  16384
#else                      // NB==19	// Surface
#define pow232nb1  16384   // = 2^(32-(NB-1))
#define pow232nb   8192    // = 2^(32-NB)
#define pow2nb1    262144  // = 2^(NB-1)
#define pow2nb     524288  // = 2^NB
#define sub32nb    13      // = 32-NB
#define minNB17    17      // = min(NB,17)
#define pow2mnb116 65536   // = min(2^(NB-1),2^16)
#define pow2c31mb  4096
#endif

/*@
axiomatic params {

  // This logic definition acts as the link between the macro NB and the nb value
  // used in the PVS theories.
  logic integer nb;
  axiom nb_def: nb == NB;

}
*/

/* ======================================================== */
/* ================= Logic Operations ===================== */
/* ======================================================== */

// Having this definition as macros instead of functions
// avoids the generation of spurious TCCs in PVS.

// closest_div_mult(num,den) = CPR@uint32.closest_div_mult(num,den,32-NB)

#define closest_div_mult(num, den)   \
    (den == 1 ? times(pow232nb, num) \
              : plus(times(pow232nb, div(num, den)), div(plus(div(times(pow232nb1, mod_uint(num, den)), den), 1), 2)))

#define l_closest_div_mult(num, den)                          \
    (den == 1 ? mul_u32(pow232nb, num)                        \
              : add_u32(mul_u32(pow232nb, div_u32(num, den)), \
                        div_u32(add_u32(div_u32(mul_u32(pow232nb1, mod_u32(num, den)), den), 1), 2)))

/*@
axiomatic uint32_operations {
  logic integer add_u32(integer a, integer b) = (a+b) % pow232;
  logic integer inv_u32(integer a) = pow232-a;
  logic integer sub_u32(integer a, integer b) = (a-b) % pow232;
  logic integer mul_u32(integer a, integer b) = (a*b) % pow232;
  logic integer shr_u32(integer a, integer n) = \floor(a/\pow(2,n));
  logic integer div_u32(integer a, integer b) = (b==0?0:\floor(a/b));
  logic integer mod_u32(integer a, integer b) = (b==0?0:a%b);
}
*/

/* ======================================================== */
/* ============== Function Declarations =================== */
/* ======================================================== */

int_type nl_awb(int_type awb);
int_type encoding(int_type nz, int_type awb_lat);
int_type rlat_int(int_type i, int_type awb_lat);
int_type local_decode(int_type nz, int_type ref, int_type mes);
int_type global_decode(int_type nz, int_type mes0, int_type mes1, int_type i);
bool north_lat(int_type i, int_type mes0, int_type mes1, int_type own);

#endif  // CPR_INT__H