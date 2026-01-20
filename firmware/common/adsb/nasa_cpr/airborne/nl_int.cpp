/*
 * nl_int.cc
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

namespace nasa_cpr::airborne {

static int_type nl_awb_nn(int_type awb) {
    // clang-format off
    return ( awb <= 124917589 ? 59: // 07721755
           ( awb <= 176907012 ? 58: //  0A8B6304
           ( awb <= 216970576 ? 57: //  0CEEB550
           ( awb <= 250890455 ? 56: //  0EF448D7
           ( awb <= 280903327 ? 55: //  10BE3E9F
           ( awb <= 308154921 ? 54: //  125E1229
           ( awb <= 333325100 ? 53: //  13DE232C
           ( awb <= 356856388 ? 52: //  15453244
           ( awb <= 379055883 ? 51: //  1697EF0B
           ( awb <= 400147004 ? 50: //  17D9C23C
           ( awb <= 420298294 ? 49: //  190D3E36
           ( awb <= 439640621 ? 48: //  1A34622D
           ( awb <= 458278009 ? 47: //  1B50C479
           ( awb <= 476294775 ? 46: //  1C63AE77
           ( awb <= 493760397 ? 45: //  1D6E2F8D
           ( awb <= 510732936 ? 44: //  1E712A88
           ( awb <= 527261514 ? 43: //  1F6D5F4A
           ( awb <= 543388133 ? 42: //  206371E5
           ( awb <= 559149057 ? 41: //  2153F001
           ( awb <= 574575849 ? 40: //  223F54E9
           ( awb <= 589696199 ? 39: //  23260CC7
           ( awb <= 604534563 ? 38: //  24087723
           ( awb <= 619112673 ? 37: //  24E6E8E1
           ( awb <= 633449951 ? 36: //  25C1ADDF
           ( awb <= 647563849 ? 35: //  26990A49
           ( awb <= 661470114 ? 34: //  276D3BA2
           ( awb <= 675183028 ? 33: //  283E79B4
           ( awb <= 688715586 ? 32: //  290CF742
           ( awb <= 702079666 ? 31: //  29D8E2B2
           ( awb <= 715286154 ? 30: //  2AA2668A
           ( awb <= 728345061 ? 29: //  2B69A9E5
           ( awb <= 741265621 ? 28: //  2C2ED0D5
           ( awb <= 754056371 ? 27: //  2CF1FCB3
           ( awb <= 766725217 ? 26: //  2DB34C61
           ( awb <= 779279500 ? 25: //  2E72DC8C
           ( awb <= 791726041 ? 24: //  2F30C7D9
           ( awb <= 804071180 ? 23: //  2FED270C
           ( awb <= 816320815 ? 22: //  30A8112F
           ( awb <= 828480417 ? 21: //  31619BA1
           ( awb <= 840555055 ? 20: //  3219DA2F
           ( awb <= 852549395 ? 19: //  32D0DF13
           ( awb <= 864467699 ? 18: //  3386BAF3
           ( awb <= 876313803 ? 17: //  343B7CCB
           ( awb <= 888091078 ? 16: //  34EF31C6
           ( awb <= 899802361 ? 15: //  35A1E4F9
           ( awb <= 911449851 ? 14: //  36539EFB
           ( awb <= 923034937 ? 13: //  37046539
           ( awb <= 934557931 ? 12: //  37B438EB
           ( awb <= 946017637 ? 11: //  38631565
           ( awb <= 957410633 ? 10: //  3910ED49
           ( awb <= 968730035 ?  9: //  39BDA5B3
           ( awb <= 979963239 ?  8: //  3A690D67
           ( awb <= 991087499 ?  7: //  3B12CB8B
           ( awb <= 1002060438 ? 6: //  3BBA3A96
           ( awb <= 1012796977 ? 5: //  3C5E0E31
           ( awb <= 1023101967 ? 4: //  3CFB4C0F
           ( awb <= 1032407178 ? 3: //  3D89488A
           ( awb <= 1037950430 ? 2: //  3DDDDDDE
            1 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    // clang-format on
}

int_type nl_awb(int_type awb) { return (awb < pow231 ? nl_awb_nn(awb) : nl_awb_nn(-awb)); }

}  // namespace nasa_cpr::airborne
