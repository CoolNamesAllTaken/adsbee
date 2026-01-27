/*
 * cpr.cc
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
#include "cpr.hh"

#include "cpr_int.hh"

namespace nasa_cpr::intent {

/* ======================================================== */
/* ================== Encoding ============================ */
/* ======================================================== */

message encode(int_type awb_lat, int_type awb_lon) {
    int_type nz = MAX(nl_awb(rlat_int(I, awb_lat)) - I, 1);
    message result = {I, encoding(60 - I, awb_lat), encoding(nz, awb_lon)};
    return result;
}

/* ======================================================== */
/* ==================== Local Decoding ==================== */
/* ======================================================== */

recovered_position local_dec(int_type reference_lat, int_type reference_longitude, message msg) {
    int_type r_lat = local_decode(60 - I, reference_lat, msg.yz);
    int_type r_lon = local_decode(MAX(nl_awb(r_lat) - I, 1), reference_longitude, msg.xz);
    recovered_position result = {1, r_lat, r_lon};
    return result;
}

// Global decoding is not applicable in intent messages.

}  // namespace nasa_cpr::intent
