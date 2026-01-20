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

namespace nasa_cpr::coarse {

/* ======================================================== */
/* ================== Encoding ============================ */
/* ======================================================== */

message encode(int i, int_type awb_lat, int_type awb_lon) {
    int_type nz = MAX(nl_awb(rlat_int(i, awb_lat)) - i, 1);
    message result = {i, encoding(60 - i, awb_lat), encoding(nz, awb_lon)};
    return result;
}

/* ======================================================== */
/* ==================== Local Decoding ==================== */
/* ======================================================== */

recovered_position local_dec(int i, int_type reference_lat, int_type reference_longitude, message msg) {
    int_type r_lat = local_decode(60 - i, reference_lat, msg.yz);
    int_type r_lon = local_decode(MAX(nl_awb(r_lat) - i, 1), reference_longitude, msg.xz);
    recovered_position result = {1, r_lat, r_lon};
    return result;
}

/* ======================================================== */
/* =================== Global Decoding ==================== */
/* ======================================================== */

recovered_position global_dec(int i, message msg0, message msg1) {
    int_type r_lat = global_decode(60, msg0.yz, msg1.yz, i);  // Recovered latitude.
    // Number of longitude cells assuming msg0 is most recent.
    int_type nl0 = nl_awb(global_decode(60, msg0.yz, msg1.yz, 0));
    // Number of longitude cells assuming msg1 is most recent.
    int_type nl1 = nl_awb(global_decode(60, msg0.yz, msg1.yz, 1));
    // Check if the number of longitude cells is the same regardless of message received order.
    int valid = (nl0 == nl1) ? 1 : 0;
    int_type r_lon = global_decode(nl0, msg0.xz, msg1.xz, i);  // Recovered longitude.
    recovered_position result = {valid, r_lat, r_lon};
    return result;
}

}  // namespace nasa_cpr::coarse
