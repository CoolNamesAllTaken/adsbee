/*
 * cpr.hh
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

#include "cpr_int.hh"

namespace nasa_cpr::intent {

// In intent messages, the only used format is even (i=0).
constexpr int I = 0;

struct message {
    int format;   // even (0) or odd (1)
    int_type yz;  // encoded latitude
    int_type xz;  // encoded longitude
};

struct recovered_position {
    int valid;         // (0) if invalid, (1) if valid
    int_type lat_awb;  // recovered latitude
    int_type lon_awb;  // recovered longitude
};

message encode(int_type awb_lat, int_type awb_lon);
recovered_position local_dec(int_type reference_lat, int_type reference_longitude, message msg);

// Global decoding is not applicable in intent messages.

}  // namespace nasa_cpr::intent
