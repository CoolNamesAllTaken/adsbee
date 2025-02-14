/*
 * cpr.h
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
#ifndef CPR__H
#define CPR__H

// C++ guard added by John 2025-02-10.
#ifdef __cplusplus
extern "C" {
#endif

#include "cpr_int.h"

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

struct message encode(int i, int_type awb_lat, int_type awb_lon);
struct recovered_position local_dec(int i, int_type reference_lat, int_type reference_longitude, struct message msg);

/**
 * Decode a global position from an evn and odd CPR message.
 * @param[in] i 0 if msg0 is most recent, 1 if msg1 is most recent.
 * @param[in] msg0 Even CPR message.
 * @param[in] msg1 Odd CPR message.
 * @return Recovered position.
 */
struct recovered_position global_dec(int i, struct message msg0, struct message msg1);

#ifdef __cplusplus
}
#endif

#endif  // CPR__H
