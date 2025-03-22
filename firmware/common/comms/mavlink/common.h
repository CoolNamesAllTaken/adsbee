/** @file
 *  @brief MAVLink comm protocol generated from common.xml
 *  @see http://mavlink.org
 */
#pragma once
#ifndef MAVLINK_COMMON_H
#define MAVLINK_COMMON_H

#ifndef MAVLINK_H
#error Wrong include order: MAVLINK_COMMON.H MUST NOT BE DIRECTLY USED. Include mavlink.h from the same directory instead or set ALL AND EVERY defines from MAVLINK.H manually accordingly, including the #define MAVLINK_H call.
#endif

#ifdef __cplusplus
extern "C" {
#endif

/** @brief Enumeration of the ADSB altimeter types */
#ifndef HAVE_ENUM_ADSB_ALTITUDE_TYPE
#define HAVE_ENUM_ADSB_ALTITUDE_TYPE
typedef enum ADSB_ALTITUDE_TYPE {
    ADSB_ALTITUDE_TYPE_PRESSURE_QNH = 0, /* Altitude reported from a Baro source using QNH reference | */
    ADSB_ALTITUDE_TYPE_GEOMETRIC = 1,    /* Altitude reported from a GNSS source | */
    ADSB_ALTITUDE_TYPE_ENUM_END = 2,     /*  | */
} ADSB_ALTITUDE_TYPE;
#endif

/** @brief ADSB classification for the type of vehicle emitting the transponder signal */
#ifndef HAVE_ENUM_ADSB_EMITTER_TYPE
#define HAVE_ENUM_ADSB_EMITTER_TYPE
typedef enum ADSB_EMITTER_TYPE {
    ADSB_EMITTER_TYPE_NO_INFO = 0,            /*  | */
    ADSB_EMITTER_TYPE_LIGHT = 1,              /*  | */
    ADSB_EMITTER_TYPE_SMALL = 2,              /*  | */
    ADSB_EMITTER_TYPE_LARGE = 3,              /*  | */
    ADSB_EMITTER_TYPE_HIGH_VORTEX_LARGE = 4,  /*  | */
    ADSB_EMITTER_TYPE_HEAVY = 5,              /*  | */
    ADSB_EMITTER_TYPE_HIGHLY_MANUV = 6,       /*  | */
    ADSB_EMITTER_TYPE_ROTOCRAFT = 7,          /*  | */
    ADSB_EMITTER_TYPE_UNASSIGNED = 8,         /*  | */
    ADSB_EMITTER_TYPE_GLIDER = 9,             /*  | */
    ADSB_EMITTER_TYPE_LIGHTER_AIR = 10,       /*  | */
    ADSB_EMITTER_TYPE_PARACHUTE = 11,         /*  | */
    ADSB_EMITTER_TYPE_ULTRA_LIGHT = 12,       /*  | */
    ADSB_EMITTER_TYPE_UNASSIGNED2 = 13,       /*  | */
    ADSB_EMITTER_TYPE_UAV = 14,               /*  | */
    ADSB_EMITTER_TYPE_SPACE = 15,             /*  | */
    ADSB_EMITTER_TYPE_UNASSGINED3 = 16,       /*  | */
    ADSB_EMITTER_TYPE_EMERGENCY_SURFACE = 17, /*  | */
    ADSB_EMITTER_TYPE_SERVICE_SURFACE = 18,   /*  | */
    ADSB_EMITTER_TYPE_POINT_OBSTACLE = 19,    /*  | */
    ADSB_EMITTER_TYPE_ENUM_END = 20,          /*  | */
} ADSB_EMITTER_TYPE;
#endif

/** @brief These flags indicate status such as data validity of each data source. Set = data valid */
#ifndef HAVE_ENUM_ADSB_FLAGS
#define HAVE_ENUM_ADSB_FLAGS
typedef enum ADSB_FLAGS {
    ADSB_FLAGS_VALID_COORDS = 1,              /*  | */
    ADSB_FLAGS_VALID_ALTITUDE = 2,            /*  | */
    ADSB_FLAGS_VALID_HEADING = 4,             /*  | */
    ADSB_FLAGS_VALID_VELOCITY = 8,            /*  | */
    ADSB_FLAGS_VALID_CALLSIGN = 16,           /*  | */
    ADSB_FLAGS_VALID_SQUAWK = 32,             /*  | */
    ADSB_FLAGS_SIMULATED = 64,                /*  | */
    ADSB_FLAGS_VERTICAL_VELOCITY_VALID = 128, /*  | */
    ADSB_FLAGS_BARO_VALID = 256,              /*  | */
    ADSB_FLAGS_SOURCE_UAT = 32768,            /*  | */
    ADSB_FLAGS_ENUM_END = 32769,              /*  | */
} ADSB_FLAGS;
#endif

#ifdef __cplusplus
}
#endif  // __cplusplus
#endif  // MAVLINK_COMMON_H