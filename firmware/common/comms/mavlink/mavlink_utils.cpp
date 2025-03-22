#include "mavlink_utils.hh"

uint8_t AircraftCategoryToMAVLINKEmitterType(Aircraft1090::Category category) {
    switch (category) {
        case Aircraft1090::Category::kCategoryInvalid:
            CONSOLE_WARNING("comms_reporting.cc::AircraftCategoryToMAVLINKEmitterType",
                            "Encountered airframe type kCategoryInvalid.");
            return UINT8_MAX;
        case Aircraft1090::Category::kCategoryNoCategoryInfo:
            return 0;  // ADSB_EMITTER_TYPE_NO_INFO
        case Aircraft1090::Category::kCategoryLight:
            return 1;  // ADSB_EMITTER_TYPE_LIGHT
        case Aircraft1090::Category::kCategoryMedium1:
            return 2;  // ADSB_EMITTER_TYPE_SMALL
        case Aircraft1090::Category::kCategoryMedium2:
            return 3;  // ADSB_EMITTER_TYPE_LARGE
        case Aircraft1090::Category::kCategoryHighVortexAircraft:
            return 4;  // ADSB_EMITTER_TYPE_HIGH_VORTEX_LARGE
        case Aircraft1090::Category::kCategoryHeavy:
            return 5;  // ADSB_EMITTER_TYPE_HEAVY
        case Aircraft1090::Category::kCategoryHighPerformance:
            return 6;  // ADSB_EMITTER_TYPE_HIGHLY_MANUV
        case Aircraft1090::Category::kCategoryRotorcraft:
            return 7;  // ADSB_EMITTER_TYPE_ROTORCRAFT
        case Aircraft1090::Category::kCategoryReserved:
            return 8;  // ADSB_EMITTER_TYPE_UNASSIGNED
        case Aircraft1090::Category::kCategoryGliderSailplane:
            return 9;  // ADSB_EMITTER_TYPE_GLIDER
        case Aircraft1090::Category::kCategoryLighterThanAir:
            return 10;  // ADSB_EMITTER_TYPE_LIGHTER_AIR
        case Aircraft1090::Category::kCategoryParachutistSkydiver:
            return 11;  // ADSB_EMITTER_TYPE_PARACHUTE
        case Aircraft1090::Category::kCategoryUltralightHangGliderParaglider:
            return 12;  // ADSB_EMITTER_TYPE_ULTRA_LIGHT
        // NOTE: no case for 13 = ADSB_EMITTER_TYPE_UNASSIGNED2
        case Aircraft1090::Category::kCategoryUnmannedAerialVehicle:
            return 14;  // ADSB_EMITTER_TYPE_UAV
        case Aircraft1090::Category::kCategorySpaceTransatmosphericVehicle:
            return 15;  // ADSB_EMITTER_TYPE_SPACE
        // NOTE: no case for 16 = ADSB_EMITTER_TYPE_UNASSIGNED3
        case Aircraft1090::Category::kCategorySurfaceEmergencyVehicle:
            return 17;  // ADSB_EMITTER_TYPE_EMERGENCY_SURFACE
        case Aircraft1090::Category::kCategorySurfaceServiceVehicle:
            return 18;  // ADSB_EMITTER_TYPE_SERVICE_SURFACE
        case Aircraft1090::Category::kCategoryGroundObstruction:
            return 19;  // ADSB_EMITTER_TYPE_POINT_OBSTACLE
        default:
            CONSOLE_WARNING("comms_reporting.cc::AircraftCategoryToMAVLINKEmitterType",
                            "Encountered unknown airframe type %d.", category);
            return UINT8_MAX;
    }
    return UINT8_MAX;
}

mavlink_adsb_vehicle_t AircraftToMAVLINKADSBVehicleMessage(const Aircraft1090 &aircraft) {
    // Set MAVLINK flags.
    uint16_t flags = 0;
    if (aircraft.HasBitFlag(Aircraft1090::BitFlag::kBitFlagPositionValid)) {
        flags |= ADSB_FLAGS_VALID_COORDS;
    }
    if (aircraft.HasBitFlag(Aircraft1090::BitFlag::kBitFlagBaroAltitudeValid)) {
        // Aircraft is reporting barometric altitude.
        flags |= ADSB_FLAGS_BARO_VALID;
        flags |= ADSB_FLAGS_VALID_ALTITUDE;
    } else if (aircraft.HasBitFlag(Aircraft1090::BitFlag::kBitFlagGNSSAltitudeValid)) {
        // Aircraft is reporting GNSS altitude.
        flags |= ADSB_FLAGS_VALID_ALTITUDE;
    }
    if (aircraft.HasBitFlag(Aircraft1090::BitFlag::kBitFlagDirectionValid)) {
        flags |= ADSB_FLAGS_VALID_HEADING;
    }
    if (aircraft.HasBitFlag(Aircraft1090::BitFlag::kBitFlagHorizontalVelocityValid)) {
        flags |= ADSB_FLAGS_VALID_VELOCITY;
    }
    if (strlen(aircraft.callsign) > Aircraft1090::kCallSignMinNumChars) {
        flags |= ADSB_FLAGS_VALID_CALLSIGN;
    }
    if (aircraft.squawk > 0) {
        flags |= ADSB_FLAGS_VALID_SQUAWK;
    }
    if (aircraft.HasBitFlag(Aircraft1090::BitFlag::kBitFlagVerticalVelocityValid)) {
        flags |= ADSB_FLAGS_VERTICAL_VELOCITY_VALID;
    }
    // TODO: Set SOURCE_UAT when adding dual band support.

    // Initialize the message
    mavlink_adsb_vehicle_t adsb_vehicle_msg = {
        .ICAO_address = aircraft.icao_address,
        // Latitude [degE7]
        .lat = static_cast<int32_t>(aircraft.latitude_deg * 1e7f),
        // Longitude [degE7]
        .lon = static_cast<int32_t>(aircraft.longitude_deg * 1e7f),
        // Altitude [mm]
        .altitude = FeetToMeters(aircraft.altitude_source == Aircraft1090::AltitudeSource::kAltitudeSourceBaro
                                     ? aircraft.baro_altitude_ft
                                     : aircraft.gnss_altitude_ft) *
                    1000,
        // Heding [cdeg]
        .heading = static_cast<uint16_t>(aircraft.direction_deg * 100.0f),
        // Horizontal Velocity [cm/s]
        .hor_velocity = static_cast<uint16_t>(KtsToMps(static_cast<int>(aircraft.velocity_kts)) * 100),
        // Vertical Velocity [cm/s]
        .ver_velocity = static_cast<int16_t>(FpmToMps(aircraft.vertical_rate_fpm) * 100),
        .flags = flags,
        .squawk = aircraft.squawk,
        .altitude_type =
            static_cast<uint8_t>(aircraft.altitude_source == Aircraft1090::AltitudeSource::kAltitudeSourceBaro ? 0 : 1),
        // Fill out callsign later.
        .emitter_type = AircraftCategoryToMAVLINKEmitterType(aircraft.category),
        // Time Since Last Contact [s]
        .tslc = static_cast<uint8_t>((get_time_since_boot_ms() - aircraft.last_message_timestamp_ms) / 1000)};
    // MAVLINK callsign field is 9 chars, so there's room to copy over the full 8 char callsign + null terminator.
    strncpy(adsb_vehicle_msg.callsign, aircraft.callsign, Aircraft1090::kCallSignMaxNumChars + 1);

    return adsb_vehicle_msg;
}