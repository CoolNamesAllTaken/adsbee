#include "mavlink_utils.hh"

uint8_t AircraftCategoryToMAVLINKEmitterType(ModeSAircraft::Category category) {
    switch (category) {
        case ModeSAircraft::Category::kCategoryInvalid:
            CONSOLE_WARNING("comms_reporting.cc::AircraftCategoryToMAVLINKEmitterType",
                            "Encountered airframe type kCategoryInvalid.");
            return UINT8_MAX;
        case ModeSAircraft::Category::kCategoryNoCategoryInfo:
            return 0;  // ADSB_EMITTER_TYPE_NO_INFO
        case ModeSAircraft::Category::kCategoryLight:
            return 1;  // ADSB_EMITTER_TYPE_LIGHT
        case ModeSAircraft::Category::kCategoryMedium1:
            return 2;  // ADSB_EMITTER_TYPE_SMALL
        case ModeSAircraft::Category::kCategoryMedium2:
            return 3;  // ADSB_EMITTER_TYPE_LARGE
        case ModeSAircraft::Category::kCategoryHighVortexAircraft:
            return 4;  // ADSB_EMITTER_TYPE_HIGH_VORTEX_LARGE
        case ModeSAircraft::Category::kCategoryHeavy:
            return 5;  // ADSB_EMITTER_TYPE_HEAVY
        case ModeSAircraft::Category::kCategoryHighPerformance:
            return 6;  // ADSB_EMITTER_TYPE_HIGHLY_MANUV
        case ModeSAircraft::Category::kCategoryRotorcraft:
            return 7;  // ADSB_EMITTER_TYPE_ROTORCRAFT
        case ModeSAircraft::Category::kCategoryReserved:
            return 8;  // ADSB_EMITTER_TYPE_UNASSIGNED
        case ModeSAircraft::Category::kCategoryGliderSailplane:
            return 9;  // ADSB_EMITTER_TYPE_GLIDER
        case ModeSAircraft::Category::kCategoryLighterThanAir:
            return 10;  // ADSB_EMITTER_TYPE_LIGHTER_AIR
        case ModeSAircraft::Category::kCategoryParachutistSkydiver:
            return 11;  // ADSB_EMITTER_TYPE_PARACHUTE
        case ModeSAircraft::Category::kCategoryUltralightHangGliderParaglider:
            return 12;  // ADSB_EMITTER_TYPE_ULTRA_LIGHT
        // NOTE: no case for 13 = ADSB_EMITTER_TYPE_UNASSIGNED2
        case ModeSAircraft::Category::kCategoryUnmannedAerialVehicle:
            return 14;  // ADSB_EMITTER_TYPE_UAV
        case ModeSAircraft::Category::kCategorySpaceTransatmosphericVehicle:
            return 15;  // ADSB_EMITTER_TYPE_SPACE
        // NOTE: no case for 16 = ADSB_EMITTER_TYPE_UNASSIGNED3
        case ModeSAircraft::Category::kCategorySurfaceEmergencyVehicle:
            return 17;  // ADSB_EMITTER_TYPE_EMERGENCY_SURFACE
        case ModeSAircraft::Category::kCategorySurfaceServiceVehicle:
            return 18;  // ADSB_EMITTER_TYPE_SERVICE_SURFACE
        case ModeSAircraft::Category::kCategoryGroundObstruction:
            return 19;  // ADSB_EMITTER_TYPE_POINT_OBSTACLE
        default:
            CONSOLE_WARNING("comms_reporting.cc::AircraftCategoryToMAVLINKEmitterType",
                            "Encountered unknown airframe type %d.", category);
            return UINT8_MAX;
    }
    return UINT8_MAX;
}

mavlink_adsb_vehicle_t AircraftToMAVLINKADSBVehicleMessage(const ModeSAircraft &aircraft) {
    // Set MAVLINK flags.
    uint16_t flags = 0;
    if (aircraft.HasBitFlag(ModeSAircraft::BitFlag::kBitFlagPositionValid)) {
        flags |= ADSB_FLAGS_VALID_COORDS;
    }
    if (aircraft.HasBitFlag(ModeSAircraft::BitFlag::kBitFlagBaroAltitudeValid)) {
        // Aircraft is reporting barometric altitude.
        flags |= ADSB_FLAGS_BARO_VALID;
        flags |= ADSB_FLAGS_VALID_ALTITUDE;
    } else if (aircraft.HasBitFlag(ModeSAircraft::BitFlag::kBitFlagGNSSAltitudeValid)) {
        // Aircraft is reporting GNSS altitude.
        flags |= ADSB_FLAGS_VALID_ALTITUDE;
    }
    if (aircraft.HasBitFlag(ModeSAircraft::BitFlag::kBitFlagDirectionValid)) {
        flags |= ADSB_FLAGS_VALID_HEADING;
    }
    if (aircraft.HasBitFlag(ModeSAircraft::BitFlag::kBitFlagHorizontalSpeedValid)) {
        flags |= ADSB_FLAGS_VALID_VELOCITY;
    }
    if (strlen(aircraft.callsign) > ModeSAircraft::kCallSignMinNumChars) {
        flags |= ADSB_FLAGS_VALID_CALLSIGN;
    }
    if (aircraft.squawk > 0) {
        flags |= ADSB_FLAGS_VALID_SQUAWK;
    }
    if (aircraft.HasBitFlag(ModeSAircraft::BitFlag::kBitFlagBaroVerticalRateValid) ||
        aircraft.HasBitFlag(ModeSAircraft::BitFlag::kBitFlagGNSSVerticalRateValid)) {
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
        // Altitude [mm]: Prefer GNSS altitude but fall back to baro altitude.
        .altitude =
            FeetToMeters(aircraft.HasBitFlag(ModeSAircraft::kBitFlagGNSSAltitudeValid) ? aircraft.gnss_altitude_ft
                                                                                       : aircraft.baro_altitude_ft) *
            1000,
        // Heading [cdeg]
        .heading = static_cast<uint16_t>(aircraft.direction_deg * 100),
        // Horizontal Velocity [cm/s]
        .hor_velocity = static_cast<uint16_t>(KtsToMps(static_cast<int>(aircraft.speed_kts)) * 100),
        // Vertical Velocity [cm/s]: Prefer GNSS vertical velocity but fall back to baro vertical velocity.
        .ver_velocity = static_cast<int16_t>(FpmToMps(aircraft.HasBitFlag(ModeSAircraft::kBitFlagGNSSVerticalRateValid)
                                                          ? aircraft.gnss_vertical_rate_fpm
                                                          : aircraft.baro_vertical_rate_fpm) *
                                             100),
        .flags = flags,
        .squawk = aircraft.squawk,
        .altitude_type = static_cast<uint8_t>(
            aircraft.altitude_source == ModeSAircraft::AltitudeSource::kAltitudeSourceBaro ? 0 : 1),
        // Fill out callsign later.
        .emitter_type = AircraftCategoryToMAVLINKEmitterType(aircraft.category),
        // Time Since Last Contact [s]
        .tslc = static_cast<uint8_t>((get_time_since_boot_ms() - aircraft.last_message_timestamp_ms) / 1000)};
    // MAVLINK callsign field is 9 chars, so there's room to copy over the full 8 char callsign + null terminator.
    strncpy(adsb_vehicle_msg.callsign, aircraft.callsign, ModeSAircraft::kCallSignMaxNumChars + 1);

    return adsb_vehicle_msg;
}