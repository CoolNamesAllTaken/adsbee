#include "ads_bee.hh"
#include "comms.hh"
#include "hal.hh"  // For timestamping.
#include "mavlink/mavlink.h"
#include "unit_conversions.hh"

extern ADSBee ads_bee;

bool CommsManager::InitReporting() { return true; }

bool CommsManager::UpdateReporting() {
    uint32_t timestamp_ms = get_time_since_boot_ms();
    if (timestamp_ms - last_report_timestamp_ms < reporting_interval_ms) {
        return true;  // No update required.
    }
    for (uint16_t iface = 0; iface < SerialInterface::kGNSSUART; iface++) {
        switch (reporting_protocols_[iface]) {
            case kNoReports:
                break;
            case kRaw:
                break;
            case kRawValidated:
                break;
            case kMAVLINK:
                ReportMAVLINK(static_cast<SerialInterface>(iface));
                break;
            case kGDL90:
                // Currently not supported.
                break;
            case kNumProtocols:
            default:
                CONSOLE_WARNING("Invalid reporting protocol %d specified for interface %d.",
                                reporting_protocols_[iface], iface);
                return false;
                break;
        }
    }
    return true;
}

uint16_t AircraftAirframeTypeToMAVLINKEmitterType(Aircraft::AirframeType airframe_type) {
    switch (airframe_type) {
        case Aircraft::AirframeType::kAirframeTypeNoCategoryInfo:
            return 0;  // ADSB_EMITTER_TYPE_NO_INFO
        case Aircraft::AirframeType::kAirframeTypeLight:
            return 1;  // ADSB_EMITTER_TYPE_LIGHT
        case Aircraft::AirframeType::kAirframeTypeMedium1:
            return 2;  // ADSB_EMITTER_TYPE_SMALL
        case Aircraft::AirframeType::kAirframeTypeMedium2:
            return 3;  // ADSB_EMITTER_TYPE_LARGE
        case Aircraft::AirframeType::kAirframeTypeHighVortexAircraft:
            return 4;  // ADSB_EMITTER_TYPE_HIGH_VORTEX_LARGE
        case Aircraft::AirframeType::kAirframeTypeHeavy:
            return 5;  // ADSB_EMITTER_TYPE_HEAVY
        case Aircraft::AirframeType::kAirframeTypeHighPerformance:
            return 6;  // ADSB_EMITTER_TYPE_HIGHLY_MANUV
        case Aircraft::AirframeType::kAirframeTypeRotorcraft:
            return 7;  // ADSB_EMITTER_TYPE_ROTORCRAFT
        case Aircraft::AirframeType::kAirframeTypeReserved:
            return 8;  // ADSB_EMITTER_TYPE_UNASSIGNED
        case Aircraft::AirframeType::kAirframeTypeGliderSailplane:
            return 9;  // ADSB_EMITTER_TYPE_GLIDER
        case Aircraft::AirframeType::kAirframeTypeLighterThanAir:
            return 10;  // ADSB_EMITTER_TYPE_LIGHTER_AIR
        case Aircraft::AirframeType::kAirframeTypeParachutistSkydiver:
            return 11;  // ADSB_EMITTER_TYPE_PARACHUTE
        case Aircraft::AirframeType::kAirframeTypeUltralightHangGliderParaglider:
            return 12;  // ADSB_EMITTER_TYPE_ULTRA_LIGHT
        // NOTE: no case for 13 = ADSB_EMITTER_TYPE_UNASSIGNED2
        case Aircraft::AirframeType::kAirframeTypeUnmannedAerialVehicle:
            return 14;  // ADSB_EMITTER_TYPE_UAV
        case Aircraft::AirframeType::kAirframeTypeSpaceTransatmosphericVehicle:
            return 15;  // ADSB_EMITTER_TYPE_SPACE
        // NOTE: no case for 16 = ADSB_EMITTER_TYPE_UNASSIGNED3
        case Aircraft::AirframeType::kAirframeTypeSurfaceEmergencyVehicle:
            return 17;  // ADSB_EMITTER_TYPE_EMERGENCY_SURFACE
        case Aircraft::AirframeType::kAirframeTypeSurfaceServiceVehicle:
            return 18;  // ADSB_EMITTER_TYPE_SERVICE_SURFACE
        case Aircraft::AirframeType::kAirframeTypeGroundObstruction:
            return 19;  // ADSB_EMITTER_TYPE_POINT_OBSTACLE
    }
}

bool CommsManager::ReportMAVLINK(SerialInterface iface) {
    for (auto &itr : ads_bee.aircraft_dictionary.dict) {
        const Aircraft &aircraft = itr.second;

        // Initialize the message
        mavlink_adsb_vehicle_t adsb_vehicle_msg = {
            .ICAO_address = aircraft.icao_address,
            // Latitude [degE7]
            .lat = static_cast<int32_t>(aircraft.latitude_deg * 1e7f),
            // Longitude [degE7]
            .lon = static_cast<int32_t>(aircraft.longitude_deg * 1e7f),
            // Altitude [mm]
            .altitude = FeetToMeters(aircraft.altitude_source == Aircraft::AltitudeSource::kAltitudeSourceBaro
                                         ? aircraft.baro_altitude_ft
                                         : aircraft.gnss_altitude_ft) *
                        1000,
            // Heding [cdeg]
            .heading = aircraft.heading_deg * 100,
            // Horizontal Velocity [cm/s]
            .hor_velocity = KtsToMps(aircraft.velocity_kts) * 100,
            // Vertical Velocity [cm/s]
            .ver_velocity = FpmToMps(aircraft.vertical_rate_fpm) * 100,
            .flags = 0,   // TODO: fix this!
            .squawk = 0,  // TODO: fix this!
            .altitude_type = aircraft.altitude_source == Aircraft::AltitudeSource::kAltitudeSourceBaro ? 0 : 1,
            // Fill out callsign later.
            .emitter_type = AircraftAirframeTypeToMAVLINKEmitterType(aircraft.airframe_type),
            // Time Since Last Contact [s]
            .tslc = (get_time_since_boot_ms() - aircraft.last_seen_timestamp_ms) / 1000};
        strncpy(adsb_vehicle_msg.callsign, aircraft.callsign, Aircraft::kCallSignMaxNumChars);
    }
    return true;
}