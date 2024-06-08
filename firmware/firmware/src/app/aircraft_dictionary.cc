#include "aircraft_dictionary.hh"

#include <cmath>

#include "comms.hh"  // For debug logging.
#include "decode_utils.hh"
#include "hal.hh"

// Conditionally define the MAX macro because the pico platform includes it by default in pico/platform.h.
#ifndef MAX
#define MAX(a, b) ((a) > (b) ? (a) : (b))
#endif

const float kRadiansToDegrees = 360.0f / (2.0f * M_PI);

/**
 * Aircraft
 */

Aircraft::Aircraft(uint32_t icao_address_in) : icao_address(icao_address_in) {
    memset(callsign, '\0', kCallSignMaxNumChars + 1);  // clear out callsign string, including extra EOS character
}

Aircraft::Aircraft() {
    memset(callsign, '\0', kCallSignMaxNumChars + 1);  // clear out callsign string, including extra EOS character
}

bool Aircraft::DecodePosition() {
    if (!(last_odd_packet_.received_timestamp_ms > 0 && last_even_packet_.received_timestamp_ms > 0)) {
        CONSOLE_WARNING(
            "Aircraft::DecodePosition: Unable to decode position without receiving an odd and even packet pair.\r\n");
        return false;  // need both an even and an odd packet to be able to decode position
    }

    // Equation 5.6
    int32_t lat_zone_index = floorf(59.0f * last_even_packet_.lat_cpr - 60.0f * last_odd_packet_.lat_cpr + 0.5f);

    bool calculate_odd =
        last_odd_packet_.calculated_timestamp_ms > last_odd_packet_.received_timestamp_ms ? false : true;
    bool calculate_even =
        last_even_packet_.calculated_timestamp_ms > last_even_packet_.received_timestamp_ms ? false : true;

    if (calculate_odd) {
        // Equation 5.7
        last_odd_packet_.lat = kCPRdLatOdd * ((lat_zone_index % 59) + last_odd_packet_.lat_cpr);
        // Equation 5.8: wrap latitude to between -90 and +90 degrees.
        last_odd_packet_.lat = wrap_latitude(last_odd_packet_.lat);
        // Calculate NL, which will be used later to calculate the number of longitude zones in this latitude band.
        last_odd_packet_.nl_cpr = calc_nl_cpr_from_lat(last_odd_packet_.lat);
        last_odd_packet_.calculated_timestamp_ms = get_time_since_boot_ms();
    }

    if (calculate_even) {
        // Equation 5.7
        last_even_packet_.lat = kCPRdLatEven * ((lat_zone_index % 60) + last_even_packet_.lat_cpr);
        // Equation 5.8: wrap latitude to between -90 and +90 degrees.
        last_even_packet_.lat = wrap_latitude(last_even_packet_.lat);
        // Calculate NL, which will be used later to calculate the number of longitude zones in this latitude band.
        last_even_packet_.nl_cpr = calc_nl_cpr_from_lat(last_even_packet_.lat);
        last_even_packet_.calculated_timestamp_ms = get_time_since_boot_ms();
    }

    /**
     * Unhandled edge case:
     *
     * Even and odd packets are both received, everything up to this point gets calculated. The calculated position
     * ends up being invalid because the number of longitude bands disagrees at the last step. Then, a new odd packet
     * arrives with a lat_cpr that would change the lat_zone_index. This should change the lat of the previously
     * calculated even packet, but this won't be refreshed until the next even packet is received. Could result in
     * some delay in getting a valid position when crossing over between latitude zones.
     *
     * Solution would be to trigger a re-ingestion of the old even packet as soon as it's known that it was calculated
     * incorrectly.
     */

    if (last_odd_packet_.nl_cpr != last_even_packet_.nl_cpr) {
        // Invalidate position if position pair is split across different latitude bands.
        position_valid = false;  // keep last known good coordinates, but mark as invalid
        CONSOLE_WARNING(
            "Aircraft::DecodePosition: NL_cpr disagrees between odd (%d) and even (%d) packets. Can't decode "
            "position.\r\n",
            last_odd_packet_.nl_cpr, last_even_packet_.nl_cpr);
        return false;
    }

    // From here on out, can just focus on the most recent packet since that's what we're using for our position.
    bool received_odd_last = last_odd_packet_.received_timestamp_ms > last_even_packet_.received_timestamp_ms;
    CPRPacket &last_packet = received_odd_last ? last_odd_packet_ : last_even_packet_;
    latitude_deg = last_packet.lat;  // Publish latitude.

    // Equation 5.10
    int32_t lon_zone_index = floorf(last_even_packet_.lon_cpr * (last_packet.nl_cpr - 1) -
                                    last_odd_packet_.lon_cpr * last_packet.nl_cpr + 0.5f);

    // Equation 5.11: Use nl_lat_cpr to calculate actual number of longitude zones
    uint16_t num_lon_zones = received_odd_last ? MAX(last_packet.nl_cpr - 1, 1) : MAX(last_packet.nl_cpr, 1);
    // Equation 5.12: longitude zone size
    float d_lon = 360.0f / num_lon_zones;

    // Equation 5.13 (calc longitude), 5.15 (wrap longitude to between -180 and +180 degrees)
    longitude_deg = wrap_longitude(d_lon * ((lon_zone_index % num_lon_zones) + last_packet.lon_cpr));
    position_valid = true;  // TODO: add "reasonable validation" that position is valid
    return true;
}

bool Aircraft::SetCPRLatLon(uint32_t n_lat_cpr, uint32_t n_lon_cpr, bool odd, bool redigesting) {
    if (n_lat_cpr > kCPRLatLonMaxCount || n_lon_cpr > kCPRLatLonMaxCount) {
        return false;  // counts out of bounds, don't parse
    }

    CPRPacket &packet = odd ? last_odd_packet_ : last_even_packet_;
    packet.received_timestamp_ms = get_time_since_boot_ms();
    packet.n_lat = n_lat_cpr;
    packet.n_lon = n_lon_cpr;
    // Equation 5.5
    packet.lat_cpr = static_cast<float>(n_lat_cpr) / kCPRLatLonMaxCount;
    packet.lon_cpr = static_cast<float>(n_lon_cpr) / kCPRLatLonMaxCount;

    return true;
}

/**
 * Aircraft Dictionary
 */

void AircraftDictionary::Init() {
    dict.clear();  // Remove all aircraft from the unordered map.
}

void AircraftDictionary::Update(uint32_t timestamp_ms) {
    // Iterate over each key-value pair in the unordered_map
    for (auto it = dict.begin(); it != dict.end(); /* No increment here */) {
        if (timestamp_ms - it->second.last_seen_timestamp_ms > config_.aircraft_prune_interval_ms) {
            it = dict.erase(it);  // Remove stale aircraft entry.
        } else {
            it++;  // Move to the next aircraft entry.
        }
    }
}

bool AircraftDictionary::IngestADSBPacket(ADSBPacket packet) {
    if (!packet.IsValid() || packet.GetDownlinkFormat() != ADSBPacket::kDownlinkFormatExtendedSquitter) {
        return false;  // Only allow valid DF17 packets.
    }

    uint32_t icao_address = packet.GetICAOAddress();
    Aircraft *aircraft_ptr = GetAircraftPtr(icao_address);
    if (aircraft_ptr == nullptr) {
        CONSOLE_WARNING(
            "AircraftDictionary::IngestADSBPacket: Unable to find or create new aircraft with ICAO address 0x%x in "
            "dictionary.\r\n",
            icao_address);
        return false;  // unable to find or create new aircraft in dictionary
    }
    aircraft_ptr->last_seen_timestamp_ms = get_time_since_boot_ms();

    switch (packet.GetTypeCodeEnum()) {
        case ADSBPacket::kTypeCodeAircraftID:
            return IngestAircraftIDMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeSurfacePosition:
            return IngestSurfacePositionMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeAirbornePositionBaroAlt:
        case ADSBPacket::kTypeCodeAirbornePositionGNSSAlt:
            return IngestAirbornePositionMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeAirborneVelocities:
            return IngestAirborneVelocitiesMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeReserved:
            return false;
            break;
        case ADSBPacket::kTypeCodeAircraftStatus:
            return IngestAircraftStatusMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeTargetStateAndStatusInfo:
            return IngestTargetStateAndStatusInfoMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeAircraftOperationStatus:
            return IngestAircraftOperationStatusMessage(*aircraft_ptr, packet);
            break;
        default:
            return false;  // kTypeCodeInvalid, etc.
    }

    return false;
}

uint16_t AircraftDictionary::GetNumAircraft() { return dict.size(); }

bool AircraftDictionary::InsertAircraft(const Aircraft &aircraft) {
    auto itr = dict.find(aircraft.icao_address);
    if (itr != dict.end()) {
        // Overwriting an existing aircraft
        itr->second = aircraft;
        return true;
    }

    if (dict.size() >= kMaxNumAircraft) {
        CONSOLE_LOG(
            "AIrcraftDictionary::InsertAircraft: Failed to add aircraft to dictionary, max number of aircraft is %d.",
            kMaxNumAircraft);
        return false;  // not enough room to add this aircraft
    }

    dict[aircraft.icao_address] = aircraft;  // add the new aircraft to the dictionary
    return true;
}

bool AircraftDictionary::RemoveAircraft(uint32_t icao_address) {
    auto itr = dict.find(icao_address);
    if (itr != dict.end()) {
        dict.erase(itr);
        return true;
    }
    return false;  // aircraft was not found in the dictionary
}

bool AircraftDictionary::GetAircraft(uint32_t icao_address, Aircraft &aircraft_out) const {
    auto itr = dict.find(icao_address);
    if (itr != dict.end()) {
        aircraft_out = itr->second;
        return true;
    }
    return false;  // aircraft not found
}

bool AircraftDictionary::ContainsAircraft(uint32_t icao_address) const {
    auto itr = dict.find(icao_address);
    if (itr != dict.end()) {
        return true;
    }
    return false;
}

Aircraft *AircraftDictionary::GetAircraftPtr(uint32_t icao_address) {
    auto itr = dict.find(icao_address);
    if (itr != dict.end()) {
        return &(itr->second);  // return address of existing aircraft
    } else if (dict.size() < kMaxNumAircraft) {
        Aircraft new_aircraft = Aircraft(icao_address);
        dict[icao_address] = new_aircraft;
        return &(dict[icao_address]);  // insert new aircraft and return its address
    }
    return nullptr;  // can't find the aircraft or insert a new one
}

/**
 * Private functions and associated helpers.
 */

/**
 * Returns the Wake Vortex value of the aircraft that sent a given ADS-B packet.
 * @param[in] packet ADS-B Packet to extract the AirframeType value from. Must be
 * @retval AirframeType that matches the combination of capability and typecode from the ADS-B packet, or
 * kAirframeTypeInvalid if there is no matching wake vortex value.
 */
Aircraft::AirframeType ExtractAirframeType(const ADSBPacket &packet) {
    if (packet.GetTypeCodeEnum() != ADSBPacket::kTypeCodeAircraftID) {
        return Aircraft::kAirframeTypeInvalid;  // Must have typecode from 1-4.
    }

    uint32_t typecode = packet.GetNBitWordFromMessage(5, 0);
    uint32_t category = packet.GetNBitWordFromMessage(3, 5);

    // Table 4.1 from The 1090Mhz Riddle (Junzi Sun), pg. 42.
    if (category == 0) {
        return Aircraft::kAirframeTypeNoCategoryInfo;
    }

    switch (typecode) {
        case 1:
            return Aircraft::kAirframeTypeReserved;
            break;
        case 2:
            switch (category) {
                case 1:
                    return Aircraft::kAirframeTypeSurfaceEmergencyVehicle;
                    break;
                case 3:
                    return Aircraft::kAirframeTypeSurfaceServiceVehicle;
                    break;
                case 4:
                case 5:
                case 6:
                case 7:
                    return Aircraft::kAirframeTypeGroundObstruction;
                    break;
                default:
                    return Aircraft::kAirframeTypeInvalid;
            }
            break;
        case 3:
            switch (category) {
                case 1:
                    return Aircraft::kAirframeTypeGliderSailplane;
                    break;
                case 2:
                    return Aircraft::kAirframeTypeLighterThanAir;
                    break;
                case 3:
                    return Aircraft::kAirframeTypeParachutistSkydiver;
                    break;
                case 4:
                    return Aircraft::kAirframeTypeUltralightHangGliderParaglider;
                    break;
                case 5:
                    return Aircraft::kAirframeTypeReserved;
                    break;
                case 6:
                    return Aircraft::kAirframeTypeUnmannedAerialVehicle;
                    break;
                case 7:
                    return Aircraft::kAirframeTypeSpaceTransatmosphericVehicle;
                    break;
                default:
                    return Aircraft::kAirframeTypeInvalid;
            }
            break;
        case 4:
            switch (category) {
                case 1:
                    return Aircraft::kAirframeTypeLight;
                    break;
                case 2:
                    return Aircraft::kAirframeTypeMedium1;
                    break;
                case 3:
                    return Aircraft::kAirframeTypeMedium2;
                    break;
                case 4:
                    return Aircraft::kAirframeTypeHighVortexAircraft;
                    break;
                case 5:
                    return Aircraft::kAirframeTypeHeavy;
                    break;
                case 6:
                    return Aircraft::kAirframeTypeHighPerformance;
                    break;
                case 7:
                    return Aircraft::kAirframeTypeRotorcraft;
                    break;
                default:
                    return Aircraft::kAirframeTypeInvalid;
            }
            break;
        default:
            return Aircraft::kAirframeTypeInvalid;
    }
}

bool AircraftDictionary::IngestAircraftIDMessage(Aircraft &aircraft, ADSBPacket packet) {
    aircraft.wake_vortex = ExtractAirframeType(packet);
    aircraft.transponder_capability = packet.GetCapability();
    for (uint16_t i = 0; i < Aircraft::kCallSignMaxNumChars; i++) {
        char callsign_char = lookup_callsign_char(packet.GetNBitWordFromMessage(6, 8 + (6 * i)));
        if (callsign_char == ' ') break;  // ignore trailing spaces
        aircraft.callsign[i] = callsign_char;
    }

    return true;
}

bool AircraftDictionary::IngestSurfacePositionMessage(Aircraft &aircraft, ADSBPacket packet) { return false; }

bool AircraftDictionary::IngestAirbornePositionMessage(Aircraft &aircraft, ADSBPacket packet) {
    // ME[5-6] - Surveillance Status
    aircraft.surveillance_status = static_cast<Aircraft::SurveillanceStatus>(packet.GetNBitWordFromMessage(2, 5));

    // ME[7] - Single Antenna Flag
    aircraft.single_antenna_flag = packet.GetNBitWordFromMessage(1, 7) ? true : false;

    // ME[8-19] - Encoded Altitude
    uint16_t encoded_altitude = packet.GetNBitWordFromMessage(12, 8);
    if (packet.GetTypeCodeEnum() == ADSBPacket::kTypeCodeAirbornePositionBaroAlt) {
        aircraft.barometric_altitude_m = encoded_altitude;
    } else {
        aircraft.gnss_altitude_m = encoded_altitude;
    }

    // ME[20] - Time
    // TODO: figure out if we need this

    // ME[21] - CPR Format
    bool odd = packet.GetNBitWordFromMessage(1, 21);

    // ME[32-?]
    aircraft.SetCPRLatLon(packet.GetNBitWordFromMessage(17, 22), packet.GetNBitWordFromMessage(17, 39), odd);
    if (aircraft.CanDecodePosition()) {
        if (!aircraft.DecodePosition()) {
            CONSOLE_WARNING("IngestAirbornePositionMessage: DecodePosition failed for aircraft 0x%x.\r\n",
                            aircraft.icao_address);
            return false;
        }
    }

    return true;
}

inline float wrapped_atan2f(float y, float x) {
    float val = atan2f(y, x);
    return val < 0.0f ? (val + (2.0f * M_PI)) : val;
}

bool AircraftDictionary::IngestAirborneVelocitiesMessage(Aircraft &aircraft, ADSBPacket packet) {
    bool decode_successful = true;

    // Decode horizontal velocity.
    ADSBPacket::AirborneVelocitiesSubtype subtype =
        static_cast<ADSBPacket::AirborneVelocitiesSubtype>(packet.GetNBitWordFromMessage(3, 5));
    bool is_supersonic = false;
    switch (subtype) {
        case ADSBPacket::AirborneVelocitiesSubtype::kAirborneVelocitiesGroundSpeedSupersonic:
            is_supersonic = true;
            // Cascade into ground speed calculation.
        case ADSBPacket::AirborneVelocitiesSubtype::kAirborneVelocitiesGroundSpeedSubsonic: {
            // Ground speed calculation.
            int v_ew_kts_plus_1 = static_cast<int>(packet.GetNBitWordFromMessage(10, 14));
            int v_ns_kts_plus_1 = static_cast<int>(packet.GetNBitWordFromMessage(10, 25));
            if (v_ew_kts_plus_1 == 0 || v_ns_kts_plus_1 == 0) {
                aircraft.velocity_source = Aircraft::VelocitySource::kVelocityNotAvailable;
                CONSOLE_WARNING(
                    "AircraftDictionary::IngestAirborneVelocitiesMessage: Ground speed not available for aircraft "
                    "0x%x.",
                    aircraft.icao_address);
                decode_successful = false;
            } else {
                aircraft.velocity_source = Aircraft::VelocitySource::kVelocitySourceGroundSpeed;
                bool direction_is_east_to_west = static_cast<bool>(packet.GetNBitWordFromMessage(1, 13));
                int v_x_kts = (v_ew_kts_plus_1 - 1) * (direction_is_east_to_west ? -1 : 1);
                bool direction_is_north_to_south = static_cast<bool>(packet.GetNBitWordFromMessage(1, 24));
                int v_y_kts = (v_ns_kts_plus_1 - 1) * (direction_is_north_to_south ? -1 : 1);
                if (is_supersonic) {
                    v_x_kts *= 4;
                    v_y_kts *= 4;
                }
                aircraft.velocity_kts = sqrtf(v_x_kts * v_x_kts + v_y_kts * v_y_kts);
                aircraft.heading_deg = wrapped_atan2f(v_x_kts, v_y_kts) * kRadiansToDegrees;
            }
            break;
        }
        case ADSBPacket::AirborneVelocitiesSubtype::kAirborneVelocitiesAirspeedSupersonic: {
            is_supersonic = true;
            // Cascade into airspeed calculation.
        }
        case ADSBPacket::AirborneVelocitiesSubtype::kAirborneVelocitiesAirspeedSubsonic: {
            int airspeed_kts_plus_1 = static_cast<int>(packet.GetNBitWordFromMessage(10, 25));
            if (airspeed_kts_plus_1 == 0) {
                CONSOLE_WARNING(
                    "AircraftDictionary::IngestAirborneVelocitiesMessage: Airspeed not available for aircraft "
                    "0x%x.",
                    aircraft.icao_address);
                decode_successful = false;
            } else {
                aircraft.velocity_kts = (airspeed_kts_plus_1 - 1) * (is_supersonic ? 4 : 1);
                bool is_true_airspeed = static_cast<bool>(packet.GetNBitWordFromMessage(1, 24));
                aircraft.velocity_source = is_true_airspeed
                                               ? Aircraft::VelocitySource::kVelocitySourceAirspeedTrue
                                               : Aircraft::VelocitySource::kVelocitySourceSirspeedIndicated;
                aircraft.heading_deg = static_cast<float>((packet.GetNBitWordFromMessage(10, 14) * 360) / 1024.0f);
            }

            break;
        }
        default:
            CONSOLE_ERROR(
                "AircraftDictionary::IngestAirborneVelocitiesMessage: Encountered invalid airborne velocities message "
                "subtype %d (valid values are 1-4).",
                subtype);
            return false;  // Don't attempt vertical rate decode if message type is invalid.
    }

    // Decode vertical rate.
    int vertical_rate_magnitude_fpm = packet.GetNBitWordFromMessage(9, 37);
    if (vertical_rate_magnitude_fpm == 0) {
        aircraft.vertical_rate_source = Aircraft::VerticalRateSource::kVerticalRateNotAvailable;
        CONSOLE_WARNING(
            "AircraftDictionary::IngestAirborneVelocitiesMessage: Vertical rate not available for aircraft "
            "0x%x.",
            aircraft.icao_address);
        decode_successful = false;
    } else {
        aircraft.vertical_rate_source = static_cast<Aircraft::VerticalRateSource>(packet.GetNBitWordFromMessage(1, 35));
        bool vertical_rate_sign_is_negative = packet.GetNBitWordFromMessage(1, 36);
        if (vertical_rate_sign_is_negative) {
            aircraft.vertical_rate_fpm = -(vertical_rate_magnitude_fpm - 1) * 64;
        } else {
            aircraft.vertical_rate_fpm = (vertical_rate_magnitude_fpm - 1) * 64;
        }
    }

    return decode_successful;
}

bool AircraftDictionary::IngestAircraftStatusMessage(Aircraft &aircraft, ADSBPacket packet) { return false; }

bool AircraftDictionary::IngestTargetStateAndStatusInfoMessage(Aircraft &aircraft, ADSBPacket packet) { return false; }

bool AircraftDictionary::IngestAircraftOperationStatusMessage(Aircraft &aircraft, ADSBPacket packet) { return false; }