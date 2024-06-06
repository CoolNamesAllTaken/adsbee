#include "aircraft_dictionary.hh"

#include <cmath>

#include "decode_utils.hh"
#include "hal.hh"
#include "stdio.h"

#define MAX(a, b) ((a) > (b) ? (a) : (b))

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
        printf(
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
        printf(
            "Aircraft::DecodePosition: NL_cpr disagrees between odd (%d) and even (%d) packets. Can't decode "
            "position.\r\n",
            last_odd_packet_.nl_cpr, last_even_packet_.nl_cpr);
        return false;
    }

    // From here on out, can just focus on the most recent packet since that's what we're using for our position.
    bool received_odd_last = last_odd_packet_.received_timestamp_ms > last_even_packet_.received_timestamp_ms;
    CPRPacket &last_packet = received_odd_last ? last_odd_packet_ : last_even_packet_;
    latitude = last_packet.lat;  // Publish latitude.

    // Equation 5.10
    int32_t lon_zone_index = floorf(last_even_packet_.lon_cpr * (last_packet.nl_cpr - 1) -
                                    last_odd_packet_.lon_cpr * last_packet.nl_cpr + 0.5f);

    // Equation 5.11: Use nl_lat_cpr to calculate actual number of longitude zones
    uint16_t num_lon_zones = received_odd_last ? MAX(last_packet.nl_cpr - 1, 1) : MAX(last_packet.nl_cpr, 1);
    // Equation 5.12: longitude zone size
    float d_lon = 360.0f / num_lon_zones;

    // Equation 5.13 (calc longitude), 5.15 (wrap longitude to between -180 and +180 degrees)
    longitude = wrap_longitude(d_lon * ((lon_zone_index % num_lon_zones) + last_packet.lon_cpr));
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
    aircraft_dictionary_.clear();  // Remove all aircraft from the unordered map.
}

void AircraftDictionary::Update(uint32_t timestamp_ms) {
    // Iterate over each key-value pair in the unordered_map
    for (auto it = aircraft_dictionary_.begin(); it != aircraft_dictionary_.end(); /* No increment here */) {
        if (timestamp_ms - it->second.last_seen_timestamp_ms > config_.aircraft_prune_interval_ms) {
            it = aircraft_dictionary_.erase(it);  // Remove stale aircraft entry.
        } else {
            it++;  // Move to the next aircraft entry.
        }
    }
}

bool AircraftDictionary::IngestADSBPacket(ADSBPacket packet) {
    if (!packet.IsValid() || packet.GetDownlinkFormat() != ADSBPacket::DF_EXTENDED_SQUITTER) {
        return false;  // Only allow valid DF17 packets.
    }

    uint32_t icao_address = packet.GetICAOAddress();
    Aircraft *aircraft_ptr = GetAircraftPtr(icao_address);
    if (aircraft_ptr == nullptr) {
        printf(
            "AircraftDictionary::IngestADSBPacket: Unable to find or create new aircraft with ICAO address 0x%x in "
            "dictionay.\r\n",
            icao_address);
        return false;  // unable to find or create new aircraft in dictionary
    }
    aircraft_ptr->last_seen_timestamp_ms = get_time_since_boot_ms();

    switch (packet.GetTypeCodeEnum()) {
        case ADSBPacket::TC_AIRCRAFT_ID:
            return IngestAircraftIDMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::TC_SURFACE_POSITION:
            return IngestSurfacePositionMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::TC_AIRBORNE_POSITION_BARO_ALT:
        case ADSBPacket::TC_AIRBORNE_POSITION_GNSS_ALT:
            return IngestAirbornePositionMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::TC_AIRBORNE_VELOCITIES:
            return IngestAirborneVelocitiesMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::TC_RESERVED:
            return false;
            break;
        case ADSBPacket::TC_AIRCRAFT_STATUS:
            return IngestAircraftStatusMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::TC_TARGET_STATE_AND_STATUS_INFO:
            return IngestTargetStateAndStatusInfoMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::TC_AIRCRAFT_OPERATION_STATUS:
            return IngestAircraftOperationStatusMessage(*aircraft_ptr, packet);
            break;
        default:
            return false;  // TC_INVALID, etc.
    }

    return false;
}

uint16_t AircraftDictionary::GetNumAircraft() { return aircraft_dictionary_.size(); }

/**
 * Adds an Aircraft object to the aircraft dictionary, hashed by ICAO address.
 * @param[in] aircraft Aircraft to insert.
 * @retval True if insertaion succeeded, false if failed.
 */
bool AircraftDictionary::InsertAircraft(const Aircraft &aircraft) {
    auto itr = aircraft_dictionary_.find(aircraft.icao_address);
    if (itr != aircraft_dictionary_.end()) {
        // Overwriting an existing aircraft
        itr->second = aircraft;
        return true;
    }

    if (aircraft_dictionary_.size() >= kMaxNumAircraft) {
        return false;  // not enough room to add this aircraft
    }

    aircraft_dictionary_[aircraft.icao_address] = aircraft;  // add the new aircraft to the dictionary
    return true;
}

/**
 * Remove an aircraft from the dictionary, by ICAO address.
 * @retval True if removal succeeded, false if aircraft was not found.
 */
bool AircraftDictionary::RemoveAircraft(uint32_t icao_address) {
    auto itr = aircraft_dictionary_.find(icao_address);
    if (itr != aircraft_dictionary_.end()) {
        aircraft_dictionary_.erase(itr);
        return true;
    }
    return false;  // aircraft was not found in the dictionary
}

/**
 * Retrieve an aircraft from the dictionary.
 * @param[in] icao_address Address to use for looking up the aircraft.
 * @param[out] aircraft_out Aircraft reference to put the retrieved aircraft into if successful.
 * @retval True if aircraft was found and retrieved, false if aircraft was not in the dictionary.
 */
bool AircraftDictionary::GetAircraft(uint32_t icao_address, Aircraft &aircraft_out) const {
    auto itr = aircraft_dictionary_.find(icao_address);
    if (itr != aircraft_dictionary_.end()) {
        aircraft_out = itr->second;
        return true;
    }
    return false;  // aircraft not found
}

/**
 * Check if an aircraft is contained in the dictionary.
 * @param[in] icao_address Address to use for looking up the aircraft.
 * @retval True if aircraft is in the dictionary, false if not.
 */
bool AircraftDictionary::ContainsAircraft(uint32_t icao_address) const {
    auto itr = aircraft_dictionary_.find(icao_address);
    if (itr != aircraft_dictionary_.end()) {
        return true;
    }
    return false;
}

/**
 * Return a pointer to an aircraft if it's in the aircraft dictionary.
 * @param[in] icao_address ICAO address of the aircraft to find.
 * @retval Pointer to the aircraft if it exists, or NULL if it wasn't in the dictionary.
 */
Aircraft *AircraftDictionary::GetAircraftPtr(uint32_t icao_address) {
    auto itr = aircraft_dictionary_.find(icao_address);
    if (itr != aircraft_dictionary_.end()) {
        return &(itr->second);  // return address of existing aircraft
    } else if (aircraft_dictionary_.size() < kMaxNumAircraft) {
        Aircraft new_aircraft = Aircraft(icao_address);
        aircraft_dictionary_[icao_address] = new_aircraft;
        return &(aircraft_dictionary_[icao_address]);  // insert new aircraft and return its address
    }
    return nullptr;  // can't find the aircraft or insert a new one
}

/**
 * Private functions and associated helpers.
 */

/**
 * Returns the Wake Vortex value of the aircraft that sent a given ADS-B packet.
 * @param[in] packet ADS-B Packet to extract the WakeVortex value from. Must be
 * @retval WakeVortex_t that matches the combination of capability and typecode from the ADS-B packet, or
 * WV_INVALID if there is no matching wake vortex value.
 */
Aircraft::WakeVortex_t ExtractWakeVortex(const ADSBPacket &packet) {
    if (packet.GetTypeCodeEnum() != ADSBPacket::TC_AIRCRAFT_ID) {
        return Aircraft::WV_INVALID;  // Must have typecode from 1-4.
    }

    uint32_t typecode = packet.GetNBitWordFromMessage(5, 0);
    uint32_t category = packet.GetNBitWordFromMessage(3, 5);

    // Table 4.1 from The 1090Mhz Riddle (Junzi Sun), pg. 42.
    if (category == 0) {
        return Aircraft::WV_NO_CATEGORY_INFO;
    }

    switch (typecode) {
        case 1:
            return Aircraft::WV_RESERVED;
            break;
        case 2:
            switch (category) {
                case 1:
                    return Aircraft::WV_SURFACE_EMERGENCY_VEHICLE;
                    break;
                case 3:
                    return Aircraft::WV_SURVACE_SERVICE_VEHICLE;
                    break;
                case 4:
                case 5:
                case 6:
                case 7:
                    return Aircraft::WV_GROUND_OBSTRUCTION;
                    break;
                default:
                    return Aircraft::WV_INVALID;
            }
            break;
        case 3:
            switch (category) {
                case 1:
                    return Aircraft::WV_GLIDER_SAILPLANE;
                    break;
                case 2:
                    return Aircraft::WV_LIGHTER_THAN_AIR;
                    break;
                case 3:
                    return Aircraft::WV_PARACHUTIST_SKYDIVER;
                    break;
                case 4:
                    return Aircraft::WV_ULTRALIGHT_HANG_GLIDER_PARAGLIDER;
                    break;
                case 5:
                    return Aircraft::WV_RESERVED;
                    break;
                case 6:
                    return Aircraft::WV_UNMANNED_AERIAL_VEHICLE;
                    break;
                case 7:
                    return Aircraft::WV_SPACE_TRANSATMOSPHERIC_VEHICLE;
                    break;
                default:
                    return Aircraft::WV_INVALID;
            }
            break;
        case 4:
            switch (category) {
                case 1:
                    return Aircraft::WV_LIGHT;
                    break;
                case 2:
                    return Aircraft::WV_MEDIUM_1;
                    break;
                case 3:
                    return Aircraft::WV_MEDIUM_2;
                    break;
                case 4:
                    return Aircraft::WV_HIGH_VORTEX_AIRCRAFT;
                    break;
                case 5:
                    return Aircraft::WV_HEAVY;
                    break;
                case 6:
                    return Aircraft::WV_HIGH_PERFORMANCE;
                    break;
                case 7:
                    return Aircraft::WV_ROTORCRAFT;
                    break;
                default:
                    return Aircraft::WV_INVALID;
            }
            break;
        default:
            return Aircraft::WV_INVALID;
    }
}

/**
 * Ingests an Aircraft Identification ADS-B message. Called by IngestADSBPacket, which makes sure that the packet
 * is valid and has the correct Downlink Format.
 * @param[out] aircraft Reference to the Aircraft to populate with info pulled from packet.
 * @param[in] packet ADSBPacket to ingest.
 * @retval True if message was ingested successfully, false otherwise.
 */
bool AircraftDictionary::IngestAircraftIDMessage(Aircraft &aircraft, ADSBPacket packet) {
    aircraft.wake_vortex = ExtractWakeVortex(packet);
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
    // ME[6-7] - Surveillance Status
    aircraft.surveillance_status = static_cast<Aircraft::SurveillanceStatus_t>(packet.GetNBitWordFromMessage(2, 6));

    // ME[8] - Single Antenna Flag
    aircraft.single_antenna_flag = packet.GetNBitWordFromMessage(1, 8) ? true : false;

    // ME[9-20] - Encoded Altitude
    uint16_t encoded_altitude = packet.GetNBitWordFromMessage(12, 9);
    if (packet.GetTypeCodeEnum() == ADSBPacket::TC_AIRBORNE_POSITION_BARO_ALT) {
        aircraft.barometric_altitude = encoded_altitude;
    } else {
        aircraft.gnss_altitude = encoded_altitude;
    }

    // ME[21] - Time
    // TODO: figure out if we need this

    // ME[22] - CPR Format
    bool odd = packet.GetNBitWordFromMessage(1, 22);

    // ME[32-?]
    aircraft.SetCPRLatLon(packet.GetNBitWordFromMessage(17, 23), packet.GetNBitWordFromMessage(17, 40), odd);

    return false;
}

bool AircraftDictionary::IngestAirborneVelocitiesMessage(Aircraft &aircraft, ADSBPacket packet) { return false; }

bool AircraftDictionary::IngestAircraftStatusMessage(Aircraft &aircraft, ADSBPacket packet) { return false; }

bool AircraftDictionary::IngestTargetStateAndStatusInfoMessage(Aircraft &aircraft, ADSBPacket packet) { return false; }

bool AircraftDictionary::IngestAircraftOperationStatusMessage(Aircraft &aircraft, ADSBPacket packet) { return false; }