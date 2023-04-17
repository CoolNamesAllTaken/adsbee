#include "aircraft_dictionary.hh"
#include "stdio.h"

#include "decode_utils.hh"
#include "hal.hh"
#include <cmath>

#define MAX(a, b) ((a) > (b) ? (a) : (b))

/**
 * Aircraft
*/

Aircraft::Aircraft(uint32_t icao_address_in)
    : icao_address(icao_address_in) 
{
    memset(callsign, '\0', kCallSignMaxNumChars+1); // clear out callsign string, including extra EOS character
}

Aircraft::Aircraft() {
    memset(callsign, '\0', kCallSignMaxNumChars+1); // clear out callsign string, including extra EOS character
}

bool Aircraft::DecodePosition() {
    if (!(last_odd_packet_.is_valid && last_even_packet_.is_valid)/*airborne_decode_state_ != CPR_DS_RECEIVED_BOTH*/) {
        printf("Aircraft::DecodePosition: Unable to decode position without valid odd and even packet pair.\r\n");
        return false; // need both an even and an odd packet to be able to decode position
    }

    // Equation 5.6
    int32_t lat_zone_index = floorf(59.0f * last_even_packet_.lat_cpr - 60.0f * last_odd_packet_.lat_cpr + 0.5f);

    // bool received_odd_last = last_odd_packet_.timestamp_us > last_even_packet_.timestamp_us;
    // CPRPacket &last_packet = received_odd_last ? last_odd_packet_ : last_even_packet_;

    // TODO: Modify this structure! Right now I'm recalculating everything every time, but really I need to recalculate
    // lat for the complementary packet ONLY if it's never been done before. Otherwise, leave it and see if the new lat
    // that we come up with disagrees. Really need to calculate both on the CPR_DS_RECEIVED_XX_ONLY -> CPR_DS_RECEIVED_BOTH
    // transition. HOWEVER this makes a pretty big assumption so the position might still not be valid! Probably need at
    // least one more packet without a disagreeing nl_cpr to make sure that the position is actually valid.

    // Equation 5.7
    last_odd_packet_.lat = kCPRdLatOdd * ((lat_zone_index % 59) + last_odd_packet_.lat_cpr);
    // Equation 5.7
    last_even_packet_.lat = kCPRdLatEven * ((lat_zone_index % 60) + last_even_packet_.lat_cpr);

    // Equation 5.8: wrap latitude to between -90 and +90 degrees.
    last_odd_packet_.lat = last_odd_packet_.lat >= 270.0f ? last_odd_packet_.lat - 360.0f: last_odd_packet_.lat;
    last_even_packet_.lat = last_even_packet_.lat >= 270.0f ? last_even_packet_.lat - 360.0f: last_even_packet_.lat;
    
    // Calculate NL, which will be used later to calculate the number of longitude zones in this latitude band.
    last_odd_packet_.nl_cpr = calc_nl_cpr_from_lat(last_odd_packet_.lat);
    last_even_packet_.nl_cpr = calc_nl_cpr_from_lat(last_even_packet_.lat);

    if (last_odd_packet_.nl_cpr != last_even_packet_.nl_cpr) {
        // Invalidate position if position pair is split across different latitude bands.
        // TODO: I'm not sure this is ever possible? Would require the packets to have different .lat values, but those are calculated collaboratively
        // between the packets so I'm not sure how they could ever disagree. Maybe a tight edge case?
        position_valid = false; // keep last known good coordinates, but mark as invalid
        printf("Aircraft::DecodePosition: NL_cpr disagrees between odd (%d) and even (%d) packets. Can't decode position.\r\n", 
            last_odd_packet_.nl_cpr, last_even_packet_.nl_cpr);
        return false;
    }

    // From here on out, can just focus on the most recent packet since that's what we're using for our position.
    bool received_odd_last = last_odd_packet_.timestamp_us > last_even_packet_.timestamp_us;
    CPRPacket &last_packet = received_odd_last ? last_odd_packet_ : last_even_packet_;

    // Equation 5.10
    int32_t lon_zone_index = floorf(last_even_packet_.lon_cpr * (last_packet.nl_cpr - 1) - last_odd_packet_.lon_cpr * last_packet.nl_cpr + 0.5f);

    // Equation 5.11: Use nl_lat_cpr to calculate actual number of longitude zones
    uint16_t num_lon_zones = received_odd_last ? MAX(last_packet.nl_cpr-1, 1) : MAX(last_packet.nl_cpr, 1);
    // Equation 5.12: longitude zone size
    float d_lon = 360.0f / num_lon_zones;
    
    // Equation 5.13
    last_packet.lon = d_lon * ((lon_zone_index % num_lon_zones) + last_packet.lon_cpr);
    // Equation 5.15: wrap longitude to between -180 and +180 degrees
    last_packet.lon = last_packet.lon >= 180.0f ? last_packet.lon - 360.0f : last_packet.lon;

    // Update public variables and mark position as valid.
    latitude = last_packet.lat;
    longitude = last_packet.lon;
    position_valid = true;
    return true;
}

/**
 * @brief Set an aircraft's position in Compact Position Reporting (CPR) format. Takes either an even or odd set of lat/lon
 * coordinates and uses them to set the aircraft's position.
 * @param[in] n_lat_cpr 17-bit latitude count.
 * @param[in] n_lon_cpr 17-bit longitude count.
 * @param[in] odd Boolean indicating that the position update is relative to an odd grid reference (if true) or an even grid reference.
 * @param[in] redigesting Boolean flag used if SetCPRLatLon is being used to re-digest a packet. Assures that it won't call itself again if set.
 * @retval True if coordinates were parsed successfully, false if not. NOTE: invalid positions can still be considered a successful parse.
*/
bool Aircraft::SetCPRLatLon(uint32_t n_lat_cpr, uint32_t n_lon_cpr, bool odd, bool redigesting) {
    if (n_lat_cpr > kCPRLatLonMaxCount || n_lon_cpr > kCPRLatLonMaxCount) {
        return false; // counts out of bounds, don't parse
    }

    CPRPacket &packet = odd ? last_odd_packet_ : last_even_packet_;
    packet.timestamp_us = get_time_since_boot_us();
    packet.n_lat = n_lat_cpr;
    packet.n_lon = n_lon_cpr;
    // Equation 5.5
    packet.lat_cpr = static_cast<float>(n_lat_cpr) / kCPRLatLonMaxCount;
    packet.lon_cpr = static_cast<float>(n_lon_cpr) / kCPRLatLonMaxCount;
    packet.is_valid = true;

    CPRPacket &other_packet = odd ? last_even_packet_ : last_odd_packet_;
    if (other_packet.is_valid) {
        airborne_decode_state_ = CPR_DS_RECEIVED_BOTH;
    } else {
        airborne_decode_state_ = odd ? CPR_DS_RECEIVED_ODD_ONLY : CPR_DS_RECEIVED_EVEN_ONLY;
    }

    return true;
}

/**
 * Aircraft Dictionary
*/

AircraftDictionary::AircraftDictionary() {

}

bool AircraftDictionary::IngestADSBPacket(ADSBPacket packet) {
    if (!packet.IsValid() || packet.GetDownlinkFormat() != ADSBPacket::DF_EXTENDED_SQUITTER) {
        return false; // Only allow valid DF17 packets.
    }

    switch(packet.GetTypeCodeEnum()) {
        case ADSBPacket::TC_AIRCRAFT_ID:
            return IngestAircraftIDMessage(packet);
            break;
        case ADSBPacket::TC_SURFACE_POSITION:
            return IngestSurfacePositionMessage(packet);
            break;
        case ADSBPacket::TC_AIRBORNE_POSITION_BARO_ALT:
        case ADSBPacket::TC_AIRBORNE_POSITION_GNSS_ALT:
            return IngestAirbornePositionMessage(packet);
            break;
        case ADSBPacket::TC_AIRBORNE_VELOCITIES:
            return IngestAirborneVelocitiesMessage(packet);
            break;
        case ADSBPacket::TC_RESERVED:
            return false;
            break;
        case ADSBPacket::TC_AIRCRAFT_STATUS:
            return IngestAircraftStatusMessage(packet);
            break;
        case ADSBPacket::TC_TARGET_STATE_AND_STATUS_INFO:
            return IngestTargetStateAndStatusInfoMessage(packet);
            break;
        case ADSBPacket::TC_AIRCRAFT_OPERATION_STATUS:
            return IngestAircraftOperationStatusMessage(packet);
            break;
        default:
            return false; // TC_INVALID, etc.
    }

    return false;
}

uint16_t AircraftDictionary::GetNumAircraft() {
    return aircraft_dictionary_.size();
}

/**
 * @brief Adds an Aircraft object to the aircraft dictionary, hashed by ICAO address.
 * @param[in] aircraft Aircraft to insert.
 * @retval True if insertaion succeeded, false if failed.
*/
bool AircraftDictionary::InsertAircraft(const Aircraft aircraft) {
    auto itr = aircraft_dictionary_.find(aircraft.icao_address);
    if (itr != aircraft_dictionary_.end()) {
        // Overwriting an existing aircraft
        itr->second = aircraft;
        return true;
    }

    if (aircraft_dictionary_.size() >= kMaxNumAircraft) {
        return false; // not enough room to add this aircraft
    }

    aircraft_dictionary_[aircraft.icao_address] = aircraft; // add the new aircraft to the dictionary
    return true;
}

/**
 * @brief Remove an aircraft from the dictionary, by ICAO address.
 * @retval True if removal succeeded, false if aircraft was not found.
*/
bool AircraftDictionary::RemoveAircraft(uint32_t icao_address) {
    auto itr = aircraft_dictionary_.find(icao_address);
    if (itr != aircraft_dictionary_.end()) {
        aircraft_dictionary_.erase(itr);
        return true;
    }
    return false; // aircraft was not found in the dictionary
}

/**
 * @brief Retrieve an aircraft from the dictionary.
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
    return false; // aircraft not found
}

/**
 * @brief Check if an aircraft is contained in the dictionary.
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
 * @brief Return a pointer to an aircraft if it's in the aircraft dictionary.
 * @param[in] icao_address ICAO address of the aircraft to find.
 * @retval Pointer to the aircraft if it exists, or NULL if it wasn't in the dictionary.
*/
Aircraft * AircraftDictionary::GetAircraftPtr(uint32_t icao_address) {
    auto itr = aircraft_dictionary_.find(icao_address);
    if (itr != aircraft_dictionary_.end()) {
        return &(itr->second); // return address of existing aircraft
    } else if (aircraft_dictionary_.size() < kMaxNumAircraft) {
        Aircraft new_aircraft = Aircraft(icao_address);
        aircraft_dictionary_[icao_address] = new_aircraft;
        return &(aircraft_dictionary_[icao_address]); // insert new aircraft and return its address
    }
    return NULL; // can't find the aircraft or insert a new one
}

/**
 * Private functions and associated helpers.
*/

/**
 * @brief Returns the Wake Vortex value of the aircraft that sent a given ADS-B packet.
 * @param[in] packet ADS-B Packet to extract the WakeVortex value from. Must be 
 * @retval WakeVortex_t that matches the combination of capability and typecode from the ADS-B packet, or
 * WV_INVALID if there is no matching wake vortex value.
*/
Aircraft::WakeVortex_t ExtractWakeVortex(const ADSBPacket &packet) {
    if (packet.GetTypeCodeEnum() != ADSBPacket::TC_AIRCRAFT_ID) {
        return Aircraft::WV_INVALID; // Must have typecode from 1-4.
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
            switch(category) {
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
            switch(category) {
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
            switch(category) {
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
 * @brief Ingests an Aircraft Identification ADS-B message. Called by IngestADSBPacket, which makes sure that the packet
 * is valid and has the correct Downlink Format.
 * @retval True if message was ingested successfully, false otherwise.
*/
bool AircraftDictionary::IngestAircraftIDMessage(ADSBPacket packet) {
    uint32_t icao_address = packet.GetICAOAddress();

    Aircraft * aircraft = GetAircraftPtr(icao_address);
    if (aircraft == NULL) {
        printf("AircraftDictionary::IngestAircraftIDMessage: Unable to find or create new aircraft in dictionay.\r\n");
        return false; // unable to find or create new aircraft in dictionary
    }

    aircraft->wake_vortex = ExtractWakeVortex(packet);
    aircraft->transponder_capability = packet.GetCapability();
    for (uint16_t i = 0; i < Aircraft::kCallSignMaxNumChars; i++) {
        char callsign_char = lookup_callsign_char(packet.GetNBitWordFromMessage(6, 8+(6*i)));
        if (callsign_char == ' ') break; // ignore trailing spaces
        aircraft->callsign[i] = callsign_char;
    }

    return true;
}

bool AircraftDictionary::IngestSurfacePositionMessage(ADSBPacket packet) {
    uint32_t icao_address = packet.GetICAOAddress();

    Aircraft * aircraft = GetAircraftPtr(icao_address);
    if (aircraft == NULL) {
        printf("AircraftDictionary::IngestSurfacePositionMessage: Unable to find or create new aircraft in dictionay.\r\n");
        return false; // unable to find or create new aircraft in dictionary
    }

    return false;
}

bool AircraftDictionary::IngestAirbornePositionMessage(ADSBPacket packet) {
    uint32_t icao_address = packet.GetICAOAddress();

    Aircraft * aircraft = GetAircraftPtr(icao_address);
    if (aircraft == NULL) {
        printf("AircraftDictionary::IngestAirbornePositionBaroAltMessage: Unable to find or create new aircraft in dictionay.\r\n");
        return false; // unable to find or create new aircraft in dictionary
    }
    
    // ME[6-7] - Surveillance Status
    aircraft->surveillance_status = static_cast<Aircraft::SurveillanceStatus_t>(packet.GetNBitWordFromMessage(2, 6));
    
    // ME[8] - Single Antenna Flag
    aircraft->single_antenna_flag = packet.GetNBitWordFromMessage(1, 8) ? true : false;

    // ME[9-20] - Encoded Altitude
    uint16_t encoded_altitude = packet.GetNBitWordFromMessage(12, 9);
    if (packet.GetTypeCodeEnum() == ADSBPacket::TC_AIRBORNE_POSITION_BARO_ALT) {
        aircraft->barometric_altitude = encoded_altitude;
    } else {
        aircraft->gnss_altitude = encoded_altitude;
    }

 

    // ME[21] - Time
    // TODO: figure out if we need this

    // ME[22] - CPR Format
    bool odd = packet.GetNBitWordFromMessage(1, 22);

    // ME[32-?]
    aircraft->SetCPRLatLon(packet.GetNBitWordFromMessage(17, 23), packet.GetNBitWordFromMessage(17, 40), odd);
    
    return false;
}

bool AircraftDictionary::IngestAirborneVelocitiesMessage(ADSBPacket packet) {
    return false;
}

bool AircraftDictionary::IngestAircraftStatusMessage(ADSBPacket packet) {
    return false;
}

bool AircraftDictionary::IngestTargetStateAndStatusInfoMessage(ADSBPacket packet) {
    return false;
}

bool AircraftDictionary::IngestAircraftOperationStatusMessage(ADSBPacket packet) {
    return false;
}