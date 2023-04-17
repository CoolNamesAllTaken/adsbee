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

    // Ingest Lat / Lon CPR values.
    if (odd) {
        cpr_odd_timestamp_us_ = get_time_since_boot_us();

        // Store counts in case they need to be used for re-digestion later.
        n_lat_cpr_odd_ = n_lat_cpr;
        n_lon_cpr_odd_ = n_lon_cpr;

        // Equation 5.5
        lat_cpr_odd_ = static_cast<float>(n_lat_cpr) / kCPRLatLonMaxCount;
        lon_cpr_odd_ = static_cast<float>(n_lon_cpr) / kCPRLatLonMaxCount;
    } else {
        cpr_even_timestamp_us_ = get_time_since_boot_us();

        // Store counts in case they need to be used for re-digestion later.
        n_lat_cpr_even_ = n_lat_cpr;
        n_lon_cpr_even_ = n_lon_cpr;

        // Equation 5.5
        lat_cpr_even_ = static_cast<float>(n_lat_cpr) / kCPRLatLonMaxCount;
        lon_cpr_even_ = static_cast<float>(n_lon_cpr) / kCPRLatLonMaxCount;
    }

    /** Calculate Latitude **/
    // Equation 5.6
    int32_t lat_zone_index = floorf(59.0f * lat_cpr_even_ - 60.0f * lat_cpr_odd_ + 0.5f);

    if (odd) {
        // Equation 5.7
        lat_odd_ = kCPRdLatOdd * ((lat_zone_index % 59) + lat_cpr_odd_);
        // Equation 5.8
        lat_odd_ = lat_odd_ >= 270.0f ? lat_odd_ - 360.0f: lat_odd_; // wrap latitude to between -90 and +90 degrees.
        nl_lat_cpr_odd = calc_nl_cpr_from_lat(lat_odd_);
    } else {
        // Equation 5.7
        lat_even_ = kCPRdLatEven * ((lat_zone_index % 60) + lat_cpr_even_);
        // Equation 5.8
        lat_even_ = lat_even_ >= 270.0f ?lat_even_ - 360.0f : lat_even_; // wrap latitude to between -90 and +90 degrees.
        nl_lat_cpr_even_ = calc_nl_cpr_from_lat(lat_even_);
    }

    uint16_t nl_lat_cpr = odd ? nl_lat_cpr_odd : nl_lat_cpr_even_; // number of longitude zones (sorta)
    // Equation 5.10
    int32_t lon_zone_index = floorf(lon_cpr_even_ * (nl_lat_cpr - 1) - lon_cpr_odd_ * nl_lat_cpr + 0.5f);

    /** Calculate Longitude **/
    // Equation 5.11: Use nl_lat_cpr to calculate actual number of longitude zones
    uint16_t num_lon_zones = odd ? MAX(nl_lat_cpr-1, 1) : MAX(nl_lat_cpr, 1);
    // Equation 5.12: longitude zone size
    float d_lon = 360.0f / num_lon_zones;
    printf("num_lon_zones=%d lon_zone_index=%d\r\n", num_lon_zones, lon_zone_index);

    if (odd) {
        // Equation 5.13
        lon_odd_ = d_lon * ((lon_zone_index % num_lon_zones) + lon_cpr_odd_);
        // Equation 5.15
        lon_odd_ = lon_odd_ >= 180.0f ? lon_odd_ - 360.0f : lon_odd_; // wrap longitude to between -180 and +180 degrees
    } else {
        // Equation 5.13
        lon_even_ = d_lon * ((lon_zone_index % num_lon_zones) + lon_cpr_even_);
        // Equation 5.15
        lon_even_ = lon_even_ >= 180.0f ? lon_even_ - 360.0f : lon_even_; // wrap longitude to between -180 and +180 degrees
    }

    // Invalidate position if position pair is split across different latitude bands. Do this check at the end
    // so that the last packet of a split pair can still be used to pair with the next incoming packet.
    if (nl_lat_cpr_odd != nl_lat_cpr_even_) {
        // Latitude bands don't match between even and odd packets, so position fix isn't valid.
        if (!redigesting) {
            // Try re-digesting the last packet in case it digested improperly because it didn't have a buddy. Only allow one
            // level of recursion by setting redigesting=true. SetCPRLatLon will take care of position_valid and other public
            // variables for us!
            if (odd && cpr_even_timestamp_us_) {
                // Invalid odd packet: try re-digesting previously received even packet
                return SetCPRLatLon(n_lat_cpr_even_, n_lon_cpr_even_, false, true); 
            } else if (!odd && cpr_odd_timestamp_us_) {
                // Invalid even packet: try re-digesting previously received odd packet
                return SetCPRLatLon(n_lat_cpr_odd_, n_lon_cpr_odd_, true, true);
            }
        }
        // Can't redigest, aircraft position is invalid, keep reporting last known good coordinates.
        position_valid = false;
    } else {
        // Aircraft position is valid, update accessible coordinates.
        latitude = odd ? lat_odd_ : lat_even_; // Equation 5.9: expose most recent latitude for public consumption
        longitude = odd ? lon_odd_ : lon_even_; // Equation 5.14
        printf("setting latitude=%f, longitude=%f\r\n", latitude, longitude);
        position_valid = true;
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