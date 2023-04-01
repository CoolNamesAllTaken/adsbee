#include "aircraft_dictionary.hh"

Aircraft::Aircraft() {
    memset(callsign, '\0', kCallSignMaxNumChars); // clear out callsign string
}

AircraftDictionary::AircraftDictionary() {

}

bool AircraftDictionary::IngestADSBPacket(ADSBPacket packet) {
    if (packet.GetDownlinkFormat() != ADSBPacket::DF_EXTENDED_SQUITTER) {
        return false; // Only DF 17 supported for now.
    }
    switch(packet.GetTypeCodeEnum()) {
        case ADSBPacket::TC_AIRCRAFT_ID:
            return IngestAircraftIDMessage(packet);
            break;
        case ADSBPacket::TC_SURFACE_POSITION:
            return IngestSurfacePositionMessage(packet);
            break;
        case ADSBPacket::TC_AIRBORNE_POSITION_BARO_ALT:
            return IngestAirbornePositionBaroAltMessage(packet);
            break;
        case ADSBPacket::TC_AIRBORNE_VELOCITIES:
            return IngestAirborneVelocitiesMessage(packet);
            break;
        case ADSBPacket::TC_AIRBORNE_POSITION_GNSS_ALT:
            return IngestAirbornePositionGNSSAltMessage(packet);
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
bool AircraftDictionary::InsertAircraft(Aircraft aircraft) {
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
bool AircraftDictionary::GetAircraft(uint32_t icao_address, Aircraft &aircraft_out) {
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
bool AircraftDictionary::ContainsAircraft(uint32_t icao_address) {
    auto itr = aircraft_dictionary_.find(icao_address);
    if (itr != aircraft_dictionary_.end()) {
        return true;
    }
    return false;
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

bool AircraftDictionary::IngestAircraftIDMessage(ADSBPacket packet) {
    Aircraft aircraft;
    aircraft.wake_vortex = ExtractWakeVortex(packet);
    for (uint16_t i = 0; i < Aircraft::kCallSignMaxNumChars; i++) {
        aircraft.callsign[i] = packet.GetNBitWordFromMessage(6, 8+(6*i));
    }
    return false; // TODO: fix
}

bool AircraftDictionary::IngestSurfacePositionMessage(ADSBPacket packet) {
    return false;
}

bool AircraftDictionary::IngestAirbornePositionBaroAltMessage(ADSBPacket packet) {
    return false;
}

bool AircraftDictionary::IngestAirborneVelocitiesMessage(ADSBPacket packet) {
    return false;
}

bool AircraftDictionary::IngestAirbornePositionGNSSAltMessage(ADSBPacket packet) {
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