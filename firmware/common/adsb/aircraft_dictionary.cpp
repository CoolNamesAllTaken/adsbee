#include "aircraft_dictionary.hh"

#include <cmath>

#include "comms.hh"  // For debug logging.
#include "decode_utils.hh"
#include "hal.hh"
#include "macros.hh"
#include "unit_conversions.hh"

#ifdef USE_NASA_CPR
#include "nasa_cpr.hh"
#endif

const float kRadiansToDegrees = 360.0f / (2.0f * M_PI);

/**
 * Aircraft
 */

Aircraft::Aircraft(uint32_t icao_address_in) : icao_address(icao_address_in) {
    // memset(callsign, '\0', kCallSignMaxNumChars + 1);  // clear out callsign string, including extra EOS character
}

Aircraft::Aircraft() {
    // memset(callsign, '\0', kCallSignMaxNumChars + 1);  // clear out callsign string, including extra EOS character
}

bool Aircraft::CanDecodePosition() {
    // TODO: There could be a condition here where we temporarily lose packets when the MLAT counter wraps around and
    // the packet timestamps all get seen as 0ms, but this probably is not a big deal.
    if (!(last_odd_packet_.received_timestamp_ms > 0 && last_even_packet_.received_timestamp_ms > 0)) {
        CONSOLE_WARNING("Aircraft::DecodePosition",
                        "Unable to decode position without receiving an odd and even packet pair.\r\n");
        return false;  // need both an even and an odd packet to be able to decode position
    }
    uint32_t cpr_interval_ms = MIN(last_odd_packet_.received_timestamp_ms - last_even_packet_.received_timestamp_ms,
                                   last_even_packet_.received_timestamp_ms - last_odd_packet_.received_timestamp_ms);
    if (cpr_interval_ms > GetMaxAllowedCPRIntervalMs()) {
        // Reject CPR packet pairings that are too far apart in time.
        WriteBitFlag(BitFlag::kBitFlagPositionValid,
                     false);  // keep last known good coordinates, but mark as invalid
        CONSOLE_WARNING("Aircraft::DecodePosition",
                        "CPR packet pair too far apart in time (%lu ms). Can't decode position.\r\n", cpr_interval_ms);
        return false;
    }
    return true;
}

bool Aircraft::DecodePosition() {
    // WARNING: There are two separate timebases in play here! The timebase for CPR packet timestamps is the MLAT
    // timebase, while higher level aircraft dictionary info is in system time.

    if (!CanDecodePosition()) {
        // Can't try forcing a decode and seeing if it's valid, since we'll end up using a stale even or odd packet
        // pairing.
        return false;
    }

#ifndef USE_NASA_CPR
    // Equation 5.6
    int32_t lat_zone_index = floorf(59.0f * last_even_packet_.lat_cpr - 60.0f * last_odd_packet_.lat_cpr + 0.5f);

    // Equation 5.7
    last_odd_packet_.lat = kCPRdLatOdd * ((lat_zone_index % 59) + last_odd_packet_.lat_cpr);
    // Equation 5.8: wrap latitude to between -90 and +90 degrees.
    last_odd_packet_.lat = WrapCPRDecodeLatitude(last_odd_packet_.lat);
    // Calculate NL, which will be used later to calculate the number of longitude zones in this latitude band.
    last_odd_packet_.nl_cpr = CalcNLCPRFromLat(last_odd_packet_.lat);

    // Equation 5.7
    last_even_packet_.lat = kCPRdLatEven * ((lat_zone_index % 60) + last_even_packet_.lat_cpr);
    // Equation 5.8: wrap latitude to between -90 and +90 degrees.
    last_even_packet_.lat = WrapCPRDecodeLatitude(last_even_packet_.lat);
    // Calculate NL, which will be used later to calculate the number of longitude zones in this latitude band.
    last_even_packet_.nl_cpr = CalcNLCPRFromLat(last_even_packet_.lat);

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
        // WriteBitFlag(BitFlag::kBitFlagPositionValid, false);  // keep last known good coordinates, but mark as
        // invalid
        CONSOLE_WARNING("Aircraft::DecodePosition",
                        "NL_cpr disagrees between odd (%d) and even (%d) packets. Can't decode "
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
    longitude_deg = WrapCPRDecodeLongitude(d_lon * ((lon_zone_index % num_lon_zones) + last_packet.lon_cpr));
    WriteBitFlag(BitFlag::kBitFlagPositionValid, true);  // TODO: Add "reasonable validation" that position is valid.

    last_track_update_timestamp_ms = get_time_since_boot_ms();  // Update last track update timestamp.
    return true;
#else
    NASACPRDecoder::DecodedPosition result;
    bool result_valid =
        NASACPRDecoder::DecodeAirborneGlobalCPR({.odd = false,
                                                 .lat_cpr = last_even_packet_.n_lat,
                                                 .lon_cpr = last_even_packet_.n_lon,
                                                 .received_timestamp_ms = last_even_packet_.received_timestamp_ms},
                                                {.odd = true,
                                                 .lat_cpr = last_odd_packet_.n_lat,
                                                 .lon_cpr = last_odd_packet_.n_lon,
                                                 .received_timestamp_ms = last_odd_packet_.received_timestamp_ms},
                                                result);

    if (result_valid) {
        WriteBitFlag(BitFlag::kBitFlagPositionValid, true);
        latitude_deg = WrapCPRDecodeLatitude(result.lat_deg);
        longitude_deg = WrapCPRDecodeLongitude(result.lon_deg);
        last_track_update_timestamp_ms = get_time_since_boot_ms();  // Update last track update timestamp.
    }
    return result_valid;
#endif
}

/**
 * Aircraft Dictionary
 */

void AircraftDictionary::Init() {
    dict.clear();  // Remove all aircraft from the unordered map.
}

void AircraftDictionary::Update(uint32_t timestamp_ms) {
    // Iterate over each key-value pair in the unordered_map. Prune if stale, update metrics if still fresh.
    for (auto it = dict.begin(); it != dict.end(); /* No increment here */) {
        if (timestamp_ms - it->second.last_message_timestamp_ms > config_.aircraft_prune_interval_ms) {
            it = dict.erase(it);  // Remove stale aircraft entry.
        } else {
            it->second.UpdateMetrics();
            it++;  // Move to the next aircraft entry.
        }
    }

    // Update aggregate statistics.
    metrics = metrics_counter_;    // Swap counter values over to publicly visible values.
    metrics_counter_ = Metrics();  // Use default constructor to clear all values.
}

bool AircraftDictionary::ContainsAircraft(uint32_t icao_address) const {
    auto itr = dict.find(icao_address);
    if (itr != dict.end()) {
        return true;
    }
    return false;
}

bool AircraftDictionary::GetAircraft(uint32_t icao_address, Aircraft &aircraft_out) const {
    auto itr = dict.find(icao_address);
    if (itr != dict.end()) {
        aircraft_out = itr->second;
        return true;
    }
    return false;  // aircraft not found
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

uint16_t AircraftDictionary::GetNumAircraft() { return dict.size(); }

bool AircraftDictionary::IngestDecoded1090Packet(Decoded1090Packet &packet) {
    int16_t source = packet.GetRaw().source;
    switch (packet.GetBufferLenBits()) {
        case Raw1090Packet::kSquitterPacketLenBits:
            // Validate packet against ICAO addresses in dictionary, or allow it in if it's a DF=11 all call reply
            // packet tha validated itself (e.g. it's a response to a spontaneous acquisition squitter with interrogator
            // ID=0, making the checksum useable).
            if (packet.GetDownlinkFormat() != Decoded1090Packet::kDownlinkFormatAllCallReply &&
                ContainsAircraft(packet.GetICAOAddress())) {
                // DF=0,4-5 (DF=11 doesn't work with this since the interrogator ID may be overlaid with the ICAO
                // address--we expect spontaneous acquisition DF=11's to come in pre-marked as valid).
                // Packet is a 56-bit Squitter packet that is incapable of validating itself, and its CRC was
                // validated against the ICAO addresses in the aircraft dictionary.
                packet.ForceValid();
            }

            if (!packet.IsValid()) {
                // Squitter frame could not validate itself, or could not be validated against ICAOs in dictionary.
                return false;
            }

            // Record a valid squitter packet.
            metrics_counter_.valid_squitter_frames++;
            if (source > 0) {
                metrics_counter_.valid_squitter_frames_by_source[source]++;
            }
            break;
        case Raw1090Packet::kExtendedSquitterPacketLenBits:
            if (packet.IsValid()) {
                metrics_counter_.valid_extended_squitter_frames++;
                if (source > 0) {
                    metrics_counter_.valid_extended_squitter_frames_by_source[source]++;
                }
            } else {
                return false;  // Extended squitter frame failed CRC.
            }
            break;
        default:
            CONSOLE_ERROR(
                "AircraftDictionary::IngestDecoded1090Packet",
                "Received packet with unrecognized bitlength %d, expected %d (Squitter) or %d (Extended Squitter).",
                packet.GetBufferLenBits(), Raw1090Packet::kSquitterPacketLenBits,
                Raw1090Packet::kExtendedSquitterPacketLenBits);
            return false;
    }

    uint16_t downlink_format = packet.GetDownlinkFormat();
    switch (downlink_format) {
        // Altitude Reply Packet.
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatAltitudeReply:
            IngestAltitudeReplyPacket(AltitudeReplyPacket(packet));
            break;
        // Identity Reply Packet.
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatIdentityReply:
            IngestIdentityReplyPacket(IdentityReplyPacket(packet));
            break;
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatAllCallReply:  // DF = 11
            IngestAllCallReplyPacket(AllCallReplyPacket(packet));
            break;
        // ADS-B Packets.
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatExtendedSquitter:                // DF = 17
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatExtendedSquitterNonTransponder:  // DF = 18
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatMilitaryExtendedSquitter:        // DF = 19
            // Handle ADS-B Packets.
            return IngestADSBPacket(ADSBPacket(packet));
            break;
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatShortRangeAirToAirSurveillance:  // DF = 0
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatLongRangeAirToAirSurveillance:   // DF = 16
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatCommBAltitudeReply:              // DF = 20
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatCommBIdentityReply:              // DF = 21
        case Decoded1090Packet::DownlinkFormat::kDownlinkFormatCommDExtendedLengthMessage:      // DF = 24
            // Silently handle currently unsupported downlink formats.
            break;

        default:
            CONSOLE_WARNING("AircraftDictionary::IngestDecoded1090Packet", "Encountered unexpected downlink format %d.",
                            downlink_format);
            return false;
    }
    return true;
}

bool AircraftDictionary::IngestIdentityReplyPacket(IdentityReplyPacket packet) {
    if (!packet.IsValid() || packet.GetDownlinkFormat() != IdentityReplyPacket::kDownlinkFormatIdentityReply) {
        return false;
    }

    uint32_t icao_address = packet.GetICAOAddress();
    Aircraft *aircraft_ptr = GetAircraftPtr(icao_address);
    if (aircraft_ptr == nullptr) {
        CONSOLE_WARNING("AircraftDictionary::IngestIdentityReplyPacket",
                        "Unable to find or create new aircraft with ICAO address 0x%lx in dictionary.\r\n",
                        icao_address);
        return false;  // unable to find or create new aircraft in dictionary
    }
    aircraft_ptr->WriteBitFlag(Aircraft::BitFlag::kBitFlagIsAirborne, packet.IsAirborne());
    aircraft_ptr->WriteBitFlag(Aircraft::BitFlag::kBitFlagAlert, packet.HasAlert());
    aircraft_ptr->WriteBitFlag(Aircraft::BitFlag::kBitFlagIdent, packet.HasIdent());
    aircraft_ptr->squawk = packet.GetSquawk();
    aircraft_ptr->IncrementNumFramesReceived(false);

    return true;
}

bool AircraftDictionary::IngestAltitudeReplyPacket(AltitudeReplyPacket packet) {
    if (!packet.IsValid() || packet.GetDownlinkFormat() != AltitudeReplyPacket::kDownlinkFormatAltitudeReply) {
        return false;
    }

    uint32_t icao_address = packet.GetICAOAddress();
    Aircraft *aircraft_ptr = GetAircraftPtr(icao_address);
    if (aircraft_ptr == nullptr) {
        CONSOLE_WARNING("AircraftDictionary::IngestAltitudeReplyPacket",
                        "Unable to find or create new aircraft with ICAO address 0x%lx in dictionary.\r\n",
                        icao_address);
        return false;  // unable to find or create new aircraft in dictionary
    }
    aircraft_ptr->WriteBitFlag(Aircraft::BitFlag::kBitFlagIsAirborne, packet.IsAirborne());
    aircraft_ptr->WriteBitFlag(Aircraft::BitFlag::kBitFlagAlert, packet.HasAlert());
    aircraft_ptr->WriteBitFlag(Aircraft::BitFlag::kBitFlagIdent, packet.HasIdent());
    aircraft_ptr->baro_altitude_ft = packet.GetAltitudeFt();
    aircraft_ptr->WriteBitFlag(Aircraft::BitFlag::kBitFlagBaroAltitudeValid, true);
    aircraft_ptr->WriteBitFlag(Aircraft::BitFlag::kBitFlagUpdatedBaroAltitude, true);
    aircraft_ptr->IncrementNumFramesReceived(false);

    return true;
}

bool AircraftDictionary::IngestAllCallReplyPacket(AllCallReplyPacket packet) {
    if (!packet.IsValid() || packet.GetDownlinkFormat() != Decoded1090Packet::kDownlinkFormatAllCallReply) {
        return false;
    }

    // Populate the dictionary with the aircraft, or look it up if the ICAO doesn't yet exist.
    uint32_t icao_address = packet.GetICAOAddress();
    Aircraft *aircraft_ptr = GetAircraftPtr(icao_address);
    if (aircraft_ptr == nullptr) {
        CONSOLE_WARNING("AircraftDictionary::IngestAllCallReplyPacket",
                        "Unable to find or create new aircraft with ICAO address 0x%lx in dictionary.\r\n",
                        icao_address);
        return false;  // unable to find or create new aircraft in dictionary
    }
    aircraft_ptr->last_message_timestamp_ms = get_time_since_boot_ms();

    // Update aircaft transponder capability.
    aircraft_ptr->transponder_capability = packet.GetCapability();

    return true;
}

bool AircraftDictionary::IngestADSBPacket(ADSBPacket packet) {
    if (!packet.IsValid() || packet.GetDownlinkFormat() != ADSBPacket::kDownlinkFormatExtendedSquitter) {
        return false;  // Only allow valid DF17 packets.
    }

    uint32_t icao_address = packet.GetICAOAddress();
    Aircraft *aircraft_ptr = GetAircraftPtr(icao_address);
    if (aircraft_ptr == nullptr) {
        CONSOLE_WARNING("AircraftDictionary::IngestADSBPacket",
                        "Unable to find or create new aircraft with ICAO address 0x%lx in dictionary.\r\n",
                        icao_address);
        return false;  // unable to find or create new aircraft in dictionary
    }
    aircraft_ptr->last_message_timestamp_ms = get_time_since_boot_ms();

    bool ret = false;
    uint16_t typecode = packet.GetTypeCode();
    switch (typecode) {
        case ADSBPacket::kTypeCodeAircraftID:      // TC = 1 (Aircraft Identification)
        case ADSBPacket::kTypeCodeAircraftID + 1:  // TC = 2 (Aircraft Identification)
        case ADSBPacket::kTypeCodeAircraftID + 2:  // TC = 3 (Aircraft Identification)
        case ADSBPacket::kTypeCodeAircraftID + 3:  // TC = 4 (Aircraft Identification)
            ret = ApplyAircraftIDMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeSurfacePosition:      // TC = 5 (Surface Position)
        case ADSBPacket::kTypeCodeSurfacePosition + 1:  // TC = 6 (Surface Position)
        case ADSBPacket::kTypeCodeSurfacePosition + 2:  // TC = 7 (Surface Position)
        case ADSBPacket::kTypeCodeSurfacePosition + 3:  // TC = 8 (Surface Position)
            ret = ApplySurfacePositionMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeAirbornePositionBaroAlt:      // TC = 9 (Airborne Position w/ Baro Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionBaroAlt + 1:  // TC = 10 (Airborne Position w/ Baro Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionBaroAlt + 2:  // TC = 11 (Airborne Position w/ Baro Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionBaroAlt + 3:  // TC = 12 (Airborne Position w/ Baro Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionBaroAlt + 4:  // TC = 13 (Airborne Position w/ Baro Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionBaroAlt + 5:  // TC = 14 (Airborne Position w/ Baro Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionBaroAlt + 6:  // TC = 15 (Airborne Position w/ Baro Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionBaroAlt + 7:  // TC = 16 (Airborne Position w/ Baro Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionBaroAlt + 8:  // TC = 17 (Airborne Position w/ Baro Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionBaroAlt + 9:  // TC = 18 (Airborne Position w/ Baro Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionGNSSAlt:      // TC = 20 (Airborne Position w/ GNSS Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionGNSSAlt + 1:  // TC = 21 (Airborne Position w/ GNSS Altitude)
        case ADSBPacket::kTypeCodeAirbornePositionGNSSAlt + 2:  // TC = 22 (Airborne Position w/ GNSS Altitude)
            ret = ApplyAirbornePositionMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeAirborneVelocities:  // TC = 19 (Airborne Velocities)
            ret = ApplyAirborneVelocitiesMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeReserved:      // TC = 23 (Reserved)
        case ADSBPacket::kTypeCodeReserved + 1:  // TC = 24 (Reserved)
        case ADSBPacket::kTypeCodeReserved + 2:  // TC = 25 (Reserved)
        case ADSBPacket::kTypeCodeReserved + 3:  // TC = 26 (Reserved)
        case ADSBPacket::kTypeCodeReserved + 4:  // TC = 27 (Reserved)
            ret = false;
            break;
        case ADSBPacket::kTypeCodeAircraftStatus:  // TC = 28 (Aircraft Status)
            ret = ApplyAircraftStatusMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeTargetStateAndStatusInfo:  // TC = 29 (Target state and status info)
            ret = ApplyTargetStateAndStatusInfoMessage(*aircraft_ptr, packet);
            break;
        case ADSBPacket::kTypeCodeAircraftOperationStatus:  // TC = 31 (Aircraft operation status)
            ret = ApplyAircraftOperationStatusMessage(*aircraft_ptr, packet);
            break;
        default:
            CONSOLE_WARNING("AircraftDictionary::IngestADSBPacket",
                            "Received ADSB message with unsupported typecode %d.", typecode);
            ret = false;  // kTypeCodeInvalid, etc.
    }
    if (ret) aircraft_ptr->IncrementNumFramesReceived(true);  // Count the received Mode S frame.
    return ret;
}

bool AircraftDictionary::InsertAircraft(const Aircraft &aircraft) {
    auto itr = dict.find(aircraft.icao_address);
    if (itr != dict.end()) {
        // Overwriting an existing aircraft
        itr->second = aircraft;
        return true;
    }

    if (dict.size() >= kMaxNumAircraft) {
        CONSOLE_INFO("AIrcraftDictionary::InsertAircraft",
                     "Failed to add aircraft to dictionary, max number of aircraft is %d.", kMaxNumAircraft);
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

bool Aircraft::SetCPRLatLon(uint32_t n_lat_cpr, uint32_t n_lon_cpr, bool odd, uint32_t received_timestamp_ms) {
    if (n_lat_cpr > kCPRLatLonMaxCount || n_lon_cpr > kCPRLatLonMaxCount) {
        CONSOLE_ERROR("Aircraft::SetCPRLatLon", "Received CPR packet with out of bounds lat/lon values (%lu, %lu).",
                      n_lat_cpr, n_lon_cpr);
        return false;  // counts out of bounds, don't parse
    }
    CPRPacket &complementary_packet = odd ? last_even_packet_ : last_odd_packet_;
    uint32_t received_timestamp_delta_ms = received_timestamp_ms > complementary_packet.received_timestamp_ms
                                               ? received_timestamp_ms - complementary_packet.received_timestamp_ms
                                               : complementary_packet.received_timestamp_ms - received_timestamp_ms;
    if (received_timestamp_delta_ms > GetMaxAllowedCPRIntervalMs()) {
        // Clear out old packet to avoid an invalid decode from packets that are too far apart in time.
        ClearCPRPackets();
    }

    CPRPacket &packet = odd ? last_odd_packet_ : last_even_packet_;
    // NOTE: Packet received timestamps are from the MLAT timer.
    packet.received_timestamp_ms = received_timestamp_ms;
    packet.n_lat = n_lat_cpr;
    packet.n_lon = n_lon_cpr;
#ifndef USE_NASA_CPR
    // Equation 5.5
    packet.lat_cpr = static_cast<float>(n_lat_cpr) / kCPRLatLonMaxCount;
    packet.lon_cpr = static_cast<float>(n_lon_cpr) / kCPRLatLonMaxCount;
#endif
    return true;
}

/**
 * Private functions and associated helpers.
 */

/**
 * Returns the Wake Vortex category of the aircraft that sent a given ADS-B packet. Note that some categories have a
 * many to one mapping!
 * @param[in] packet ADS-B Packet to extract the Category value from. Must be
 * @retval Category that matches the combination of capability and typecode from the ADS-B packet, or
 * kCategoryInvalid if there is no matching wake vortex value.
 */
Aircraft::Category ExtractCategory(const ADSBPacket &packet) {
    uint8_t typecode = packet.GetNBitWordFromMessage(5, 0);
    uint8_t capability = packet.GetNBitWordFromMessage(3, 5);

    // Table 4.1 from The 1090Mhz Riddle (Junzi Sun), pg. 42.
    if (capability == 0) {
        return Aircraft::kCategoryNoCategoryInfo;
    }

    switch (typecode) {
        case 1:
            return Aircraft::kCategoryReserved;
            break;
        case 2:
            switch (capability) {
                case 1:
                    return Aircraft::kCategorySurfaceEmergencyVehicle;
                    break;
                case 3:
                    return Aircraft::kCategorySurfaceServiceVehicle;
                    break;
                case 4:
                case 5:
                case 6:
                case 7:
                    return Aircraft::kCategoryGroundObstruction;
                    break;
                default:
                    return Aircraft::kCategoryInvalid;
            }
            break;
        case 3:
            switch (capability) {
                case 1:
                    return Aircraft::kCategoryGliderSailplane;
                    break;
                case 2:
                    return Aircraft::kCategoryLighterThanAir;
                    break;
                case 3:
                    return Aircraft::kCategoryParachutistSkydiver;
                    break;
                case 4:
                    return Aircraft::kCategoryUltralightHangGliderParaglider;
                    break;
                case 5:
                    return Aircraft::kCategoryReserved;
                    break;
                case 6:
                    return Aircraft::kCategoryUnmannedAerialVehicle;
                    break;
                case 7:
                    return Aircraft::kCategorySpaceTransatmosphericVehicle;
                    break;
                default:
                    return Aircraft::kCategoryInvalid;
            }
            break;
        case 4:
            switch (capability) {
                case 1:
                    return Aircraft::kCategoryLight;
                    break;
                case 2:
                    return Aircraft::kCategoryMedium1;
                    break;
                case 3:
                    return Aircraft::kCategoryMedium2;
                    break;
                case 4:
                    return Aircraft::kCategoryHighVortexAircraft;
                    break;
                case 5:
                    return Aircraft::kCategoryHeavy;
                    break;
                case 6:
                    return Aircraft::kCategoryHighPerformance;
                    break;
                case 7:
                    return Aircraft::kCategoryRotorcraft;
                    break;
                default:
                    return Aircraft::kCategoryInvalid;
            }
            break;
        default:
            return Aircraft::kCategoryInvalid;
    }
}

bool AircraftDictionary::ApplyAircraftIDMessage(Aircraft &aircraft, ADSBPacket packet) {
    aircraft.category = ExtractCategory(packet);
    aircraft.category_raw = packet.GetNBitWordFromMessage(8, 0);
    aircraft.transponder_capability = packet.GetCapability();
    for (uint16_t i = 0; i < Aircraft::kCallSignMaxNumChars; i++) {
        char callsign_char = LookupCallsignChar(packet.GetNBitWordFromMessage(6, 8 + (6 * i)));
        aircraft.callsign[i] = callsign_char;
    }

    return true;
}

bool AircraftDictionary::ApplySurfacePositionMessage(Aircraft &aircraft, ADSBPacket packet) {
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagIsAirborne, false);

    if (aircraft.NICBitIsValid(Aircraft::NICBit::kNICBitA) && aircraft.NICBitIsValid(Aircraft::NICBit::kNICBitC)) {
        // Assign NIC based on NIC supplement bits A and C and received TypeCode.
        switch ((packet.GetTypeCode() << 3) | (aircraft.nic_bits & 0b101)) {
            case (5 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan7p5Meters;
                break;
            case (6 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan25Meters;
                break;
            case (7 << 3) | 0b100:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan75Meters;
                break;
            case (7 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan0p1NauticalMiles;
                break;
            case (8 << 3) | 0b101:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan0p2NauticalMiles;
                break;
            case (8 << 3) | 0b100:
                // Should be <0.3NM, but NIC value is shared with <0.6NM.
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan0p6NauticalMiles;
                break;
            case (8 << 3) | 0b001:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan0p6NauticalMiles;
                break;
            case (8 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCUnknown;
                break;
            default:
                CONSOLE_WARNING("AircraftDictionary::ApplySurfacePositionMessage",
                                "Unable to assign NIC with typecode %d and nic_bits %d.", packet.GetTypeCode(),
                                aircraft.nic_bits);
        }
    }

    return false;
}

bool AircraftDictionary::ApplyAirbornePositionMessage(Aircraft &aircraft, ADSBPacket packet) {
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagIsAirborne, true);
    uint16_t typecode = packet.GetTypeCode();

    bool decode_successful = true;
    // ME[5-6] - Surveillance Status
    uint8_t surveillance_status = packet.GetNBitWordFromMessage(2, 5);
    switch (surveillance_status) {
        case 0:  // No condition.
            aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagAlert, false);
            aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagIdent, false);
            break;
        // NOTE: It's possible to have both an alert and an IDENT at the same time, but that can't be conveyed through a
        // single Airborne Position message.
        case 1:  // Permanent alert.
        case 2:  // Temporary alert.
            // Treat permanent and temporary alerts the same.
            aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagAlert, true);
            break;
        case 3:  // SPI condition.
            aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagIdent, true);
            break;
    }

    // ME[7] - NIC B Supplement (Formerly Single Antenna Flag)
    aircraft.WriteNICBit(Aircraft::NICBit::kNICBitB, packet.GetNBitWordFromMessage(1, 7));

    if (aircraft.NICBitIsValid(Aircraft::NICBit::kNICBitA) && aircraft.NICBitIsValid(Aircraft::NICBit::kNICBitB)) {
        // Assign NIC based on NIC supplement bits A and B and received TypeCode.
        switch ((typecode << 3) | (aircraft.nic_bits & 0b101)) {
            case (9 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan7p5Meters;
                break;
            case (10 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan25Meters;
                break;
            case (11 << 3) | 0b110:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan75Meters;
                break;
            case (11 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan0p1NauticalMiles;
                break;
            case (12 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan0p2NauticalMiles;
                break;
            case (13 << 3) | 0b010:  // Should be <0.3NM, but NIC value is shared with <0.6NM.
            case (13 << 3) | 0b000:  // Should be <0.5NM, but NIC value is shared with <0.6NM.
            case (13 << 3) | 0b110:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan0p6NauticalMiles;
                break;
            case (14 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan1NauticalMile;
                break;
            case (15 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan2NauticalMiles;
                break;
            case (16 << 3) | 0b110:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan4NauticalMiles;
                break;
            case (16 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan8NauticalMiles;
                break;
            case (17 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan20NauticalMiles;
                break;
            case (18 << 3) | 0b000:
                aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCUnknown;
                break;
            default:
                // Check for TypeCodes that can determine a NIC without needing to consult NIC supplement bits.
                switch (typecode) {
                    case 20:
                        aircraft.navigation_integrity_category =
                            Aircraft::NICRadiusOfContainment::kROCLessThan7p5Meters;
                        break;
                    case 21:
                        aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCLessThan25Meters;
                        break;
                    case 22:
                        aircraft.navigation_integrity_category = Aircraft::NICRadiusOfContainment::kROCUnknown;
                        break;
                    default:
                        CONSOLE_WARNING("AircraftDictionary::ApplyAirbornePositionMessage",
                                        "Unable to assign NIC with typecode %d and nic_bits %d.", typecode,
                                        aircraft.nic_bits);
                }
        }
    }

    // ME[8-19] - Encoded Altitude
    switch (packet.GetTypeCodeEnum()) {
        case ADSBPacket::TypeCode::kTypeCodeAirbornePositionBaroAlt: {
            uint16_t encoded_altitude_ft_with_q_bit = static_cast<uint16_t>(packet.GetNBitWordFromMessage(12, 8));
            if (encoded_altitude_ft_with_q_bit == 0) {
                aircraft.altitude_source = Aircraft::AltitudeSource::kAltitudeNotAvailable;
                CONSOLE_WARNING("AircraftDictionary::ApplyAirbornePositionMessage",
                                "Altitude information not available for aircraft 0x%lx.", aircraft.icao_address);
                decode_successful = false;
            } else {
                aircraft.altitude_source = Aircraft::AltitudeSource::kAltitudeSourceBaro;
                bool q_bit = (encoded_altitude_ft_with_q_bit & (0b000000010000)) ? true : false;
                // Remove Q bit.
                uint16_t encoded_altitude_ft = ((encoded_altitude_ft_with_q_bit & 0b111111100000) >> 1) |
                                               (encoded_altitude_ft_with_q_bit & 0b1111);
                aircraft.baro_altitude_ft = q_bit ? (encoded_altitude_ft * 25) - 1000 : 25 * encoded_altitude_ft;
                // FIXME: Does not currently support baro altitudes above 50175ft. Something about gray codes?
                aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagBaroAltitudeValid, true);
                aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagUpdatedBaroAltitude, true);
            }
            break;
        }
        case ADSBPacket::TypeCode::kTypeCodeAirbornePositionGNSSAlt: {
            aircraft.altitude_source = Aircraft::AltitudeSource::kAltitudeSourceGNSS;
            uint16_t gnss_altitude_m = static_cast<uint16_t>(packet.GetNBitWordFromMessage(12, 8));
            aircraft.gnss_altitude_ft = MetersToFeet(gnss_altitude_m);
            aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagGNSSAltitudeValid, true);
            aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagUpdatedGNSSAltitude, true);
            break;
        }
        default:
            CONSOLE_WARNING("AircraftDictionary::ApplyAirbornePositionMessage",
                            "Received packet with unsupported typecode %d.", packet.GetTypeCode());
            return false;
    }

    // ME[20] - Time
    // TODO: figure out if we need this

    // ME[21] - CPR Format
    bool odd = packet.GetNBitWordFromMessage(1, 21);

    // ME[32-?]
    aircraft.SetCPRLatLon(packet.GetNBitWordFromMessage(17, 22), packet.GetNBitWordFromMessage(17, 39), odd,
                          packet.GetTimestampMs());
    if (!aircraft.CanDecodePosition()) {
        // Can't decode aircraft position, but this is not an error. Return decode_successful in case there were other
        // errors.
        return decode_successful;
    }
    if (aircraft.DecodePosition()) {
        // Position decode succeeded.
        aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagUpdatedPosition, true);
    } else {
        // Position decode failed.
        decode_successful = false;
    }

    return decode_successful;
}

inline float wrapped_atan2f(float y, float x) {
    float val = atan2f(y, x);
    return val < 0.0f ? (val + (2.0f * M_PI)) : val;
}

bool AircraftDictionary::ApplyAirborneVelocitiesMessage(Aircraft &aircraft, ADSBPacket packet) {
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagIsAirborne, true);
    bool decode_successful = true;

    // Decode horizontal velocity.
    ADSBPacket::AirborneVelocitiesSubtype subtype =
        static_cast<ADSBPacket::AirborneVelocitiesSubtype>(packet.GetNBitWordFromMessage(3, 5));
    bool is_supersonic = false;
    switch (subtype) {
        case ADSBPacket::AirborneVelocitiesSubtype::kAirborneVelocitiesGroundSpeedSupersonic:
            is_supersonic = true;
            [[fallthrough]];  // Cascade into ground speed calculation.
        case ADSBPacket::AirborneVelocitiesSubtype::kAirborneVelocitiesGroundSpeedSubsonic: {
            // Ground speed calculation.
            int v_ew_kts_plus_1 = static_cast<int>(packet.GetNBitWordFromMessage(10, 14));
            int v_ns_kts_plus_1 = static_cast<int>(packet.GetNBitWordFromMessage(10, 25));
            if (v_ew_kts_plus_1 == 0 || v_ns_kts_plus_1 == 0) {
                aircraft.velocity_source = Aircraft::VelocitySource::kVelocitySourceNotAvailable;
                CONSOLE_WARNING("AircraftDictionary::ApplyAirborneVelocitiesMessage",
                                "Ground speed not available for aircraft 0x%lx.", aircraft.icao_address);
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
                aircraft.direction_deg = wrapped_atan2f(v_x_kts, v_y_kts) * kRadiansToDegrees;
            }
            break;
        }
        case ADSBPacket::AirborneVelocitiesSubtype::kAirborneVelocitiesAirspeedSupersonic: {
            is_supersonic = true;
            [[fallthrough]];  // Cascade into airspeed calculation.
        }
        case ADSBPacket::AirborneVelocitiesSubtype::kAirborneVelocitiesAirspeedSubsonic: {
            int airspeed_kts_plus_1 = static_cast<int>(packet.GetNBitWordFromMessage(10, 25));
            if (airspeed_kts_plus_1 == 0) {
                CONSOLE_WARNING("AircraftDictionary::ApplyAirborneVelocitiesMessage",
                                "Airspeed not available for aircraft 0x%lx.", aircraft.icao_address);
                decode_successful = false;
            } else {
                aircraft.velocity_kts = (airspeed_kts_plus_1 - 1) * (is_supersonic ? 4 : 1);
                bool is_true_airspeed = static_cast<bool>(packet.GetNBitWordFromMessage(1, 24));
                aircraft.velocity_source = is_true_airspeed
                                               ? Aircraft::VelocitySource::kVelocitySourceAirspeedTrue
                                               : Aircraft::VelocitySource::kVelocitySourceAirspeedIndicated;
                aircraft.direction_deg = static_cast<float>((packet.GetNBitWordFromMessage(10, 14) * 360) / 1024.0f);
            }

            break;
        }
        default:
            CONSOLE_ERROR("AircraftDictionary::ApplyAirborneVelocitiesMessage",
                          "Encountered invalid airborne velocities message subtype %d (valid values are 1-4).",
                          subtype);
            return false;  // Don't attempt vertical rate decode if message type is invalid.
    }
    // Latching bit flags.
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagDirectionValid, true);
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagHorizontalVelocityValid, true);
    // Non-latching bit flags.
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagUpdatedDirection, true);
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagUpdatedHorizontalVelocity, true);

    // Decode vertical rate.
    int vertical_rate_magnitude_fpm = packet.GetNBitWordFromMessage(9, 37);
    if (vertical_rate_magnitude_fpm == 0) {
        aircraft.vertical_rate_source = Aircraft::VerticalRateSource::kVerticalRateNotAvailable;
        CONSOLE_WARNING("AircraftDictionary::ApplyAirborneVelocitiesMessage",
                        "Vertical rate not available for aircraft 0x%lx.", aircraft.icao_address);
        decode_successful = false;
    } else {
        aircraft.vertical_rate_source = static_cast<Aircraft::VerticalRateSource>(packet.GetNBitWordFromMessage(1, 35));
        bool vertical_rate_sign_is_negative = packet.GetNBitWordFromMessage(1, 36);
        if (vertical_rate_sign_is_negative) {
            aircraft.vertical_rate_fpm = -(vertical_rate_magnitude_fpm - 1) * 64;
        } else {
            aircraft.vertical_rate_fpm = (vertical_rate_magnitude_fpm - 1) * 64;
        }
        aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagVerticalVelocityValid, true);
        aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagUpdatedVerticalVelocity, true);
    }

    // Decode altitude difference between GNSS and barometric altitude.
    bool gnss_alt_below_baro_alt = static_cast<bool>(packet.GetNBitWordFromMessage(1, 48));
    uint16_t encoded_gnss_alt_baro_alt_difference_ft = static_cast<uint16_t>(packet.GetNBitWordFromMessage(7, 49));
    if (encoded_gnss_alt_baro_alt_difference_ft == 0) {
        CONSOLE_WARNING("AircraftDictionary::ApplyAirborneVelocitiesMessage",
                        "Difference between GNSS and baro altitude not available for aircraft 0x%lx.",
                        aircraft.icao_address);
        // Don't set decode_successful to false so that we ignore missing GNSS/Baro altitude info.
    } else {
        int gnss_alt_baro_alt_difference_ft =
            (encoded_gnss_alt_baro_alt_difference_ft - 1) * 25 * (gnss_alt_below_baro_alt ? -1 : 1);
        switch (aircraft.altitude_source) {
            case Aircraft::AltitudeSource::kAltitudeSourceBaro:
                aircraft.gnss_altitude_ft = aircraft.baro_altitude_ft + gnss_alt_baro_alt_difference_ft;
                aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagGNSSAltitudeValid, true);
                aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagUpdatedGNSSAltitude, true);
                break;
            case Aircraft::AltitudeSource::kAltitudeSourceGNSS:
                aircraft.baro_altitude_ft = aircraft.gnss_altitude_ft - gnss_alt_baro_alt_difference_ft;
                aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagBaroAltitudeValid, true);
                aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagUpdatedBaroAltitude, true);
                break;
            default:
                // Don't sweat it if the aircraft doesn't have an altitude yet.
                break;
        }
    }

    return decode_successful;
}

bool AircraftDictionary::ApplyAircraftStatusMessage(Aircraft &aircraft, ADSBPacket packet) { return false; }

bool AircraftDictionary::ApplyTargetStateAndStatusInfoMessage(Aircraft &aircraft, ADSBPacket packet) { return false; }

bool AircraftDictionary::ApplyAircraftOperationStatusMessage(Aircraft &aircraft, ADSBPacket packet) {
    // TODO: get nac/navigation_integrity_category, and supplement airborne status from here.
    // https://mode-s.org/decode/content/ads-b/6-operation-status.html
    // More about navigation_integrity_category/nac here: https://mode-s.org/decode/content/ads-b/7-uncertainty.html

    // ME[5-7] - Subtype Code
    ADSBPacket::OperationStatusSubtype subtype =
        static_cast<ADSBPacket::OperationStatusSubtype>(packet.GetNBitWordFromMessage(3, 5));

    // ME[8-23] - Airborne or Surface Capacity Class Code
    // ME[11] - 1090ES In
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagHas1090ESIn, packet.GetNBitWordFromMessage(1, 11));
    // Other fields handled in switch statement.

    // ME[24-39] - Operational Altitude Replyode
    // ME[26] - TCAS RA Active
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagTCASRA, packet.GetNBitWordFromMessage(1, 26));
    // ME[27] - IDENT Switch Active
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagIdent, packet.GetNBitWordFromMessage(1, 27));
    // ME[29] - Single Antenna Flag
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagSingleAntenna, packet.GetNBitWordFromMessage(1, 29));
    // ME[30-31] - System Design Assurance
    aircraft.system_design_assurance =
        static_cast<Aircraft::SystemDesignAssurance>(packet.GetNBitWordFromMessage(2, 30));

    // ME[40-42] - ADS-B Version Number
    aircraft.adsb_version = packet.GetNBitWordFromMessage(3, 40);

    // ME[43] - NIC Supplement A
    aircraft.WriteNICBit(Aircraft::NICBit::kNICBitC, packet.GetNBitWordFromMessage(1, 43));

    // ME[44-47] - Navigational Accuracy Category, Position
    aircraft.navigation_accuracy_category_position =
        static_cast<Aircraft::NACEstimatedPositionUncertainty>(packet.GetNBitWordFromMessage(4, 44));

    // ME[50-51] - Source Integrity Level (SIL)
    uint8_t source_integrity_level = packet.GetNBitWordFromMessage(2, 50);
    // ME[53] - Horizontal Reference Direction (HRD)
    aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagHeadingUsesMagneticNorth, packet.GetNBitWordFromMessage(1, 53));
    // ME[54] - SIL Supplement
    uint8_t sil_supplement = packet.GetNBitWordFromMessage(1, 54);
    aircraft.source_integrity_level = static_cast<Aircraft::SILProbabilityOfExceedingNICRadiusOfContainmnent>(
        (sil_supplement << 2) | source_integrity_level);

    // Conditional fields (meaning depends on subtype).
    switch (subtype) {
        case ADSBPacket::OperationStatusSubtype::kOperationStatusSubtypeAirborne:  // ST = 0
        {
            // ME[10] - TCAS Operational
            aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagTCASOperational, packet.GetNBitWordFromMessage(1, 10));

            // ME[14] - Air Referenced Velocity (ARV) Report Capability - Ignored
            // ME[15] - Target State (TS) Report Capability - Ignored
            // ME[16-17] - Trajectory Change (TC) Report Capability - Ignored
            // ME[18] - UAT In
            aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagHasUATIn, packet.GetNBitWordFromMessage(1, 18));

            // ME[48-49] - GVA
            aircraft.geometric_vertical_accuracy = static_cast<Aircraft::GVA>(packet.GetNBitWordFromMessage(2, 48));

            // ME[52] - NIC Baro
            aircraft.navigation_integrity_category_baro =
                static_cast<Aircraft::NICBarometricAltitudeIntegrity>(packet.GetNBitWordFromMessage(1, 52));

            break;
        }
        case ADSBPacket::OperationStatusSubtype::kOperationStatusSubtypeSurface:  // ST = 1
        {
            // ME[14] - B2 Low
            aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagIsClassB2GroundVehicle,
                                  packet.GetNBitWordFromMessage(1, 14));
            // ME[15] - UAT In
            aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagHasUATIn, packet.GetNBitWordFromMessage(1, 15));
            // ME[16-18] - NACv
            aircraft.navigation_accuracy_category_velocity =
                static_cast<Aircraft::NACHorizontalVelocityError>(packet.GetNBitWordFromMessage(3, 16));
            // ME[19] - NIC Supplement C
            aircraft.WriteNICBit(Aircraft::NICBit::kNICBitC, packet.GetNBitWordFromMessage(1, 19));

            // ME[20-23] Aircraft/Vehicle Length and Width Code
            switch (packet.GetNBitWordFromMessage(4, 20)) {
                case 0:
                    aircraft.length_m = 0;
                    aircraft.width_m = 0;
                    break;
                case 1:
                    aircraft.length_m = 15;
                    aircraft.width_m = 23;
                    break;
                case 2:
                    aircraft.length_m = 25;
                    aircraft.width_m = 29;  // Rounded up from 28.5.
                    break;
                case 3:
                    aircraft.length_m = 25;
                    aircraft.width_m = 34;
                    break;
                case 4:
                    aircraft.length_m = 35;
                    aircraft.width_m = 33;
                    break;
                case 5:
                    aircraft.length_m = 35;
                    aircraft.width_m = 38;
                    break;
                case 6:
                    aircraft.length_m = 45;
                    aircraft.width_m = 40;  // Rounded up from 39.5.
                    break;
                case 7:
                    aircraft.length_m = 45;
                    aircraft.width_m = 45;
                    break;
                case 8:
                    aircraft.length_m = 55;
                    aircraft.width_m = 45;
                    break;
                case 9:
                    aircraft.length_m = 55;
                    aircraft.width_m = 52;
                    break;
                case 10:
                    aircraft.length_m = 65;
                    aircraft.width_m = 60;  // Rounded up from 59.5.
                    break;
                case 11:
                    aircraft.length_m = 65;
                    aircraft.width_m = 67;
                    break;
                case 12:
                    aircraft.length_m = 75;
                    aircraft.width_m = 73;  // Rounded up from 72.5.
                    break;
                case 13:
                    aircraft.length_m = 75;
                    aircraft.width_m = 80;
                    break;
                case 14:
                    aircraft.length_m = 85;
                    aircraft.width_m = 80;
                    break;
                case 15:
                    aircraft.length_m = 85;
                    aircraft.width_m = 90;
                    break;
            }

            // ME[32-39] - GPS Antenna Offset
            // Only present in surface position operation status packets.
            switch (packet.GetNBitWordFromMessage(8, 32)) {
                case 0b000:  // No data.
                    break;
                case 0b001:  // 2 meters left of roll axis.
                    aircraft.gnss_antenna_offset_right_of_roll_axis_m = -2;
                    break;
                case 0b010:  // 4 meters left of roll axis.
                    aircraft.gnss_antenna_offset_right_of_roll_axis_m = -4;
                    break;
                case 0b011:  // 6 meters left of roll axis.
                    aircraft.gnss_antenna_offset_right_of_roll_axis_m = -6;
                    break;
                case 0b100:  // Centered on roll axis.
                    aircraft.gnss_antenna_offset_right_of_roll_axis_m = 0;
                    break;
                case 0b101:  // 2 meters right of roll axis.
                    aircraft.gnss_antenna_offset_right_of_roll_axis_m = 2;
                    break;
                case 0b110:  // 4 meters right of roll axis.
                    aircraft.gnss_antenna_offset_right_of_roll_axis_m = 4;
                    break;
                case 0b111:  // 6 meters right of roll axis.
                    aircraft.gnss_antenna_offset_right_of_roll_axis_m = 6;
                    break;
            }

            // ME[52] Track Angle / Heading for Surface Position Messages
            aircraft.WriteBitFlag(Aircraft::BitFlag::kBitFlagDirectionIsHeading, packet.GetNBitWordFromMessage(1, 52));

            break;
        }
        default:
            CONSOLE_ERROR("AircraftDictionary::ApplyAircraftOperationStatusMessage",
                          "Received unsupported Operation Status (TC=31) message subtype %d. Expected 0 or 1.",
                          subtype);
            return false;
    }
    return true;
}