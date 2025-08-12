#include "aircraft_dictionary.hh"

#include <cmath>

#include "comms.hh"  // For debug logging.
#include "decode_utils.hh"
#include "geo_utils.hh"
#include "hal.hh"
#include "macros.hh"
#include "nasa_cpr.hh"
#include "unit_conversions.hh"

const float kDegreesPerRadian = 360.0f / (2.0f * M_PI);

// This velocity determines the maximum distance an aircraft can jump between position updates without its new position
// needing a second sample to confirm it. This catches position reports that return as valid from the CPR decoder but
// are for an obviously incorrect position.
const uint32_t kCPRPositionFilterVelocityMps =
    1000;  // This is faster than the SR-71, so we're just catching really big jumps for now.

/**
 * ModeSAircraft
 */

ModeSAircraft::ModeSAircraft(uint32_t icao_address_in) : icao_address(icao_address_in) {
    // memset(callsign, '\0', kCallSignMaxNumChars + 1);  // clear out callsign string, including extra EOS character
}

ModeSAircraft::ModeSAircraft() {
    // memset(callsign, '\0', kCallSignMaxNumChars + 1);  // clear out callsign string, including extra EOS character
}

bool ModeSAircraft::CanDecodePosition() {
    // TODO: There could be a condition here where we temporarily lose packets when the MLAT counter wraps around and
    // the packet timestamps all get seen as 0ms, but this probably is not a big deal.
    if (!(last_odd_packet_.received_timestamp_ms > 0 && last_even_packet_.received_timestamp_ms > 0)) {
        CONSOLE_WARNING("ModeSAircraft::DecodePosition",
                        "Unable to decode position without receiving an odd and even packet pair for ICAO 0x%lx.",
                        icao_address);
        return false;  // need both an even and an odd packet to be able to decode position
    }
    uint32_t cpr_interval_ms = MIN(last_odd_packet_.received_timestamp_ms - last_even_packet_.received_timestamp_ms,
                                   last_even_packet_.received_timestamp_ms - last_odd_packet_.received_timestamp_ms);
    if (cpr_interval_ms > GetMaxAllowedCPRIntervalMs()) {
        // Reject CPR packet pairings that are too far apart in time.
        WriteBitFlag(BitFlag::kBitFlagPositionValid,
                     false);  // keep last known good coordinates, but mark as invalid
        CONSOLE_WARNING("ModeSAircraft::DecodePosition",
                        "CPR packet pair too far apart in time (%lu ms). Can't decode position.", cpr_interval_ms);
        return false;
    }
    return true;
}

bool ModeSAircraft::DecodePosition(bool filter_cpr_position) {
    // WARNING: There are two separate timebases in play here! The timebase for CPR packet timestamps is the MLAT
    // timebase, while higher level aircraft dictionary info is in system time.

    if (!CanDecodePosition()) {
        // Can't try forcing a decode and seeing if it's valid, since we'll end up using a stale even or odd packet
        // pairing.
        return false;
    }

    uint32_t most_recent_received_timestamp_ms =
        MAX(last_even_packet_.received_timestamp_ms, last_odd_packet_.received_timestamp_ms);

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

    if (!result_valid) {
        CONSOLE_WARNING("ModeSAircraft::DecodePosition",
                        "Can't decode position from packet pair that spans different latitude zones.");
        return false;  // Aircraft crossed between latitude zones, can't decode from this packet pair.
    }

#ifdef FILTER_CPR_POSITIONS
    if (filter_cpr_position) {
        // Calculate how far the aircraft has jumped since its last position update, and goof check it against a maximum
        // velocity value. Could use the aircraft's known velocity, but just using a very large value for now.
        uint32_t ms_since_last_track_update = most_recent_received_timestamp_ms - last_track_update_timestamp_ms;
        uint32_t max_distance_meters =
            kCPRPositionFilterVelocityMps * ms_since_last_track_update / 1000;  // mps to meters
        uint32_t distance_meters =
            CalculateGeoidalDistanceMetersAWB(lat_awb_, lon_awb_, result.lat_awb, result.lon_awb);

        if (most_recent_received_timestamp_ms <= last_filter_received_timestamp_ms_) {
            // Don't allow calling DecodePosition() twice without a new packet to override the filter.
            CONSOLE_WARNING("ModeSAircraft::DecodePosition",
                            "Received CPR position update for ICAO 0x%lx, but timestamp %lu ms is not newer than last "
                            "filter received timestamp %lu ms.",
                            icao_address, most_recent_received_timestamp_ms, last_filter_received_timestamp_ms_);
            return false;
        }

        last_filter_received_timestamp_ms_ = most_recent_received_timestamp_ms;

        // Store the updated position. A location jump can be "confirmed" with a subsequent update from near the new
        // candidate position. Thus, sudden jumps in position, take two subsequent position updates that are relatively
        // close together in order to be reflected in the aircraft's position.
        lat_awb_ = result.lat_awb;
        lon_awb_ = result.lon_awb;

        // Note: Ignore position check during first position update, to allow recording aircraft position upon receiving
        // the first packet.
        if (HasBitFlag(BitFlag::kBitFlagPositionValid) && distance_meters > max_distance_meters) {
            CONSOLE_WARNING("ModeSAircraft::DecodePosition",
                            "Filtered CPR position update for ICAO 0x%lx, distance %lu m exceeds max %lu m.",
                            icao_address, distance_meters, max_distance_meters);
            return false;  // Filter out CPR positions that are too far from the last known position.
        }
    }
#endif

    WriteBitFlag(BitFlag::kBitFlagPositionValid, true);
    latitude_deg = WrapCPRDecodeLatitude(result.lat_deg);
    longitude_deg = WrapCPRDecodeLongitude(result.lon_deg);
    last_track_update_timestamp_ms = most_recent_received_timestamp_ms;  // Update last track update timestamp.

    return true;
}

/**
 * Returns the Wake Vortex category of the aircraft that sent a given ADS-B packet. Note that some categories have a
 * many to one mapping!
 * @param[in] packet ADS-B Packet to extract the Category value from. Must be
 * @retval Category that matches the combination of capability and typecode from the ADS-B packet, or
 * kCategoryInvalid if there is no matching wake vortex value.
 */
ModeSAircraft::Category ExtractCategory(const ADSBPacket &packet) {
    uint8_t typecode = packet.GetNBitWordFromMessage(5, 0);
    uint8_t capability = packet.GetNBitWordFromMessage(3, 5);

    // Table 4.1 from The 1090Mhz Riddle (Junzi Sun), pg. 42.
    if (capability == 0) {
        return ModeSAircraft::kCategoryNoCategoryInfo;
    }

    switch (typecode) {
        case 1:
            return ModeSAircraft::kCategoryReserved;
            break;
        case 2:
            switch (capability) {
                case 1:
                    return ModeSAircraft::kCategorySurfaceEmergencyVehicle;
                    break;
                case 3:
                    return ModeSAircraft::kCategorySurfaceServiceVehicle;
                    break;
                case 4:
                case 5:
                case 6:
                case 7:
                    return ModeSAircraft::kCategoryGroundObstruction;
                    break;
                default:
                    return ModeSAircraft::kCategoryInvalid;
            }
            break;
        case 3:
            switch (capability) {
                case 1:
                    return ModeSAircraft::kCategoryGliderSailplane;
                    break;
                case 2:
                    return ModeSAircraft::kCategoryLighterThanAir;
                    break;
                case 3:
                    return ModeSAircraft::kCategoryParachutistSkydiver;
                    break;
                case 4:
                    return ModeSAircraft::kCategoryUltralightHangGliderParaglider;
                    break;
                case 5:
                    return ModeSAircraft::kCategoryReserved;
                    break;
                case 6:
                    return ModeSAircraft::kCategoryUnmannedAerialVehicle;
                    break;
                case 7:
                    return ModeSAircraft::kCategorySpaceTransatmosphericVehicle;
                    break;
                default:
                    return ModeSAircraft::kCategoryInvalid;
            }
            break;
        case 4:
            switch (capability) {
                case 1:
                    return ModeSAircraft::kCategoryLight;
                    break;
                case 2:
                    return ModeSAircraft::kCategoryMedium1;
                    break;
                case 3:
                    return ModeSAircraft::kCategoryMedium2;
                    break;
                case 4:
                    return ModeSAircraft::kCategoryHighVortexAircraft;
                    break;
                case 5:
                    return ModeSAircraft::kCategoryHeavy;
                    break;
                case 6:
                    return ModeSAircraft::kCategoryHighPerformance;
                    break;
                case 7:
                    return ModeSAircraft::kCategoryRotorcraft;
                    break;
                default:
                    return ModeSAircraft::kCategoryInvalid;
            }
            break;
        default:
            return ModeSAircraft::kCategoryInvalid;
    }
}

bool ModeSAircraft::ApplyAircraftIDMessage(ADSBPacket packet) {
    category = ExtractCategory(packet);
    category_raw = packet.GetNBitWordFromMessage(8, 0);
    transponder_capability = packet.GetCapability();
    for (uint16_t i = 0; i < ModeSAircraft::kCallSignMaxNumChars; i++) {
        char callsign_char = LookupCallsignChar(packet.GetNBitWordFromMessage(6, 8 + (6 * i)));
        callsign[i] = callsign_char;
    }

    return true;
}

bool ModeSAircraft::ApplySurfacePositionMessage(ADSBPacket packet) {
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagIsAirborne, false);

    if (NICBitIsValid(ModeSAircraft::NICBit::kNICBitA) && NICBitIsValid(ModeSAircraft::NICBit::kNICBitC)) {
        // Assign NIC based on NIC supplement bits A and C and received TypeCode.
        switch ((packet.GetTypeCode() << 3) | (nic_bits & 0b101)) {
            case (5 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan7p5Meters;
                break;
            case (6 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan25Meters;
                break;
            case (7 << 3) | 0b100:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan75Meters;
                break;
            case (7 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan0p1NauticalMiles;
                break;
            case (8 << 3) | 0b101:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan0p2NauticalMiles;
                break;
            case (8 << 3) | 0b100:
                // Should be <0.3NM, but NIC value is shared with <0.6NM.
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan0p6NauticalMiles;
                break;
            case (8 << 3) | 0b001:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan0p6NauticalMiles;
                break;
            case (8 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCUnknown;
                break;
            default:
                CONSOLE_WARNING("AircraftDictionary::ApplySurfacePositionMessage",
                                "Unable to assign NIC with typecode %d and nic_bits %d for ICAO 0x%lx.",
                                packet.GetTypeCode(), nic_bits, icao_address);
        }
    }

    CONSOLE_WARNING("AircraftDictionary::ApplySurfacePositionMessage",
                    "Surface position messages not yet supported. Received message with ICAO 0x%lx", icao_address);
    return false;
}

bool ModeSAircraft::ApplyAirbornePositionMessage(ADSBPacket packet, bool filter_cpr_position) {
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagIsAirborne, true);
    uint16_t typecode = packet.GetTypeCode();

    bool decode_successful = true;
    // ME[5-6] - Surveillance Status
    uint8_t surveillance_status = packet.GetNBitWordFromMessage(2, 5);
    switch (surveillance_status) {
        case 0:  // No condition.
            WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagAlert, false);
            WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagIdent, false);
            break;
        // NOTE: It's possible to have both an alert and an IDENT at the same time, but that can't be conveyed
        // through a single Airborne Position message.
        case 1:  // Permanent alert.
        case 2:  // Temporary alert.
            // Treat permanent and temporary alerts the same.
            WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagAlert, true);
            break;
        case 3:  // SPI condition.
            WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagIdent, true);
            break;
    }

    // ME[7] - NIC B Supplement (Formerly Single Antenna Flag)
    WriteNICBit(ModeSAircraft::NICBit::kNICBitB, packet.GetNBitWordFromMessage(1, 7));

    if (NICBitIsValid(ModeSAircraft::NICBit::kNICBitA) && NICBitIsValid(ModeSAircraft::NICBit::kNICBitB)) {
        // Assign NIC based on NIC supplement bits A and B and received TypeCode.
        switch ((typecode << 3) | (nic_bits & 0b101)) {
            case (9 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan7p5Meters;
                break;
            case (10 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan25Meters;
                break;
            case (11 << 3) | 0b110:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan75Meters;
                break;
            case (11 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan0p1NauticalMiles;
                break;
            case (12 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan0p2NauticalMiles;
                break;
            case (13 << 3) | 0b010:  // Should be <0.3NM, but NIC value is shared with <0.6NM.
            case (13 << 3) | 0b000:  // Should be <0.5NM, but NIC value is shared with <0.6NM.
            case (13 << 3) | 0b110:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan0p6NauticalMiles;
                break;
            case (14 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan1NauticalMile;
                break;
            case (15 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan2NauticalMiles;
                break;
            case (16 << 3) | 0b110:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan4NauticalMiles;
                break;
            case (16 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan8NauticalMiles;
                break;
            case (17 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan20NauticalMiles;
                break;
            case (18 << 3) | 0b000:
                navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCUnknown;
                break;
            default:
                // Check for TypeCodes that can determine a NIC without needing to consult NIC supplement bits.
                switch (typecode) {
                    case 20:
                        navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan7p5Meters;
                        break;
                    case 21:
                        navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCLessThan25Meters;
                        break;
                    case 22:
                        navigation_integrity_category = ModeSAircraft::NICRadiusOfContainment::kROCUnknown;
                        break;
                    default:
                        CONSOLE_WARNING("AircraftDictionary::ApplyAirbornePositionMessage",
                                        "Unable to assign NIC with typecode %d and nic_bits %d for ICAO 0x%lx.",
                                        typecode, nic_bits, icao_address);
                }
        }
    }

    // ME[8-19] - Encoded Altitude
    switch (packet.GetTypeCodeEnum()) {
        case ADSBPacket::TypeCode::kTypeCodeAirbornePositionBaroAlt: {
            uint16_t encoded_altitude_ft_with_q_bit = static_cast<uint16_t>(packet.GetNBitWordFromMessage(12, 8));
            if (encoded_altitude_ft_with_q_bit == 0) {
                altitude_source = ModeSAircraft::AltitudeSource::kAltitudeNotAvailable;
                CONSOLE_WARNING("AircraftDictionary::ApplyAirbornePositionMessage",
                                "Altitude information not available for ICAO 0x%lx.", icao_address);
                decode_successful = false;
            } else {
                altitude_source = ModeSAircraft::AltitudeSource::kAltitudeSourceBaro;
                bool q_bit = (encoded_altitude_ft_with_q_bit & (0b000000010000)) ? true : false;
                // Remove Q bit.
                uint16_t encoded_altitude_ft = ((encoded_altitude_ft_with_q_bit & 0b111111100000) >> 1) |
                                               (encoded_altitude_ft_with_q_bit & 0b1111);
                baro_altitude_ft = q_bit ? (encoded_altitude_ft * 25) - 1000 : 25 * encoded_altitude_ft;
                // FIXME: Does not currently support baro altitudes above 50175ft. Something about gray codes?
                WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagBaroAltitudeValid, true);
                WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagUpdatedBaroAltitude, true);
            }
            break;
        }
        case ADSBPacket::TypeCode::kTypeCodeAirbornePositionGNSSAlt: {
            altitude_source = ModeSAircraft::AltitudeSource::kAltitudeSourceGNSS;
            uint16_t gnss_altitude_m = static_cast<uint16_t>(packet.GetNBitWordFromMessage(12, 8));
            gnss_altitude_ft = MetersToFeet(gnss_altitude_m);
            WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagGNSSAltitudeValid, true);
            WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagUpdatedGNSSAltitude, true);
            break;
        }
        default:
            CONSOLE_WARNING("AircraftDictionary::ApplyAirbornePositionMessage",
                            "Received packet with unsupported typecode %d with ICAO 0x%lx.", packet.GetTypeCode(),
                            icao_address);
            return false;
    }

    // ME[20] - Time
    // TODO: figure out if we need this

    // ME[21] - CPR Format
    bool odd = packet.GetNBitWordFromMessage(1, 21);

    // ME[32-?]
    SetCPRLatLon(packet.GetNBitWordFromMessage(17, 22), packet.GetNBitWordFromMessage(17, 39), odd,
                 packet.GetTimestampMs());
    if (!CanDecodePosition()) {
        // Can't decode aircraft position, but this is not an error. Return decode_successful in case there were
        // other errors.
        return decode_successful;
    }
    if (DecodePosition(filter_cpr_position)) {
        // Position decode succeeded.
        WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagUpdatedPosition, true);
    } else {
        // We should have been able to recover a position, but position decode failed. This happens if our position
        // filter algorithm rejects the decoded position result.
        decode_successful = false;
        CONSOLE_WARNING("AircraftDictionary::ApplyAirbornePositionMessage",
                        "Had valid packets, but aircraft position decode failed for ICAO 0x%lx.", icao_address);
    }

    return decode_successful;
}

inline float wrapped_atan2f(float y, float x) {
    float val = atan2f(y, x);
    return val < 0.0f ? (val + (2.0f * M_PI)) : val;
}

bool ModeSAircraft::ApplyAirborneVelocitiesMessage(ADSBPacket packet) {
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagIsAirborne, true);
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
                velocity_source = ModeSAircraft::VelocitySource::kVelocitySourceNotAvailable;
                CONSOLE_WARNING("AircraftDictionary::ApplyAirborneVelocitiesMessage",
                                "Ground speed not available for ICAO 0x%lx.", icao_address);
                decode_successful = false;
            } else {
                velocity_source = ModeSAircraft::VelocitySource::kVelocitySourceGroundSpeed;
                bool direction_is_east_to_west = static_cast<bool>(packet.GetNBitWordFromMessage(1, 13));
                int v_x_kts = (v_ew_kts_plus_1 - 1) * (direction_is_east_to_west ? -1 : 1);
                bool direction_is_north_to_south = static_cast<bool>(packet.GetNBitWordFromMessage(1, 24));
                int v_y_kts = (v_ns_kts_plus_1 - 1) * (direction_is_north_to_south ? -1 : 1);
                if (is_supersonic) {
                    v_x_kts *= 4;
                    v_y_kts *= 4;
                }
                velocity_kts = sqrtf(v_x_kts * v_x_kts + v_y_kts * v_y_kts);
                direction_deg = wrapped_atan2f(v_x_kts, v_y_kts) * kDegreesPerRadian;
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
                                "Airspeed not available for ICAO 0x%lx.", icao_address);
                decode_successful = false;
            } else {
                velocity_kts = (airspeed_kts_plus_1 - 1) * (is_supersonic ? 4 : 1);
                bool is_true_airspeed = static_cast<bool>(packet.GetNBitWordFromMessage(1, 24));
                velocity_source = is_true_airspeed ? ModeSAircraft::VelocitySource::kVelocitySourceAirspeedTrue
                                                   : ModeSAircraft::VelocitySource::kVelocitySourceAirspeedIndicated;
                direction_deg = static_cast<float>((packet.GetNBitWordFromMessage(10, 14) * 360) / 1024.0f);
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
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagDirectionValid, true);
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagHorizontalVelocityValid, true);
    // Non-latching bit flags.
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagUpdatedDirection, true);
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagUpdatedHorizontalVelocity, true);

    // Decode vertical rate.
    int vertical_rate_magnitude_fpm = packet.GetNBitWordFromMessage(9, 37);
    if (vertical_rate_magnitude_fpm == 0) {
        vertical_rate_source = ModeSAircraft::VerticalRateSource::kVerticalRateNotAvailable;
        CONSOLE_WARNING("AircraftDictionary::ApplyAirborneVelocitiesMessage",
                        "Vertical rate not available for ICAO 0x%lx.", icao_address);
        decode_successful = false;
    } else {
        vertical_rate_source = static_cast<ModeSAircraft::VerticalRateSource>(packet.GetNBitWordFromMessage(1, 35));
        bool vertical_rate_sign_is_negative = packet.GetNBitWordFromMessage(1, 36);
        if (vertical_rate_sign_is_negative) {
            vertical_rate_fpm = -(vertical_rate_magnitude_fpm - 1) * 64;
        } else {
            vertical_rate_fpm = (vertical_rate_magnitude_fpm - 1) * 64;
        }
        WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagVerticalVelocityValid, true);
        WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagUpdatedVerticalVelocity, true);
    }

    // Decode altitude difference between GNSS and barometric altitude.
    bool gnss_alt_below_baro_alt = static_cast<bool>(packet.GetNBitWordFromMessage(1, 48));
    uint16_t encoded_gnss_alt_baro_alt_difference_ft = static_cast<uint16_t>(packet.GetNBitWordFromMessage(7, 49));
    if (encoded_gnss_alt_baro_alt_difference_ft == 0) {
        CONSOLE_WARNING("AircraftDictionary::ApplyAirborneVelocitiesMessage",
                        "Difference between GNSS and baro altitude not available for aircraft 0x%lx.", icao_address);
        // Don't set decode_successful to false so that we ignore missing GNSS/Baro altitude info.
    } else {
        int gnss_alt_baro_alt_difference_ft =
            (encoded_gnss_alt_baro_alt_difference_ft - 1) * 25 * (gnss_alt_below_baro_alt ? -1 : 1);
        switch (altitude_source) {
            case ModeSAircraft::AltitudeSource::kAltitudeSourceBaro:
                gnss_altitude_ft = baro_altitude_ft + gnss_alt_baro_alt_difference_ft;
                WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagGNSSAltitudeValid, true);
                WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagUpdatedGNSSAltitude, true);
                break;
            case ModeSAircraft::AltitudeSource::kAltitudeSourceGNSS:
                baro_altitude_ft = gnss_altitude_ft - gnss_alt_baro_alt_difference_ft;
                WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagBaroAltitudeValid, true);
                WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagUpdatedBaroAltitude, true);
                break;
            default:
                // Don't sweat it if the aircraft doesn't have an altitude yet.
                break;
        }
    }

    return decode_successful;
}

bool ModeSAircraft::ApplyAircraftStatusMessage(ADSBPacket packet) { return false; }

bool ModeSAircraft::ApplyTargetStateAndStatusInfoMessage(ADSBPacket packet) { return false; }

bool ModeSAircraft::ApplyAircraftOperationStatusMessage(ADSBPacket packet) {
    // TODO: get nac/navigation_integrity_category, and supplement airborne status from here.
    // https://mode-s.org/decode/content/ads-b/6-operation-status.html
    // More about navigation_integrity_category/nac here: https://mode-s.org/decode/content/ads-b/7-uncertainty.html

    // ME[5-7] - Subtype Code
    ADSBPacket::OperationStatusSubtype subtype =
        static_cast<ADSBPacket::OperationStatusSubtype>(packet.GetNBitWordFromMessage(3, 5));

    // ME[8-23] - Airborne or Surface Capacity Class Code
    // ME[11] - 1090ES In
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagHas1090ESIn, packet.GetNBitWordFromMessage(1, 11));
    // Other fields handled in switch statement.

    // ME[24-39] - Operational Altitude Replyode
    // ME[26] - TCAS RA Active
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagTCASRA, packet.GetNBitWordFromMessage(1, 26));
    // ME[27] - IDENT Switch Active
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagIdent, packet.GetNBitWordFromMessage(1, 27));
    // ME[29] - Single Antenna Flag
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagSingleAntenna, packet.GetNBitWordFromMessage(1, 29));
    // ME[30-31] - System Design Assurance
    system_design_assurance = static_cast<ModeSAircraft::SystemDesignAssurance>(packet.GetNBitWordFromMessage(2, 30));

    // ME[40-42] - ADS-B Version Number
    adsb_version = packet.GetNBitWordFromMessage(3, 40);

    // ME[43] - NIC Supplement A
    WriteNICBit(ModeSAircraft::NICBit::kNICBitC, packet.GetNBitWordFromMessage(1, 43));

    // ME[44-47] - Navigational Accuracy Category, Position
    navigation_accuracy_category_position =
        static_cast<ModeSAircraft::NACEstimatedPositionUncertainty>(packet.GetNBitWordFromMessage(4, 44));

    // ME[50-51] - Source Integrity Level (SIL)
    uint8_t source_integrity_level = packet.GetNBitWordFromMessage(2, 50);
    // ME[53] - Horizontal Reference Direction (HRD)
    WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagHeadingUsesMagneticNorth, packet.GetNBitWordFromMessage(1, 53));
    // ME[54] - SIL Supplement
    uint8_t sil_supplement = packet.GetNBitWordFromMessage(1, 54);
    source_integrity_level = static_cast<ModeSAircraft::SILProbabilityOfExceedingNICRadiusOfContainmnent>(
        (sil_supplement << 2) | source_integrity_level);

    // Conditional fields (meaning depends on subtype).
    switch (subtype) {
        case ADSBPacket::OperationStatusSubtype::kOperationStatusSubtypeAirborne:  // ST = 0
        {
            // ME[10] - TCAS Operational
            WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagTCASOperational, packet.GetNBitWordFromMessage(1, 10));

            // ME[14] - Air Referenced Velocity (ARV) Report Capability - Ignored
            // ME[15] - Target State (TS) Report Capability - Ignored
            // ME[16-17] - Trajectory Change (TC) Report Capability - Ignored
            // ME[18] - UAT In
            WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagHasUATIn, packet.GetNBitWordFromMessage(1, 18));

            // ME[48-49] - GVA
            geometric_vertical_accuracy = static_cast<ModeSAircraft::GVA>(packet.GetNBitWordFromMessage(2, 48));

            // ME[52] - NIC Baro
            navigation_integrity_category_baro =
                static_cast<ModeSAircraft::NICBarometricAltitudeIntegrity>(packet.GetNBitWordFromMessage(1, 52));

            break;
        }
        case ADSBPacket::OperationStatusSubtype::kOperationStatusSubtypeSurface:  // ST = 1
        {
            // ME[14] - B2 Low
            WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagIsClassB2GroundVehicle, packet.GetNBitWordFromMessage(1, 14));
            // ME[15] - UAT In
            WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagHasUATIn, packet.GetNBitWordFromMessage(1, 15));
            // ME[16-18] - NACv
            navigation_accuracy_category_velocity =
                static_cast<ModeSAircraft::NACHorizontalVelocityError>(packet.GetNBitWordFromMessage(3, 16));
            // ME[19] - NIC Supplement C
            WriteNICBit(ModeSAircraft::NICBit::kNICBitC, packet.GetNBitWordFromMessage(1, 19));

            // ME[20-23] Aircraft/Vehicle Length and Width Code
            switch (packet.GetNBitWordFromMessage(4, 20)) {
                case 0:
                    length_m = 0;
                    width_m = 0;
                    break;
                case 1:
                    length_m = 15;
                    width_m = 23;
                    break;
                case 2:
                    length_m = 25;
                    width_m = 29;  // Rounded up from 28.5.
                    break;
                case 3:
                    length_m = 25;
                    width_m = 34;
                    break;
                case 4:
                    length_m = 35;
                    width_m = 33;
                    break;
                case 5:
                    length_m = 35;
                    width_m = 38;
                    break;
                case 6:
                    length_m = 45;
                    width_m = 40;  // Rounded up from 39.5.
                    break;
                case 7:
                    length_m = 45;
                    width_m = 45;
                    break;
                case 8:
                    length_m = 55;
                    width_m = 45;
                    break;
                case 9:
                    length_m = 55;
                    width_m = 52;
                    break;
                case 10:
                    length_m = 65;
                    width_m = 60;  // Rounded up from 59.5.
                    break;
                case 11:
                    length_m = 65;
                    width_m = 67;
                    break;
                case 12:
                    length_m = 75;
                    width_m = 73;  // Rounded up from 72.5.
                    break;
                case 13:
                    length_m = 75;
                    width_m = 80;
                    break;
                case 14:
                    length_m = 85;
                    width_m = 80;
                    break;
                case 15:
                    length_m = 85;
                    width_m = 90;
                    break;
            }

            // ME[32-39] - GPS Antenna Offset
            // Only present in surface position operation status packets.
            switch (packet.GetNBitWordFromMessage(8, 32)) {
                case 0b000:  // No data.
                    break;
                case 0b001:  // 2 meters left of roll axis.
                    gnss_antenna_offset_right_of_roll_axis_m = -2;
                    break;
                case 0b010:  // 4 meters left of roll axis.
                    gnss_antenna_offset_right_of_roll_axis_m = -4;
                    break;
                case 0b011:  // 6 meters left of roll axis.
                    gnss_antenna_offset_right_of_roll_axis_m = -6;
                    break;
                case 0b100:  // Centered on roll axis.
                    gnss_antenna_offset_right_of_roll_axis_m = 0;
                    break;
                case 0b101:  // 2 meters right of roll axis.
                    gnss_antenna_offset_right_of_roll_axis_m = 2;
                    break;
                case 0b110:  // 4 meters right of roll axis.
                    gnss_antenna_offset_right_of_roll_axis_m = 4;
                    break;
                case 0b111:  // 6 meters right of roll axis.
                    gnss_antenna_offset_right_of_roll_axis_m = 6;
                    break;
            }

            // ME[52] Track Angle / Heading for Surface Position Messages
            WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagDirectionIsHeading, packet.GetNBitWordFromMessage(1, 52));

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

/**
 * UATAircraft
 */
UATAircraft::UATAircraft(uint32_t icao_address_in) : icao_address(icao_address_in) {};
UATAircraft::~UATAircraft() {};

/**
 * Aircraft Dictionary
 */

void AircraftDictionary::Init() {
    dict.clear();  // Remove all aircraft from the unordered map.
}

void AircraftDictionary::Update(uint32_t timestamp_ms) {
    // Iterate over each key-value pair in the unordered_map. Prune if stale, update metrics if still fresh.
    for (auto it = dict.begin(); it != dict.end(); /* No increment here */) {
        uint32_t last_message_timestamp_ms =
            std::visit([](auto &aircraft) -> uint32_t { return aircraft.last_message_timestamp_ms; }, it->second);

        // Extract the last message timestamp of the underlying ModeSAircraft or UATAircraft.
        if (timestamp_ms - last_message_timestamp_ms > config_.aircraft_prune_interval_ms) {
            it = dict.erase(it);  // Remove stale aircraft entry. Iterator is incremented to the next element.
        } else {
            // Call UpdateMetrics on the underlying aircraft type.
            std::visit(
                [](auto &aircraft) {
                    // Update the metrics for the aircraft.
                    UpdateMetrics();
                },
                it->second);

            it++;  // Move to the next aircraft entry.
        }
    }

    // Update aggregate statistics.
    metrics = metrics_counter_;    // Swap counter values over to publicly visible values.
    metrics_counter_ = Metrics();  // Use default constructor to clear all values.
}

bool AircraftDictionary::ContainsAircraft(uint32_t uid) const {
    auto itr = dict.find(uid);
    if (itr != dict.end()) {
        return true;
    }
    return false;
}

bool AircraftDictionary::IngestDecodedModeSPacket(DecodedModeSPacket &packet) {
    // Check validity and record stats.
    int16_t source = packet.GetRaw().source;
    switch (packet.GetBufferLenBits()) {
        case RawModeSPacket::kSquitterPacketLenBits:
            // Validate packet against ICAO addresses in dictionary, or allow it in if it's a DF=11 all call reply
            // packet tha validated itself (e.g. it's a response to a spontaneous acquisition squitter with interrogator
            // ID=0, making the checksum useable).
            if (packet.GetDownlinkFormat() != DecodedModeSPacket::kDownlinkFormatAllCallReply &&
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
        case RawModeSPacket::kExtendedSquitterPacketLenBits:
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
                "AircraftDictionary::IngestDecodedModeSPacket",
                "Received packet with unrecognized bitlength %d, expected %d (Squitter) or %d (Extended Squitter).",
                packet.GetBufferLenBits(), RawModeSPacket::kSquitterPacketLenBits,
                RawModeSPacket::kExtendedSquitterPacketLenBits);
            return false;
    }

    // Ingest packet.
    bool ingest_ret = false;
    uint16_t downlink_format = packet.GetDownlinkFormat();
    switch (downlink_format) {
        // Altitude Reply Packet.
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatAltitudeReply:
            ingest_ret = IngestAltitudeReplyPacket(AltitudeReplyPacket(packet));
            break;
        // Identity Reply Packet.
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatIdentityReply:
            ingest_ret = IngestIdentityReplyPacket(IdentityReplyPacket(packet));
            break;
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatAllCallReply:  // DF = 11
            ingest_ret = IngestAllCallReplyPacket(AllCallReplyPacket(packet));
            break;
        // ADS-B Packets.
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatExtendedSquitter:                // DF = 17
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatExtendedSquitterNonTransponder:  // DF = 18
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatMilitaryExtendedSquitter:        // DF = 19
            // Handle ADS-B Packets.
            ingest_ret = IngestADSBPacket(ADSBPacket(packet));
            break;
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatShortRangeAirToAirSurveillance:  // DF = 0
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatLongRangeAirToAirSurveillance:   // DF = 16
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatCommBAltitudeReply:              // DF = 20
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatCommBIdentityReply:              // DF = 21
        case DecodedModeSPacket::DownlinkFormat::kDownlinkFormatCommDExtendedLengthMessage:      // DF = 24
            // Silently handle currently unsupported downlink formats.
            ingest_ret = true;
            break;

        default:
            CONSOLE_WARNING("AircraftDictionary::IngestDecodedModeSPacket",
                            "Encountered unexpected downlink format %d for ICAO 0x%lx.", downlink_format,
                            packet.GetICAOAddress());
            ingest_ret = false;
    }
    return ingest_ret;
}

bool AircraftDictionary::IngestIdentityReplyPacket(IdentityReplyPacket packet) {
    if (!packet.IsValid() || packet.GetDownlinkFormat() != IdentityReplyPacket::kDownlinkFormatIdentityReply) {
        return false;
    }

    uint32_t icao_address = packet.GetICAOAddress();
    ModeSAircraft *aircraft_ptr = GetAircraftPtr(icao_address);
    if (aircraft_ptr == nullptr) {
        CONSOLE_WARNING("AircraftDictionary::IngestIdentityReplyPacket",
                        "Unable to find or create new aircraft with ICAO address 0x%lx in dictionary.\r\n",
                        icao_address);
        return false;  // unable to find or create new aircraft in dictionary
    }
    aircraft_ptr->WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagIsAirborne, packet.IsAirborne());
    aircraft_ptr->WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagAlert, packet.HasAlert());
    aircraft_ptr->WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagIdent, packet.HasIdent());
    aircraft_ptr->squawk = packet.GetSquawk();
    aircraft_ptr->IncrementNumFramesReceived(false);

    return true;
}

bool AircraftDictionary::IngestAltitudeReplyPacket(AltitudeReplyPacket packet) {
    if (!packet.IsValid() || packet.GetDownlinkFormat() != AltitudeReplyPacket::kDownlinkFormatAltitudeReply) {
        return false;
    }

    uint32_t icao_address = packet.GetICAOAddress();
    ModeSAircraft *aircraft_ptr = GetAircraftPtr(icao_address);
    if (aircraft_ptr == nullptr) {
        CONSOLE_WARNING("AircraftDictionary::IngestAltitudeReplyPacket",
                        "Unable to find or create new aircraft with ICAO address 0x%lx in dictionary.\r\n",
                        icao_address);
        return false;  // unable to find or create new aircraft in dictionary
    }
    aircraft_ptr->WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagIsAirborne, packet.IsAirborne());
    aircraft_ptr->WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagAlert, packet.HasAlert());
    aircraft_ptr->WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagIdent, packet.HasIdent());
    aircraft_ptr->baro_altitude_ft = packet.GetAltitudeFt();
    aircraft_ptr->WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagBaroAltitudeValid, true);
    aircraft_ptr->WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagUpdatedBaroAltitude, true);
    aircraft_ptr->IncrementNumFramesReceived(false);

    return true;
}

bool AircraftDictionary::IngestAllCallReplyPacket(AllCallReplyPacket packet) {
    if (!packet.IsValid() || packet.GetDownlinkFormat() != DecodedModeSPacket::kDownlinkFormatAllCallReply) {
        return false;
    }

    // Populate the dictionary with the aircraft, or look it up if the ICAO doesn't yet exist.
    uint32_t icao_address = packet.GetICAOAddress();
    ModeSAircraft *aircraft_ptr = GetAircraftPtr(icao_address);
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
    ModeSAircraft *aircraft_ptr = GetAircraftPtr(icao_address);
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
            ret = aircraft_ptr->ApplyAircraftIDMessage(packet);
            break;
        case ADSBPacket::kTypeCodeSurfacePosition:      // TC = 5 (Surface Position)
        case ADSBPacket::kTypeCodeSurfacePosition + 1:  // TC = 6 (Surface Position)
        case ADSBPacket::kTypeCodeSurfacePosition + 2:  // TC = 7 (Surface Position)
        case ADSBPacket::kTypeCodeSurfacePosition + 3:  // TC = 8 (Surface Position)
            ret = aircraft_ptr->ApplySurfacePositionMessage(packet);
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
            ret = aircraft_ptr->ApplyAirbornePositionMessage(packet, config_.enable_cpr_position_filter);
            break;
        case ADSBPacket::kTypeCodeAirborneVelocities:  // TC = 19 (Airborne Velocities)
            ret = aircraft_ptr->ApplyAirborneVelocitiesMessage(packet);
            break;
        case ADSBPacket::kTypeCodeReserved:      // TC = 23 (Reserved)
        case ADSBPacket::kTypeCodeReserved + 1:  // TC = 24 (Reserved)
        case ADSBPacket::kTypeCodeReserved + 2:  // TC = 25 (Reserved)
        case ADSBPacket::kTypeCodeReserved + 3:  // TC = 26 (Reserved)
        case ADSBPacket::kTypeCodeReserved + 4:  // TC = 27 (Reserved)
            ret = false;
            break;
        case ADSBPacket::kTypeCodeAircraftStatus:  // TC = 28 (Aircraft Status)
            ret = aircraft_ptr->ApplyAircraftStatusMessage(packet);
            break;
        case ADSBPacket::kTypeCodeTargetStateAndStatusInfo:  // TC = 29 (Target state and status info)
            ret = aircraft_ptr->ApplyTargetStateAndStatusInfoMessage(packet);
            break;
        case ADSBPacket::kTypeCodeAircraftOperationStatus:  // TC = 31 (Aircraft operation status)
            ret = aircraft_ptr->ApplyAircraftOperationStatusMessage(packet);
            break;
        default:
            CONSOLE_WARNING("AircraftDictionary::IngestADSBPacket",
                            "Received ADSB message with unsupported typecode %d for ICAO 0x%lx.", typecode,
                            packet.GetICAOAddress());
            ret = false;  // kTypeCodeInvalid, etc.
    }
    if (ret) {
        aircraft_ptr->IncrementNumFramesReceived(true);  // Count the received Mode S frame.
    } else {
        CONSOLE_WARNING("AircraftDictionary::IngestADSBPacket",
                        "Failed to apply ADSB message with typecode %d to ICAO 0x%lx.", typecode,
                        packet.GetICAOAddress());
    }
    return ret;
}

bool AircraftDictionary::InsertAircraft(AircraftEntry_t &aircraft) {
    uint32_t uid = aircraft.GetUID();
    auto itr = dict.find(uid);
    if (itr != dict.end()) {
        // Overwriting an existing aircraft
        itr->second = aircraft;
        return true;
    }

    if (dict.size() >= kMaxNumAircraft) {
        CONSOLE_INFO("AircraftDictionary::InsertAircraft",
                     "Failed to add aircraft to dictionary, reached max number of aircraft (%d).", kMaxNumAircraft);
        return false;  // not enough room to add this aircraft
    }

    dict[uid] = aircraft;  // add the new aircraft to the dictionary
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

bool AircraftDictionary::GetAircraft(uint32_t uid, AircraftEntry_t &aircraft_out, bool insert_if_not_found) {
    auto itr = dict.find(uid);
    if (itr != dict.end()) {
        // Found aircraft with UID in the dictionary.
        aircraft_out = itr->second;
        return true;
    } else if (insert_if_not_found) {
        // Aircraft not found, but requested to be inserted.
        if (dict.size() >= kMaxNumAircraft) {
            CONSOLE_INFO("AircraftDictionary::GetAircraft",
                         "Failed to create new aircraft with UID 0x%lx, reached max number of aircraft (%d).", uid,
                         kMaxNumAircraft);
            return false;  // not enough room to add this aircraft
        }
        Aircraft::AircraftType type = Aircraft::UIDToAircraftAType(uid);
        uint32_t icao_address = Aircraft::UIDToICAOAddress(uid);
        switch (type) {
            case Aircraft::kAircraftTypeModeSAircraft: {
                dict[uid] = ModeSAircraft(icao_address);
                aircraft_out = dict[uid];
                break;
            }
            case Aircraft::kAircraftTypeUATAircraft: {
                dict[uid] = UATAircraft(icao_address);
                aircraft_out = dict[uid];
                break;
            }
            default:
                CONSOLE_ERROR("AircraftDictionary::GetAircraft",
                              "Unable to create new aircraft with UID 0x%lx, unsupported aircraft type %d.", uid,
                              static_cast<int>(type));
                return false;  // Unsupported aircraft type, cannot create new aircraft.
        }
        return true;
    }
    // Aircraft not found and not requested to be inserted.
    return false;
}

bool ModeSAircraft::SetCPRLatLon(uint32_t n_lat_cpr, uint32_t n_lon_cpr, bool odd, uint32_t received_timestamp_ms) {
    if (n_lat_cpr > kCPRLatLonMaxCount || n_lon_cpr > kCPRLatLonMaxCount) {
        CONSOLE_ERROR("ModeSAircraft::SetCPRLatLon",
                      "Received CPR packet with out of bounds lat/lon values (%lu, %lu).", n_lat_cpr, n_lon_cpr);
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
    return true;
}

/**
 * Private functions and associated helpers.
 */
