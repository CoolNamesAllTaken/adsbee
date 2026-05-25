#pragma once
#include "aircraft_dictionary.hh"
#include "stdio.h"

const uint16_t kAircraftJSONMessageStrMaxLen = 512;

// Emergency priority status strings matching readsb nomenclature.
static const char* const kUATEmergencyStrings[] = {"none",     "general",  "lifeguard", "minfuel",
                                                    "nordo",    "unlawful", "downed",    "reserved"};
static const uint8_t kUATEmergencyStringsCount =
    sizeof(kUATEmergencyStrings) / sizeof(kUATEmergencyStrings[0]);

/**
 * Converts an EmitterCategory enum value to the readsb-style "A0"–"D7" category string.
 * Category 0 is "A0" (no category info); negative values are invalid.
 * @param[out] buf Output buffer (must hold at least 3 bytes: letter + digit + NUL).
 * @param[in] buf_len Length of output buffer.
 * @param[in] category EmitterCategory enum value.
 * @retval True if a valid category string was written, false if category is invalid.
 */
static inline bool EmitterCategoryToStr(char* buf, size_t buf_len, ADSBTypes::EmitterCategory category) {
    if (category < 0) return false;
    snprintf(buf, buf_len, "%c%d", (char)('A' + (category / 8)), category % 8);
    return true;
}

/**
 * Serializes a ModeSAircraft to a single-line readsb-compatible JSON object.
 * @param[out] buf Character array of at least kAircraftJSONMessageStrMaxLen bytes.
 * @param[in] aircraft Aircraft to serialize.
 * @retval Number of characters written (excluding the NUL terminator), or negative on error.
 */
inline int16_t WriteAircraftJSONModeSAircraftStr(char buf[], const ModeSAircraft& aircraft) {
    int16_t n = 0;
    const int16_t max = kAircraftJSONMessageStrMaxLen;

    // hex (always)
    n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                  "{\"hex\":\"%06x\"",
#else
                  "{\"hex\":\"%06lx\"",
#endif
                  aircraft.icao_address);

    // type
    const char* type_str = "adsb_icao";
    if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagIsNonTransponder)) {
        type_str = "adsr_icao";
    } else if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagIsClassB2GroundVehicle)) {
        type_str = "adsb_icao_nt";
    }
    n += snprintf(buf + n, max - n, ",\"type\":\"%s\"", type_str);

    // flight (only if set — default is "?")
    if (aircraft.callsign[0] != '?' && aircraft.callsign[0] != '\0') {
        n += snprintf(buf + n, max - n, ",\"flight\":\"%s\"", aircraft.callsign);
    }

    // squawk
    if (aircraft.squawk != ADSBTypes::kSquawkCodeNotYetReceived) {
        n += snprintf(buf + n, max - n, ",\"squawk\":\"%04o\"", aircraft.squawk & 07777);
    }

    // category ("A0"–"D7")
    if (aircraft.emitter_category != ADSBTypes::kEmitterCategoryInvalid) {
        char cat_str[4];
        if (EmitterCategoryToStr(cat_str, sizeof(cat_str), aircraft.emitter_category)) {
            n += snprintf(buf + n, max - n, ",\"category\":\"%s\"", cat_str);
        }
    }

    // lat / lon
    if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagPositionValid)) {
        n += snprintf(buf + n, max - n, ",\"lat\":%.5f,\"lon\":%.5f", aircraft.latitude_deg,
                      aircraft.longitude_deg);
    }

    // alt_baro
    if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagBaroAltitudeValid)) {
        n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                      ",\"alt_baro\":%d",
#else
                      ",\"alt_baro\":%ld",
#endif
                      aircraft.baro_altitude_ft);
    }

    // alt_geom
    if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagGNSSAltitudeValid)) {
        n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                      ",\"alt_geom\":%d",
#else
                      ",\"alt_geom\":%ld",
#endif
                      aircraft.gnss_altitude_ft);
    }

    // gs (ground speed)
    if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagHorizontalSpeedValid)) {
        n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                      ",\"gs\":%d",
#else
                      ",\"gs\":%ld",
#endif
                      aircraft.speed_kts);
    }

    // track / mag_heading / true_heading
    if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagDirectionValid)) {
        const char* dir_key;
        if (!aircraft.HasBitFlag(ModeSAircraft::kBitFlagDirectionIsHeading)) {
            dir_key = "track";
        } else if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagHeadingUsesMagneticNorth)) {
            dir_key = "mag_heading";
        } else {
            dir_key = "true_heading";
        }
        n += snprintf(buf + n, max - n, ",\"%s\":%.1f", dir_key, aircraft.direction_deg);
    }

    // baro_rate
    if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagBaroVerticalRateValid)) {
        n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                      ",\"baro_rate\":%d",
#else
                      ",\"baro_rate\":%ld",
#endif
                      aircraft.baro_vertical_rate_fpm);
    }

    // geom_rate
    if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagGNSSVerticalRateValid)) {
        n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                      ",\"geom_rate\":%d",
#else
                      ",\"geom_rate\":%ld",
#endif
                      aircraft.gnss_vertical_rate_fpm);
    }

    // Integrity / accuracy fields (always present)
    n += snprintf(buf + n, max - n,
                  ",\"nic\":%d,\"nic_baro\":%d,\"nac_p\":%d,\"nac_v\":%d"
                  ",\"sil\":%d,\"gva\":%d,\"sda\":%d,\"version\":%d",
                  aircraft.navigation_integrity_category, aircraft.navigation_integrity_category_baro,
                  aircraft.navigation_accuracy_category_position, aircraft.navigation_accuracy_category_velocity,
                  aircraft.surveillance_integrity_level, aircraft.geometric_vertical_accuracy,
                  aircraft.system_design_assurance, aircraft.adsb_version);

    // rssi and message count (always present)
    n += snprintf(buf + n, max - n, ",\"rssi\":%d,\"messages\":%u", aircraft.last_message_signal_strength_dbm,
                  (unsigned)(aircraft.metrics.valid_squitter_frames + aircraft.metrics.valid_extended_squitter_frames));

    // alert / spi (only when set)
    if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagAlert)) {
        n += snprintf(buf + n, max - n, ",\"alert\":1");
    }
    if (aircraft.HasBitFlag(ModeSAircraft::kBitFlagIdent)) {
        n += snprintf(buf + n, max - n, ",\"spi\":1");
    }

    n += snprintf(buf + n, max - n, "}\n");

    if (n >= max) return -1;  // Buffer overrun.
    return n;
}

/**
 * Serializes a UATAircraft to a single-line readsb-compatible JSON object.
 * @param[out] buf Character array of at least kAircraftJSONMessageStrMaxLen bytes.
 * @param[in] aircraft Aircraft to serialize.
 * @retval Number of characters written (excluding the NUL terminator), or negative on error.
 */
inline int16_t WriteAircraftJSONUATAircraftStr(char buf[], const UATAircraft& aircraft) {
    int16_t n = 0;
    const int16_t max = kAircraftJSONMessageStrMaxLen;

    UATAircraft::AddressQualifier aq = aircraft.GetAddressQualifier();
    uint32_t icao_24bit = aircraft.icao_address & ~Aircraft::kAddressQualifierMask;

    // Non-ICAO addresses get a '~' prefix per readsb convention.
    bool is_non_icao = (aq == UATAircraft::kADSBTargetWithSelfAssignedTemporaryAddress ||
                        aq == UATAircraft::kTISBTargetWithTrackFileIdentifier);

    // hex (always)
    n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                  "{\"hex\":\"%s%06x\"",
#else
                  "{\"hex\":\"%s%06lx\"",
#endif
                  is_non_icao ? "~" : "", icao_24bit);

    // type (derived from address qualifier)
    const char* type_str;
    switch (aq) {
        case UATAircraft::kADSBTargetWithICAO24BitAddress:
            type_str = "adsb_icao";
            break;
        case UATAircraft::kADSBTargetWithSelfAssignedTemporaryAddress:
            type_str = "adsb_other";
            break;
        case UATAircraft::kTISBTargetWithICAO24BitAddress:
            type_str = "tisb_icao";
            break;
        case UATAircraft::kTISBTargetWithTrackFileIdentifier:
            type_str = "tisb_trackfile";
            break;
        case UATAircraft::kSurfaceVehicle:
        case UATAircraft::kFixedADSBBeacon:
        default:
            type_str = "adsb_icao";
            break;
    }
    n += snprintf(buf + n, max - n, ",\"type\":\"%s\"", type_str);

    // flight
    if (aircraft.callsign[0] != '?' && aircraft.callsign[0] != '\0') {
        n += snprintf(buf + n, max - n, ",\"flight\":\"%s\"", aircraft.callsign);
    }

    // squawk
    if (aircraft.squawk != ADSBTypes::kSquawkCodeNotYetReceived) {
        n += snprintf(buf + n, max - n, ",\"squawk\":\"%04o\"", aircraft.squawk & 07777);
    }

    // category
    if (aircraft.emitter_category != ADSBTypes::kEmitterCategoryInvalid) {
        char cat_str[4];
        if (EmitterCategoryToStr(cat_str, sizeof(cat_str), aircraft.emitter_category)) {
            n += snprintf(buf + n, max - n, ",\"category\":\"%s\"", cat_str);
        }
    }

    // lat / lon
    if (aircraft.HasBitFlag(UATAircraft::kBitFlagPositionValid)) {
        n += snprintf(buf + n, max - n, ",\"lat\":%.5f,\"lon\":%.5f", aircraft.latitude_deg,
                      aircraft.longitude_deg);
    }

    // alt_baro
    if (aircraft.HasBitFlag(UATAircraft::kBitFlagBaroAltitudeValid)) {
        n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                      ",\"alt_baro\":%d",
#else
                      ",\"alt_baro\":%ld",
#endif
                      aircraft.baro_altitude_ft);
    }

    // alt_geom
    if (aircraft.HasBitFlag(UATAircraft::kBitFlagGNSSAltitudeValid)) {
        n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                      ",\"alt_geom\":%d",
#else
                      ",\"alt_geom\":%ld",
#endif
                      aircraft.gnss_altitude_ft);
    }

    // gs
    if (aircraft.HasBitFlag(UATAircraft::kBitFlagHorizontalSpeedValid)) {
        n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                      ",\"gs\":%d",
#else
                      ",\"gs\":%ld",
#endif
                      aircraft.speed_kts);
    }

    // track / mag_heading / true_heading
    if (aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionValid)) {
        const char* dir_key;
        if (!aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionIsHeading)) {
            dir_key = "track";
        } else if (aircraft.HasBitFlag(UATAircraft::kBitFlagHeadingUsesMagneticNorth)) {
            dir_key = "mag_heading";
        } else {
            dir_key = "true_heading";
        }
        n += snprintf(buf + n, max - n, ",\"%s\":%.1f", dir_key, aircraft.direction_deg);
    }

    // baro_rate
    if (aircraft.HasBitFlag(UATAircraft::kBitFlagBaroVerticalRateValid)) {
        n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                      ",\"baro_rate\":%d",
#else
                      ",\"baro_rate\":%ld",
#endif
                      aircraft.baro_vertical_rate_fpm);
    }

    // geom_rate
    if (aircraft.HasBitFlag(UATAircraft::kBitFlagGNSSVerticalRateValid)) {
        n += snprintf(buf + n, max - n,
#if defined(ON_PICO) || defined(ON_HOST)
                      ",\"geom_rate\":%d",
#else
                      ",\"geom_rate\":%ld",
#endif
                      aircraft.gnss_vertical_rate_fpm);
    }

    // Integrity / accuracy fields (always present)
    n += snprintf(buf + n, max - n,
                  ",\"nic\":%d,\"nic_baro\":%d,\"nac_p\":%d,\"nac_v\":%d"
                  ",\"sil\":%d,\"gva\":%d,\"sda\":%d",
                  aircraft.navigation_integrity_category, aircraft.navigation_integrity_category_baro,
                  aircraft.navigation_accuracy_category_position, aircraft.navigation_accuracy_category_velocity,
                  aircraft.surveillance_integrity_level, aircraft.geometric_vertical_accuracy,
                  aircraft.system_design_assurance);

    // version (only if set)
    if (aircraft.uat_version >= 0) {
        n += snprintf(buf + n, max - n, ",\"version\":%d", aircraft.uat_version);
    }

    // rssi and message count (always present)
    n += snprintf(buf + n, max - n, ",\"rssi\":%d,\"messages\":%u", aircraft.last_message_signal_strength_dbm,
                  (unsigned)aircraft.metrics.valid_frames);

    // emergency (only if not none)
    if (aircraft.emergency_priority_status != UATAircraft::kEmergencyPriorityStatusNone) {
        uint8_t idx = aircraft.emergency_priority_status;
        if (idx < kUATEmergencyStringsCount) {
            n += snprintf(buf + n, max - n, ",\"emergency\":\"%s\"", kUATEmergencyStrings[idx]);
        }
    }

    n += snprintf(buf + n, max - n, "}\n");

    if (n >= max) return -1;  // Buffer overrun.
    return n;
}
