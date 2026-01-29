#pragma once

#include "aircraft_dictionary.hh"
#include "macros.hh"  // for MIN macro.

// GDL90 is implemented based on this spec:
// https://www.faa.gov/sites/faa.gov/files/air_traffic/technology/adsb/archival/GDL90_Public_ICD_RevA.PDF

class GDL90Reporter {
   public:
    // Largest payload is 432 Byte UAT uplink message, this is an arbitrary expansion to account for added escape chars.
    static constexpr uint16_t kGDL90MessageMaxLenBytes = 600;
    static constexpr uint8_t kGDL90FlagByte = 0x7E;
    static constexpr uint8_t kGDL90ControlEscapeChar = 0x7D;

    static const uint16_t kGDL90CRC16Table[256];

    // Per the GDL90 data interface specification, the MSb of GDL90MessageType is always 0, so the value can range from
    // 0-127.
    enum GDL90MessageID : uint8_t {
        kGDL90MessageIDHeartbeat = 0,
        kGDL90MessageIDInitialization = 2,
        kGDL90MessageIDUplinkData = 7,
        kGDL90MessageIDHeightAboveTerrain = 9,
        kGDL90MessageIDOwnshipReport = 10,
        kGDL90MessageIDOwnshipGeometricAltitude = 11,
        kGDL90MessageIDTrafficReport = 20,
        kGDL90MessageIDBasicReport = 30,
        kGDL90MessageIDLongReport = 31
    };

    struct GDL90TargetReportData {
        enum AddressType : uint8_t {
            kAddressTypeADSBWithICAOAddress = 0,
            kAddressTypeADSBWithSelfAssignedAddress = 1,
            kAddressTypeTISBWithICAOAddress = 2,
            kAddressTypeTISBWithTrackFileID = 3,
            kAddressTypeSurfaceVehicle = 4,
            kAddressTypeGroundStationBeacon = 5
            // IDs 6-15 reserved.
        };

        // Indicate what type of data is contained in the 'tt' field in the ownship and traffic report messages.
        enum MiscIndicatorTrackOrHeadingValue : uint8_t {
            kMiscIndicatorTTNotValid = 0,
            kMiscIndicatorTTIsTrueTrackAngle = 0b1,
            kMiscIndicatorTTIsMagneticHeading = 0b10,
            kMiscIndicatorTTIsTrueHeading = 0b11
        };
        void SetMiscIndicator(MiscIndicatorTrackOrHeadingValue tt_value, bool report_is_extrapolated,
                              bool aircraft_is_airborne) {
            misc_indicators = (aircraft_is_airborne << 3) | (report_is_extrapolated << 2) | (tt_value & 0b11);
        }

        enum EmergencyPriorityCode : uint8_t {
            kEmergencyPriorityCodeNoEmergency = 0,
            kEmergencyPriorityCodeGeneralEmergency = 1,
            kEmergencyPriorityCodeMedicalEmergency = 2,
            kEmergencyPriorityCodeMinimumFuel = 3,
            kEmergencyPriorityCodeNoCommunication = 4,
            kEmergencyPriorityCodeUnlawfulInterference = 5,
            kEmergencyPriorityCodeDownedAircraft = 6
            // Codes 7-15 reserved.
        };

        // Note: Target with no valid position has lat, lon, and NIC set to 0.
        bool traffic_alert_status = false;  // 1 = Traffic Alert is active for this target.
        AddressType address_type =
            kAddressTypeADSBWithICAOAddress;  // Type of address conveyed in Participant Address field.
        uint32_t participant_address;         // 24 bit ICAO address.
        float latitude_deg = 0.0f;
        float longitude_deg = 0.0f;
        int16_t altitude_ft;
        uint8_t misc_indicators;
        uint8_t navigation_integrity_category = 0;      // Navigation Integrity Category (NIC).
        uint8_t navigation_accuracy_category_position;  // Navigation Accuracy Category for Postion (NACp).
        float speed_kts;
        int vertical_rate_fpm;
        float direction_deg;
        uint8_t emitter_category;
        char callsign[9] = "        ";  // 8 spaces + null terminator, 0-9 and A-Z
        EmergencyPriorityCode emergency_priority_code = kEmergencyPriorityCodeNoEmergency;  // 4 bits.
    };

    /**
     * Calculates the CRC for a buffer that contains a message ID and message data, then adds escapes, frames it with
     * flag bytes, and writes it to an output buffer.
     * @param[out] to_buf Output buffer to write to.
     * @param[in] to_buf_num_bytes Size of the output buffer, in bytes.
     * @param[in] unescaped_message Byte buffer that includes the message ID and message data, with no escapes added and
     * no framing bytes.
     * @param[in] unescaped_message_len_bytes Length of unescaped_message buffer, in bytes.
     * @retval Number of Bytes written to to_buf.
     */
    uint16_t WriteGDL90Message(uint8_t* to_buf, uint16_t to_buf_num_bytes, uint8_t* unescaped_message,
                               uint8_t unescaped_message_len_bytes);

    /**
     * Write a payload to a buffer, automatically adding escape sequences as required. Everything except for start and
     * end of message flags should be passed in as part of the payload.
     * @param[out] to_buf Buffer to write to.
     * @param[in] to_buf_num_bytes Number of bytes available in to_buf.
     * @param[in] from_buf Buffer to read from.
     * @param[in] from_buf_len_bytes Number of bytes to read in.
     * @retval Number of bytes written to to_buf.
     */
    uint16_t WriteBufferWithGDL90Escapes(uint8_t* to_buf, uint16_t to_buf_num_bytes, const uint8_t* from_buf,
                                         uint16_t from_buf_num_bytes);

    /**
     * Write a GDL90 Heartbeat message.
     * @param[out] to_buf Buffer to write to.
     * @param[in] to_buf_num_bytes Size of the output buffer, in bytes.
     * @param[in] timestamp_sec_since_0000z Timestamp in seconds since 0000Z.
     * @param[in] message_counts Number of messages sent since the last heartbeat.
     * @retval Number of Bytes written to to_buf.
     */
    uint16_t WriteGDL90HeartbeatMessage(uint8_t* to_buf, uint16_t to_buf_num_bytes, uint32_t timestamp_sec_since_0000z,
                                        uint16_t message_counts);

    /**
     * Write a GDL90 Initialization message.
     * @param[out] to_buf Buffer to write to.
     * @param[in] to_buf_num_bytes Size of the output buffer, in bytes.
     * @retval Number of Bytes written to to_buf.
     */
    uint16_t WriteGDL90InitMessage(uint8_t* to_buf, uint16_t to_buf_num_bytes);
    /**
     * Write a GDL90 message for an uplink message received from UAT ground broadcast transceivers.
     * @param[out] to_buf Buffer to write to.
     * @param[in] to_buf_num_bytes Size of the output buffer, in bytes.
     * @param[in] uplink_payload Pointer to the uplink message payload data.
     * @param[in] uplink_payload_len_bytes Length of the uplink message payload, in bytes.
     * @param[in] tor_80ns_ticks Time Of Reception of the uplink data message, in 80ns ticks since the reference
     * timestamp in the Heartbeat message. Should never be larger than 1 second. Default value of 0xFFFFFF indicates
     * insufficient timing accuracy to provide a valid TOR.
     * @retval Number of Bytes written to to_buf.
     */
    uint16_t WriteGDL90UplinkDataMessage(uint8_t* to_buf, uint16_t to_buf_num_bytes, const uint8_t* uplink_payload,
                                         uint16_t uplink_payload_len_bytes, uint32_t tor_80ns_ticks = 0xFFFFFF);
    /**
     * Convert from MLAT 48MHz 64-bit counts to 24-bit UAT TOR ticks with resolution of 80ns.
     * @param[in] mlat_48mhz_64bit_counts 48MHz 64-bit counts.
     * @retval 24-bit UAT TOR ticks.
     */
    static inline uint32_t MLAT48MHz64BitCountsToUATTORTicks(uint64_t mlat_48mhz_64bit_counts) {
        // Convert from 48MHz 64-bit counts to UAT TOR ticks (1 tick = 25/96 microseconds).
        // Mask down to 32 bits to avoid overflow, apply scaling, then mask to 24 bits for return value.
        return static_cast<uint32_t>(((mlat_48mhz_64bit_counts & 0xFFFFFFFF) * 96 / 25) & 0xFFFFFF);
    }

    /**
     * Write a GDL90 message for ownship or traffic data.
     * @param[out] to_buf Buffer to write to.
     * @param[in] to_buf_num_bytes Size of the output buffer, in bytes.
     * @param[in] data GDL90TargetReportData struct to use when populating the target report message.
     * @param[in] ownship Set to true if this message is an ownship report, false if it's a traffic report.
     */
    uint16_t WriteGDL90TargetReportMessage(uint8_t* to_buf, uint16_t to_buf_num_bytes,
                                           const GDL90TargetReportData& data, bool ownship = false);
    /**
     * Write a GDL90 message for ownship or traffic data. This function calls the version that takes a
     * GDL90TargetReportData object, and is provided for convenience when sending Aircraft from an AircraftDictionary.
     * @param[out] to_buf Buffer to write to.
     * @param[in] to_buf_num_bytes Size of the output buffer, in bytes.
     * @param[in] aircraft Reference to Aircraft object to report. Could be a ModeSAircraft or UATAircraft.
     * @param[in] ownship Set to true if this message is an ownship report, false if it's a traffic report.
     */
    uint16_t WriteGDL90TargetReportMessage(uint8_t* to_buf, uint16_t to_buf_num_bytes, const ModeSAircraft& aircraft,
                                           bool ownship = false);
    uint16_t WriteGDL90TargetReportMessage(uint8_t* to_buf, uint16_t to_buf_num_bytes, const UATAircraft& aircraft,
                                           bool ownship = false);

    // Bit Flags for Message ID 0 (Heartbeat).
    bool uat_initialized = true;
    bool gnss_position_valid = false;
    bool maintenance_required = false;
    bool utc_timing_is_valid = false;
    bool csa_requested = false;
    bool csa_not_available = false;

    // Bit Flags for Message ID 2 (Initialization).
    bool audio_test = false;
    bool audio_inhibit = false;
    bool cdti_ok = false;
    bool csa_audio_disable = false;
    bool csa_disable = false;

    /**
     * Calculate a 16-bit CRC using the pre-calculated GDL90 CRC table.
     * @param[in] buf Pointer to the message payload.
     * @param[in] buf_len_bytes Payload length in bytes.
     * @retval Calculated 16-bit CRC value.
     */
    inline uint16_t CalculateGDL90CRC16(uint8_t* buf, uint16_t buf_len_bytes) {
        uint32_t i;
        uint16_t crc = 0;
        for (i = 0; i < buf_len_bytes; i++) {
            crc = kGDL90CRC16Table[crc >> 8] ^ (crc << 8) ^ buf[i];
        }
        return crc;
    }
};