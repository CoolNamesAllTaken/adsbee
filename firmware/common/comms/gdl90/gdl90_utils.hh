#ifndef GDL90_UTILS_HH_
#define GDL90_UTILS_HH_

#include "aircraft_dictionary.hh"
#include "macros.hh"  // for MIN macro.

// GDL90 is implemented based on this spec:
// https://www.faa.gov/sites/faa.gov/files/air_traffic/technology/adsb/archival/GDL90_Public_ICD_RevA.PDF

class GDL90Reporter {
   public:
    static const uint16_t kGDL90MessageMaxLenBytes = 436;
    static const uint8_t kGDL90FlagByte = 0x7E;
    static const uint8_t kGDL90ControlEscapeChar = 0x7D;

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
        bool traffic_alert_status = false;  // 1 = Traffic Alert is active for this target.
        uint8_t address_type;               // Type of address conveyed in Participant Address field.
        uint32_t participant_address;       // 24 bit ICAO address.
        float latitude_deg;                 // 24-bit signed binary fraction. Resolution = 180/2^23 degrees.
        float longitude_deg;                // 24-bit signed binary fraction. Resolution = 180/2^23 degrees.
        float altitude_ft;                  // 12-bit offset integer. Resolution = 25 feet.
        uint8_t misc_indicators;
        uint8_t navigation_integrity_category;          // Navigation Integrity Category (NIC).
        uint8_t navigation_accuracy_category_position;  // Navigation Accuracy Category for Postion (NACp).
        float velocity_kts;
        int vertical_rate_fpm;
        float track_heading_deg;
        uint8_t emitter_category;
        char callsign[9];                 // 8 characters, 0-9 and A-Z
        uint8_t emergency_priority_code;  // 4 bits.
    };

    /**
     * Calculates the CRC for a buffer that contains a message ID and message data, then adds escapes, frames it with
     * flag bytes, and writes it to an output buffer.
     * @param[out] to_buf Output buffer to write to.
     * @param[in] unescaped_message Byte buffer that includes the message ID and message data, with no escapes added and
     * no framing bytes.
     * @param[in] unescaped_message_len_bytes Length of unescaped_message buffer, in bytes.
     * @retval Number of Bytes written to to_buf.
     */
    uint16_t WriteGDL90Message(uint8_t *to_buf, uint8_t *unescaped_message, uint8_t unescaped_message_len_bytes);

    /**
     * Write a payload to a buffer, automatically adding escape sequences as required. Everything except for start and
     * end of message flags should be passed in as part of the payload.
     * @param[out] to_buf Buffer to write to.
     * @param[in] from_buf Buffer to read from.
     * @param[in] from_buf_len_bytes Number of bytes to read in.
     * @retval Number of bytes written to to_buf.
     */
    uint16_t WriteBufferWithGDL90Escapes(uint8_t *to_buf, const uint8_t *from_buf, uint16_t from_buf_num_bytes);

    uint16_t WriteGDL90HeartbeatMessage(uint8_t *to_buf, uint32_t timestamp_sec_since_0000z, uint16_t message_counts);
    uint16_t WriteGDL90InitMessage(uint8_t *to_buf);
    /**
     * Write a GDL90 message for an uplink message received from UAT ground broadcast transceivers.
     * @param[out] to_buf Buffer to write to.
     * @param[in] tor_us Time Of Arrival of the uplink data message, in microseconds since the reference timestamp in
     * the Heartbeat message. Should never be larger than 1 second.
     */
    uint16_t WriteGDL90UplinkDataMessage(uint8_t *to_buf, uint8_t *uplink_payload, uint16_t uplink_payload_len_bytes,
                                         uint32_t tor_us = 0xFFFFFFFF);
    uint16_t WriteGDL90TargetReportMessage(uint8_t *to_buf, const GDL90TargetReportData &data, bool ownship = false);

    // uint16_t AircraftToGDL90Frame(const Aircraft &aircraft) {}

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
    uint16_t CalculateGDL90CRC16(uint8_t *buf, uint16_t buf_len_bytes) {
        uint32_t i;
        uint16_t crc = 0;
        for (i = 0; i < buf_len_bytes; i++) {
            crc = kGDL90CRC16Table[crc >> 8] ^ (crc << 8) ^ buf[i];
        }
        return crc;
    }
};

#endif