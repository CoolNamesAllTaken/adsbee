#pragma once

#include <cstdint>

#include "adsb_types.hh"
#include "buffer_utils.hh"

static const uint16_t kUATSyncNumBits = 36;
static const uint16_t kUATSyncNumBytes = CeilBitsToBytes(kUATSyncNumBits);

class RawUATADSBPacket {
   public:
    static const uint64_t kSyncWord = 0b1110'10101100'11011101'10100100'11100010;  // 0xEACDDA4E2

    // Split the 36-bit sync word into 32 most-significant bits (used as the Sync word by the MCU), and 4
    // least-significant bits that get ingested as the first Byte of the message, used to discriminate between uplink
    // and ADS-B packets.
    static const uint32_t kSyncWordMS32 = (kSyncWord >> 4) & 0xFFFFFFFF;
    static const uint8_t kSyncWordLS4 = kSyncWord & 0xF;

    /**
     * UAT downlink message parameters.
     */
    static const uint16_t kShortADSBMessagePayloadNumBits = 144;
    static const uint16_t kShortADSBMessagePayloadNumBytes = CeilBitsToBytes(kShortADSBMessagePayloadNumBits);
    static const uint16_t kShortADSBMessageFECParityNumBits = 96;
    static const uint16_t kShortADSBMessageFECParityNumBytes = CeilBitsToBytes(kShortADSBMessageFECParityNumBits);
    static const uint16_t kShortADSBMessageNumBits =
        kShortADSBMessagePayloadNumBits + kShortADSBMessageFECParityNumBits;
    static const uint16_t kShortADSBMessageNumBytes = CeilBitsToBytes(kShortADSBMessageNumBits);

    static const uint16_t kLongADSBMessagePayloadNumBits = 272;
    static const uint16_t kLongADSBMessagePayloadNumBytes = CeilBitsToBytes(kLongADSBMessagePayloadNumBits);
    static const uint16_t kLongADSBMessageFECParityNumBits = 112;
    static const uint16_t kLongADSBMessageFECParityNumBytes = CeilBitsToBytes(kLongADSBMessageFECParityNumBits);
    static const uint16_t kLongADSBMessageNumBits = kLongADSBMessagePayloadNumBits + kLongADSBMessageFECParityNumBits;
    static const uint16_t kLongADSBMessageNumBytes = CeilBitsToBytes(kLongADSBMessageNumBits);

    static const uint16_t kADSBMessageMaxSizeBytes =
        kLongADSBMessagePayloadNumBytes + kLongADSBMessageFECParityNumBytes;  // For convenience.

    RawUATADSBPacket(const char *rx_string, int16_t sigs_dbm_in = INT16_MIN, int16_t sigq_bits_in = INT16_MIN,
                     uint64_t mlat_48mhz_64bit_counts = 0);
    RawUATADSBPacket(uint8_t rx_buffer[kADSBMessageMaxSizeBytes], uint16_t rx_buffer_len_bytes,
                     int16_t sigs_dbm_in = INT16_MIN, int16_t sigq_bits_in = INT16_MIN,
                     uint64_t mlat_48mhz_64bit_counts = 0);

    /**
     * Default constructor.
     */
    RawUATADSBPacket() {}

    uint8_t encoded_message[kADSBMessageMaxSizeBytes] = {0};
    uint16_t encoded_message_len_bits = 0;

    int16_t sigs_dbm = INT16_MIN;          // Signal strength, in dBm.
    int16_t sigq_bits = INT16_MIN;         // Signal quality (num bits corrected by FEC, 0 = best).
    uint64_t mlat_48mhz_64bit_counts = 0;  // High resolution MLAT counter.
};

class DecodedUATADSBPacket {
   public:
    static const uint16_t kMaxPacketSizeBytes = RawUATADSBPacket::kADSBMessageMaxSizeBytes;
    static const uint16_t kMaxPacketLenBits = 420;  // 420 bits = 52.5 bytes, round up to 53 bytes.
    static const uint16_t kDebugStrLen = 200;

    // Some data blocks are at the same offset in UAT ADS-B messages when they are present, regardless of MDB type code.
    // These offsets are defined here for convenience. Note that some other message data block members have different
    // offsets depending on the MDB type code, so they are not defined here.
    static const uint16_t kHeaderOffsetBytes = 0;
    static const uint16_t kStateVectorOffsetBytes = 4;
    static const uint16_t kModeStatusOffsetBytes = 17;
    static const uint16_t kAuxiliaryStateVectorOffsetBytes = 29;

    static constexpr float kDegPerAWBTick = 360.0f / 16777216.0f;  // 360 degrees / 2^24, for lat/lon

    enum UATADSBMessageFormat : uint8_t {
        kUATADSBMessageFormatInvalid = 0,
        kUATADSBMessageFormatShort = 1,
        kUATADSBMessageFormatLong = 2
    };

    /**
     * Data Block Fields
     */
    static inline int32_t AltitudeEncodedToAltitudeFt(uint16_t altitude_encoded) {
        if (altitude_encoded == 0) {
            return INT32_MIN;  // Invalid altitude.
        } else if (altitude_encoded == 4095) {
            return INT32_MAX;  // Maximum altitude (greater than 101,350 ft).
        }
        return 25 * (altitude_encoded - 1) - 1000;  // Convert to feet.
    };

    /**
     * Decode North horizontal velocity in kts from the horizontal velocity field in the state vector. Helper function
     * used by HorizontalVelocityToTrackAndSpeedKts when the aircraft is not on the ground.
     * @param[in] horizontal_velocity Horizontal velocity in the state vector, in kts.
     * @param[in] air_ground_state Air-ground state from the UAT state vector.
     * @return North velocity in kts, or INT32_MIN if N/S velocity is not available.
     */
    static inline int32_t HorizontalVelocityToNorthVelocityKts(uint32_t horizontal_velocity,
                                                               ADSBTypes::AirGroundState air_ground_state) {
        uint32_t data = horizontal_velocity >> 11;
        uint32_t north_velocity = data & 0x3FF;  // Get the 10-bit north velocity.
        if (north_velocity <= 0) {
            return INT32_MIN;  // N/S velocity not available.
        }
        uint32_t multiplier = ADSBTypes::AirGroundStateIsSupersonic(air_ground_state) ? 4 : 1;
        // Sign bit 1 is north, 0 is south.
        return (north_velocity - 1) * ((data & (1 << 10)) == 0 ? 1 : -1) * multiplier;
    }

    /**
     * Decode East horizontal velocity in kts from the horizontal velocity field in the state vector. Helper function
     * used by HorizontalVelocityToTrackAndSpeedKts when the aircraft is not on the ground.
     * @param[in] horizontal_velocity Horizontal velocity in the state vector, in kts.
     * @param[in] air_ground_state Air-ground state from the UAT state vector.
     * @return East velocity in kts, or INT32_MIN if E/W velocity is not available.
     */
    static inline int32_t HorizontalVelocityToEastVelocityKts(uint32_t horizontal_velocity,
                                                              ADSBTypes::AirGroundState air_ground_state) {
        uint32_t data = horizontal_velocity & 0x7FF;  // Get the 11-bit east/west velocity.
        uint32_t east_velocity = data & 0x3FF;        // Get the 10-bit east velocity.
        if (east_velocity <= 0) {
            return INT32_MIN;  // E/W velocity not available.
        }
        uint32_t multiplier = ADSBTypes::AirGroundStateIsSupersonic(air_ground_state) ? 4 : 1;
        // Sign bit 1 is east, 0 is west.
        return (east_velocity - 1) * ((data & (1 << 10)) == 0 ? 1 : -1) * multiplier;
    }

    /**
     * Calculates the aircraft track from north/east velocity contained in the horizontal_velocity and air_ground_state
     * fields. If horizontal velocity info is not available, track is set to 0.0f, speed is set to INT32_MIN, and
     * returned direction is set to kDirectionTypeNotAvailable.
     * @param[in] horizontal_velocity Horizontal velocity in the state vector, in kts.
     * @param[in] air_ground_state Air-ground state from the UAT state vector.
     * @param[out] direction_deg_ref Output parameter for the calculated direction in degrees.
     * @param[out] speed_kts_ref Output parameter for the calculated speed in kts.
     * @retval DirectionType indicating the type of direction calculated.
     */
    static ADSBTypes::DirectionType HorizontalVelocityToDirectionDegAndSpeedKts(
        uint32_t horizontal_velocity, ADSBTypes::AirGroundState air_ground_state, float &direction_deg_ref,
        int32_t &speed_kts_ref);

    /**
     * Decodes the vertical velocity field from a UAT ADS-B packet. Uses an AirGroundState to determine whether the
     * field can be interpreted as a vertical velocity. Returns the vertical rate source used to measure the vertcial
     * velcoity if it was decoded successfully, or returns kVerticalRateSourceNotAvailable while setting the vertical
     * rate to INT32_MIN otherwise.
     * @param[in] vertical_velocity Encoded vertical velocity field.
     * @param[in] air_ground_state AirGroundState used to interpret the vertical velcoity field.
     * @param[out] vertical_rate_fpm_ref Reference that gets set to the decoded vertical rate.
     * @retval The source the vertical rate is from, or kVerticalRateSourceNotAvailable if decoding was unsuccessful.
     */
    static ADSBTypes::VerticalRateSource VerticalVelocityToVerticalRateFpm(uint32_t vertical_velocity,
                                                                           ADSBTypes::AirGroundState air_ground_state,
                                                                           int32_t &vertical_rate_fpm_ref);

    /**
     * Decodes either the Aircraft / Vehicle length and width or GNSS sensor position offset from the Aircraft/Vehicle
     * field that is transmitted in place of vertical rate while the aircraft is on the ground.
     * @param[in] av_dimensions_encoded Encoded Aircraft/Vehicle field.
     * @param[out] width_m_ref Reference that gets set to the decoded width.
     * @param[out] length_m_ref Reference that gets set to the decoded length.
     * @retval AVDimensionsType that indicates whether the decoded dimensions were AV size or AV GNSS sensor offset
     * position.
     */
    static ADSBTypes::AVDimensionsType DecodeAVDimensions(uint32_t av_dimensions_encoded, int16_t &width_m_ref,
                                                          int16_t &length_m_ref);

    struct __attribute__((packed)) UATHeader {
        uint8_t mdb_type_code     : 5;  // Message Data Block (MDB) type code.
        uint8_t address_qualifier : 3;
        uint32_t icao_address     : 24;  // ICAO address of the aircraft.
    };

    struct __attribute__((packed)) UATStateVector {
        uint32_t latitude_awb                      : 23;
        uint32_t longitude_awb                     : 24;
        bool altitude_is_geometric_altitude        : 1;
        uint16_t altitude_encoded                  : 12;
        uint8_t nic                                : 4;
        ADSBTypes::AirGroundState air_ground_state : 2;
        uint8_t reserved                           : 1;
        uint32_t horizontal_velocity               : 22;
        union {
            uint16_t vertical_velocity          : 11;
            uint16_t aircraft_length_width_code : 11;
        };
        bool utc_coupled_or_tis_b_site_id : 5;  // True if UTC is coupled, false if not.
    };

    struct __attribute__((packed)) UATModeStatus {
        uint16_t
            emitter_category_and_callsign_chars_1_2 : 16;  // Emitter category and first two characters of callsign.
        uint16_t callsign_chars_3_4_5               : 16;  // Next three characters of callsign.
        uint16_t callsign_chars_6_7_8               : 16;  // Last three characters of callsign.
        uint8_t emergency_priority_status           : 3;   // Emergency / priority status.
        uint8_t uat_version                         : 3;   // UAT protocol version.
        uint8_t sil                                 : 2;   // Source Integrity Level (SIL).
        uint8_t transmit_mso                        : 6;
        uint8_t reserved1                           : 2;  // Reserved bits.
        uint8_t nac_p                               : 4;  // Navigation Accuracy Category Position (NACp).
        uint8_t nac_v                               : 3;  // Navigation Accuracy Category Velocity (NACv).
        uint8_t nic_baro                    : 1;  // Navigation Integrity Category Barometric Altitude (NICbaro).
        uint8_t capability_codes            : 2;  // Capability codes.
        uint8_t operational_modes           : 3;  // Operational modes.
        uint8_t heading_uses_magnetic_north : 1;  // True if heading uses magnetic north, false if true north.
        uint8_t csid      : 1;  // 1 if callsign can be interpreted as usual. 0 for alternate national use.
        uint8_t reserved2 : 8;
    };

    struct __attribute__((packed)) UATAuxiliaryStateVector {
        uint16_t secondary_altitude_encoded : 12;
        uint32_t reserved                   : 28;
    };

    struct __attribute__((packed)) UATTargetState {
        uint16_t target_heading_or_track_angle_info : 15;
        uint32_t target_altitude_info               : 17;
    };

    struct __attribute__((packed)) UATTrajectoryChange {
        uint32_t reserved;  // Currently set to all 0's by transponders for 2005 version of tech manual.
    };

    DecodedUATADSBPacket(const RawUATADSBPacket &packet_in);
    DecodedUATADSBPacket() : raw_((char *)"") { debug_string[0] = '\0'; }
    DecodedUATADSBPacket(const char *rx_string, int32_t sigs_dbm = INT32_MIN, int32_t sigq_bits = INT32_MIN,
                         uint64_t mlat_48mhz_64bit_counts = 0);

    /**
     * Decoding functions for message data blocks.
     */
    static void DecodeHeader(uint8_t *data, UATHeader &header_ref);
    static void DecodeStateVector(uint8_t *data, UATStateVector &state_vector_ref);
    static void DecodeModeStatus(uint8_t *data, UATModeStatus &mode_status_ref);
    static void DecodeAuxiliaryStateVector(uint8_t *data, UATAuxiliaryStateVector &aux_state_vector_ref);
    static void DecodeTargetState(uint8_t *data, UATTargetState &target_state_ref);

    /**
     * Returns true if the packet is valid (FEC decoded successfully and packet has a recognized format).
     * @return True if the packet is valid, false otherwise.
     */
    inline bool IsValid() const { return is_valid_; }

    /**
     * Function used for testing, when we want to populate the payload but not the FEC parity bytes.
     * @retval True if the valid was ingested successfully, false otherwise.
     */
    inline bool ReconstructWithoutFEC() {
        ConstructUATPacket(false);  // Re-run packet digestion without FEC correction.
        return is_valid_;
    }

    int GetBufferLenBits() const { return raw_.encoded_message_len_bits; }
    RawUATADSBPacket GetRaw() const { return raw_; }
    RawUATADSBPacket *GetRawPtr() { return &raw_; }

    /**
     * Returns the ICAO address of the aircraft if the packet is valid and has a header, otherwise returns 0.
     */
    uint32_t GetICAOAddress() const;

    UATADSBMessageFormat message_format = kUATADSBMessageFormatInvalid;
    // Oversize the payload field since we copy the encoded message to it and correct / decode in place.
    uint8_t decoded_payload[RawUATADSBPacket::kLongADSBMessageNumBytes] = {0};

    // Always has header.
    bool has_state_vector = false;            // True if the packet has a state vector.
    bool has_mode_status = false;             // True if the packet has a mode status.
    bool has_auxiliary_state_vector = false;  // True if the packet has an auxiliary
    bool has_target_state = false;            // True if the packet has a target state.
    bool has_trajectory_change = false;       // True if the packet has a trajectory change

    UATHeader header = {0};                                // Pointer to the UAT header.
    UATStateVector state_vector = {0};                     // Pointer to the UAT state vector.
    UATModeStatus mode_status = {0};                       // Pointer to the UAT mode status.
    UATAuxiliaryStateVector auxiliary_state_vector = {0};  // Pointer to the UAT auxiliary state vector.
    UATTargetState target_state = {0};                     // Pointer to the UAT target state.
    UATTrajectoryChange trajectory_change = {0};           // Pointer to the UAT trajectory change.

    char debug_string[kDebugStrLen] = "";

   protected:
    bool is_valid_ = false;
    RawUATADSBPacket raw_;

   private:
    /**
     * Helper function that consolidates constructor implementation for the various constructors.
     * @param[in] run_fec If true, runs Reed-Solomon FEC decoding on the received message. If false, does not run FEC.
     *                    Used for testing purposes when we want to populate the payload but not the FEC parity bytes.
     *                    Defaults to true (set run_fec to false to skip FEC decoding).
     */
    void ConstructUATPacket(bool run_fec = true);
};

class RawUATUplinkPacket {
   public:
    static const uint64_t kSyncWord = 0b0001'01010011'00100010'01011011'00011101;  // 0x153225B1D

    // Split the 36-bit sync word into 32 most-significant bits (used as the Sync word by the MCU), and 4
    // least-significant bits that get ingested as the first Byte of the message, used to discriminate between uplink
    // and ADS-B packets.
    static const uint32_t kSyncWordMS32 = (kSyncWord >> 4) & 0xFFFFFFFF;
    static const uint8_t kSyncWordLS4 = kSyncWord & 0xF;

    static const uint16_t kUplinkMessageNumBlocks = 6;
    static const uint16_t kUplinkMessageBlockPayloadNumBytes = 72;
    static const uint16_t kUplinkMessageBlockFECParityNumBytes = 20;
    static const uint16_t kUplinkMessageBlockNumBytes =
        kUplinkMessageBlockPayloadNumBytes + kUplinkMessageBlockFECParityNumBytes;

    static const uint16_t kUplinkMessagePayloadNumBytes = kUplinkMessageNumBlocks * kUplinkMessageBlockPayloadNumBytes;

    static const uint16_t kUplinkMessageLenBytes =
        kUplinkMessageNumBlocks * kUplinkMessageBlockNumBytes;  // Maximum size of a UAT uplink message.

    struct __attribute__((packed)) UATUplinkDataBlock {
        uint32_t ground_station_latitude_awb  : 23;  // Ground station latitude in AWB format.
        uint32_t ground_station_longitude_awb : 24;  // Ground station longitude in AWB format.
        bool pos_valid                        : 1;   // Position validity flag.
        bool utc_coupled                      : 1;
        bool reserved1                        : 1;
        bool app_data_valid                   : 1;
        uint8_t slot_id                       : 5;
        uint8_t tis_b_site_id                 : 4;
        uint8_t reserved2                     : 4;
        // Subsequent Bytes are application data.
    };
};