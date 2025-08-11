#pragma once

#include <cstdint>

#include "buffer_utils.hh"

class RawUATADSBPacket {
   public:
    static const uint16_t kSyncNumBits = 36;
    static const uint16_t kSyncNumBytes = CeilBitsToBytes(kSyncNumBits);

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

    RawUATADSBPacket(const char *rx_string, int16_t source_in = -1, int16_t sigs_dbm_in = INT16_MIN,
                     int16_t sigq_db_in = INT16_MIN, uint64_t mlat_48mhz_64bit_counts = 0);
    RawUATADSBPacket(uint8_t rx_buffer[kADSBMessageMaxSizeBytes], uint16_t rx_buffer_len_bytes, int16_t source_in = -1,
                     int16_t sigs_dbm_in = INT16_MIN, int16_t sigq_db_in = INT16_MIN,
                     uint64_t mlat_48mhz_64bit_counts = 0);

    /**
     * Default constructor.
     */
    RawUATADSBPacket() {}

    uint8_t encoded_message[kADSBMessageMaxSizeBytes] = {0};
    uint16_t encoded_message_len_bits = 0;

    int8_t source = -1;                    // Source of the ADS-B packet (PIO state machine number).
    int16_t sigs_dbm = INT16_MIN;          // Signal strength, in dBm.
    int16_t sigq_db = INT16_MIN;           // Signal quality (dB above noise floor), in dB.
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

    enum UATADSBMessageFormat : uint8_t {
        kUATADSBMessageFormatInvalid = 0,
        kUATADSBMessageFormatShort = 1,
        kUATADSBMessageFormatLong = 2
    };

    DecodedUATADSBPacket(const RawUATADSBPacket &packet_in);
    DecodedUATADSBPacket() : raw_((char *)"") { debug_string[0] = '\0'; }
    DecodedUATADSBPacket(const char *rx_string, int16_t source = -1, int32_t sigs_dbm = INT32_MIN,
                         int32_t sigq_db = INT32_MIN, uint64_t mlat_48mhz_64bit_counts = 0);

    /**
     * Returns true if the packet is valid (FEC decoded successfully and packet has a recognized format).
     * @return True if the packet is valid, false otherwise.
     */
    bool IsValid() const { return is_valid_; }

    /**
     * Function used for testing, when we want to populate the payload but not the FEC parity bytes.
     */
    void ForceValid() { is_valid_ = true; }

    int GetBufferLenBits() const { return raw_.encoded_message_len_bits; }
    RawUATADSBPacket GetRaw() const { return raw_; }
    RawUATADSBPacket *GetRawPtr() { return &raw_; }

    static inline int32_t AltitudeEncodedToAltitudeFt(uint16_t altitude_encoded) {
        if (altitude_encoded == 0) {
            return INT32_MIN;  // Invalid altitude.
        } else if (altitude_encoded == 4095) {
            return INT32_MAX;  // Maximum altitude (greater than 101,350 ft).
        }
        return 25 * (altitude_encoded - 1) - 1000;  // Convert to feet.
    };

    struct __attribute__((packed)) UATHeader {
        uint8_t mdb_type_code     : 5;  // Message Data Block (MDB) type code.
        uint8_t address_qualifier : 3;
    };

    struct __attribute__((packed)) UATStateVector {
        uint32_t latitude_awb               : 23;
        uint32_t longitude_awb              : 24;
        bool altitude_is_geometric_altitude : 1;
        uint16_t altitude_encoded           : 12;
        uint8_t nic                         : 4;
        uint8_t air_ground_state            : 2;
        uint8_t reserved                    : 1;
        uint32_t horizontal_velocity        : 20;
        union {
            uint16_t vertical_velocity          : 11;
            uint16_t aircraft_length_width_code : 11;
        };
    };

    struct __attribute__((packed)) UATModeStatus {
        uint8_t emitter_category_and_callsign_chars_1_2 : 8;  // Emitter category and first two characters of callsign.
        uint8_t callsign_chars_3_4_5                    : 8;  // Next three characters of callsign.
        uint8_t callsign_chars_6_7_8                    : 8;  // Last three characters of callsign.
        uint8_t emergency_priority_status               : 3;  // Emergency / priority status.
        uint8_t uat_version                             : 3;  // UAT protocol version.
        uint8_t sil                                     : 2;  // Source Integrity Level (SIL).
        uint8_t transmit_mso                            : 6;
        uint8_t reserved1                               : 2;  // Reserved bits.
        uint8_t nac_p                                   : 4;  // Navigation Accuracy Category Position (NACp).
        uint8_t nac_v                                   : 3;  // Navigation Accuracy Category Velocity (NACv).
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

    UATADSBMessageFormat message_format = kUATADSBMessageFormatInvalid;
    // Oversize the payload field since we copy the encoded message to it and correct / decode in place.
    uint8_t decoded_payload[RawUATADSBPacket::kLongADSBMessageNumBytes] = {0};

    char debug_string[kDebugStrLen] = "";

    // Everything is made available directly from the decoded buffer, except for items that require post-processing like
    // lat/lon.

    UATHeader *header = nullptr;                                // Pointer to the UAT header.
    UATStateVector *state_vector = nullptr;                     // Pointer to the UAT state vector.
    UATModeStatus *mode_status = nullptr;                       // Pointer to the UAT mode status.
    UATAuxiliaryStateVector *auxiliary_state_vector = nullptr;  // Pointer to the UAT auxiliary state vector.
    UATTargetState *target_state = nullptr;                     // Pointer to the UAT target state.
    UATTrajectoryChange *trajectory_change = nullptr;           // Pointer to the UAT trajectory change.

    // Latitude and logitude are decoded on the receiver side as a courtesy, since it has access to an FPU. Everything
    // else gets handled by the aircraft dictionary that is ingesting the packet.
    float latitude_deg = 0.0f;   // Latitude in degrees.
    float longitude_deg = 0.0f;  // Longitude in degrees.

   protected:
    bool is_valid_ = false;
    RawUATADSBPacket raw_;

   private:
    /**
     * Helper function that consolidates constructor implementation for the various constructors.
     */
    void ConstructUATPacket();
};

class RawUATUplinkPacket {
   public:
    /**
     * UAT uplink message parameters.
     */
    static const uint16_t kUplinkMessageNumBlocks = 6;
    static const uint16_t kUplinkMessageBlockPayloadNumBytes = 72;
    static const uint16_t kUplinkMessageBlockFECParityNumBytes = 20;
    static const uint16_t kUplinkMessageBlockNumBytes =
        kUplinkMessageBlockPayloadNumBytes + kUplinkMessageBlockFECParityNumBytes;

    static const uint16_t kUplinkMessagePayloadNumBytes = kUplinkMessageNumBlocks * kUplinkMessageBlockPayloadNumBytes;

    static const uint16_t kUplinkMessageMaxSizeBytes =
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