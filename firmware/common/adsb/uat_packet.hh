#pragma once

#include <cstdint>

#include "unit_conversions.hh"

class RawUATPacket {
   public:
    static const uint16_t kSyncNumBits = 36;
    static const uint16_t kSyncNumBytes = kSyncNumBits / kBitsPerByte;
    static const uint16_t kShortPayloadNumBits = 144;
    static const uint16_t kShortPayloadNumBytes = kShortPayloadNumBits / kBitsPerByte;
    static const uint16_t kLongPayloadNumBits = 272;
    static const uint16_t kLongPayloadNumBytes = kLongPayloadNumBits / kBitsPerByte;
    static const uint16_t kMaxPayloadSizeBytes = kLongPayloadNumBytes;  // For convenience.
    static const uint16_t kShortFECParityNumBits = 96;
    static const uint16_t kLongFECParityNumBits = 112;

    RawUATPacket(const char *rx_string, int16_t source_in = -1, int16_t sigs_dbm_in = INT16_MIN,
                 int16_t sigq_db_in = INT16_MIN, uint64_t mlat_48mhz_64bit_counts = 0);
    RawUATPacket(uint8_t rx_buffer[kMaxPayloadSizeBytes], uint16_t rx_buffer_len_bytes, int16_t source_in = -1,
                 int16_t sigs_dbm_in = INT16_MIN, int16_t sigq_db_in = INT16_MIN, uint64_t mlat_48mhz_64bit_counts = 0);

    /**
     * Default constructor.
     */
    RawUATPacket() {}

    uint8_t buffer[kMaxPayloadSizeBytes] = {0};
    uint16_t buffer_len_bits = 0;
    int8_t source = -1;                    // Source of the ADS-B packet (PIO state machine number).
    int16_t sigs_dbm = INT16_MIN;          // Signal strength, in dBm.
    int16_t sigq_db = INT16_MIN;           // Signal quality (dB above noise floor), in dB.
    uint64_t mlat_48mhz_64bit_counts = 0;  // High resolution MLAT counter.
};

class DecodedUATPacket {
   public:
    static const uint16_t kMaxPacketSizeBytes = RawUATPacket::kMaxPayloadSizeBytes;
    static const uint16_t kMaxPacketLenBits = 420;  // 420 bits = 52.5 bytes, round up to 53 bytes.
    static const uint16_t kDebugStrLen = 200;

    DecodedUATPacket(const RawUATPacket &packet_in);
    DecodedUATPacket() : raw_((char *)"") { debug_string[0] = '\0'; }
    DecodedUATPacket(const char *rx_string, int16_t source = -1, int32_t sigs_dbm = INT32_MIN,
                     int32_t sigq_db = INT32_MIN, uint64_t mlat_48mhz_64bit_counts = 0);

    bool IsValid() const { return is_valid_; }

    int GetBufferLenBits() const { return raw_.buffer_len_bits; }
    RawUATPacket GetRaw() const { return raw_; }
    RawUATPacket *GetRawPtr() { return &raw_; }

    static inline int32_t AltitudeEncodedToAltitudeFt(uint16_t altitude_encoded) {
        if (altitude_encoded == 0) {
            return INT32_MIN;  // Invalid altitude.
        } else if (altitude_encoded == 4095) {
            return INT32_MAX;  // Maximum altitude (greater than 101,350 ft).
        }
        return 25 * (altitude_encoded - 1) - 1000;  // Convert to feet.
    };

    enum AddressQualifier : uint8_t {
        kADSBTargetWithICAO24BitAddress = 0,
        kADSBTargetWithSelfAssignedTemporaryAddress = 1,
        kTISBTargetWithICAO24BitAddress = 2,
        kTISBTargetWithTrackFileIdentifier = 3,
        kSurfaceVehicle = 4,
        kFixedADSBBeacon = 5
    };

    enum NICRadiusOfContainment : uint8_t {
        kROCUnknown = 0,
        kROCLessThan20NauticalMiles = 1,
        kROCLessThan8NauticalMiles = 2,
        kROCLessThan4NauticalMiles = 3,
        kROCLessThan2NauticalMiles = 4,
        kROCLessThan1NauticalMile = 5,
        kROCLessThan0p6NauticalMiles = 6,  // Lump together with <0.5NM and <0.3NM since they share a NIC value.
        kROCLessThan0p2NauticalMiles = 7,
        kROCLessThan0p1NauticalMiles = 8,
        kROCLessThan75Meters = 9,
        kROCLessThan25Meters = 10,
        kROCLessThan7p5Meters = 11
    };

    enum AirGroundState : uint8_t {
        kAirGroundStateAirborneSubsonic = 0,
        kAirGroundStateAirborneSupersonic = 1,
        kAirGroundStateOnGround = 2,
        kAirGroundStateTISBUplink = 3
    };

    struct __attribute__((packed)) UATHeader {
        uint8_t type_code                  : 5;
        AddressQualifier address_qualifier : 3;
    };

    struct __attribute__((packed)) UATStateVector {
        uint32_t latitute_wgs84                              : 23;
        uint32_t longitude_wgs84                             : 24;
        bool altitude_is_geometric_altitude                  : 1;
        uint16_t altitude_encoded                            : 12;
        NICRadiusOfContainment navigation_integrity_category : 4;
        AirGroundState air_ground_state                      : 2;
        uint8_t reserved                                     : 1;
        uint32_t horizontal_velocity                         : 20;
        union {
            uint16_t vertical_velocity          : 11;
            uint16_t aircraft_length_width_code : 11;
        };
    };

    char debug_string[kDebugStrLen] = "";

   protected:
    bool is_valid_ = false;
    RawUATPacket raw_;

   private:
    void ConstructUATPacket();
};