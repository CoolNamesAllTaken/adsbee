#pragma once

#include <cstdint>

#include "fec.hh"  // For Reed-Solomon encoding/decoding.

class RawUATADSBPacket {
   public:
    static const uint16_t kSyncNumBits = 36;
    static const uint16_t kSyncNumBytes = CeilBitsToBytes(kSyncNumBits);

    RawUATADSBPacket(const char *rx_string, int16_t source_in = -1, int16_t sigs_dbm_in = INT16_MIN,
                     int16_t sigq_db_in = INT16_MIN, uint64_t mlat_48mhz_64bit_counts = 0);
    RawUATADSBPacket(uint8_t rx_buffer[UATReedSolomon::kADSBMessageMaxSizeBytes], uint16_t rx_buffer_len_bytes,
                     int16_t source_in = -1, int16_t sigs_dbm_in = INT16_MIN, int16_t sigq_db_in = INT16_MIN,
                     uint64_t mlat_48mhz_64bit_counts = 0);

    /**
     * Default constructor.
     */
    RawUATADSBPacket() {}

    uint8_t encoded_message[UATReedSolomon::kADSBMessageMaxSizeBytes] = {0};
    uint16_t encoded_message_len_bits = 0;

    int8_t source = -1;                    // Source of the ADS-B packet (PIO state machine number).
    int16_t sigs_dbm = INT16_MIN;          // Signal strength, in dBm.
    int16_t sigq_db = INT16_MIN;           // Signal quality (dB above noise floor), in dB.
    uint64_t mlat_48mhz_64bit_counts = 0;  // High resolution MLAT counter.
};

class DecodedUATADSBPacket {
   public:
    static const uint16_t kMaxPacketSizeBytes = UATReedSolomon::kADSBMessageMaxSizeBytes;
    static const uint16_t kMaxPacketLenBits = 420;  // 420 bits = 52.5 bytes, round up to 53 bytes.
    static const uint16_t kDebugStrLen = 200;

    enum UATADSBMessageFormat : uint8_t {
        kUATADSBMessageFormatInvalid = 0,
        kUATADSBMessageFormatShort = 1,
        kUATADSBMessageFormatLong = 2
    };

    DecodedUATADSBPacket(const RawUATADSBPacket &packet_in);
    DecodedUATADSBPacket() : raw_((char *)"") { debug_string[0] = '\0'; }
    DecodedUATADSBPacket(const char *rx_string, int16_t source = -1, int32_t sigs_dbm = INT32_MIN,
                         int32_t sigq_db = INT32_MIN, uint64_t mlat_48mhz_64bit_counts = 0);

    bool IsValid() const { return is_valid_; }

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

    UATADSBMessageFormat message_format = kUATADSBMessageFormatInvalid;
    // Oversize the payload field since we copy the encoded message to it and correct / decode in place.
    uint8_t decoded_payload[UATReedSolomon::kLongADSBMessageNumBytes] = {0};

    char debug_string[kDebugStrLen] = "";

   protected:
    bool is_valid_ = false;
    RawUATADSBPacket raw_;

   private:
    void ConstructUATPacket();
};

class RawUATUplinkPacket {
   public:
};