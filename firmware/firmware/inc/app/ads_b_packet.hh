#ifndef _ADS_B_PACKET_HH_
#define _ADS_B_PACKET_HH_

#include <cstdint>
#include "buffer_utils.hh"

// Useful resource: https://mode-s.org/decode/content/ads-b/1-basics.html

class ADSBPacket {
public:
    static const uint16_t kMaxPacketLenWords32 = 4;
    static const uint16_t kMaxDFStrLen = 50;
    static const uint16_t kMaxTCStrLen = 50;

    // Bitlengths of each field in the ADS-B frame. See Table 3.1 in The 1090MHz Riddle (Junzi Sun) pg. 35.
    static const uint16_t kDFNUmBits = 5; // [1-5] Downlink Format bitlength.
    static const uint16_t kCANumBits = 3; // [6-8] Capability bitlength.
    static const uint16_t kICAONumBits = 24; // [9-32] ICAO Address bitlength.
    static const uint16_t kMENumBits = 56; // [33-88] Extended Squitter Message bitlength.
    static const uint16_t kTCNumBits = 5; // [33-37] Type code bitlength. Not always included.
    static const uint16_t kPINumBits = 24; // Parity / Interrogator ID bitlength.

    static const uint16_t kMEFirstBitIndex = kDFNUmBits + kCANumBits + kICAONumBits;

    ADSBPacket(uint32_t rx_buffer[kMaxPacketLenWords32], uint16_t rx_buffer_len);
    ADSBPacket(char * rx_string);

    // copy constructor is implicitly generated

    // Bits 1-5: Downlink Format (DF)
    typedef enum {
        DF_INVALID = -1,
        // DF 0-11 = short messages (56 bits)
        DF_SHORT_RANGE_AIR_SURVEILLANCE = 0,
        DF_ALTITUDE_REPLY = 4,
        DF_IDENTITY_REPLY = 5,
        DF_ALL_CALL_REPLY = 11,
        // DF 16-24 = long messages (112 bits)
        DF_LONG_RANGE_AIR_SURVEILLANCE = 16,
        DF_EXTENDED_SQUITTER = 17,
        DF_EXTENDED_SQUITTER_NON_TRANSPONDER = 18,
        DF_MILITARY_EXTENDED_SQUITTER = 19,
        DF_COMM_B_ALTITUDE_REPLY = 20,
        DF_COMM_B_IDENTITY_REPLY = 21,
        DF_COMM_D_EXTENDED_LENGTH_MESSAGE = 24
        // DF 1-3, 6-10, 11-15, 22-23 not used
    } DownlinkFormat_t;
    // Bits 6-8 [3]: Capability (CA)
    // Bits 9-32 [24]: ICAO Aircraft Address (ICAO)
    // Bits 33-88 [56]: Message, Extended Squitter (ME)
    // (Bits 33-37 [5]): Type code (TC)
    typedef enum {
        TC_INVALID = 0,
        TC_AIRCRAFT_ID = 1, // 1–4	Aircraft identification
        TC_SURFACE_POSITION = 5, // 5–8	Surface position
        TC_AIRBORNE_POSITION_BARO_ALT = 9, // 9–18	Airborne position (w/Baro Altitude)
        TC_AIRBORNE_VELOCITIES = 19, // 19	Airborne velocities
        TC_AIRBORNE_POSITION_GNSS_ALT = 20, // 20–22	Airborne position (w/GNSS Height)
        TC_RESERVED = 23, // 23–27	Reserved
        TC_AIRCRAFT_STATUS = 28, // 28	Aircraft status
        TC_TARGET_STATE_AND_STATUS_INFO = 29, // 29	Target state and status information
        TC_AIRCRAFT_OPERATION_STATUS = 31 // 31	Aircraft operation status
    } TypeCode_t;
    // Bits 89-112 [24]: Parity / Interrogator ID (PI)

    bool IsValid() const;
    uint16_t GetDownlinkFormat() const;
    uint16_t GetCapability() const;
    uint32_t GetICAOAddress() const;

    uint16_t GetTypeCode() const;
    TypeCode_t GetTypeCodeEnum() const;

    uint16_t GetDownlinkFormatString(char str_buf[kMaxDFStrLen]) const;
    
    uint16_t DumpPacketBuffer(uint32_t to_buffer[kMaxPacketLenWords32]) const;

    // Exposed for testing only.

    uint32_t GetNBitWordFromMessage(uint16_t n, uint16_t first_bit_index) const {
        return get_n_bit_word_from_buffer(n, kMEFirstBitIndex + first_bit_index, packet_buffer_);
    };

    uint32_t Get24BitWordFromPacketBuffer(uint16_t first_bit_index) const {
        return get_n_bit_word_from_buffer(24, first_bit_index, packet_buffer_);
    };
    
    uint32_t CalculateCRC24() const;

private:

    bool is_valid_ = false;
    uint32_t packet_buffer_[kMaxPacketLenWords32];
    uint16_t packet_buffer_len_bits_ = 0;

    uint16_t downlink_format_ = static_cast<uint16_t>(DF_INVALID);
    uint16_t capability_ = 0;
    uint32_t icao_address_ = 0;

    uint16_t typecode_ = static_cast<uint16_t>(TC_INVALID);
    uint32_t parity_interrogator_id = 0;

    void ConstructADSBPacket();

};

// // For table of ADS-B message types, see Table 3.3 in The 1090MHz Riddle (Junzi Sun), pg. 37.
// // Typecode 1-4
// class AircraftIdentificationPacket : public ADSBPacket {
//     AircraftIdentificationPacket(ADSBPacket const& packet)
//         : ADSBPacket(packet) {};
// };

// // Typecode 5-8
// class SurfacePositionPacket : public ADSBPacket {

// };

// // Typecode 9-18, 20-22
// class AirbornePositionPacket : public ADSBPacket {

// };

// // Typecode 19
// class AirborneVelocityPacket : public ADSBPacket {

// };

// // Typecode 28
// class AircraftStatusPacket : public ADSBPacket {

// };

// Typecode 29
// Typecode 31

#endif /* _ADS_B_PACKET_HH_ */