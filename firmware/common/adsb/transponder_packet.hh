#ifndef _ADSB_PACKET_HH_
#define _ADSB_PACKET_HH_

#include <cstdint>

#include "buffer_utils.hh"
#include "unit_conversions.hh"

// Useful resource: https://mode-s.org/decode/content/ads-b/1-basics.html

class RawTransponderPacket {
   public:
    static const uint16_t kMaxPacketLenWords32 = 4;

    RawTransponderPacket(char *rx_string, int rssi_dbm = INT32_MIN, uint64_t mlat_48mhz_64bit_counts = 0);
    RawTransponderPacket(uint32_t rx_buffer[kMaxPacketLenWords32], uint16_t rx_buffer_len_words32,
                         int rssi_dbm = INT32_MIN, uint64_t mlat_48mhz_64bit_counts = 0);
    /**
     * Default constructor.
     */
    RawTransponderPacket() {
        for (uint16_t i = 0; i < kMaxPacketLenWords32; i++) {
            buffer[i] = 0;
        }
    }

    uint32_t buffer[kMaxPacketLenWords32];
    uint16_t buffer_len_bits = 0;
    int rssi_dbm = INT32_MIN;
    uint64_t mlat_48mhz_64bit_counts = 0;  // High resolution MLAT counter.
};

class DecodedTransponderPacket {
   public:
    static const uint16_t kMaxPacketLenWords32 = RawTransponderPacket::kMaxPacketLenWords32;
    static const uint16_t kDFNUmBits = 5;     // [1-5] Downlink Format bitlength.
    static const uint16_t kMaxDFStrLen = 50;  // Max length of TypeCode string.
    static const uint16_t kDebugStrLen = 200;
    static const uint16_t kSquitterPacketLenBits = 56;
    static const uint16_t kSquitterPacketNumWords32 = 2;  // 56 bits = 1.75 words, round up to 2.
    static const uint16_t kExtendedSquitterPacketLenBits = 112;
    static const uint16_t kExtendedSquitterPacketNumWords32 = 4;  // 112 bits = 3.5 words, round up to 4.

    // Bits 1-5: Downlink Format (DF)
    enum DownlinkFormat {
        kDownlinkFormatInvalid = -1,
        // DF 0-11 = short messages (56 bits)
        kDownlinkFormatShortRangeAirToAirSurveillance = 0,  // All-call request from ground station.
        kDownlinkFormatAltitudeReply = 4,
        kDownlinkFormatIdentityReply = 5,
        kDownlinkFormatAllCallReply = 11,
        // DF 16-24 = long messages (112 bits)
        kDownlinkFormatLongRangeAirToAirSurveillance = 16,   // ACAS/TCAS message.
        kDownlinkFormatExtendedSquitter = 17,                // Aircraft (taxiing or airborne).
        kDownlinkFormatExtendedSquitterNonTransponder = 18,  // Surface vehicle or aircraft in special ground operation.
        kDownlinkFormatMilitaryExtendedSquitter = 19,        // Used by military aircraft, protocol is not public.
        // We don't currently do anything with CommB, CommC, CommD.
        kDownlinkFormatCommBAltitudeReply = 20,  // Data being sent as reply to request from Comm-B ground station.
        kDownlinkFormatCommBIdentityReply = 21,  // Reply to ground station via Comm-C (higher capacity than Comm-B).
        kDownlinkFormatCommDExtendedLengthMessage = 24
        // DF 1-3, 6-10, 11-15, 22-23 not used
    };

    // Constructors
    /**
     * DecodedTransponderPacket constructor.
     * @param[in] rx_buffer Buffer to read from. Must be packed such that all 32 bits of each word are filled, with each
     * word left (MSb) aligned such that the total number of bits is 112. Words must be big-endian, with the MSb of the
     * first word being the oldest bit.
     * @param[in] rx_buffer_len_words32 Number of 32-bit words to read from the rx_buffer.
     * @param[in] rssi_dbm RSSI of the packet that was received, in dBm. Defaults to INT32_MIN if not set.
     * @param[in] mlat_48mhz_64bit_counts Counts of a 12MHz clock used for the 6-byte multilateration timestamp.
     */
    DecodedTransponderPacket(uint32_t rx_buffer[kMaxPacketLenWords32], uint16_t rx_buffer_len, int rssi_dbm = INT32_MIN,
                             uint64_t mlat_48mhz_64bit_counts = 0);

    /**
     * DecodedTransponderPacket constructor from string.
     * @param[in] rx_string String of nibbles as hex characters. Big-endian, MSB (oldest byte) first.
     * @param[in] rssi_dbm RSSI of the packet that was received, in dBm. Defaults to INT32_MIN if not set.
     * @param[in] mlat_12mhz_counts Counts of a 12MHz clock used for the 6-byte multilateration timestamp.
     */
    DecodedTransponderPacket(char *rx_string, int rssi_dbm = INT32_MIN, uint64_t mlat_48mhz_64bit_counts = 0);

    /**
     * DecodedTransponderPacket constructor from RawTransponderPacket. Uses RawTransponderPacket's implicit constructor.
     * @param[in] packet_in RawTransponderPacket to use when creating the DecodedTransponderPacket.
     */
    DecodedTransponderPacket(const RawTransponderPacket &packet_in);

    /**
     * Default constructor.
     */
    DecodedTransponderPacket() : packet((char *)"", INT32_MIN, 0) { debug_string[0] = '\0'; };

    bool IsValid() const { return is_valid_; };

    /**
     * Forces the validity of the packet to true. Used to mark 56-bit (Squitter) packets as valid after they have been
     * externally verified against the aircraft dictionary, since they don't have a 0 CRC and are thus set as invalid
     * upon construction.
     */
    void ForceValid() { is_valid_ = true; }

    int GetRSSIdBm() const { return packet.rssi_dbm; }
    uint64_t GetMLAT12MHzCounter() const { return (packet.mlat_48mhz_64bit_counts >> 2) & 0xFFFFFFFFFFFF; }
    uint16_t GetDownlinkFormat() const { return downlink_format_; };
    uint16_t GetDownlinkFormatString(char str_buf[kMaxDFStrLen]) const;
    DownlinkFormat GetDownlinkFormatEnum();
    uint32_t GetICAOAddress() const { return icao_address_; };
    uint16_t GetPacketBufferLenBits() const { return packet.buffer_len_bits; };

    /**
     * Dumps the internal packet buffer to a destination and returns the number of bytes written.
     * @param[in] to_buffer Destination buffer, must be of length kMaxPacketLenWords32 or larger.
     * @retval Number of bytes written to destination buffer.
     */
    uint16_t DumpPacketBuffer(uint32_t to_buffer[kMaxPacketLenWords32]) const;
    uint16_t DumpPacketBuffer(uint8_t to_buffer[kMaxPacketLenWords32 * kBytesPerWord]) const;

    // Exposed for testing only.
    uint32_t Get24BitWordFromPacketBuffer(uint16_t first_bit_index) const {
        return GetNBitWordFromBuffer(24, first_bit_index, packet.buffer);
    };

    /**
     * Calculates the 24-bit CRC checksum of the ADS-B packet and returns the checksum value. The returned
     * value should match the last 24-bits in the 112-bit ADS-B packet if the packet is valid.
     * @retval CRC checksum.
     */
    uint32_t CalculateCRC24(uint16_t packet_len_bits = kExtendedSquitterPacketLenBits) const;

    char debug_string[kDebugStrLen] = "";

   protected:
    bool is_valid_ = false;
    RawTransponderPacket packet;

    uint32_t icao_address_ = 0;
    uint16_t downlink_format_ = static_cast<uint16_t>(kDownlinkFormatInvalid);

    uint32_t parity_interrogator_id = 0;

   private:
    void ConstructTransponderPacket();
};

class ADSBPacket : public DecodedTransponderPacket {
   public:
    static const uint16_t kMaxTCStrLen = 50;

    // Bitlengths of each field in the ADS-B frame. See Table 3.1 in The 1090MHz Riddle (Junzi Sun) pg. 35.
    static const uint16_t kCANumBits = 3;     // [6-8] Capability bitlength.
    static const uint16_t kICAONumBits = 24;  // [9-32] ICAO Address bitlength.
    static const uint16_t kMENumBits = 56;    // [33-88] Extended Squitter Message bitlength.
    static const uint16_t kTCNumBits = 5;     // [33-37] Type code bitlength. Not always included.
    static const uint16_t kPINumBits = 24;    // Parity / Interrogator ID bitlength.

    static const uint16_t kMEFirstBitIndex = kDFNUmBits + kCANumBits + kICAONumBits;

    /**
     * Constructor. Can only create an ADSBPacket from an existing DecodedTransponderPacket, which is is referenced as
     * the parent of the ADSBPacket. Think of this as a way to use the ADSBPacket as a "window" into the contents of the
     * parent DecodedTransponderPacket. The ADSBPacket cannot exist without the parent DecodedTransponderPacket!
     */
    ADSBPacket(const DecodedTransponderPacket &decoded_packet) : DecodedTransponderPacket(decoded_packet) {
        ConstructADSBPacket();
    };

    // Bits 6-8 [3]: Capability (CA)
    // Bits 9-32 [24]: ICAO Aircraft Address (ICAO)
    // Bits 33-88 [56]: Message, Extended Squitter (ME)
    // (Bits 33-37 [5]): Type code (TC)
    enum TypeCode : uint8_t {
        kTypeCodeInvalid = 0,
        kTypeCodeAircraftID = 1,                 // 1–4     Aircraft identification
        kTypeCodeSurfacePosition = 5,            // 5–8     Surface position
        kTypeCodeAirbornePositionBaroAlt = 9,    // 9–18	Airborne position (w/Baro Altitude)
        kTypeCodeAirborneVelocities = 19,        // 19      Airborne velocities
        kTypeCodeAirbornePositionGNSSAlt = 20,   // 20–22	Airborne position (w/GNSS Height)
        kTypeCodeReserved = 23,                  // 23–27	Reserved
        kTypeCodeAircraftStatus = 28,            // 28      Aircraft status
        kTypeCodeTargetStateAndStatusInfo = 29,  // 29      Target state and status information
        kTypeCodeAircraftOperationStatus = 31    // 31      Aircraft operation status
    };
    // Bits 89-112 [24]: Parity / Interrogator ID (PI)

    // Subtype enums used for specific packet types (not instantiated as part of the ADSBPacket class).
    // Airborne Velocitites (TC = 19)
    enum AirborneVelocitiesSubtype : uint8_t {
        kAirborneVelocitiesGroundSpeedSubsonic = 1,
        kAirborneVelocitiesGroundSpeedSupersonic = 2,
        kAirborneVelocitiesAirspeedSubsonic = 3,
        kAirborneVelocitiesAirspeedSupersonic = 4
    };

    // Operation Status (TC = 31)
    enum OperationStatusSubtype : uint8_t { kOperationStatusSubtypeAirborne = 0, kOperationStatusSubtypeSurface = 1 };

    inline uint16_t GetCapability() const { return capability_; };
    inline uint16_t GetTypeCode() const { return typecode_; };
    TypeCode GetTypeCodeEnum() const;

    // Exposed for testing only.
    inline uint32_t GetNBitWordFromMessage(uint16_t n, uint16_t first_bit_index) const {
        return GetNBitWordFromBuffer(n, kMEFirstBitIndex + first_bit_index, packet.buffer);
    };

   private:
    uint16_t capability_ = 0;

    uint16_t typecode_ = static_cast<uint16_t>(kTypeCodeInvalid);

    void ConstructADSBPacket();
};

class ModeCPacket : public DecodedTransponderPacket {
   public:
    enum DownlinkRequest : uint8_t {
        kDownlinkRequestNone = 0b00000,
        kDownlinkRequestSendCommBMessage = 0b00001,
        kDownlinkRequestCommBBroadcastMessage1Available = 0b00100,
        kDownlinkRequestCommBBroadcastMessage2Available = 0b00101
    };

    enum UtilityMessageType : uint8_t {
        kUtilityMessageNoInformation = 0b00,
        kUtilityMessageCommBInterrogatorIdentifierCode = 0b10,
        kUtilityMessageCommCInterrogatorIdentifierCode = 0b10,
        kUtilityMessageCommDInterrogatorIdentifierCode = 0b11
    };

    ModeCPacket(const DecodedTransponderPacket &decoded_packet);

    bool IsAirborne() const { return is_airborne_; }
    bool HasAlert() const { return has_alert_; }
    bool HasIdent() const { return has_ident_; }
    DownlinkRequest GetDownlinkRequest() const { return downlink_request_; }
    uint8_t GetUtilityMessage() const { return utility_message_; }
    int32_t GetAltitudeFt() const { return altitude_ft_; }

   private:
    bool is_airborne_ = false;
    bool has_alert_ = false;
    bool has_ident_ = false;

    DownlinkRequest downlink_request_ = kDownlinkRequestNone;
    uint8_t utility_message_ = 0b0;
    UtilityMessageType utility_message_type_ = kUtilityMessageNoInformation;

    int32_t altitude_ft_ = -1;
};

class ModeAPacket : public DecodedTransponderPacket {
   public:
    enum DownlinkRequest : uint8_t {
        kDownlinkRequestNone = 0b00000,
        kDownlinkRequestSendCommBMessage = 0b00001,
        kDownlinkRequestCommBBroadcastMessage1Available = 0b00100,
        kDownlinkRequestCommBBroadcastMessage2Available = 0b00101
    };

    enum UtilityMessageType : uint8_t {
        kUtilityMessageNoInformation = 0b00,
        kUtilityMessageCommBInterrogatorIdentifierCode = 0b10,
        kUtilityMessageCommCInterrogatorIdentifierCode = 0b10,
        kUtilityMessageCommDInterrogatorIdentifierCode = 0b11
    };

    ModeAPacket(const DecodedTransponderPacket &decoded_packet);

    bool IsAirborne() const { return is_airborne_; }
    bool HasAlert() const { return has_alert_; }
    bool HasIdent() const { return has_ident_; }
    DownlinkRequest GetDownlinkRequest() const { return downlink_request_; }
    uint8_t GetUtilityMessage() const { return utility_message_; }
    uint16_t GetSquawk() const { return squawk_; }

   private:
    bool is_airborne_ = false;
    bool has_alert_ = false;
    bool has_ident_ = false;

    DownlinkRequest downlink_request_ = kDownlinkRequestNone;
    uint8_t utility_message_ = 0b0;
    UtilityMessageType utility_message_type_ = kUtilityMessageNoInformation;

    uint16_t squawk_ = 0xFFFF;
};

#endif /* _ADSB_PACKET_HH_ */