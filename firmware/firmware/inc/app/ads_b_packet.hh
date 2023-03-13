#ifndef _ADS_B_PACKET_HH_
#define _ADS_B_PACKET_HH_

#include <cstdint>

// Useful resource: https://mode-s.org/decode/content/ads-b/1-basics.html

class ADSBPacket {
public:
    static const uint16_t kMaxPacketLenWords32 = 4;
    static const uint16_t kMaxDFStrLen = 50;
    static const uint16_t kMaxTCStrLen = 50;

    ADSBPacket(uint32_t rx_buffer[kMaxPacketLenWords32], uint16_t rx_buffer_len);

    // Bits 1-5: Downlink Format (DF)
    typedef enum {
        DF_INVALID = 0,
        DF_ES_TRANSPONDER = 17,
        DF_NON_TRANSPONDER = 18
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

    bool IsValid();
    uint16_t GetDownlinkFormat();
    uint16_t GetCapability();
    uint32_t GetICAOAddress();
    uint16_t GetTypeCode();

    uint16_t GetDownlinkFormatString(char str_buf[kMaxDFStrLen]);
    uint16_t GetTypeCodeString(char str_buf[kMaxTCStrLen]);
    
    uint16_t DumpPacketBuffer(uint32_t to_buffer[kMaxPacketLenWords32]);

    // Exposed for testing only.
    uint32_t Get24BitWordFromBuffer(uint16_t first_bit_index, uint32_t buffer[]);
    uint32_t Get24BitWordFromPacketBuffer(uint16_t first_bit_index) {return Get24BitWordFromBuffer(first_bit_index, packet_buffer_);};
    uint32_t CalculateCRC24();

private:

    bool is_valid_ = false;
    uint32_t packet_buffer_[kMaxPacketLenWords32];
    uint16_t packet_buffer_len_bits_ = 0;

    uint16_t downlink_format_ = static_cast<uint16_t>(DF_INVALID);
    uint16_t capability_ = 0;
    uint32_t icao_address_ = 0;

    uint16_t typecode_ = static_cast<uint16_t>(TC_INVALID);
    uint32_t parity_interrogator_id = 0;

};

#endif /* _ADS_B_PACKET_HH_ */