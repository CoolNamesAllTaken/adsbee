#include "transponder_packet.hh"

#include <cstdint>
#include <cstdio>   // for snprintf
#include <cstring>  // for strlen

#include "comms.hh"  // For debug prints.
#include "decode_utils.hh"

#define BYTES_PER_WORD_32 4
#define BITS_PER_WORD_32  32
#define BYTES_PER_WORD_24 3
#define BITS_PER_WORD_24  24
#define BITS_PER_WORD_25  25
#define BITS_PER_BYTE     8
#define NIBBLES_PER_BYTE  2
#define BITS_PER_NIBBLE   4

#define MASK_MSBIT_WORD24 (0b1 << (BITS_PER_WORD_24 - 1))
#define MASK_MSBIT_WORD25 (0b1 << BITS_PER_WORD_24)
#define MASK_WORD24       0xFFFFFF

#define CHAR_TO_HEX(c)    ((c >= 'A') ? (c >= 'a') ? (c - 'a' + 10) : (c - 'A' + 10) : (c - '0'))

const uint32_t kExtendedSquitterLastWordIngestionMask = 0xFFFF0000;
const uint32_t kExtendedSquitterLastWordPopCount = 16;
const uint32_t kSquitterLastWordIngestionMask = 0xFFFFFF00;
const uint32_t kSquitterLastWordPopCount = 24;

const uint32_t kCRC24Generator = 0x1FFF409;
const uint16_t kCRC24GeneratorNumBits = 25;

/** DecodedTransponderPacket **/

RawTransponderPacket::RawTransponderPacket(uint32_t rx_buffer[kMaxPacketLenWords32], uint16_t rx_buffer_len_words32,
                                           int rssi_dbm_in, uint64_t mlat_48mhz_64bit_counts_in) {
    // Set the last word indgestion behavior based on packet length.
    uint32_t last_word_ingestion_mask, last_word_popcount;
    if (rx_buffer_len_words32 > 2) {
        // 112 bit packet (Extended Squitter)
        last_word_ingestion_mask = kExtendedSquitterLastWordIngestionMask;
        last_word_popcount = kExtendedSquitterLastWordPopCount;
    } else {
        // 56 bit packet (Squitter)
        last_word_ingestion_mask = kSquitterLastWordIngestionMask;
        last_word_popcount = kSquitterLastWordPopCount;
    }

    // Pack the packet buffer.
    for (uint16_t i = 0; i < rx_buffer_len_words32 && i < kMaxPacketLenWords32; i++) {
        if (i == rx_buffer_len_words32 - 1) {
            buffer[i] = rx_buffer[i] & last_word_ingestion_mask;  // Trim any crap off of last word.
            buffer_len_bits += last_word_popcount;
        } else {
            buffer[i] = rx_buffer[i];
            buffer_len_bits += BITS_PER_WORD_32;
        }
    }
    rssi_dbm = rssi_dbm_in;
    mlat_48mhz_64bit_counts = mlat_48mhz_64bit_counts_in;
}

RawTransponderPacket::RawTransponderPacket(char *rx_string, int rssi_dbm_in, uint64_t mlat_48mhz_64bit_counts_in) {
    uint16_t rx_num_bytes = strlen(rx_string) / NIBBLES_PER_BYTE;
    for (uint16_t i = 0; i < rx_num_bytes && i < kMaxPacketLenWords32 * BYTES_PER_WORD_32; i++) {
        uint8_t byte = (CHAR_TO_HEX(rx_string[i * NIBBLES_PER_BYTE]) << BITS_PER_NIBBLE) |
                       CHAR_TO_HEX(rx_string[i * NIBBLES_PER_BYTE + 1]);
        uint16_t byte_offset = i % BYTES_PER_WORD_32;  // number of Bytes to shift right from MSB of current word
        if (byte_offset == 0) {
            buffer[i / BYTES_PER_WORD_32] = byte << (3 * BITS_PER_BYTE);  // need to clear out the word
        } else {
            buffer[i / BYTES_PER_WORD_32] |= byte << ((3 - byte_offset) * BITS_PER_BYTE);
        }
        buffer_len_bits += BITS_PER_BYTE;
    }
    rssi_dbm = rssi_dbm_in;
    mlat_48mhz_64bit_counts = mlat_48mhz_64bit_counts_in;
}

DecodedTransponderPacket::DecodedTransponderPacket(uint32_t rx_buffer[kMaxPacketLenWords32],
                                                   uint16_t rx_buffer_len_words32, int rssi_dbm,
                                                   uint64_t mlat_48mhz_64bit_counts)
    : packet(rx_buffer, rx_buffer_len_words32, rssi_dbm, mlat_48mhz_64bit_counts) {
    ConstructTransponderPacket();
}

DecodedTransponderPacket::DecodedTransponderPacket(char *rx_string, int rssi_dbm, uint64_t mlat_48mhz_64bit_counts)
    : packet(rx_string, rssi_dbm, mlat_48mhz_64bit_counts) {
    ConstructTransponderPacket();
}

DecodedTransponderPacket::DecodedTransponderPacket(const RawTransponderPacket &packet_in) : packet(packet_in) {
    ConstructTransponderPacket();
}

DecodedTransponderPacket::DownlinkFormat DecodedTransponderPacket::GetDownlinkFormatEnum() {
    switch (downlink_format_) {
        // DF 0-11 = short messages (56 bits)
        case DownlinkFormat::kDownlinkFormatShortRangeAirToAirSurveillance:
        case DownlinkFormat::kDownlinkFormatAltitudeReply:
        case DownlinkFormat::kDownlinkFormatIdentityReply:
        case DownlinkFormat::kDownlinkFormatAllCallReply:
        // DF 16-24 = long messages (112 bits)
        case DownlinkFormat::kDownlinkFormatLongRangeAirToAirSurveillance:
        case DownlinkFormat::kDownlinkFormatExtendedSquitter:
        case DownlinkFormat::kDownlinkFormatExtendedSquitterNonTransponder:
        case DownlinkFormat::kDownlinkFormatMilitaryExtendedSquitter:
        case DownlinkFormat::kDownlinkFormatCommBAltitudeReply:
        case DownlinkFormat::kDownlinkFormatCommBIdentityReply:
        case DownlinkFormat::kDownlinkFormatCommDExtendedLengthMessage:
            // DF 1-3, 6-10, 11-15, 22-23 not used
            return static_cast<DownlinkFormat>(downlink_format_);
            break;
        default:
            return DownlinkFormat::kDownlinkFormatInvalid;
    }
    // Bits 1-5: Downlink Format (DF)
    enum DownlinkFormat {
        kDownlinkFormatInvalid = -1,
        // DF 0-11 = short messages (56 bits)
        kDownlinkFormatShortRangeAirToAirSurveillance = 0,
        kDownlinkFormatAltitudeReply = 4,
        kDownlinkFormatIdentityReply = 5,
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
    };
}

uint16_t DecodedTransponderPacket::DumpPacketBuffer(uint32_t to_buffer[kMaxPacketLenWords32]) const {
    uint16_t bytes_written = packet.buffer_len_bits / BITS_PER_BYTE;
    for (uint16_t i = 0; i < kMaxPacketLenWords32; i++) {
        to_buffer[i] = packet.buffer[i];
    }
    return bytes_written;
}

uint16_t DecodedTransponderPacket::DumpPacketBuffer(uint8_t to_buffer[kMaxPacketLenWords32 * kBytesPerWord]) const {
    uint16_t bytes_written = packet.buffer_len_bits / BITS_PER_BYTE;
    for (uint16_t i = 0; i < kMaxPacketLenWords32; i++) {
        // First received bit is MSb.
        to_buffer[i * kBytesPerWord] = packet.buffer[i] >> 24;
        to_buffer[i * kBytesPerWord + 1] = (packet.buffer[i] >> 16) & 0xFF;
        to_buffer[i * kBytesPerWord + 2] = (packet.buffer[i] >> 8) & 0xFF;
        to_buffer[i * kBytesPerWord + 3] = packet.buffer[i] & 0xFF;
    }
    return bytes_written;
}

uint32_t DecodedTransponderPacket::CalculateCRC24(uint16_t packet_len_bits) const {
    // CRC calculation algorithm from https://mode-s.org/decode/book-the_1090mhz_riddle-junzi_sun.pdf pg. 91.
    // Must be called on buffer that does not have extra bit ingested at end and has all words left-aligned.
    uint32_t crc_buffer[kMaxPacketLenWords32];
    for (uint16_t i = 0; i < kMaxPacketLenWords32; i++) {
        crc_buffer[i] = packet.buffer[i];
    }

    // Overwrite 24-bit parity word with zeros.
    SetNBitWordInBuffer(BITS_PER_WORD_24, 0x0, packet_len_bits - BITS_PER_WORD_24, crc_buffer);

    // CRC is a conditional convolve operation using the 25-bit generator word.
    for (uint16_t i = 0; i < packet_len_bits - BITS_PER_WORD_24; i++) {
        uint32_t word = GetNBitWordFromBuffer(BITS_PER_WORD_25, i, crc_buffer);
        if (word & MASK_MSBIT_WORD25) {
            // Most significant bit is a 1. XOR with generator!
            SetNBitWordInBuffer(BITS_PER_WORD_25, word ^ kCRC24Generator, i, crc_buffer);
        }
    }

    return GetNBitWordFromBuffer(BITS_PER_WORD_24, packet_len_bits - BITS_PER_WORD_24, crc_buffer);
}

void DecodedTransponderPacket::ConstructTransponderPacket() {
    if (packet.buffer_len_bits != kExtendedSquitterPacketLenBits && packet.buffer_len_bits != kSquitterPacketNumBits) {
        snprintf(debug_string, kDebugStrLen,
                 "Bit number mismatch while decoding packet. Expected %d or %d but got %d!\r\n",
                 kExtendedSquitterPacketLenBits, kSquitterPacketNumBits, packet.buffer_len_bits);

        return;  // leave is_valid_ as false
    }

    downlink_format_ = packet.buffer[0] >> 27;
    uint32_t calculated_checksum = CalculateCRC24(packet.buffer_len_bits);
    uint32_t parity_value = Get24BitWordFromBuffer(packet.buffer_len_bits - BITS_PER_WORD_24, packet.buffer);

    switch (static_cast<DownlinkFormat>(downlink_format_)) {
        case kDownlinkFormatShortRangeAirToAirSurveillance:  // DF = 0
        case kDownlinkFormatAltitudeReply:                   // DF = 4
        case kDownlinkFormatIdentityReply:                   // DF = 5
        case kDownlinkFormatAllCallReply:                    // DF = 11
        {
            // Process a 56-bit message.
            is_valid_ = false;  // Calculated checksum is XORed with the ICAO address. See ADS-B Decoding Guide pg. 22.
            // ICAO address is a best guess, needs to be confirmed from the aircraft dictionary.
            icao_address_ = parity_value ^ calculated_checksum;
            break;
        }
        default:  // All other DFs. Note: DF=17-19 for ADS-B.
        {
            // Process a 112-bit message.
            icao_address_ = packet.buffer[0] & 0xFFFFFF;
            if (calculated_checksum == parity_value) {
                is_valid_ = true;  // mark packet as valid if CRC matches the parity bits
            } else {
                // is_valid_ is set to false by default
                snprintf(debug_string, kDebugStrLen, "Invalid checksum, expected %06lx but calculated %06lx.\r\n",
                         parity_value, calculated_checksum);
            }
        }
    }
}

/** ADSBPacket **/

/**
 * Helper function used by constructors.
 */
void ADSBPacket::ConstructADSBPacket() {
    capability_ = (packet.buffer[0] >> 24) & 0b111;
    typecode_ = packet.buffer[1] >> 27;
    parity_interrogator_id = packet.buffer[1] & 0xFFFFFF;
}

ADSBPacket::TypeCode ADSBPacket::GetTypeCodeEnum() const {
    // Table 3.3 from The 1090Mhz Riddle (Junzi Sun), pg. 37.
    switch (typecode_) {
        case 1:
        case 2:
        case 3:
        case 4:
            return kTypeCodeAircraftID;
            break;
        case 5:
        case 6:
        case 7:
        case 8:
            return kTypeCodeSurfacePosition;
            break;
        case 9:
        case 10:
        case 11:
        case 12:
        case 13:
        case 14:
        case 15:
        case 16:
        case 17:
        case 18:
            return kTypeCodeAirbornePositionBaroAlt;
            break;
        case 19:
            return kTypeCodeAirborneVelocities;
            break;
        case 20:
        case 21:
        case 22:
            return kTypeCodeAirbornePositionGNSSAlt;
            break;
        case 23:
        case 24:
        case 25:
        case 26:
        case 27:
            return kTypeCodeReserved;
            break;
        case 28:
            return kTypeCodeAircraftStatus;
            break;
        case 29:
            return kTypeCodeTargetStateAndStatusInfo;
            break;
        case 31:
            return kTypeCodeAircraftOperationStatus;
            break;
        default:
            return kTypeCodeInvalid;
    }
}

ModeCPacket::ModeCPacket(const DecodedTransponderPacket &decoded_packet) : DecodedTransponderPacket(decoded_packet) {
    uint8_t flight_status = GetNBitWordFromBuffer(3, 5, packet.buffer);  // FS = Bits 5-7.
    switch (flight_status) {
        case 0b000:  // No alert, no SPI, aircraft is airborne.
            has_alert_ = false;
            is_airborne_ = true;
            break;
        case 0b001:  // No alert, no SPI, aircraft is on ground.
            has_alert_ = false;
            is_airborne_ = false;
            break;
        case 0b010:  // Alert, no SPI, aircraft is airborne.
            has_alert_ = true;
            is_airborne_ = true;
            break;
        case 0b011:  // Alert, no SPI, aircraft is on ground.
            has_alert_ = true;
            is_airborne_ = false;
            break;
        case 0b100:  // Alert, SPI, aircraft is airborne or on ground.
            has_alert_ = true;
            // Default is_airborne_ to false when not known.
            break;
        case 0b101:
            // No alert, SPI, aircaft is airborne or on ground.
            has_alert_ = false;
            // Default is_airborne_ to false when not known.
            break;
        case 0b110:  // Reserved.
            break;
        case 0b111:  // Not assigned.
            break;
    }

    downlink_request_ = static_cast<DownlinkRequest>(GetNBitWordFromBuffer(5, 8, packet.buffer));
    utility_message_ = GetNBitWordFromBuffer(4, 13, packet.buffer);
    utility_message_type_ = static_cast<UtilityMessageType>(GetNBitWordFromBuffer(2, 17, packet.buffer));
    altitude_ft_ = AltitudeCodeToAltitudeFt(GetNBitWordFromBuffer(13, 19, packet.buffer));
};

ModeAPacket::ModeAPacket(const DecodedTransponderPacket &decoded_packet) : DecodedTransponderPacket(decoded_packet) {
    uint8_t flight_status = GetNBitWordFromBuffer(3, 5, packet.buffer);  // FS = Bits 5-7.
    switch (flight_status) {
        case 0b000:  // No alert, no SPI, aircraft is airborne.
            has_alert_ = false;
            has_ident_ = false;
            is_airborne_ = true;
            break;
        case 0b001:  // No alert, no SPI, aircraft is on ground.
            has_alert_ = false;
            has_ident_ = false;
            is_airborne_ = false;
            break;
        case 0b010:  // Alert, no SPI, aircraft is airborne.
            has_alert_ = true;
            has_ident_ = false;
            is_airborne_ = true;
            break;
        case 0b011:  // Alert, no SPI, aircraft is on ground.
            has_alert_ = true;
            has_ident_ = false;
            is_airborne_ = false;
            break;
        case 0b100:  // Alert, SPI, aircraft is airborne or on ground.
            has_alert_ = true;
            has_ident_ = true;
            // Default is_airborne_ to false when not known.
            break;
        case 0b101:
            // No alert, SPI, aircaft is airborne or on ground.
            has_ident_ = true;
            has_alert_ = false;
            // Default is_airborne_ to false when not known.
            break;
        case 0b110:  // Reserved.
            break;
        case 0b111:  // Not assigned.
            break;
    }

    downlink_request_ = static_cast<DownlinkRequest>(GetNBitWordFromBuffer(5, 8, packet.buffer));
    utility_message_ = GetNBitWordFromBuffer(4, 13, packet.buffer);
    utility_message_type_ = static_cast<UtilityMessageType>(GetNBitWordFromBuffer(2, 17, packet.buffer));
    squawk_ = IdentityCodeToSquawk(GetNBitWordFromBuffer(13, 19, packet.buffer));
};