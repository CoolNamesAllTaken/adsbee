#include "ads_b_packet.hh"

#include <cstdint>
#include <cstdio>   // for snprintf
#include <cstring>  // for strlen

#include "comms.hh"  // For debug prints.

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
const uint32_t kSquitterLastWordIngestionMask = 0xFFFFFF00;

const uint32_t kCRC24Generator = 0x1FFF409;
const uint16_t kCRC24GeneratorNumBits = 25;

/** TransponderPacket **/

TransponderPacket::TransponderPacket(uint32_t rx_buffer[kMaxPacketLenWords32], uint16_t rx_buffer_len_words32,
                                     int rssi_dbm) {
    // Choose the correct last word ingestion mask based on the message type.
    uint32_t last_word_ingestion_mask =
        rx_buffer_len_words32 > 2 ? kExtendedSquitterLastWordIngestionMask : kSquitterLastWordIngestionMask;

    // Pack the packet buffer.
    for (uint16_t i = 0; i < rx_buffer_len_words32 && i < kMaxPacketLenWords32; i++) {
        if (i == rx_buffer_len_words32 - 1) {
            // Last word in packet.
            // Last word may have accidentally ingested a subsequent preamble as a bit (takes a while to know message is
            // over).
            packet_buffer_[i] = rx_buffer[i] & last_word_ingestion_mask;  // trim any crap off of last word
            packet_buffer_len_bits_ += 16;
        } else {
            packet_buffer_[i] = rx_buffer[i];
            packet_buffer_len_bits_ += BITS_PER_WORD_32;
        }
    }
    rssi_dbm_ = rssi_dbm;
    ConstructTransponderPacket();
}

TransponderPacket::TransponderPacket(char* rx_string, int rssi_dbm) {
    uint16_t rx_num_bytes = strlen(rx_string) / NIBBLES_PER_BYTE;
    for (uint16_t i = 0; i < rx_num_bytes && i < kMaxPacketLenWords32 * BYTES_PER_WORD_32; i++) {
        uint8_t byte = (CHAR_TO_HEX(rx_string[i * NIBBLES_PER_BYTE]) << BITS_PER_NIBBLE) |
                       CHAR_TO_HEX(rx_string[i * NIBBLES_PER_BYTE + 1]);
        uint16_t byte_offset = i % BYTES_PER_WORD_32;  // number of Bytes to shift right from MSB of current word
        if (byte_offset == 0) {
            packet_buffer_[i / BYTES_PER_WORD_32] = byte << (3 * BITS_PER_BYTE);  // need to clear out the word
        } else {
            packet_buffer_[i / BYTES_PER_WORD_32] |= byte << ((3 - byte_offset) * BITS_PER_BYTE);
        }
        packet_buffer_len_bits_ += BITS_PER_BYTE;
    }
    rssi_dbm_ = rssi_dbm;
    ConstructTransponderPacket();
}

TransponderPacket::DownlinkFormat TransponderPacket::GetDownlinkFormatEnum() {
    switch (downlink_format_) {
        // DF 0-11 = short messages (56 bits)
        case DownlinkFormat::DF_SHORT_RANGE_AIR_SURVEILLANCE:
        case DownlinkFormat::DF_ALTITUDE_REPLY:
        case DownlinkFormat::DF_IDENTITY_REPLY:
        case DownlinkFormat::DF_ALL_CALL_REPLY:
        // DF 16-24 = long messages (112 bits)
        case DownlinkFormat::DF_LONG_RANGE_AIR_SURVEILLANCE:
        case DownlinkFormat::DF_EXTENDED_SQUITTER:
        case DownlinkFormat::DF_EXTENDED_SQUITTER_NON_TRANSPONDER:
        case DownlinkFormat::DF_MILITARY_EXTENDED_SQUITTER:
        case DownlinkFormat::DF_COMM_B_ALTITUDE_REPLY:
        case DownlinkFormat::DF_COMM_B_IDENTITY_REPLY:
        case DownlinkFormat::DF_COMM_D_EXTENDED_LENGTH_MESSAGE:
            // DF 1-3, 6-10, 11-15, 22-23 not used
            return static_cast<DownlinkFormat>(downlink_format_);
            break;
        default:
            return DownlinkFormat::DF_INVALID;
    }
    // Bits 1-5: Downlink Format (DF)
    enum DownlinkFormat {
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
    };
}

uint16_t TransponderPacket::DumpPacketBuffer(uint32_t to_buffer[kMaxPacketLenWords32]) const {
    uint16_t bytes_written = packet_buffer_len_bits_ / BITS_PER_BYTE;
    for (uint16_t i = 0; i < kMaxPacketLenWords32; i++) {
        to_buffer[i] = packet_buffer_[i];
    }
    return bytes_written;
}

uint32_t TransponderPacket::CalculateCRC24(uint16_t packet_len_bits) const {
    // CRC calculation algorithm from https://mode-s.org/decode/book-the_1090mhz_riddle-junzi_sun.pdf pg. 91.
    // Must be called on buffer that does not have extra bit ingested at end and has all words left-aligned.
    uint32_t crc_buffer[kMaxPacketLenWords32];
    for (uint16_t i = 0; i < kMaxPacketLenWords32; i++) {
        crc_buffer[i] = packet_buffer_[i];
    }

    // Overwrite 24-bit parity word with zeros.
    set_n_bit_word_in_buffer(BITS_PER_WORD_24, 0x0, packet_len_bits - BITS_PER_WORD_24, crc_buffer);

    // CRC is a conditional convolve operation using the 25-bit generator word.
    for (uint16_t i = 0; i < packet_len_bits - BITS_PER_WORD_24; i++) {
        uint32_t word = get_n_bit_word_from_buffer(BITS_PER_WORD_25, i, crc_buffer);
        if (word & MASK_MSBIT_WORD25) {
            // Most significant bit is a 1. XOR with generator!
            set_n_bit_word_in_buffer(BITS_PER_WORD_25, word ^ kCRC24Generator, i, crc_buffer);
        }
    }

    return get_n_bit_word_from_buffer(BITS_PER_WORD_24, packet_len_bits - BITS_PER_WORD_24, crc_buffer);
}

void TransponderPacket::ConstructTransponderPacket() {
    if (packet_buffer_len_bits_ != kExtendedSquitterPacketLenBits &&
        packet_buffer_len_bits_ != kSquitterPacketNumBits) {
        snprintf(debug_string, kDebugStrLen,
                 "Bit number mismatch while decoding packet. Expected %d or %d but got %d!\r\n",
                 kExtendedSquitterPacketLenBits, kSquitterPacketNumBits, packet_buffer_len_bits_);

        return;  // leave is_valid_ as false
    }

    downlink_format_ = packet_buffer_[0] >> 27;
    uint32_t calculated_checksum = CalculateCRC24(packet_buffer_len_bits_);
    uint32_t parity_value = get_24_bit_word_from_buffer(packet_buffer_len_bits_ - BITS_PER_WORD_24, packet_buffer_);

    switch (static_cast<DownlinkFormat>(downlink_format_)) {
        case DF_SHORT_RANGE_AIR_SURVEILLANCE:
        case DF_ALTITUDE_REPLY:
        case DF_IDENTITY_REPLY:
        case DF_ALL_CALL_REPLY: {
            // Process a 56-bit message.
            is_valid_ = false;  // Calculated checksum is XORed with the ICAO address. See ADS-B Decoding Guide pg. 22.
            // ICAO address is a best guess, needs to be confirmed from the aircraft dictionary.
            icao_address_ = parity_value ^ calculated_checksum;
            break;
        }
        default: {
            // Process a 112-bit message.
            if (calculated_checksum == parity_value) {
                is_valid_ = true;  // mark packet as valid if CRC matches the parity bits
                icao_address_ = packet_buffer_[0] & 0xFFFFFF;
            } else {
                // is_valid_ is set to false by default
                snprintf(debug_string, kDebugStrLen, "Invalid checksum, expected %06x but calculated %06x.\r\n",
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
    capability_ = (packet_buffer_[0] >> 24) & 0b111;
    typecode_ = packet_buffer_[1] >> 27;
    parity_interrogator_id = packet_buffer_[1] & 0xFFFFFF;
}

ADSBPacket::TypeCode ADSBPacket::GetTypeCodeEnum() const {
    // Table 3.3 from The 1090Mhz Riddle (Junzi Sun), pg. 37.
    switch (typecode_) {
        case 1:
        case 2:
        case 3:
        case 4:
            return TC_AIRCRAFT_ID;
            break;
        case 5:
        case 6:
        case 7:
        case 8:
            return TC_SURFACE_POSITION;
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
            return TC_AIRBORNE_POSITION_BARO_ALT;
            break;
        case 19:
            return TC_AIRBORNE_VELOCITIES;
            break;
        case 20:
        case 21:
        case 22:
            return TC_AIRBORNE_POSITION_GNSS_ALT;
            break;
        case 23:
        case 24:
        case 25:
        case 26:
        case 27:
            return TC_RESERVED;
            break;
        case 28:
            return TC_AIRCRAFT_STATUS;
            break;
        case 29:
            return TC_TARGET_STATE_AND_STATUS_INFO;
            break;
        case 31:
            return TC_AIRCRAFT_OPERATION_STATUS;
            break;
        default:
            return TC_INVALID;
    }
}