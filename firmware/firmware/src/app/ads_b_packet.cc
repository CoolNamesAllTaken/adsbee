#include "ads_b_packet.hh"
#include <cstdint>
#include "string.h"

#define VERBOSE
#ifdef VERBOSE
#include "stdio.h"
#endif

#define BYTES_PER_WORD_32 4
#define BITS_PER_WORD_32 32
#define BYTES_PER_WORD_24 3
#define BITS_PER_WORD_24 24
#define BITS_PER_WORD_25 25
#define BITS_PER_BYTE 8
#define NIBBLES_PER_BYTE 2
#define BITS_PER_NIBBLE 4

#define MASK_MSBIT_WORD24 (0b1<<(BITS_PER_WORD_24-1))
#define MASK_MSBIT_WORD25 (0b1<<BITS_PER_WORD_24)
#define MASK_WORD24 0xFFFFFF

#define CHAR_TO_HEX(c) ((c >= 'A') ? (c >= 'a') ? (c - 'a' + 10) : (c - 'A' + 10) : (c - '0'))

const uint32_t kLastWordExtraBitIngestionMask = 0xFFFF0000;
const uint16_t kExtendedSquitterPacketNumWords32 = 4; // 112 bits = 3.5 words, round up to 4.
const uint16_t kExtendedSquitterPacketNumBits = 112;

const uint32_t kCRC24Generator = 0x1FFF409;
const uint16_t kCRC24GeneratorNumBits = 25;

/**
 * @brief ADSBPacket constructor.
 * @param[in] rx_buffer Buffer to read from. Must be packed such that all 32 bits of each word are filled, with the last
 * word being right-aligned such that the total number of bits is 112. Words must be big-endian, with the MSb of the first
 * word being the oldest bit.
 * @param[in] rx_buffer_len_words32 Number of 32-bit words to read from the rx_buffer.
*/
ADSBPacket::ADSBPacket(uint32_t rx_buffer[kMaxPacketLenWords32], uint16_t rx_buffer_len_words32) {
    // Pack the packet buffer.
    for (uint16_t i = 0; i < rx_buffer_len_words32 && i < kMaxPacketLenWords32; i++) {
        if (i == kMaxPacketLenWords32-1) {
            // Last word in packet.
            // Last word may have accidentally ingested a subsequent preamble as a bit (takes a while to know message is over).
            packet_buffer_[i] = rx_buffer[i] & ~kLastWordExtraBitIngestionMask; // trim any crap off of last word
            packet_buffer_[i] <<= 16; // left-align last word
            packet_buffer_len_bits_ += 16;
        } else {
            packet_buffer_[i] = rx_buffer[i];
            packet_buffer_len_bits_ += BITS_PER_WORD_32;
        }
    }

    ConstructADSBPacket();
}

ADSBPacket::ADSBPacket(char * rx_string) {
    uint16_t rx_num_bytes = strlen(rx_string) / NIBBLES_PER_BYTE;
    for (uint16_t i = 0; i < rx_num_bytes && i < kMaxPacketLenWords32*BYTES_PER_WORD_32; i++) {
        uint8_t byte = (CHAR_TO_HEX(rx_string[i*NIBBLES_PER_BYTE]) << BITS_PER_NIBBLE) | CHAR_TO_HEX(rx_string[i*NIBBLES_PER_BYTE+1]);
        uint16_t bit_offset = i % BYTES_PER_WORD_32; // number of Bytes to shift right from MSB of current word
        if (bit_offset == 0) {
            packet_buffer_[i / BYTES_PER_WORD_32] = byte << (3*BITS_PER_BYTE); // need to clear out the word
        } else {
            packet_buffer_[i / BYTES_PER_WORD_32] |= byte << ((3-bit_offset)*BITS_PER_BYTE);
        }
        packet_buffer_len_bits_ += BITS_PER_BYTE;
    }

    ConstructADSBPacket();
}

/**
 * @brief Helper function used by constructors.
*/
void ADSBPacket::ConstructADSBPacket() {
    if (packet_buffer_len_bits_ != kExtendedSquitterPacketNumBits) {
        #ifdef VERBOSE
        printf("ADSBPacket::ADSBPacket: Bit number mismatch while decoding packet. Expected %d but got %d!\r\n",
            kExtendedSquitterPacketNumBits,
            packet_buffer_len_bits_);
        #endif
        return; // leave is_valid_ as false
    }

    downlink_format_ = packet_buffer_[0] >> 27;
    capability_ = (packet_buffer_[0] >> 24) & 0b111;
    icao_address_ = packet_buffer_[0] & 0xFFFFFF;
    typecode_ = packet_buffer_[1] >> 27;
    parity_interrogator_id = packet_buffer_[1] & 0xFFFFFF;

    uint16_t calculated_checksum = CalculateCRC24();
    uint16_t parity_value = get_24_bit_word_from_buffer(kExtendedSquitterPacketNumBits - BITS_PER_WORD_24, packet_buffer_);
    if (calculated_checksum == parity_value) {
        is_valid_ = true; // mark packet as valid if CRC matches the parity bits
    } else {
        // is_valid_ is set to false by default
        #ifdef VERBOSE
        printf("ADSBPacket::ADSBPacket: Invalid checksum, expected %x but calculated %x.\r\n", parity_value, calculated_checksum);
        #endif
    }
}

bool ADSBPacket::IsValid() const {
    return is_valid_;
}

uint16_t ADSBPacket::GetDownlinkFormat() const {
    return downlink_format_;
}

uint16_t ADSBPacket::GetCapability() const {
    return capability_;
}

uint32_t ADSBPacket::GetICAOAddress() const {
    return icao_address_;
}

/**
 * @brief Returns the typecode of the aircraft that sent the packet.
 * @retval Aircraft typecode as a uint16_t.
*/
uint16_t ADSBPacket::GetTypeCode() const {
    return typecode_;
}

/**
 * @brief Returns the typecode of the aircraft that sent the ADS-B packet as an enum.
 * @retval Aircraft typecode as TypeCode_t.
*/
ADSBPacket::TypeCode_t ADSBPacket::GetTypeCodeEnum() const {
    // Table 3.3 from The 1090Mhz Riddle (Junzi Sun), pg. 37.
    switch(typecode_) {
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



/**
 * @brief Dumps the internal packet buffer to a destination and returns the number of bytes written.
 * @param[in] to_buffer Destination buffer, must be of length kMaxPacketLenWords32 or larger.
 * @retval Number of bytes written to destination buffer.
*/
uint16_t ADSBPacket::DumpPacketBuffer(uint32_t to_buffer[kMaxPacketLenWords32]) const {
    uint16_t bytes_written = packet_buffer_len_bits_ / BITS_PER_BYTE;
    for (uint16_t i = 0; i < kMaxPacketLenWords32; i++) {
        to_buffer[i] = packet_buffer_[i];
    }
    return bytes_written;

}

/**
 * @brief Calculates the 24-bit CRC checksum of the ADS-B packet and returns the checksum value. The returned
 * value should match the last 24-bits in the 112-bit ADS-B packet if the packet is valid.
 * @retval CRC checksum.
*/
uint32_t ADSBPacket::CalculateCRC24() const {
    // CRC calculation algorithm from https://mode-s.org/decode/book-the_1090mhz_riddle-junzi_sun.pdf pg. 91.
    // Must be called on buffer that does not have extra bit ingested at end and has all words left-aligned.
    uint32_t crc_buffer[kMaxPacketLenWords32];
    for (uint16_t i = 0; i < kMaxPacketLenWords32; i++) {
        crc_buffer[i] = packet_buffer_[i];
    }

    // Overwrite 24-bit parity word with zeros.
    set_n_bit_word_in_buffer(BITS_PER_WORD_24, 0x0, kExtendedSquitterPacketNumBits-BITS_PER_WORD_24, crc_buffer);

    // CRC is a conditional convolve operation using the 25-bit generator word.
    for (uint16_t i = 0; i < kExtendedSquitterPacketNumBits-BITS_PER_WORD_24; i++) {
        uint32_t word = get_n_bit_word_from_buffer(BITS_PER_WORD_25, i, crc_buffer);
        if (word & MASK_MSBIT_WORD25) {
            // Most significant bit is a 1. XOR with generator!
            set_n_bit_word_in_buffer(BITS_PER_WORD_25, word ^ kCRC24Generator, i, crc_buffer);
        }
    }

    return get_n_bit_word_from_buffer(BITS_PER_WORD_24, kExtendedSquitterPacketNumBits-BITS_PER_WORD_24, crc_buffer);
}