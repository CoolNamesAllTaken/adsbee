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

#define MASK_MSBIT_WORD24 (0b1<<(BITS_PER_WORD_24-1))
#define MASK_MSBIT_WORD25 (0b1<<BITS_PER_WORD_24)
#define MASK_WORD24 0xFFFFFF

const uint32_t kLastWordExtraBitIngestionMask = 0xFFFF0000;
const uint16_t kExtendedSquitterPacketNumWords32 = 4; // 112 bits = 3.5 words, round up to 4.
const uint16_t kExtendedSquitterPacketNumBits = 112;

const uint32_t kCRC24Generator = 0x1FFF409;
const uint16_t kCRC24GeneratorNumBits = 25;

ADSBPacket::ADSBPacket(uint32_t rx_buffer[kMaxPacketLenWords32], uint16_t rx_buffer_len_words32)
{
    if (rx_buffer_len_words32 < 4) {
        #ifdef VERBOSE
        printf("ADSBPacket::ADSBPacket: Received non-ES packet!\r\n");
        #endif 
        return; // leave is_valid_ as false.
    }
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
    if (packet_buffer_len_bits_ != kExtendedSquitterPacketNumBits) {
        #ifdef VERBOSE
        printf("ADSBPacket::ADSBPacket: Bit number mismatch while decoding packet. Expected %d but got %d!\r\n",
            kExtendedSquitterPacketNumBits,
            packet_buffer_len_bits_);
        #endif
        return; // leave is_valid_ as false.
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

bool ADSBPacket::IsValid() {
    return is_valid_;
}

uint16_t ADSBPacket::GetDownlinkFormat() {
    return downlink_format_;
}

uint16_t ADSBPacket::GetCapability() {
    return capability_;
}

uint32_t ADSBPacket::GetICAOAddress() {
    return icao_address_;
}

uint16_t ADSBPacket::GetTypeCode() {
    return typecode_;
}

/**
 * @brief Dumps the internal packet buffer to a destination and returns the number of bytes written.
 * @param[in] to_buffer Destination buffer, must be of length kMaxPacketLenWords32 or larger.
 * @retval Number of bytes written to destination buffer.
*/
uint16_t ADSBPacket::DumpPacketBuffer(uint32_t to_buffer[kMaxPacketLenWords32]) {
    uint16_t bytes_written = packet_buffer_len_bits_ / BITS_PER_BYTE;
    for (uint16_t i = 0; i < kMaxPacketLenWords32; i++) {
        to_buffer[i] = packet_buffer_[i];
    }
    return bytes_written;

}

uint32_t ADSBPacket::CalculateCRC24() {
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