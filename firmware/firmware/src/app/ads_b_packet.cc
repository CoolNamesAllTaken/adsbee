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
#define BITS_PER_BYTE 8

#define MASK_MSBIT_WORD24 (0b1<<(BITS_PER_WORD_24-1))
#define MASK_WORD24 0xFFFFFF

const uint32_t kLastWordExtraBitIngestionMask = 0xFFFF0000;
const uint16_t kExtendedSquitterPacketNumWords32 = 4; // 112 bits = 3.5 words, round up to 4.
const uint16_t kExtendedSquitterPacketNumBits = 112;

const uint32_t kCRC24Generator = 0x1FFF409;
const uint32_t kCRC24WordNumBits = 25;

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
            // Last word in packet. Check for extra bit ingestion!
            if (rx_buffer[i] & kLastWordExtraBitIngestionMask) {
                packet_buffer_[i] = rx_buffer[i]>>1; // get rid of extra last bit
            } else {
                packet_buffer_[i] = rx_buffer[i];
            }
            packet_buffer_[i] <<= 16; // left-align last word
            packet_buffer_len_bits_ += 16;
            printf("made it to last word: 0x%x -> 0x%x\r\n", rx_buffer[i], packet_buffer_[i]);
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

    is_valid_ = true;
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
    // CRC calculation algorithm from https://mode-s.org/decode/book-the_1090mhz_riddle-junzi_sun.pdf pg. 93.
    // Must be called on buffer that does not have extra bit ingested at end and has all words left-aligned.
    // Buffer used for CRC will be 1 bit longer than the regular message (parity bits are removed, then original
    // message is padded by length of CRC generator, which is 25 bits). 1 extra word is overkill but why not.
    uint32_t crc_buffer[kMaxPacketLenWords32+1];
    for (uint16_t i = 0; i < kMaxPacketLenWords32; i++) {
        crc_buffer[i] = packet_buffer_[i];
    }
    // DumpPacketBuffer(crc_buffer); // copy to new buffer to calculate CRC-24
    uint32_t remainder = get_n_bit_word_from_buffer(24, 0, packet_buffer_); // Calculate CRC with 
    for (uint16_t i = 0; i < kExtendedSquitterPacketNumBits-BITS_PER_WORD_24; i++) {
        printf("i = %d, remainder = 0x%x\r\n", i, remainder);
        print_binary_32(remainder);
        if (remainder & MASK_MSBIT_WORD24) {
            print_binary_32(kCRC24Generator);
            // printf("\tXOR!\r\n");
            // Most significant bit is a 1. XOR with generator!
            remainder ^= kCRC24Generator;
            print_binary_32(remainder);
        }
        // Emulate shifting along the packet by removing the MSb and importing the next LSb.
        remainder = ((remainder << 1) & MASK_WORD24) | get_n_bit_word_from_buffer(1, i+BITS_PER_WORD_24, packet_buffer_);

    }
    // Do this one last time, since supposed to XOR 24-bit words starting from bit 0 to bit 88,
    // but want to avoid the shifting fakery on the last word.
    if (remainder & MASK_MSBIT_WORD24) {
        printf("\tXOR!\r\n");
        // Most significant bit is a 1. XOR with generator!
        remainder ^= kCRC24Generator;
    }
    return remainder;
}