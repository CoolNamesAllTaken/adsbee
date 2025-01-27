#ifndef _BUFFER_UTILS_HH_
#define _BUFFER_UTILS_HH_

#include <cstdint>

#include "unit_conversions.hh"

void PrintBinary32(uint32_t);  // for debugging

uint32_t Get24BitWordFromBuffer(uint32_t first_bit_index, const uint32_t buffer[]);
uint32_t GetNBitWordFromBuffer(uint16_t n, uint32_t first_bit_index, const uint32_t buffer[]);
void SetNBitWordInBuffer(uint16_t n, uint32_t word, uint32_t first_bit_index, uint32_t buffer[]);

inline void ByteBufferToWordBuffer(const uint8_t byte_buffer[], uint32_t word_buffer[], uint16_t num_bytes) {
    uint16_t num_words = num_bytes / kBytesPerWord + (num_bytes % kBytesPerWord ? 1 : 0);
    for (uint16_t i = 0; i < num_words; i++) {
        uint16_t bytes_remaining = num_bytes - i * kBytesPerWord;

        word_buffer[i] = 0x0;
        word_buffer[i] |= byte_buffer[i * kBytesPerWord] << 24;
        if (--bytes_remaining == 0) break;
        word_buffer[i] |= byte_buffer[i * kBytesPerWord + 1] << 16;
        if (--bytes_remaining == 0) break;
        word_buffer[i] |= byte_buffer[i * kBytesPerWord + 2] << 8;
        if (--bytes_remaining == 0) break;
        word_buffer[i] |= byte_buffer[i * kBytesPerWord + 3];
    }
}

inline void WordBufferToByteBuffer(const uint32_t word_buffer[], uint8_t byte_buffer[], uint16_t num_bytes) {
    uint16_t num_words = num_bytes / kBytesPerWord + (num_bytes % kBytesPerWord ? 1 : 0);
    for (uint16_t i = 0; i < num_words; i++) {
        uint16_t bytes_remaining = num_bytes - i * kBytesPerWord;

        byte_buffer[i * kBytesPerWord] = word_buffer[i] >> 24;
        if (--bytes_remaining == 0) break;
        byte_buffer[i * kBytesPerWord + 1] = (word_buffer[i] >> 16) & 0xFF;
        if (--bytes_remaining == 0) break;
        byte_buffer[i * kBytesPerWord + 2] = (word_buffer[i] >> 8) & 0xFF;
        if (--bytes_remaining == 0) break;
        byte_buffer[i * kBytesPerWord + 3] = word_buffer[i] & 0xFF;
    }
}

// CRC16 is used for inter-processor communication and reporting, not for ADS-B message decode.

/**
 * Calculates the 16-bit CRC of a buffer.
 * @param[in] buf Pointer to the buffer to calculate a CRC for.
 * @param[in] buf_len_bytes Number of bytes to calculate the CRC over.
 * @retval 16-bit CRC.
 */
uint16_t CalculateCRC16(const uint8_t *buf, int32_t buf_len_bytes);

#endif /* _BUFFER_UTILS_HH_ */