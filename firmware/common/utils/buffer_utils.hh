#ifndef _BUFFER_UTILS_HH_
#define _BUFFER_UTILS_HH_

#include <cstdint>

#include "unit_conversions.hh"

#define CHAR_TO_HEX(c) ((c >= 'A') ? (c >= 'a') ? (c - 'a' + 10) : (c - 'A' + 10) : (c - '0'))

/**
 * Check that the contents of a byte buffer match a string of hex characters. Must use a string of full Bytes.
 * @param[in] buffer Buffer to check.
 * @param[in] str String to check against. Must be a string of hex characters, with an even number of nibbles (full
 * Bytes).
 * @retval True if the buffer matches the string, false otherwise.
 */
bool ByteBufferMatchesString(const uint8_t *buffer, const char *str);

void PrintBinary32(uint32_t);  // for debugging

uint32_t Get24BitWordFromBuffer(uint32_t first_bit_index, const uint32_t buffer[]);

/**
 * Extract an n-bit word from a big-endian buffer of 32-bit words. Does NOT guard against falling off the end of
 * the buffer, so be careful!
 * @param[in] n Bitlength of word to extract.
 * @param[in] first_bit_index Bit index begin reading from (index of MSb of word to read). MSb of first word in buffer
 * is bit 0.
 * @param[in] buffer Buffer to read from.
 * @retval Right-aligned n-bit word that was read from the buffer.
 */
uint32_t GetNBitWordFromBuffer(uint16_t n, uint32_t first_bit_index, const uint32_t buffer[]);

/**
 * Insert an n-bit word into a big-endian buffer of 32-bit words. Does NOT guard against falling off the end of
 * the buffer, so be careful!
 * @param[in] n Bitlength of word to insert.
 * @param[in] word Word to insert. Must be right-aligned.
 * @param[in] first_bit_index Bit index where the MSb of word should be inserted. MSb of first word in buffer is bit 0.
 * @param[in] buffer Buffer to insert into.
 */
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