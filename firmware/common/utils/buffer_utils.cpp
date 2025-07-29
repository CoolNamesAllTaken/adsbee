#include "buffer_utils.hh"

#include "comms.hh"

#define BITMASK_32_ALL   0xFFFFFFFF
#define WORD_32_NUM_BITS 32

bool ByteBufferMatchesString(const uint8_t *buffer, const char *str) {
    uint16_t len_nibbles = strlen(str);
    if (len_nibbles % kNibblesPerByte != 0) {
        return false;  // String length must be a multiple of 2.
    }
    uint16_t len_bytes = strlen(str) / kNibblesPerByte;

    for (uint16_t i = 0; i < len_bytes; i++) {
        if (buffer[i] != CHAR_TO_HEX(str[i * kNibblesPerByte]) << 4 | CHAR_TO_HEX(str[i * kNibblesPerByte + 1])) {
            return false;
        }
    }
    return true;
}

// NOTE: Buffer operations are done big-endian (oldest bits are stored in the MSB), since input buffer shifts left.

uint32_t Get24BitWordFromBuffer(uint32_t first_bit_index, const uint32_t buffer[]) {
    return GetNBitWordFromBuffer(24, first_bit_index, buffer);
}

uint32_t GetNBitWordFromBuffer(uint16_t n, uint32_t first_bit_index, const uint32_t buffer[]) {
    // NOTE: Bit 0 is the MSb in this format, since the input shift register shifts left (oldest bit is MSb).
    if (n > WORD_32_NUM_BITS || n < 1) {
        CONSOLE_ERROR(
            "GetNBitWordFromBuffer: Tried to get %d bit word from buffer, but word bitlength must be between 1 "
            "and 32.\r\n",
            n);
        return 0;
    }
    uint32_t first_word_index_32 = first_bit_index / WORD_32_NUM_BITS;
    uint16_t bit_offset_32 = first_bit_index % WORD_32_NUM_BITS;
    // Get a 32-bit word, then mask it down to n bits.
    // Grab the lower portion of the word.
    uint32_t word_n = ((buffer[first_word_index_32] << bit_offset_32));
    uint16_t first_subword_length = WORD_32_NUM_BITS - bit_offset_32;
    if (first_subword_length < n) {
        // Grab the upper portion of the word from the next 32-bit word in the buffer.
        word_n |= (buffer[first_word_index_32 + 1] >> (first_subword_length));
    }
    word_n &= BITMASK_32_ALL << (32 - n);  // mask to the upper n bits
    word_n >>= (WORD_32_NUM_BITS - n);     // right-align
    return word_n;
}

void SetNBitWordInBuffer(uint16_t n, uint32_t word, uint32_t first_bit_index, uint32_t buffer[]) {
    if (n > WORD_32_NUM_BITS || n < 1) {
        CONSOLE_ERROR(
            "SetNBitWordInBuffer: Tried to set %d-bit word in buffer, but word bitlength must be between 1 and "
            "32.\r\n",
            n);
        return;
    }

    word &= BITMASK_32_ALL >> (WORD_32_NUM_BITS - n);  // mask insertion word to n LSb's.
    word <<= (WORD_32_NUM_BITS - n);                   // left-align insertion word for easier handling.

    uint32_t first_word_index_32 = first_bit_index / WORD_32_NUM_BITS;
    uint16_t bit_offset_32 = first_bit_index % WORD_32_NUM_BITS;
    // Blank out up to n least significant bits of first word starting at bit_offset_32.
    buffer[first_word_index_32] &= ~((BITMASK_32_ALL << (WORD_32_NUM_BITS - n)) >> bit_offset_32);
    buffer[first_word_index_32] |= word >> bit_offset_32;  // insert insertion word into first word of buffer
    uint16_t first_subword_length = WORD_32_NUM_BITS - bit_offset_32;
    if (first_subword_length < n) {
        // Insertion word spills over into second word of buffer.
        // Blank n-first_subword_length most significant bits of second word.
        buffer[first_word_index_32 + 1] &= BITMASK_32_ALL >> (n - first_subword_length);
        buffer[first_word_index_32 + 1] |= word << first_subword_length;
    }
}

void PrintBinary32(uint32_t value) {
    CONSOLE_PRINTF("\t0b");
    for (int j = 31; j >= 0; j--) {
        CONSOLE_PRINTF(value & (0b1 << j) ? "1" : "0");
    }
    CONSOLE_PRINTF("\r\n");
}

/**
 * Swaps the endianness of a 16-bit value.
 * @param[in] value Value to swap the MSB and LSB of.
 * @retval Value with endianness swapped.
 */
uint16_t swap16(uint16_t value) { return (value << 8) | (value >> 8); }

uint16_t CalculateCRC16(const uint8_t *buf, int32_t buf_len_bytes) {
    uint8_t x;
    uint16_t crc = 0xFFFF;
    while (buf_len_bytes--) {
        x = crc >> 8 ^ *buf++;
        x ^= x >> 4;
        crc = (crc << 8) ^ ((uint16_t)(x << 12)) ^ ((uint16_t)(x << 5)) ^ ((uint16_t)x);
    }
    return swap16(crc);
}