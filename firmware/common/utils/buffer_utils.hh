#ifndef _BUFFER_UTILS_HH_
#define _BUFFER_UTILS_HH_

#include <cstdint>

void print_binary_32(uint32_t); // for debugging

uint32_t get_24_bit_word_from_buffer(uint32_t first_bit_index, const uint32_t buffer[]);
uint32_t get_n_bit_word_from_buffer(uint16_t n, uint32_t first_bit_index, const uint32_t buffer[]);
void set_n_bit_word_in_buffer(uint16_t n, uint32_t word, uint32_t first_bit_index, uint32_t buffer[]);

// CRC16 is used for inter-processor communication and reporting, not for ADS-B message decode.

/**
 * Calculates the 16-bit CRC of a buffer.
 * @param[in] data_p Pointer to the buffer to calculate a CRC for.
 * @param[in] length Number fo bytes to calculate the CRC over.
 * @retval 16-bit CRC.
 */
uint16_t crc16(const uint8_t *data_p, uint32_t length)
{
    uint8_t x;
    uint16_t crc = 0xFFFF;
    while (length--)
    {
        x = crc >> 8 ^ *data_p++;
        x ^= x >> 4;
        crc = (crc << 8) ^ ((uint16_t)(x << 12)) ^ ((uint16_t)(x << 5)) ^ ((uint16_t)x);
    }
    return swap16(crc);
}

/**
 * Swaps the endianness of a 16-bit value.
 * @param[in] value Value to swap the MSB and LSB of.
 * @retval Value with endianness swapped.
 */
uint16_t swap16(uint16_t value)
{
    return (value << 8) | (value >> 8);
}

#endif /* _BUFFER_UTILS_HH_ */