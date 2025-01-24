#include "crc.hh"

#include "comms.hh"
#include "crc_tables.hh"
#include "unit_conversions.hh"

uint32_t crc24(uint8_t *buffer, uint16_t buffer_len_bytes, uint32_t initial_value) {
    uint32_t crc = initial_value;
    for (uint16_t i = 0; i < buffer_len_bytes; i++) {
        uint8_t byte = buffer[i];
        crc = ((crc << 8) ^ crc24_table[((crc >> 16) ^ byte) & 0xFF]) & 0xFFFFFF;
    }
    return crc;
}

uint32_t crc24_syndrome(uint8_t *buffer, uint16_t buffer_len_bytes, uint32_t initial_value) {
    uint32_t calculated_crc = crc24(buffer, buffer_len_bytes - 3, initial_value);
    uint32_t buffer_crc =
        (buffer[buffer_len_bytes - 3] << 16) | (buffer[buffer_len_bytes - 2] << 8) | buffer[buffer_len_bytes - 1];
    return calculated_crc ^ buffer_crc;
}

int16_t crc24_find_single_bit_error(uint32_t syndrome, uint16_t message_len_bits) {
    const uint32_t *syndrome_table = nullptr;
    switch (message_len_bits) {
        case 112:
            // 112-bit Extended Squitter packets are processed as received with the 24-bit CRC at the end.
            syndrome_table = crc24_single_bit_syndrome_112;
            break;
        case 56:
            // 56-bit Squitter packets have their 24-bit CRC XOR'ed with their ICAO address. Thus the syndrome is the
            // ICAO.
            syndrome_table = crc24_single_bit_syndrome_56;
            break;
        default:
            CONSOLE_ERROR("crc24_find_single_bit_error", "Invalid message length: %d\r\n", message_len_bits);
            return -2;
    }

    for (uint16_t i = 0; i < message_len_bits; i++) {
        if (syndrome == syndrome_table[i]) {
            return i;
        }
    }
    return -1;
}

void flip_bit(uint8_t *message, uint16_t index) {
    message[index / kBitsPerByte] ^= (1 << ((kBitsPerByte - 1) - (index & (kBitsPerByte - 1))));
}