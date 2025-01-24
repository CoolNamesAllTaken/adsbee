#include "crc.hh"

#include "crc_tables.hh"

uint32_t crc24(uint8_t *buffer, uint16_t buffer_len_bytes, uint32_t initial_value) {
    uint32_t crc = initial_value;
    for (uint16_t i = 0; i < buffer_len_bytes; i++) {
        uint8_t byte = buffer[i];
        crc = ((crc << 8) ^ crc24_table[((crc >> 16) ^ byte) & 0xFF]) & 0xFFFFFF;
    }
    return crc;
}