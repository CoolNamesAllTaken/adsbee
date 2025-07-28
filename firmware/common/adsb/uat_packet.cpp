#include "uat_packet.hh"

#include <cstring>  // for strlen

#include "rs.hpp"

#define CHAR_TO_HEX(c) ((c >= 'A') ? (c >= 'a') ? (c - 'a' + 10) : (c - 'A' + 10) : (c - '0'))

RawUATPacket::RawUATPacket(const char *rx_string, int16_t source_in, int16_t sigs_dbm_in, int16_t sigq_db_in,
                           uint64_t mlat_48mhz_64bit_counts_in)
    : source(source_in),
      sigs_dbm(sigs_dbm_in),
      sigq_db(sigq_db_in),
      mlat_48mhz_64bit_counts(mlat_48mhz_64bit_counts_in) {
    uint16_t rx_num_bytes = strlen(rx_string) / kNibblesPerByte;
    for (uint16_t i = 0; i < rx_num_bytes && i < kMaxPayloadSizeBytes * kBytesPerWord; i++) {
        uint8_t byte = (CHAR_TO_HEX(rx_string[i * kNibblesPerByte]) << kBitsPerNibble) |
                       CHAR_TO_HEX(rx_string[i * kNibblesPerByte + 1]);
        buffer[i] = byte;
        buffer_len_bits += kBitsPerByte;
    }
}

DecodedUATPacket::DecodedUATPacket(const char *rx_string, int16_t source, int32_t sigs_dbm, int32_t sigq_db,
                                   uint64_t mlat_48mhz_64bit_counts)
    : raw_(rx_string, source, sigs_dbm, sigq_db, mlat_48mhz_64bit_counts) {
    // Validate the packet.
    ConstructUATPacket();
}

void DecodedUATPacket::ConstructUATPacket() {
    // Check if the packet is valid by validating the Reed-Solomon code.
}