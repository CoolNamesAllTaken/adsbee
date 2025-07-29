#include "uat_packet.hh"

#include <cstring>  // for strlen

#include "rs.hpp"
#include "utils/buffer_utils.hh"  // for CHAR_TO_HEX

RawUATADSBPacket::RawUATADSBPacket(const char *rx_string, int16_t source_in, int16_t sigs_dbm_in, int16_t sigq_db_in,
                                   uint64_t mlat_48mhz_64bit_counts_in)
    : source(source_in),
      sigs_dbm(sigs_dbm_in),
      sigq_db(sigq_db_in),
      mlat_48mhz_64bit_counts(mlat_48mhz_64bit_counts_in) {
    uint16_t rx_num_bytes = strlen(rx_string) / kNibblesPerByte;
    for (uint16_t i = 0; i < rx_num_bytes && i < kADSBMessageMaxSizeBytes * kBytesPerWord; i++) {
        uint8_t byte = (CHAR_TO_HEX(rx_string[i * kNibblesPerByte]) << kBitsPerNibble) |
                       CHAR_TO_HEX(rx_string[i * kNibblesPerByte + 1]);
        encoded_message[i] = byte;
        encoded_message_len_bits += kBitsPerByte;
    }
}

DecodedUATADSBPacket::DecodedUATADSBPacket(const char *rx_string, int16_t source, int32_t sigs_dbm, int32_t sigq_db,
                                           uint64_t mlat_48mhz_64bit_counts)
    : raw_(rx_string, source, sigs_dbm, sigq_db, mlat_48mhz_64bit_counts) {
    // Validate the packet.
    ConstructUATPacket();
}

void DecodedUATADSBPacket::ConstructUATPacket() {
    // Check if the packet is valid by validating the Reed-Solomon code.
    // We don't actually know the number of bits with high certainty. First interpret as a long ADS-B message, and if
    // that doesn't work, try it as a short ADS-B message.

    if (uat_long_adsb_rs.Decode(raw_.encoded_message, decoded_payload) == 0) {
        message_format = kUATADSBMessageFormatLong;
    } else if (uat_short_adsb_rs.Decode(raw_.encoded_message, decoded_payload) == 0) {
        message_format = kUATADSBMessageFormatShort;
    } else {
        is_valid_ = false;  // Invalid packet.
        return;
    }

    // switch (raw_.encoded_message_len_bits) {
    //     case RawUATADSBPacket::kShortADSBMessageNumBits:
    //         if (uat_short_adsb_rs.Decode(raw_.encoded_message, decoded_payload) != 0) {
    //             is_valid_ = false;
    //             return;
    //         }
    //         message_format = kUATADSBMessageFormatShort;
    //         break;
    //     case RawUATADSBPacket::kLongADSBMessageNumBits:
    //         if (uat_long_adsb_rs.Decode(raw_.encoded_message, decoded_payload) != 0) {
    //             is_valid_ = false;
    //             return;
    //         }
    //         message_format = kUATADSBMessageFormatLong;
    //         break;
    //     default:
    //         is_valid_ = false;
    //         return;  // Invalid packet length.
    // }
    is_valid_ = true;
}