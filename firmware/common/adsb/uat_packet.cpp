#include "uat_packet.hh"

#include <cstring>  // for strlen

#include "comms.hh"               // for CONSOLE_INFO, CONSOLE_ERROR
#include "utils/buffer_utils.hh"  // for CHAR_TO_HEX

RawUATADSBPacket::RawUATADSBPacket(const char *rx_string, int16_t source_in, int16_t sigs_dbm_in, int16_t sigq_db_in,
                                   uint64_t mlat_48mhz_64bit_counts_in)
    : source(source_in),
      sigs_dbm(sigs_dbm_in),
      sigq_db(sigq_db_in),
      mlat_48mhz_64bit_counts(mlat_48mhz_64bit_counts_in) {
    uint16_t rx_num_bytes = strlen(rx_string) / kNibblesPerByte;
    for (uint16_t i = 0; i < rx_num_bytes && i < RawUATADSBPacket::kADSBMessageMaxSizeBytes * kBytesPerWord; i++) {
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

    // Decoding only available on CC1312 and in non-embedded unit tests.
#if defined(ON_TI) || defined(ON_HOST)
    // Copy to the decoded_payload buffer and correct in place. If correction fails, the buffer will not be modified.
    memcpy(decoded_payload, raw_.encoded_message, RawUATADSBPacket::kADSBMessageMaxSizeBytes);
    int num_bytes_corrected = uat_rs.DecodeLongADSBMessage(decoded_payload);
    if (num_bytes_corrected >= 0) {
        CONSOLE_INFO("DecodedUATADSBPacket", "Decoded Long ADS-B message with %d bytes corrected.",
                     num_bytes_corrected);
        message_format = kUATADSBMessageFormatLong;
    } else {
        num_bytes_corrected = uat_rs.DecodeShortADSBMessage(decoded_payload);
        if (num_bytes_corrected >= 0) {
            CONSOLE_INFO("DecodedUATADSBPacket", "Decoded Short ADS-B message with %d bytes corrected.",
                         num_bytes_corrected);
            message_format = kUATADSBMessageFormatShort;
        } else {
            CONSOLE_ERROR("DecodedUATADSBPacket", "Failed to decode UAT ADS-B message, invalid packet.");
            is_valid_ = false;  // Invalid packet.
            return;
        }
    }
#endif /* ON_PICO */

    is_valid_ = true;
}