#include "fec.hh"

#include "comms.hh"
#include "rs.h"  // For init_rs_char, decode_rs_char
#include "uat_packet.hh"

static const int kUplinkGaloisFieldPolynomial = 0x187;
static const int kADSBGaloisFieldPolynomial = 0x187;
static const int kSymbolSizeBits = 8;
static const int kFirstCodeRoot = 120;
static const int kPrimitive = 1;
static const int kShortADSBMessageNumRoots = 12;
static const int kShortADSBMessagePaddingBytes = 225;
static const int kLongADSBMessageNumRoots = 14;
static const int kLongADSBMessagePaddingBytes = 207;
static const int kUplinkMessageNumRoots = 20;
static const int kUplinkMessagePaddingBytes = 163;

static const int kADSBShortMessageMaxNumByteCorrections = 6;
static const int kLongADSBMessageMaxNumByteCorrections = 7;

static const int kUplinkMessageMaxNumByteCorrectionsPerBlock = 10;

UATReedSolomon uat_rs;

UATReedSolomon::UATReedSolomon() {
    rs_adsb_short = init_rs_char(kSymbolSizeBits, kADSBGaloisFieldPolynomial, kFirstCodeRoot, kPrimitive,
                                 kShortADSBMessageNumRoots, kShortADSBMessagePaddingBytes);
    rs_adsb_long = init_rs_char(kSymbolSizeBits, kADSBGaloisFieldPolynomial, kFirstCodeRoot, kPrimitive,
                                kLongADSBMessageNumRoots, kLongADSBMessagePaddingBytes);
    rs_uplink = init_rs_char(kSymbolSizeBits, kUplinkGaloisFieldPolynomial, kFirstCodeRoot, kPrimitive,
                             kUplinkMessageNumRoots, kUplinkMessagePaddingBytes);
    if (rs_adsb_short == nullptr || rs_adsb_long == nullptr || rs_uplink == nullptr) {
        CONSOLE_ERROR("UATReedSolomon", "Failed to initialize Reed-Solomon decoders.");  // Maybe out of heap.
        while (true) {
            // Spin indefinitely
        };
    }
}

int UATReedSolomon::DecodeShortADSBMessage(uint8_t message_buf[RawUATADSBPacket::kShortADSBMessageNumBytes]) {
    if (message_buf == nullptr) {
        return -1;  // Invalid input.
    }
    int num_bytes_corrected = decode_rs_char(rs_adsb_short, (unsigned char *)message_buf, nullptr, 0);
    if (num_bytes_corrected >= 0 && num_bytes_corrected <= kADSBShortMessageMaxNumByteCorrections &&
        (message_buf[0] >> 3) == 0) {
        return num_bytes_corrected;  // Return number of bits corrected.
    }
    return -1;
}

int UATReedSolomon::DecodeLongADSBMessage(uint8_t message_buf[RawUATADSBPacket::kLongADSBMessageNumBytes]) {
    if (message_buf == nullptr) {
        return -1;  // Invalid input.
    }
    int num_bytes_corrected = decode_rs_char(rs_adsb_long, (unsigned char *)message_buf, nullptr, 0);
    if (num_bytes_corrected >= 0 && num_bytes_corrected <= kLongADSBMessageMaxNumByteCorrections &&
        (message_buf[0] >> 3) != 0) {
        return num_bytes_corrected;  // Return number of bits corrected.
    }
    return -1;
}

int UATReedSolomon::DecodeUplinkMessage(
    uint8_t encoded_message_buf[RawUATUplinkPacket::kUplinkMessageMaxSizeBytes],
    uint8_t decoded_payload_buf[RawUATUplinkPacket::kUplinkMessagePayloadNumBytes +
                                RawUATUplinkPacket::kUplinkMessageBlockFECParityNumBytes]) {
    if (encoded_message_buf == nullptr) {
        return -1;  // Invalid input.
    }
    int total_bytes_corrected = 0;

    for (int block = 0; block < RawUATUplinkPacket::kUplinkMessageNumBlocks; block++) {
        uint8_t *block_data = &(decoded_payload_buf[block * RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes]);
        for (int byte_index = 0; byte_index < RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes; byte_index++) {
            // De-interleave per UAT tech manual Table 2-6.
            block_data[byte_index] =
                encoded_message_buf[byte_index * RawUATUplinkPacket::kUplinkMessageBlockNumBytes + block];
        }

        int num_bytes_corrected = decode_rs_char(rs_uplink, block_data, nullptr, 0);
        if (num_bytes_corrected < 0 || num_bytes_corrected > kUplinkMessageMaxNumByteCorrectionsPerBlock) {
            return -1;  // Invalid message.
        }

        total_bytes_corrected += num_bytes_corrected;
    }

    return total_bytes_corrected;
}