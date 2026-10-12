#include "fec.hh"

#include <array>
#include <bit>
#include <cstring>  // for memcpy

#include "buffer_utils.hh"  // for PrintByteBuffer
#include "comms.hh"
#include "rs.h"  // For init_rs_char, decode_rs_char, encode_rs_char
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

namespace {

constexpr uint8_t GaloisMultiply(uint8_t a, uint8_t b) {
    uint16_t product = 0;
    for (int bit = 0; bit < kSymbolSizeBits; bit++) {
        if (b & (1 << bit)) {
            product ^= a << bit;
        }
    }
    for (int bit = 2 * kSymbolSizeBits - 2; bit >= kSymbolSizeBits; bit--) {
        if (product & (1 << bit)) {
            product ^= kUplinkGaloisFieldPolynomial << (bit - kSymbolSizeBits);
        }
    }
    return static_cast<uint8_t>(product);
}

// Row f holds f times the uplink generator polynomial without its leading term, highest power first. One row per
// received byte takes the place of the bit-serial division by the generator.
constexpr auto kUplinkRemainderTable = [] {
    // Generator polynomial, lowest power first: the product of (x + alpha^i) for the kUplinkMessageNumRoots
    // consecutive powers i of alpha = 2 that start at kFirstCodeRoot.
    std::array<uint8_t, kUplinkMessageNumRoots + 1> generator = {1};
    uint8_t root = 1;
    for (int i = 0; i < kFirstCodeRoot * kPrimitive; i++) {
        root = GaloisMultiply(root, 2);
    }
    for (int degree = 0; degree < kUplinkMessageNumRoots; degree++) {
        for (int i = degree + 1; i > 0; i--) {
            generator[i] = generator[i - 1] ^ GaloisMultiply(generator[i], root);
        }
        generator[0] = GaloisMultiply(generator[0], root);
        for (int i = 0; i < kPrimitive; i++) {
            root = GaloisMultiply(root, 2);
        }
    }

    std::array<std::array<uint32_t, kUplinkMessageNumRoots / 4>, 256> table = {};
    for (int f = 0; f < 256; f++) {
        for (int i = 0; i < kUplinkMessageNumRoots; i++) {
            uint32_t product = GaloisMultiply(static_cast<uint8_t>(f), generator[kUplinkMessageNumRoots - 1 - i]);
            table[f][i / 4] |= product << (8 * (i % 4));
        }
    }
    return table;
}();
static_assert(kUplinkMessageNumRoots % 4 == 0);
static_assert(std::endian::native == std::endian::little);

}  // namespace

UATReedSolomon uat_rs;

bool UATReedSolomon::UplinkBlockIsCodeword(const uint8_t block_buf[RawUATUplinkPacket::kUplinkMessageBlockNumBytes]) {
    // Remainder of the block divided by the generator polynomial, highest power in the low byte of word 0.
    uint32_t r0 = 0, r1 = 0, r2 = 0, r3 = 0, r4 = 0;
    static_assert(kUplinkMessageNumRoots == 20);
    for (int i = 0; i < RawUATUplinkPacket::kUplinkMessageBlockNumBytes; i++) {
        const uint32_t* row = kUplinkRemainderTable[r0 & 0xFF].data();
        r0 = ((r0 >> 8) | (r1 << 24)) ^ row[0];
        r1 = ((r1 >> 8) | (r2 << 24)) ^ row[1];
        r2 = ((r2 >> 8) | (r3 << 24)) ^ row[2];
        r3 = ((r3 >> 8) | (r4 << 24)) ^ row[3];
        r4 = ((r4 >> 8) | (static_cast<uint32_t>(block_buf[i]) << 24)) ^ row[4];
    }
    return (r0 | r1 | r2 | r3 | r4) == 0;
}

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
    // Decode a copy so a rejected frame leaves message_buf untouched for the next format attempt.
    uint8_t scratch[RawUATADSBPacket::kShortADSBMessageNumBytes];
    memcpy(scratch, message_buf, sizeof(scratch));
    int num_bytes_corrected = decode_rs_char(rs_adsb_short, scratch, nullptr, 0);
    if (num_bytes_corrected >= 0 && num_bytes_corrected <= kADSBShortMessageMaxNumByteCorrections &&
        (scratch[0] >> 3) == 0) {
        memcpy(message_buf, scratch, sizeof(scratch));
        return num_bytes_corrected;  // Return number of bytes corrected.
    }
    return -1;
}

int UATReedSolomon::DecodeLongADSBMessage(uint8_t message_buf[RawUATADSBPacket::kLongADSBMessageNumBytes]) {
    if (message_buf == nullptr) {
        return -1;  // Invalid input.
    }
    // Decode a copy so a rejected frame (e.g. payload type 0, only legal in a basic message) leaves message_buf
    // untouched for the basic-message attempt.
    uint8_t scratch[RawUATADSBPacket::kLongADSBMessageNumBytes];
    memcpy(scratch, message_buf, sizeof(scratch));
    int num_bytes_corrected = decode_rs_char(rs_adsb_long, scratch, nullptr, 0);
    if (num_bytes_corrected >= 0 && num_bytes_corrected <= kLongADSBMessageMaxNumByteCorrections &&
        (scratch[0] >> 3) != 0) {
        memcpy(message_buf, scratch, sizeof(scratch));
        return num_bytes_corrected;  // Return number of bytes corrected.
    }
    return -1;
}

int UATReedSolomon::DecodeUplinkMessage(uint8_t decoded_payload_buf[RawUATUplinkPacket::kUplinkMessagePayloadNumBytes],
                                        uint8_t encoded_message_buf[RawUATUplinkPacket::kUplinkMessageNumBytes]) {
    if (encoded_message_buf == nullptr || decoded_payload_buf == nullptr) {
        return -1;  // Invalid input.
    }
    int total_bytes_corrected = 0;

    // Each of the 6 blocks is de-interleaved into its own 92-byte scratch buffer, RS-corrected there, and the corrected
    // codeword is scattered back into encoded_message_buf. The RS decoder corrects errors at any position in the block
    // (parity symbols included) and the code is systematic, so the corrected 92-byte codeword is byte-identical to what
    // re-encoding the corrected 72-byte payload would produce -- there is no need for a separate encode pass to leave
    // the interleaved message in a corrected state.
    uint8_t block_buf[RawUATUplinkPacket::kUplinkMessageBlockNumBytes];
    for (int block = 0; block < RawUATUplinkPacket::kUplinkMessageNumBlocks; block++) {
        for (int byte_index = 0; byte_index < RawUATUplinkPacket::kUplinkMessageBlockNumBytes; byte_index++) {
            // De-interleave per UAT tech manual Table 2-6.
            block_buf[byte_index] = encoded_message_buf[byte_index * RawUATUplinkPacket::kUplinkMessageNumBlocks + block];
        }

        // A block without errors skips the decoder. Otherwise decode with 0 erasures (erasures list is nullptr), which
        // corrects block_buf in place.
        int num_bytes_corrected =
            UplinkBlockIsCodeword(block_buf) ? 0 : decode_rs_char(rs_uplink, block_buf, nullptr, 0);
        if (num_bytes_corrected < 0 || num_bytes_corrected > kUplinkMessageMaxNumByteCorrectionsPerBlock) {
            return -1;  // Invalid message. Blocks decoded so far may already have been corrected in place.
        }

        if (num_bytes_corrected > 0) {
            // Write the corrected codeword (payload + parity) back into the interleaved message so that callers hold a
            // corrected encoded message without an encode pass.
            for (int byte_index = 0; byte_index < RawUATUplinkPacket::kUplinkMessageBlockNumBytes; byte_index++) {
                encoded_message_buf[byte_index * RawUATUplinkPacket::kUplinkMessageNumBlocks + block] =
                    block_buf[byte_index];
            }
        }
        memcpy(&(decoded_payload_buf[block * RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes]), block_buf,
               RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes);

        total_bytes_corrected += num_bytes_corrected;
    }

    return total_bytes_corrected;
}

void UATReedSolomon::DeInterleaveUplinkMessage(
    uint8_t deinterleaved_buf[RawUATUplinkPacket::kUplinkMessagePayloadNumBytes],
    const uint8_t encoded_message_buf[RawUATUplinkPacket::kUplinkMessageNumBytes]) {
    if (encoded_message_buf == nullptr || deinterleaved_buf == nullptr) {
        return;  // Invalid input.
    }

    // De-interleave straight into the output. Requires the buffers not to overlap (documented in fec.hh); with that
    // guarantee no intermediate assembly buffer is needed.
    for (int block = 0; block < RawUATUplinkPacket::kUplinkMessageNumBlocks; block++) {
        uint8_t* block_data = &(deinterleaved_buf[block * RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes]);
        for (int byte_index = 0; byte_index < RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes; byte_index++) {
            // De-interleave per UAT tech manual Table 2-6.
            block_data[byte_index] = encoded_message_buf[byte_index * RawUATUplinkPacket::kUplinkMessageNumBlocks + block];
        }
    }
}

bool UATReedSolomon::EncodeShortADSBMessage(uint8_t message_buf[]) {
    if (message_buf == nullptr) {
        return false;  // Invalid input.
    }
    encode_rs_char(rs_adsb_short, (unsigned char*)message_buf,
                   (unsigned char*)(message_buf + RawUATADSBPacket::kShortADSBMessagePayloadNumBytes));
    return true;
}

bool UATReedSolomon::EncodeLongADSBMessage(uint8_t message_buf[]) {
    if (message_buf == nullptr) {
        return false;  // Invalid input.
    }
    encode_rs_char(rs_adsb_long, (unsigned char*)message_buf,
                   (unsigned char*)(message_buf + RawUATADSBPacket::kLongADSBMessagePayloadNumBytes));
    return true;
}

bool UATReedSolomon::EncodeUplinkMessage(uint8_t encoded_message_buf[], uint8_t decoded_payload_buf[]) {
    if (encoded_message_buf == nullptr) {
        return false;  // Invalid input.
    }

    // PrintByteBuffer("EncodeUplinkMessage: Decoded payload before encode:", decoded_payload_buf,
    //                 RawUATUplinkPacket::kUplinkMessagePayloadNumBytes);
    for (int block = 0; block < RawUATUplinkPacket::kUplinkMessageNumBlocks; block++) {
        uint8_t* block_data = &(decoded_payload_buf[block * RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes]);
        uint8_t block_parity[RawUATUplinkPacket::kUplinkMessageBlockFECParityNumBytes];
        encode_rs_char(rs_uplink, block_data, block_parity);
        // PrintByteBuffer("\tBlock Data:", block_data, RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes);
        // PrintByteBuffer("\tBlock Parity:", block_parity, RawUATUplinkPacket::kUplinkMessageBlockFECParityNumBytes);
        for (int byte_index = 0; byte_index < RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes; byte_index++) {
            // Interleave payload per UAT tech manual Table 2-6.
            encoded_message_buf[byte_index * RawUATUplinkPacket::kUplinkMessageNumBlocks + block] =
                block_data[byte_index];
        }
        for (int byte_index = 0; byte_index < RawUATUplinkPacket::kUplinkMessageBlockFECParityNumBytes; byte_index++) {
            // Interleave parity per UAT tech manual Table 2-6.
            encoded_message_buf[(RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes *
                                 RawUATUplinkPacket::kUplinkMessageNumBlocks) +
                                (byte_index * RawUATUplinkPacket::kUplinkMessageNumBlocks) + block] =
                block_parity[byte_index];
        }
    }
    // PrintByteBuffer("\tEncoded Message:", encoded_message_buf, RawUATUplinkPacket::kUplinkMessageNumBytes);

    return true;
}