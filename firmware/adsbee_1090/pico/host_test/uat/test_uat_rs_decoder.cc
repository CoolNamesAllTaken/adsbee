#include <cstring>

#include "fec.hh"
#include "gtest/gtest.h"
#include "uat_packet.hh"

namespace {

// Deterministic xorshift64 so that failures are reproducible.
struct XorShift64 {
    uint64_t state;
    explicit XorShift64(uint64_t seed) : state(seed) {}
    uint8_t NextByte() {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        return static_cast<uint8_t>(state >> 32);
    }
    uint32_t NextBelow(uint32_t n) {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        return static_cast<uint32_t>((state >> 32) % n);
    }
};

// Returns true if buf[0:n] is a valid codeword of the shortened code (payload re-encodes to the same parity).
bool IsCodeword(void* rs, const uint8_t* buf, uint16_t payload_len, uint16_t parity_len) {
    uint8_t parity[32];
    encode_rs_char(rs, const_cast<uint8_t*>(buf), parity);
    return memcmp(parity, buf + payload_len, parity_len) == 0;
}

struct CodeParams {
    const char* name;
    void* rs;
    uint16_t payload_len;
    uint16_t parity_len;
};

}  // namespace

/**
 * A successful decode must produce a valid codeword, including when error locations fall in the shortened code's zero
 * padding.
 */
TEST(UATReedSolomon, RandomFramesNeverDecodeToNonCodewords) {
    const CodeParams codes[] = {
        {"basic ADS-B RS(30,18)", uat_rs.rs_adsb_short, RawUATADSBPacket::kShortADSBMessagePayloadNumBytes,
         RawUATADSBPacket::kShortADSBMessageFECParityNumBytes},
        {"long ADS-B RS(48,34)", uat_rs.rs_adsb_long, RawUATADSBPacket::kLongADSBMessagePayloadNumBytes,
         RawUATADSBPacket::kLongADSBMessageFECParityNumBytes},
    };
    const int kNumTrials = 40000;
    for (const auto& code : codes) {
        SCOPED_TRACE(code.name);
        XorShift64 rng(0x5eed0000u + code.payload_len);
        int num_accepted = 0;
        int num_bogus = 0;
        for (int trial = 0; trial < kNumTrials; trial++) {
            uint8_t buf[RawUATADSBPacket::kADSBMessageMaxSizeBytes];
            uint16_t len = code.payload_len + code.parity_len;
            for (uint16_t i = 0; i < len; i++) buf[i] = rng.NextByte();
            uint8_t original[RawUATADSBPacket::kADSBMessageMaxSizeBytes];
            memcpy(original, buf, len);

            int ret = decode_rs_char(code.rs, buf, nullptr, 0);
            if (ret >= 0) {
                num_accepted++;
                if (!IsCodeword(code.rs, buf, code.payload_len, code.parity_len)) num_bogus++;
            } else {
                // A failed decode must leave the buffer untouched.
                EXPECT_EQ(memcmp(buf, original, len), 0);
            }
        }
        EXPECT_EQ(num_bogus, 0) << num_accepted << " random frames accepted";
        // Genuine decodes of random data are astronomically unlikely (~1e-9 for RS(30,18) at radius 6).
        EXPECT_EQ(num_accepted, 0);
    }
}

/**
 * Up to t = nroots/2 byte errors anywhere in the frame are corrected, with an exact reported count.
 */
TEST(UATReedSolomon, CorrectsUpToTErrorsAnywhereInFrame) {
    const CodeParams codes[] = {
        {"basic ADS-B RS(30,18)", uat_rs.rs_adsb_short, RawUATADSBPacket::kShortADSBMessagePayloadNumBytes,
         RawUATADSBPacket::kShortADSBMessageFECParityNumBytes},
        {"long ADS-B RS(48,34)", uat_rs.rs_adsb_long, RawUATADSBPacket::kLongADSBMessagePayloadNumBytes,
         RawUATADSBPacket::kLongADSBMessageFECParityNumBytes},
        {"uplink block RS(92,72)", uat_rs.rs_uplink, RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes,
         RawUATUplinkPacket::kUplinkMessageBlockFECParityNumBytes},
    };
    for (const auto& code : codes) {
        SCOPED_TRACE(code.name);
        XorShift64 rng(0xc0de0000u + code.payload_len);
        const uint16_t len = code.payload_len + code.parity_len;
        const int t = code.parity_len / 2;
        for (int trial = 0; trial < 300; trial++) {
            uint8_t codeword[RawUATUplinkPacket::kUplinkMessageBlockNumBytes];
            for (uint16_t i = 0; i < code.payload_len; i++) codeword[i] = rng.NextByte();
            encode_rs_char(code.rs, codeword, codeword + code.payload_len);

            int num_errors = trial % (t + 1);
            uint8_t received[RawUATUplinkPacket::kUplinkMessageBlockNumBytes];
            memcpy(received, codeword, len);
            bool corrupted[RawUATUplinkPacket::kUplinkMessageBlockNumBytes] = {false};
            // Sometimes hit the first and last bytes: they border the padding and the end of the block.
            for (int e = 0; e < num_errors; e++) {
                uint16_t pos;
                if (e == 0 && trial % 3 == 0) {
                    pos = 0;
                } else if (e == 1 && trial % 3 == 0) {
                    pos = len - 1;
                } else {
                    do {
                        pos = rng.NextBelow(len);
                    } while (corrupted[pos]);
                }
                if (corrupted[pos]) continue;
                corrupted[pos] = true;
                uint8_t flip;
                do {
                    flip = rng.NextByte();
                } while (flip == 0);
                received[pos] ^= flip;
            }
            int expected_corrections = 0;
            for (uint16_t i = 0; i < len; i++) expected_corrections += corrupted[i] ? 1 : 0;

            EXPECT_EQ(decode_rs_char(code.rs, received, nullptr, 0), expected_corrections);
            EXPECT_EQ(memcmp(received, codeword, len), 0);
        }
    }
}

/**
 * The table check must give the decoder's verdict on "no errors" for clean blocks, for blocks with errors anywhere, and
 * for noise.
 */
TEST(UATReedSolomon, UplinkBlockIsCodewordAgreesWithDecoder) {
    const uint16_t kPayloadLen = RawUATUplinkPacket::kUplinkMessageBlockPayloadNumBytes;
    const uint16_t kBlockLen = RawUATUplinkPacket::kUplinkMessageBlockNumBytes;
    XorShift64 rng(0x5eed0382u);
    for (int trial = 0; trial < 2000; trial++) {
        uint8_t block[kBlockLen];
        for (uint16_t i = 0; i < kPayloadLen; i++) {
            block[i] = trial == 0 ? 0 : rng.NextByte();
        }
        encode_rs_char(uat_rs.rs_uplink, block, block + kPayloadLen);
        ASSERT_TRUE(UATReedSolomon::UplinkBlockIsCodeword(block)) << "trial " << trial;

        // One wrong byte at every position in turn, then a growing number of wrong bytes.
        uint8_t damaged[kBlockLen];
        memcpy(damaged, block, kBlockLen);
        damaged[trial % kBlockLen] ^= 1 + rng.NextBelow(255);
        ASSERT_FALSE(UATReedSolomon::UplinkBlockIsCodeword(damaged)) << "trial " << trial;
        for (uint32_t i = 0; i < 1 + static_cast<uint32_t>(trial) % 30; i++) {
            damaged[rng.NextBelow(kBlockLen)] ^= 1 + rng.NextBelow(255);
        }
        uint8_t decoded[kBlockLen];
        memcpy(decoded, damaged, kBlockLen);
        bool decoder_says_clean = decode_rs_char(uat_rs.rs_uplink, decoded, nullptr, 0) == 0;
        ASSERT_EQ(UATReedSolomon::UplinkBlockIsCodeword(damaged), decoder_says_clean) << "trial " << trial;

        uint8_t noise[kBlockLen];
        for (uint16_t i = 0; i < kBlockLen; i++) {
            noise[i] = rng.NextByte();
        }
        memcpy(decoded, noise, kBlockLen);
        decoder_says_clean = decode_rs_char(uat_rs.rs_uplink, decoded, nullptr, 0) == 0;
        ASSERT_EQ(UATReedSolomon::UplinkBlockIsCodeword(noise), decoder_says_clean) << "trial " << trial;
    }
}

/**
 * An uplink with correctable errors in some blocks and none in others decodes to the sent payload, and the encoded
 * message comes back corrected.
 */
TEST(UATReedSolomon, UplinkWithCleanAndDamagedBlocksDecodes) {
    XorShift64 rng(0x5eed0383u);
    for (int trial = 0; trial < 200; trial++) {
        uint8_t payload[RawUATUplinkPacket::kUplinkMessagePayloadNumBytes];
        for (uint8_t& byte : payload) {
            byte = rng.NextByte();
        }
        uint8_t encoded[RawUATUplinkPacket::kUplinkMessageNumBytes];
        ASSERT_TRUE(uat_rs.EncodeUplinkMessage(encoded, payload));

        uint8_t received[RawUATUplinkPacket::kUplinkMessageNumBytes];
        memcpy(received, encoded, sizeof(received));
        int num_errors = 0;
        for (uint16_t block = 0; block < RawUATUplinkPacket::kUplinkMessageNumBlocks; block++) {
            // Block (trial % 7) stays clean; trial % 7 == 6 damages every block.
            if (block == trial % 7) {
                continue;
            }
            uint32_t num_block_errors = 1 + rng.NextBelow(10);
            bool used[RawUATUplinkPacket::kUplinkMessageBlockNumBytes] = {};
            for (uint32_t i = 0; i < num_block_errors; i++) {
                uint32_t byte_index = rng.NextBelow(RawUATUplinkPacket::kUplinkMessageBlockNumBytes);
                if (used[byte_index]) {
                    continue;
                }
                used[byte_index] = true;
                received[byte_index * RawUATUplinkPacket::kUplinkMessageNumBlocks + block] ^= 1 + rng.NextBelow(255);
                num_errors++;
            }
        }
        uint8_t decoded[RawUATUplinkPacket::kUplinkMessagePayloadNumBytes];
        ASSERT_EQ(uat_rs.DecodeUplinkMessage(decoded, received), num_errors) << "trial " << trial;
        ASSERT_EQ(memcmp(decoded, payload, sizeof(payload)), 0) << "trial " << trial;
        ASSERT_EQ(memcmp(received, encoded, sizeof(encoded)), 0) << "trial " << trial;
    }
}
