#include "mode_s_soft_demod.hh"

#ifdef ON_PICO
#include "pico.h"
#define SOFT_DEMOD_FUNC(name) __time_critical_func(name)
#else
#define SOFT_DEMOD_FUNC(name) name
#endif

namespace mode_s_soft_demod {

static constexpr uint32_t kBitsPerGroup = 8;  // 8 bits are 96 samples: exactly 3 capture words.
static constexpr uint32_t kSamplesPerGroup = kBitsPerGroup * kSamplesPerBit;

// Bit margins of up to 8 consecutive bits: HI samples in the first chip of a bit minus those in its second chip.
// Positive for a 1; the size is the confidence. Reads 3 words from the word of first_sample on, and a fourth one
// unless first_sample is on a word boundary. Only the first 4 margins are written if num_bits is 4 or less.
static inline void BitMargins(const uint32_t* samples, uint32_t first_sample, int margins[kBitsPerGroup],
                              uint32_t num_bits = kBitsPerGroup) {
    const uint32_t* words = samples + (first_sample >> 5);
    uint32_t shift = first_sample & 31;
    uint32_t a = words[0];
    uint32_t b = words[1];
    uint32_t c = words[2];
    if (shift != 0) {
        // Line the 96 samples up with the word boundaries, so every chip below sits at a fixed position.
        a = (a << shift) | (b >> (32 - shift));
        b = (b << shift) | (c >> (32 - shift));
        c = (c << shift) | (words[3] >> (32 - shift));
    }
    auto count = [](uint32_t chip) { return static_cast<int>(kPopCount6[chip & 0x3F]); };
    margins[0] = count(a >> 26) - count(a >> 20);
    margins[1] = count(a >> 14) - count(a >> 8);
    margins[2] = count(a >> 2) - count((a << 4) | (b >> 28));
    margins[3] = count(b >> 22) - count(b >> 16);
    if (num_bits > 4) {
        margins[4] = count(b >> 10) - count(b >> 4);
        margins[5] = count((b << 2) | (c >> 30)) - count(c >> 24);
        margins[6] = count(c >> 18) - count(c >> 12);
        margins[7] = count(c >> 6) - count(c);
    }
}

bool SOFT_DEMOD_FUNC(Demodulate)(const uint32_t* samples, uint16_t num_words, Result& result) {
    result = Result();
    int margins[kBitsPerGroup];

    // Timing: keep the start offset whose first bits are the most confident.
    uint32_t best_offset = kNominalStartOffsetSamples;
    uint32_t best_confidence = 0;
    uint32_t best_ties = kTimingSearchBits;
    for (uint32_t offset = kMinStartOffsetSamples; offset <= kMaxStartOffsetSamples; offset++) {
        uint32_t confidence = 0;
        uint32_t ties = 0;
        for (uint32_t bits_done = 0; bits_done < kTimingSearchBits; bits_done += kBitsPerGroup) {
            uint32_t bits_in_group =
                kTimingSearchBits - bits_done < kBitsPerGroup ? kTimingSearchBits - bits_done : kBitsPerGroup;
            BitMargins(samples, offset + bits_done * kSamplesPerBit, margins, bits_in_group);
            for (uint32_t i = 0; i < bits_in_group; i++) {
                confidence += static_cast<uint32_t>(margins[i] < 0 ? -margins[i] : margins[i]);
                ties += margins[i] == 0;
            }
        }
        if (confidence > best_confidence) {
            best_confidence = confidence;
            best_offset = offset;
            best_ties = ties;
        }
    }
    if (best_ties > kMaxTiesInSearchBits) {
        return false;  // Noise or the tail of another message.
    }

    // Bit decisions, one message byte at a time. The first bit of the downlink format tells the length: DF16 and up
    // are 112 bits.
    uint32_t len_bits = kMaxMessageBits;
    uint32_t available_samples = num_words * 32 - best_offset;
    uint32_t first_sample = best_offset;
    for (uint32_t bits_done = 0; bits_done < len_bits; bits_done += kBitsPerGroup, first_sample += kSamplesPerGroup) {
        BitMargins(samples, first_sample, margins);
        uint32_t byte = 0;
        for (uint32_t i = 0; i < kBitsPerGroup; i++) {
            byte = (byte << 1) | (margins[i] > 0);
        }
        result.buffer[bits_done >> 5] |= byte << (24 - (bits_done & 31));
        if (bits_done == 0) {
            if (!(byte & 0x80)) {
                len_bits = kShortMessageBits;
            }
            if (len_bits * kSamplesPerBit > available_samples) {
                result.buffer[0] = 0;
                return false;  // Capture was cut short but the message is long.
            }
        }
    }
    result.len_bits = static_cast<uint16_t>(len_bits);
    result.start_offset_samples = static_cast<uint8_t>(best_offset);

    // CRC guided fix for formats whose parity covers the message alone.
    uint32_t downlink_format = result.buffer[0] >> 27;
    if (downlink_format != 11 && downlink_format != 17 && downlink_format != 18) {
        return true;
    }
    uint32_t remainder = CRC24Remainder(result.buffer, len_bits);
    if (remainder == 0 || (downlink_format == 11 && remainder < 0x80)) {
        return true;  // Intact (DF11 replies carry an interrogator code in the low 7 bits).
    }
    // The CRC failed: go over the message again for the confidence of every bit and collect the least confident.
    static uint8_t confidences[kMaxMessageBits];  // Static: called from one context, small stack.
    first_sample = best_offset;
    for (uint32_t bits_done = 0; bits_done < len_bits; bits_done += kBitsPerGroup, first_sample += kSamplesPerGroup) {
        BitMargins(samples, first_sample, margins);
        for (uint32_t i = 0; i < kBitsPerGroup; i++) {
            confidences[bits_done + i] = static_cast<uint8_t>(margins[i] < 0 ? -margins[i] : margins[i]);
        }
    }
    uint16_t weak_bits[kMaxWeakBits];
    uint16_t num_weak_bits = 0;
    for (uint32_t level = 0; level <= kWeakBitMaxConfidence && num_weak_bits < kMaxWeakBits; level++) {
        for (uint32_t i = 0; i < len_bits && num_weak_bits < kMaxWeakBits; i++) {
            if (confidences[i] == level) {
                weak_bits[num_weak_bits++] = i;
            }
        }
    }
    auto syndrome = [len_bits](uint16_t bit_index) { return kBitSyndromes.syndrome[len_bits - 1 - bit_index]; };
    auto flip = [&result](uint16_t bit_index) { result.buffer[bit_index >> 5] ^= 1u << (31 - (bit_index & 31)); };
    for (uint16_t a = 0; a < num_weak_bits; a++) {
        if (syndrome(weak_bits[a]) == remainder) {
            flip(weak_bits[a]);
            result.num_flipped_bits = 1;
            return true;
        }
    }
    if (kMaxFlippedBits >= 2) {
        for (uint16_t a = 0; a < num_weak_bits; a++) {
            for (uint16_t b = a + 1; b < num_weak_bits; b++) {
                if ((syndrome(weak_bits[a]) ^ syndrome(weak_bits[b])) == remainder) {
                    flip(weak_bits[a]);
                    flip(weak_bits[b]);
                    result.num_flipped_bits = 2;
                    return true;
                }
            }
        }
    }
    return true;  // Not fixable here: the decoder decides what to do with it.
}

}  // namespace mode_s_soft_demod
