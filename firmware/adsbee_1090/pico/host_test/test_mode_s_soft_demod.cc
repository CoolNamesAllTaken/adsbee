#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

#include "../application/mode_s_soft_demod.hh"
#include "gtest/gtest.h"

using namespace mode_s_soft_demod;

// Comparator captures from a 1090U on the bench (pulse sampler output, first sample in the MSB of the first word).
// Bench capture: -86 dBm, trigger offset 300 mV. Sent 8DADF01D9A9571EA7F468007AAB8.
static const uint32_t kWeakTwoFixes[kCaptureWords + 1] = {
    0x07C600C0, 0x1E01FCC0, 0x5C0017F0, 0x07C001CF, 0xC001F300, 0x3C0019B8, 0x07001007, 0x00EC001E, 0x03F00C01,
    0xF03F81F8, 0x0E1E0700, 0x24001FF0, 0x07E001F8, 0x0FF80660, 0x01FDC001, 0x3FE001D0, 0x1FF80001, 0x7C001CFC,
    0x001FF003, 0xC07C001E, 0x01E03EE8, 0x05401807, 0xE001FFC0, 0x011BC000, 0xF800FE07, 0x80080760, 0x7C03C07C,
    0x001AF800, 0x1E03601C, 0xF005C001, 0xEFC003E0, 0x1F81E00C, 0x03C01F00, 0xC01F03E0, 0x1F80303F, 0xFC060030,
    0x0060011E, 0x4001DFC0, 0x01FDC001, 0xE3C0017C, 0x003801C0, 0x01E01E01, 0xE0000000,
};
static const char kWeakTwoFixesSent[] = "8DADF01D9A9571EA7F468007AAB8";

// Bench capture: -86 dBm, trigger offset 300 mV. Sent 8DADF01758955AB5A7A1319F3F2B.
static const uint32_t kWeakOneFix[kCaptureWords + 1] = {
    0xC7F000F8, 0x0F003FC0, 0x1E0002FC, 0x03F000BF, 0xC000CEE0, 0x1E000DFC, 0x00F00000, 0xE01E000F, 0x80FC0780,
    0xE00F007C, 0x0278000F, 0xFF010016, 0x0009FE00, 0x0C7E0230, 0x00F80F00, 0xCFE00178, 0x079E000F, 0xE7000CEE,
    0x000FB000, 0x07F603C0, 0x004FF000, 0xE26000FF, 0xE01E0005, 0x3E000F8E, 0x03C000CE, 0xE000F803, 0xF803F03C,
    0x01E001CF, 0xC000F807, 0x80B803CE, 0x000E007F, 0x800C0007, 0x80380DFC, 0x01E000FC, 0x0BFE03F0, 0x1803603F,
    0x001FC0D3, 0x203E01E0, 0x1E03801E, 0x000F80CB, 0xC0007870, 0x00EFE018, 0x00000000,
};
static const char kWeakOneFixSent[] = "8DADF01758955AB5A7A1319F3F2B";

// Bench capture: -6 dBm, trigger offset 600 mV. Sent 8DADF01567B44832B1FD554E664A.
static const uint32_t kStrong[kCaptureWords + 1] = {
    0x1FF803F8, 0x3F83FFE0, 0xFE003FFE, 0x0FE003FF, 0xE003FFE0, 0xFE003FFE, 0x0FE0FE0F, 0xE0FE003F, 0x83F83F83,
    0xF83F83F8, 0x3FFE003F, 0xFE003FFE, 0x003FFE0F, 0xE003F83F, 0xFE0FE0FE, 0x0FE003FF, 0xE0FE003F, 0xFE003F83,
    0xF83FFE00, 0x3F83FFE0, 0x03F83F83, 0xF83F83FF, 0xC0FE003F, 0x83FFE003, 0xFFE003FF, 0xE0FE003F, 0x83F83FFE,
    0x0FE0FE0F, 0xE0FE0FE0, 0xFE003FFE, 0x003FFE00, 0x3FFE003F, 0xFE003FFE, 0x003FFE00, 0x3F83FFE0, 0xFE0FE003,
    0xF83FFE0F, 0xE003F83F, 0xFE0FE003, 0xF83FFE00, 0x3F83FFE0, 0x03FFE003, 0xF8000000,
};
static const char kStrongSent[] = "8DADF01567B44832B1FD554E664A";

// Bench capture: -60 dBm, trigger offset 600 mV. Sent 5DADF01CC41466.
static const uint32_t kShort[kCaptureWords + 1] = {
    0x003FFF00, 0x1FFF07E0, 0x7E001FFE, 0x07E001FF, 0xE001FFE0, 0x7E001FFE, 0x07E07E07, 0xE07E001F, 0x81F81F81,
    0xF81F81F8, 0x1FFE07E0, 0x7E001F81, 0xFFE07E00, 0x1F81F81F, 0xFE001F81, 0xF81F81F8, 0x1FFE001F, 0xFE001F81,
    0xF81FFE07, 0xE001F81F, 0xFE07E001, 0xF8000000, 0x00000000, 0x00000400, 0x00000000, 0x00020000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000E00,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
};
static const char kShortSent[] = "5DADF01CC41466";

static const char kDF17[] = "8D4840D6202CC371C32CE0576098";

// DF11 all-call reply for address 0x4840D6 whose parity carries the given interrogator code.
static std::string MakeDF11(uint32_t interrogator_code) {
    uint32_t buffer[2] = {0x5D4840D6, 0};
    uint32_t parity = CRC24Remainder(buffer, 56) ^ interrogator_code;
    char hex[15];
    snprintf(hex, sizeof(hex), "5D4840D6%06X", static_cast<unsigned>(parity));
    return hex;
}

static std::vector<uint8_t> HexToBits(const char* hex) {
    std::vector<uint8_t> bits;
    for (const char* c = hex; *c; c++) {
        int nibble = std::stoi(std::string(1, *c), nullptr, 16);
        for (int b = 3; b >= 0; b--) {
            bits.push_back((nibble >> b) & 1);
        }
    }
    return bits;
}

static std::string BufferToHex(const Result& result) {
    static const char kDigits[] = "0123456789ABCDEF";
    std::string hex;
    for (uint16_t i = 0; i < result.len_bits / 4; i++) {
        hex += kDigits[(result.buffer[i / 8] >> (28 - 4 * (i % 8))) & 0xF];
    }
    return hex;
}

// Ideal sampler output for a message: start_offset quiet samples, then pulse_samples HI samples at the start of the
// pulse chip of each bit.
struct Capture {
    uint32_t words[kCaptureWords + 1] = {0};

    void Set(uint32_t sample, bool value) {
        if (sample >= (kCaptureWords + 1) * 32) {
            return;
        }
        uint32_t mask = 1u << (31 - (sample & 31));
        words[sample >> 5] = value ? (words[sample >> 5] | mask) : (words[sample >> 5] & ~mask);
    }

    // early_samples moves the rising edge of every pulse earlier (later if negative) without moving its falling
    // edge.
    Capture(const char* hex, uint16_t start_offset, uint16_t pulse_samples = kSamplesPerChip,
            int16_t early_samples = 0) {
        std::vector<uint8_t> bits = HexToBits(hex);
        pulse_samples += early_samples;
        for (size_t i = 0; i < bits.size(); i++) {
            uint32_t pulse_start = start_offset + i * kSamplesPerBit + (bits[i] ? 0 : kSamplesPerChip) - early_samples;
            for (uint16_t k = 0; k < pulse_samples; k++) {
                Set(pulse_start + k, true);
            }
        }
    }

    // Removes the pulse of one bit.
    void BlankBit(uint16_t start_offset, uint16_t bit_index) {
        for (uint16_t k = 0; k < kSamplesPerBit + 2; k++) {
            Set(start_offset + bit_index * kSamplesPerBit + k, false);
        }
    }
};

TEST(ModeSSoftDemod, CRC24RemainderOfIntactMessagesIsZero) {
    Capture capture(kDF17, kNominalStartOffsetSamples);
    Result result;
    ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result));
    EXPECT_EQ(CRC24Remainder(result.buffer, 112), 0u);
    result.buffer[1] ^= 0x00010000;  // Bit 47.
    EXPECT_EQ(CRC24Remainder(result.buffer, 112), kBitSyndromes.syndrome[112 - 1 - 47]);
}

TEST(ModeSSoftDemod, CRC24RemainderMatchesBitwiseDivision) {
    uint32_t state = 0x1090;
    for (uint16_t round = 0; round < 200; round++) {
        uint32_t buffer[4];
        for (uint32_t& word : buffer) {
            state = state * 1664525 + 1013904223;  // Linear congruential generator: any bit pattern will do.
            word = state;
        }
        for (uint16_t len_bits : {56, 112}) {
            uint32_t expected = 0;
            for (uint16_t i = 0; i < len_bits; i++) {
                expected = (expected << 1) | ((buffer[i >> 5] >> (31 - (i & 31))) & 1);
                if (expected & 0x1000000) {
                    expected ^= kCRC24Generator;
                }
            }
            EXPECT_EQ(CRC24Remainder(buffer, len_bits), expected & 0xFFFFFF);
        }
    }
}

TEST(ModeSSoftDemod, DecodesAtEveryStartOffset) {
    for (uint16_t offset = kMinStartOffsetSamples; offset <= kMaxStartOffsetSamples; offset++) {
        Capture capture(kDF17, offset);
        Result result;
        ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result)) << "offset " << offset;
        EXPECT_EQ(result.len_bits, 112);
        EXPECT_EQ(BufferToHex(result), kDF17) << "offset " << offset;
        EXPECT_EQ(result.start_offset_samples, offset);
        EXPECT_EQ(result.num_flipped_bits, 0);
    }
}

TEST(ModeSSoftDemod, ShortMessageFromFullAndShortCapture) {
    std::string df11 = MakeDF11(0);
    Capture capture(df11.c_str(), kNominalStartOffsetSamples);
    Result result;
    ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result));
    EXPECT_EQ(result.len_bits, 56);
    EXPECT_EQ(BufferToHex(result), df11);
    EXPECT_EQ(CRC24Remainder(result.buffer, 56), 0u);
    EXPECT_EQ(result.buffer[1] & 0xFF, 0u);
    EXPECT_EQ(result.buffer[2], 0u);
    EXPECT_EQ(result.buffer[3], 0u);

    // Cut short by the short capture alarm: the words past the short capture are not valid.
    for (uint16_t i = kShortCaptureWords; i <= kCaptureWords; i++) {
        capture.words[i] = 0xFFFFFFFF;
    }
    ASSERT_TRUE(Demodulate(capture.words, kShortCaptureWords, result));
    EXPECT_EQ(BufferToHex(result), df11);
}

TEST(ModeSSoftDemod, LongMessageInShortCaptureIsRejected) {
    Capture capture(kDF17, kNominalStartOffsetSamples);
    Result result;
    EXPECT_FALSE(Demodulate(capture.words, kShortCaptureWords, result));
    EXPECT_EQ(result.len_bits, 0);
}

TEST(ModeSSoftDemod, NarrowAndWidePulses) {
    // Weak signals leave 3 of 6 samples HI; strong ones spill 2 samples into the next chip.
    for (uint16_t pulse_samples : {3, 4, 8}) {
        Capture capture(kDF17, kNominalStartOffsetSamples, pulse_samples);
        Result result;
        ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result)) << pulse_samples;
        EXPECT_EQ(BufferToHex(result), kDF17) << pulse_samples;
    }
}

TEST(ModeSSoftDemod, FixesUpToTwoWeakBits) {
    // A missing pulse leaves a bit without pulse position: it reads 0 with no confidence.
    Capture capture(kDF17, kNominalStartOffsetSamples);
    capture.BlankBit(kNominalStartOffsetSamples, 34);  // A 1 bit.
    Result result;
    ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result));
    EXPECT_EQ(BufferToHex(result), kDF17);
    EXPECT_EQ(result.num_flipped_bits, 1);

    capture.BlankBit(kNominalStartOffsetSamples, 64);  // Another 1 bit.
    ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result));
    EXPECT_EQ(BufferToHex(result), kDF17);
    EXPECT_EQ(result.num_flipped_bits, 2);
}

TEST(ModeSSoftDemod, DoesNotFlipConfidentBits) {
    // A wrong bit with a clean pulse is not a candidate: the message is handed on unchanged, CRC failing.
    std::string corrupted = kDF17;
    corrupted[10] = corrupted[10] == '2' ? '3' : '2';
    Capture capture(corrupted.c_str(), kNominalStartOffsetSamples);
    Result result;
    ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result));
    EXPECT_EQ(BufferToHex(result), corrupted);
    EXPECT_EQ(result.num_flipped_bits, 0);
    EXPECT_NE(CRC24Remainder(result.buffer, 112), 0u);
}

TEST(ModeSSoftDemod, ThreeWeakWrongBitsAreLeftAlone) {
    Capture capture(kDF17, kNominalStartOffsetSamples);
    for (uint16_t bit : {5, 34, 64}) {  // All 1 bits.
        capture.BlankBit(kNominalStartOffsetSamples, bit);
    }
    Result result;
    ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result));
    EXPECT_EQ(result.num_flipped_bits, 0);
    EXPECT_NE(BufferToHex(result), kDF17);
}

TEST(ModeSSoftDemod, AllCallReplies) {
    // Squitter (interrogator code 0) with a missing pulse: fixed.
    std::string squitter = MakeDF11(0);
    Capture capture(squitter.c_str(), kNominalStartOffsetSamples);
    capture.BlankBit(kNominalStartOffsetSamples, 9);  // A 1 bit of the address.
    Result result;
    ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result));
    EXPECT_EQ(BufferToHex(result), squitter);
    EXPECT_EQ(result.num_flipped_bits, 1);

    // Reply with interrogator code 5 in the parity: the remainder is the code, nothing to fix.
    std::string reply = MakeDF11(5);
    Capture reply_capture(reply.c_str(), kNominalStartOffsetSamples);
    ASSERT_TRUE(Demodulate(reply_capture.words, kCaptureWords, result));
    EXPECT_EQ(BufferToHex(result), reply);
    EXPECT_EQ(result.num_flipped_bits, 0);
    EXPECT_EQ(CRC24Remainder(result.buffer, 56), 5u);
}

TEST(ModeSSoftDemod, RejectsNoise) {
    Result result;
    uint32_t quiet[kCaptureWords + 1] = {0};
    EXPECT_FALSE(Demodulate(quiet, kCaptureWords, result));

    // Sparse comparator chatter: single HI samples every 23 samples.
    uint32_t chatter[kCaptureWords + 1] = {0};
    for (uint32_t sample = 5; sample < kCaptureWords * 32; sample += 23) {
        chatter[sample >> 5] |= 1u << (31 - (sample & 31));
    }
    EXPECT_FALSE(Demodulate(chatter, kCaptureWords, result));
}

TEST(ModeSSoftDemod, BenchCaptures) {
    Result result;
    ASSERT_TRUE(Demodulate(kStrong, kCaptureWords, result));
    EXPECT_EQ(BufferToHex(result), kStrongSent);
    EXPECT_EQ(result.num_flipped_bits, 0);

    ASSERT_TRUE(Demodulate(kShort, kCaptureWords, result));
    EXPECT_EQ(BufferToHex(result), kShortSent);
    ASSERT_TRUE(Demodulate(kShort, kShortCaptureWords, result));
    EXPECT_EQ(BufferToHex(result), kShortSent);

    ASSERT_TRUE(Demodulate(kWeakOneFix, kCaptureWords, result));
    EXPECT_EQ(BufferToHex(result), kWeakOneFixSent);
    EXPECT_EQ(result.num_flipped_bits, 1);

    ASSERT_TRUE(Demodulate(kWeakTwoFixes, kCaptureWords, result));
    EXPECT_EQ(BufferToHex(result), kWeakTwoFixesSent);
    EXPECT_EQ(result.num_flipped_bits, 2);
}

TEST(ModeSSoftDemod, DataStartOfIdealPulses) {
    // Pulses of nominal width: the data starts at the start offset, 4 counts per sample.
    for (uint16_t offset = kMinStartOffsetSamples; offset <= kMaxStartOffsetSamples; offset++) {
        Capture capture(kDF17, offset);
        Result result;
        ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result)) << "offset " << offset;
        EXPECT_EQ(result.data_start_48mhz_counts, offset * kCountsPerSample) << "offset " << offset;
    }
}

TEST(ModeSSoftDemod, DataStartFollowsPulseCenters) {
    const uint16_t kOffset = 4;
    struct Shape {
        uint16_t pulse_samples;  // Before early_samples is applied.
        int16_t early_samples;
        int16_t center_shift_counts;  // Half the change of the falling edge minus that of the rising edge.
    };
    // Strong signals widen a pulse on both sides, weak ones narrow it on both sides: the timing must not move. A
    // pulse that only grows or shrinks on one side moves by half of that.
    const Shape kShapes[] = {{6, 0, 0}, {7, 1, 0},  {8, 1, 2},  {5, -1, 0}, {8, 0, 4},
                             {7, 0, 2}, {5, 0, -2}, {4, 0, -4}, {6, 1, -2}, {6, 2, -4}};
    for (const Shape& shape : kShapes) {
        Capture capture(kDF17, kOffset, shape.pulse_samples, shape.early_samples);
        Result result;
        ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result));
        EXPECT_EQ(BufferToHex(result), kDF17);
        EXPECT_EQ(result.data_start_48mhz_counts, kOffset * kCountsPerSample + shape.center_shift_counts)
            << "pulse " << shape.pulse_samples << " samples, " << shape.early_samples << " early";
    }
}

TEST(ModeSSoftDemod, DataStartIsFinerThanOneSample) {
    // Half of the pulses one sample late, as when the true position lies between two samples and noise decides.
    Capture capture(kDF17, 4);
    std::vector<uint8_t> bits = HexToBits(kDF17);
    for (uint16_t i = 0; i < kTimingEdgeBits; i += 2) {
        uint32_t pulse_start = 4 + i * kSamplesPerBit + (bits[i] ? 0 : kSamplesPerChip);
        capture.Set(pulse_start, false);
        capture.Set(pulse_start + kSamplesPerChip, true);
    }
    Result result;
    ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result));
    EXPECT_EQ(result.start_offset_samples, 4);
    EXPECT_EQ(result.data_start_48mhz_counts, 4 * kCountsPerSample + kCountsPerSample / 2);
}

TEST(ModeSSoftDemod, DataStartWithOneKindOfEdge) {
    // DF0 with zeros in its first bytes: no falling mid-bit edges to average with the rising ones.
    Capture capture("00000000A5A5A5", 5);
    Result result;
    ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result));
    EXPECT_EQ(result.len_bits, 56);
    EXPECT_EQ(result.data_start_48mhz_counts, 5 * kCountsPerSample + kDataStartFallbackCounts);
}

// Bench captures of one transmitter at five levels (attenuator steps), with the data start that an independent
// implementation of the estimate (Python, on the same samples) gives for each.
struct TimedCapture {
    const char* sent;
    int16_t data_start_48mhz_counts;
    uint32_t words[kCaptureWords + 1];
};
static const TimedCapture kTimedCaptures[] = {
    // -1 dBm.
    {"8DADF0015872210C3A83DABD0156",
     22,
     {0x07F001FC, 0x1FC1FFF0, 0x7F001FFF, 0x07F001FF, 0xF001FFF0, 0x7F001FFF, 0x07F03F07, 0xF03F001F, 0xC1FC1FC1,
      0xFC1FC0FC, 0x0FC0FC0F, 0xC0FC0FFF, 0x001FFF00, 0x0FFF03F0, 0x00FE0FE0, 0xFE0FFF83, 0xF83F800F, 0xE0FFF800,
      0xFE0FE0FF, 0xF800FE0F, 0xE0FE0FFF, 0x800FE0FE, 0x0FE0FFF8, 0x3F800FE0, 0xFE0FE0FF, 0xF83F83F8, 0x00FFF800,
      0xFFF800FE, 0x0FE0FE0F, 0xE0FFF83F, 0x83F83F80, 0x0FFF83F8, 0x00FFF800, 0xFFF800FF, 0xF83F83F8, 0x3F800FFF,
      0x800FE0FE, 0x0FE0FE0F, 0xE0FE0FFF, 0x800FFF80, 0x0FFF800F, 0xFF81F800, 0x7F000000}},
    // -16 dBm.
    {"8DADF0009816B4B5A5DE558E5C77",
     24,
     {0x07FC01FF, 0x1FE0FFF0, 0x3F000FFF, 0x03F000FF, 0xF000FFF0, 0x3F000FFF, 0x03F03F03, 0xF03F000F, 0xE0FC0FC0,
      0xFC0FC0FC, 0x0FC0FC0F, 0xC0FC0FC0, 0xFFF000FE, 0x0FFF03F0, 0x00FE0FC0, 0xFC0FC0FC, 0x0FFF000F, 0xFF03F000,
      0xFFF000FF, 0xF03F000F, 0xFF000FF0, 0xFFF000FF, 0xF03F000F, 0xFF000FFF, 0x83F800FF, 0xF800FF0F, 0xFF000FFF,
      0x81F81F80, 0x0FFF81F8, 0x1F81F800, 0xFF07FF80, 0x0FFF800F, 0xFF8007FF, 0x81F8007F, 0x07E07FF8, 0x1F81F800,
      0x7F07FF80, 0x07FF81F8, 0x1F8007F0, 0x7E07FF81, 0xF81F8007, 0xFF81F81F, 0x80000000}},
    // -31 dBm.
    {"8DADF001636BDABB894936125C72",
     25,
     {0x07F801FE, 0x1FE1FFF8, 0x3F801FFF, 0x83F800FF, 0xF800FFF8, 0x3F800FFF, 0x83F83F83, 0xF83F800F, 0xE0FE0FE0,
      0xFE0FE0FE, 0x0FE0FE0F, 0xE0FE0FFF, 0x800FFF83, 0xF800FE0F, 0xE0FFF83F, 0x800FFF83, 0xF800FFF8, 0x00FFF83F,
      0x83F83F80, 0x0FFF83F8, 0x00FFF800, 0xFFF800FF, 0xF83F83F8, 0x00FFF83F, 0xC3F800FE, 0x0FF0FFF8, 0x00FF0FFF,
      0xC00FFFC0, 0x0FF0FFF8, 0x00FF0FFF, 0xC00FF0FF, 0xF81FC00F, 0xFFC1FC00, 0xFF07F07F, 0x07FFC007, 0xF07FFC00,
      0x7F07FFC0, 0x07FFC1FC, 0x1FC007F0, 0x7F07FFC1, 0xFC1FC007, 0xF07FFC00, 0x7F000000}},
    // -46 dBm.
    {"8DADF0059B89CB4B0FDC9B17F688",
     22,
     {0x07F001FC, 0x1FC1FFF0, 0x7F001FFF, 0x07F001FF, 0xF001FFF0, 0x7F001FFF, 0x03F07F03, 0xF07F001F, 0xC1FC1FC0,
      0xFC0FC0FC, 0x0FC0FC0F, 0xFF000FFF, 0x03F000FE, 0x0FFF03F0, 0x00FFF03F, 0x03F000FE, 0x0FE0FFF0, 0x00FE0FFF,
      0x03F03F00, 0x0FE0FFF0, 0x00FFF03F, 0x800FFF80, 0x0FE0FFF8, 0x00FFF83F, 0x800FE0FE, 0x0FE0FFF8, 0x3F83F83F,
      0x83F83F80, 0x0FFF83F8, 0x3F800FE0, 0xFFF800FE, 0x0FFF83F8, 0x00FFF83F, 0x800FE0FE, 0x0FFF800F, 0xFF83F83F,
      0x81F83F81, 0xF83F800F, 0xFF81F800, 0xFFF800FE, 0x07E07FF8, 0x00FE07E0, 0x7E000000}},
    // -61 dBm.
    {"8DADF0009D618D3A8251DF51C20D",
     24,
     {0x07F001FE, 0x0FC0FFF0, 0x3F000FFF, 0x03F000FF, 0xF000FFF0, 0x3F000FFF, 0x03F03F03, 0xF03F000F, 0xC0FE0FE0,
      0xFC0FC0FC, 0x0FE0FE0F, 0xC0FC0FE0, 0xFFF000FE, 0x0FFF83F8, 0x3F800FFF, 0x800FFF83, 0xF800FE0F, 0xE0FE0FFF,
      0x81F800FE, 0x0FE0FFF8, 0x1F800FFF, 0x800FE0FF, 0xF81F81F8, 0x00FFF800, 0x7FF800FE, 0x0FE07E07, 0xE07FF800,
      0x7E07FF80, 0x07FF8007, 0xE07E07FF, 0x81F81F80, 0x07FF81F8, 0x1F81F81F, 0x8007FF80, 0x07FF8007, 0xE07E07FF,
      0x81F81F80, 0x07E07E07, 0xE07FF800, 0x7F07E07E, 0x07E07FF8, 0x1F8007FF, 0xC0000000}},
};

TEST(ModeSSoftDemod, DataStartOfBenchCaptures) {
    for (const TimedCapture& capture : kTimedCaptures) {
        Result result;
        ASSERT_TRUE(Demodulate(capture.words, kCaptureWords, result)) << capture.sent;
        EXPECT_EQ(BufferToHex(result), capture.sent);
        EXPECT_EQ(result.num_flipped_bits, 0);
        EXPECT_EQ(result.data_start_48mhz_counts, capture.data_start_48mhz_counts) << capture.sent;
    }
}
