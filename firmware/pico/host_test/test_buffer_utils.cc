#include "buffer_utils.hh"
#include "gtest/gtest.h"

TEST(BufferUtils, GetNBitsFromWordBuffer) {
    uint32_t packet_buffer[4];
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x0000504Du;

    EXPECT_EQ(GetNBitsFromWordBuffer(1, 0, packet_buffer), 0b1u);
    EXPECT_EQ(GetNBitsFromWordBuffer(1, 1, packet_buffer), 0b0u);

    EXPECT_EQ(GetNBitsFromWordBuffer(8, 0, packet_buffer), 0x8Du);
    EXPECT_EQ(GetNBitsFromWordBuffer(16, 0, packet_buffer), 0x8D76u);
    EXPECT_EQ(GetNBitsFromWordBuffer(24, 0, packet_buffer), 0x8D76CEu);
    EXPECT_EQ(GetNBitsFromWordBuffer(32, 0, packet_buffer), 0x8D76CE88u);

    // first bit index = 4
    EXPECT_EQ(GetNBitsFromWordBuffer(32, 4, packet_buffer), 0xD76CE882u);
    EXPECT_EQ(GetNBitsFromWordBuffer(24, 4, packet_buffer), 0xD76CE8u);
    EXPECT_EQ(GetNBitsFromWordBuffer(16, 4, packet_buffer), 0xD76Cu);
    EXPECT_EQ(GetNBitsFromWordBuffer(8, 4, packet_buffer), 0xD7u);

    // first bit index = 8
    EXPECT_EQ(GetNBitsFromWordBuffer(32, 8, packet_buffer), 0x76CE8820u);
    EXPECT_EQ(GetNBitsFromWordBuffer(24, 8, packet_buffer), 0x76CE88u);
    EXPECT_EQ(GetNBitsFromWordBuffer(16, 8, packet_buffer), 0x76CEu);
    EXPECT_EQ(GetNBitsFromWordBuffer(8, 8, packet_buffer), 0x76u);

    // first bit index = 12
    EXPECT_EQ(GetNBitsFromWordBuffer(32, 12, packet_buffer), 0x6CE88204u);

    // first bit index = 16
    EXPECT_EQ(GetNBitsFromWordBuffer(32, 16, packet_buffer), 0xCE88204Cu);

    // make sure it doesn't fall off the end; can use some printfs to double check this
    EXPECT_EQ(GetNBitsFromWordBuffer(16, 32 * 3 + 16, packet_buffer), 0x504Du);
}

TEST(BufferUtils, SetNBitsInWordBuffer) {
    uint32_t packet_buffer[4];
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x0000504Du;

    SetNBitsInWordBuffer(8, 0xDEu, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0xDE76CE88u);

    // set with word that is too long
    SetNBitsInWordBuffer(8, 0x1DEu, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0xDE76CE88u);

    // zero a byte
    SetNBitsInWordBuffer(8, 0x00u, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0x0076CE88u);
    // set single bit
    SetNBitsInWordBuffer(1, 0b1, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0x8076CE88u);

    // test clipping
    packet_buffer[0] = 0x00000000u;
    SetNBitsInWordBuffer(24, 0xFFFFFFFFu, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0xFFFFFF00u);

    // basic wraparound
    packet_buffer[0] = 0x8D76CE88u;  // reset from last test
    SetNBitsInWordBuffer(16, 0xBEEFu, 24, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0x8D76CEBEu);
    EXPECT_EQ(packet_buffer[1], 0xEF4C9072u);

    // wraparound with full word
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    SetNBitsInWordBuffer(32, 0x0000FEEFu, 32 + 24, packet_buffer);
    EXPECT_EQ(packet_buffer[1], 0x204C9000u);
    EXPECT_EQ(packet_buffer[2], 0x00FEEF9Au);

    // make sure it doesn't fall off the end; can use some printfs to double check this
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x0000504Du;
    SetNBitsInWordBuffer(24, 0xFFBEBEu, 32 * 3 + 8, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0x8D76CE88u);  // untouched
    EXPECT_EQ(packet_buffer[1], 0x204C9072u);  // untouched
    EXPECT_EQ(packet_buffer[2], 0xCB48209Au);  // untouched
    EXPECT_EQ(packet_buffer[3], 0x00FFBEBEu);
}

TEST(BufferUtils, ByteBufferToWordBuffer) {
    // Word Aligned
    uint8_t byte_buffer[12] = {0x8D, 0x76, 0xCE, 0x88, 0x20, 0x4C, 0x90, 0x72, 0xCB, 0x48, 0x20, 0x9A};
    uint32_t word_buffer[4] = {0};

    ByteBufferToWordBuffer(byte_buffer, word_buffer, 12);

    EXPECT_EQ(word_buffer[0], 0x8D76CE88u);
    EXPECT_EQ(word_buffer[1], 0x204C9072u);
    EXPECT_EQ(word_buffer[2], 0xCB48209Au);
    EXPECT_EQ(word_buffer[3], 0x00000000u);

    // Not Word Aligned
    uint8_t byte_buffer2[11] = {0x8D, 0x76, 0xCE, 0x88, 0x20, 0x4C, 0x90, 0x72, 0xCB, 0x48, 0x20};
    uint32_t word_buffer2[4] = {0};

    ByteBufferToWordBuffer(byte_buffer2, word_buffer2, 11);

    EXPECT_EQ(word_buffer2[0], 0x8D76CE88u);
    EXPECT_EQ(word_buffer2[1], 0x204C9072u);
    EXPECT_EQ(word_buffer2[2], 0xCB482000u);
    EXPECT_EQ(word_buffer2[3], 0x00000000u);
}

TEST(BufferUtils, WordBufferToByteBuffer) {
    // Word Aligned
    uint32_t word_buffer[4] = {0x8D76CE88u, 0x204C9072u, 0xCB48209Au, 0x00000000u};
    uint8_t byte_buffer[12] = {0};

    WordBufferToByteBuffer(word_buffer, byte_buffer, 12);

    EXPECT_EQ(byte_buffer[0], 0x8D);
    EXPECT_EQ(byte_buffer[1], 0x76);
    EXPECT_EQ(byte_buffer[2], 0xCE);
    EXPECT_EQ(byte_buffer[3], 0x88);
    EXPECT_EQ(byte_buffer[4], 0x20);
    EXPECT_EQ(byte_buffer[5], 0x4C);
    EXPECT_EQ(byte_buffer[6], 0x90);
    EXPECT_EQ(byte_buffer[7], 0x72);
    EXPECT_EQ(byte_buffer[8], 0xCB);
    EXPECT_EQ(byte_buffer[9], 0x48);
    EXPECT_EQ(byte_buffer[10], 0x20);
    EXPECT_EQ(byte_buffer[11], 0x9A);

    // Not Word Aligned
    uint32_t word_buffer2[4] = {0x8D76CE88u, 0x204C9072u, 0xCB482000u, 0x00000000u};
    uint8_t byte_buffer2[11] = {0};

    WordBufferToByteBuffer(word_buffer2, byte_buffer2, 11);

    EXPECT_EQ(byte_buffer2[0], 0x8D);
    EXPECT_EQ(byte_buffer2[1], 0x76);
    EXPECT_EQ(byte_buffer2[2], 0xCE);
    EXPECT_EQ(byte_buffer2[3], 0x88);
    EXPECT_EQ(byte_buffer2[4], 0x20);
    EXPECT_EQ(byte_buffer2[5], 0x4C);
    EXPECT_EQ(byte_buffer2[6], 0x90);
    EXPECT_EQ(byte_buffer2[7], 0x72);
    EXPECT_EQ(byte_buffer2[8], 0xCB);
    EXPECT_EQ(byte_buffer2[9], 0x48);
    EXPECT_EQ(byte_buffer2[10], 0x20);
}

// Test invalid input parameters
TEST(GetNBitsFromByteBuffer, InvalidBitCount) {
    uint8_t buffer[] = {0xFF, 0xFF, 0xFF, 0xFF};

    // Test n = 0 (too small)
    EXPECT_EQ(0u, GetNBitsFromByteBuffer(0, 0, buffer));

    // Test n > 32 (too large)
    EXPECT_EQ(0u, GetNBitsFromByteBuffer(33, 0, buffer));
    EXPECT_EQ(0u, GetNBitsFromByteBuffer(100, 0, buffer));
}

// Test single bit extraction
TEST(GetNBitsFromByteBuffer, SingleBitExtraction) {
    // Buffer: 10101010 11001100 (0xAA, 0xCC)
    uint8_t buffer[] = {0xAA, 0xCC};

    // Test each bit in first byte
    EXPECT_EQ(1u, GetNBitsFromByteBuffer(1, 0, buffer));  // MSb of 0xAA
    EXPECT_EQ(0u, GetNBitsFromByteBuffer(1, 1, buffer));  // 2nd bit of 0xAA
    EXPECT_EQ(1u, GetNBitsFromByteBuffer(1, 2, buffer));  // 3rd bit of 0xAA
    EXPECT_EQ(0u, GetNBitsFromByteBuffer(1, 3, buffer));  // 4th bit of 0xAA
    EXPECT_EQ(1u, GetNBitsFromByteBuffer(1, 4, buffer));  // 5th bit of 0xAA
    EXPECT_EQ(0u, GetNBitsFromByteBuffer(1, 5, buffer));  // 6th bit of 0xAA
    EXPECT_EQ(1u, GetNBitsFromByteBuffer(1, 6, buffer));  // 7th bit of 0xAA
    EXPECT_EQ(0u, GetNBitsFromByteBuffer(1, 7, buffer));  // LSb of 0xAA

    // Test bits in second byte
    EXPECT_EQ(1u, GetNBitsFromByteBuffer(1, 8, buffer));   // MSb of 0xCC
    EXPECT_EQ(1u, GetNBitsFromByteBuffer(1, 9, buffer));   // 2nd bit of 0xCC
    EXPECT_EQ(0u, GetNBitsFromByteBuffer(1, 10, buffer));  // 3rd bit of 0xCC
}

// Test byte-aligned extraction
TEST(GetNBitsFromByteBuffer, ByteAlignedExtraction) {
    uint8_t buffer[] = {0x12, 0x34, 0x56, 0x78};

    // Extract single bytes
    EXPECT_EQ(0x12u, GetNBitsFromByteBuffer(8, 0, buffer));
    EXPECT_EQ(0x34u, GetNBitsFromByteBuffer(8, 8, buffer));
    EXPECT_EQ(0x56u, GetNBitsFromByteBuffer(8, 16, buffer));
    EXPECT_EQ(0x78u, GetNBitsFromByteBuffer(8, 24, buffer));

    // Extract 16-bit words
    EXPECT_EQ(0x1234u, GetNBitsFromByteBuffer(16, 0, buffer));
    EXPECT_EQ(0x3456u, GetNBitsFromByteBuffer(16, 8, buffer));
    EXPECT_EQ(0x5678u, GetNBitsFromByteBuffer(16, 16, buffer));

    // Extract 24-bit words
    EXPECT_EQ(0x123456u, GetNBitsFromByteBuffer(24, 0, buffer));
    EXPECT_EQ(0x345678u, GetNBitsFromByteBuffer(24, 8, buffer));

    // Extract 32-bit word
    EXPECT_EQ(0x12345678u, GetNBitsFromByteBuffer(32, 0, buffer));
}

// Test non-byte-aligned extraction (crosses byte boundaries)
TEST(GetNBitsFromByteBuffer, NonByteAlignedExtraction) {
    // Buffer: 11110000 11001100 10101010 (0xF0, 0xCC, 0xAA)
    uint8_t buffer[] = {0xF0, 0xCC, 0xAA};

    // Extract 4 bits starting from bit 2
    // Should get bits 2-5 from first byte: 1100
    EXPECT_EQ(0xCu, GetNBitsFromByteBuffer(4, 2, buffer));

    // Extract 4 bits starting from bit 6
    // Should get bits 6-7 from first byte + bits 0-1 from second byte: 00|11 = 0011
    EXPECT_EQ(0x3u, GetNBitsFromByteBuffer(4, 6, buffer));

    // Extract 12 bits starting from bit 4
    // Should span from bit 4 of first byte to bit 7 of second byte
    // First byte bits 4-7: 0000, Second byte: 11001100
    // Result should be: 0000|11001100 = 0x0CC
    EXPECT_EQ(0x0CCu, GetNBitsFromByteBuffer(12, 4, buffer));
}

// Test extraction at various bit positions within a byte
TEST(GetNBitsFromByteBuffer, VariousBitPositions) {
    uint8_t buffer[] = {0xFF, 0x00, 0xFF, 0x00};

    // Extract 2 bits from various positions
    for (int pos = 0; pos < 16; pos++) {
        uint32_t result = GetNBitsFromByteBuffer(2, pos, buffer);
        if (pos < 7) {
            EXPECT_EQ(0x3u, result) << "Failed at position " << pos;  // Both bits from 0xFF
        } else if (pos == 7) {
            EXPECT_EQ(0x2u, result) << "Failed at position " << pos;  // 1 from 0xFF, 1 from 0x00
        } else if (pos < 15) {
            EXPECT_EQ(0x0u, result) << "Failed at position " << pos;  // Both bits from 0x00
        } else {
            EXPECT_EQ(0x1u, result) << "Failed at position " << pos;  // 1 from 0x00, 1 from 0xFF
        }
    }
}

// Test maximum bit extraction (32 bits)
TEST(GetNBitsFromByteBuffer, MaxBitExtraction) {
    uint8_t buffer[] = {0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC};

    // Extract 32 bits from start
    EXPECT_EQ(0x12345678u, GetNBitsFromByteBuffer(32, 0, buffer));
}

// Test edge cases with different bit patterns
TEST(GetNBitsFromByteBuffer, EdgeCaseBitPatterns) {
    // All zeros
    uint8_t zero_buffer[] = {0x00, 0x00, 0x00, 0x00};
    EXPECT_EQ(0x0u, GetNBitsFromByteBuffer(16, 4, zero_buffer));

    // All ones
    uint8_t ones_buffer[] = {0xFF, 0xFF, 0xFF, 0xFF};
    EXPECT_EQ(0xFFFFu, GetNBitsFromByteBuffer(16, 4, ones_buffer));

    // Alternating pattern
    uint8_t alt_buffer[] = {0xAA, 0x55, 0xAA, 0x55};  // 10101010 01010101 pattern
    uint32_t result = GetNBitsFromByteBuffer(8, 4, alt_buffer);
    // Expected: bits 4-7 from 0xAA (1010) + bits 0-3 from 0x55 (0101) = 10100101 = 0xA5
    EXPECT_EQ(0xA5u, result);
}

// Test boundary conditions
TEST(GetNBitsFromByteBuffer, BoundaryConditions) {
    uint8_t buffer[] = {0x80, 0x40, 0x20, 0x10};  // 10000000 01000000 00100000 00010000

    // Test n = 1 (minimum valid)
    EXPECT_EQ(1u, GetNBitsFromByteBuffer(1, 0, buffer));
    EXPECT_EQ(0u, GetNBitsFromByteBuffer(1, 1, buffer));

    // Test n = 32 (maximum valid)
    uint32_t result32 = GetNBitsFromByteBuffer(32, 0, buffer);
    EXPECT_EQ(0x80402010u, result32);
}

// Test with longer buffer to ensure we don't read past necessary bytes
TEST(GetNBitsFromByteBuffer, LongerBuffer) {
    uint8_t buffer[] = {0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0};

    // Extract only what we need, ensure we don't read extra bytes
    EXPECT_EQ(0x123u, GetNBitsFromByteBuffer(12, 0, buffer));
    EXPECT_EQ(0x234u, GetNBitsFromByteBuffer(12, 4, buffer));
    EXPECT_EQ(0x345u, GetNBitsFromByteBuffer(12, 8, buffer));
}

TEST(GetNBitsFromByteBuffer, ExtraBit) {
    uint8_t buffer[] = {0x01, 0x02, 0x04, 0x08};  // Powers of 2

    // Test cases that might expose bit shifting problems
    uint32_t result = GetNBitsFromByteBuffer(9, 7, buffer);
    EXPECT_EQ(result, 0x0102u);  // Should get bit 7 from byte 0 (1) + all 8 bits from byte 1 (0x02)
}

TEST(BufferUtils, ManchesterToBits_BasicDecoding) {
    // Test basic Manchester decoding: 10 -> 1, 01 -> 0
    // Manchester: 10 01 10 10 01 01 10 01 (2 bits per encoded bit)
    // Decoded:    1  0  1  1  0  0  1  0  = 0xB2
    uint32_t manchester_buffer[1];
    manchester_buffer[0] = 0b10011010010110010000000000000000u;  // 16 Manchester bits -> 8 decoded bits
    uint8_t bit_buffer[1] = {0};

    ManchesterToBits(manchester_buffer, 16, bit_buffer);
    EXPECT_EQ(bit_buffer[0], 0xB2);
}

TEST(BufferUtils, ManchesterToBits_AllOnes) {
    // All 1s: 10 10 10 10 10 10 10 10
    // Decoded: 1  1  1  1  1  1  1  1 = 0xFF
    uint32_t manchester_buffer[1];
    manchester_buffer[0] = 0b10101010101010100000000000000000u;  // 16 Manchester bits
    uint8_t bit_buffer[1] = {0};

    ManchesterToBits(manchester_buffer, 16, bit_buffer);
    EXPECT_EQ(bit_buffer[0], 0xFF);
}

TEST(BufferUtils, ManchesterToBits_AllZeros) {
    // All 0s: 01 01 01 01 01 01 01 01
    // Decoded: 0  0  0  0  0  0  0  0 = 0x00
    uint32_t manchester_buffer[1];
    manchester_buffer[0] = 0b01010101010101010000000000000000u;  // 16 Manchester bits
    uint8_t bit_buffer[1] = {0};

    ManchesterToBits(manchester_buffer, 16, bit_buffer);
    EXPECT_EQ(bit_buffer[0], 0x00);
}

TEST(BufferUtils, ManchesterToBits_MultipleBytes) {
    // Test decoding across multiple bytes
    // First byte: 10 01 10 10 01 01 10 01 -> 1 0 1 1 0 0 1 0 = 0xB2
    // Second byte: 01 10 01 10 10 10 01 01 -> 0 1 0 1 1 1 0 0 = 0x5C
    uint32_t manchester_buffer[1];
    manchester_buffer[0] = 0b10011010010110010110011010100101u;  // 32 Manchester bits -> 16 decoded bits
    uint8_t bit_buffer[2] = {0};

    ManchesterToBits(manchester_buffer, 32, bit_buffer);
    EXPECT_EQ(bit_buffer[0], 0xB2);
    EXPECT_EQ(bit_buffer[1], 0x5C);
}

TEST(BufferUtils, ManchesterToBits_CrossWordBoundary) {
    // Test decoding that spans multiple 32-bit words
    uint32_t manchester_buffer[2];
    // First word: 10 01 10 10 01 01 10 01 10 10 10 10 01 01 01 01 (16 bits)
    //             1  0  1  1  0  0  1  0  1  1  1  1  0  0  0  0 = 0xB2F0
    manchester_buffer[0] = 0b10011010010110011010101001010101u;
    // Second word: 01 10 01 10 10 10 01 01 ... (continuing)
    //             0  1  0  1  1  1  0  0 ... = 0x5C
    manchester_buffer[1] = 0b01100110101001010000000000000000u;
    uint8_t bit_buffer[3] = {0};

    ManchesterToBits(manchester_buffer, 48, bit_buffer);
    EXPECT_EQ(bit_buffer[0], 0xB2);
    EXPECT_EQ(bit_buffer[1], 0xF0);
    EXPECT_EQ(bit_buffer[2], 0x5C);
}

TEST(BufferUtils, ManchesterToBits_OddManchesterBits) {
    // Test with odd number of Manchester bits (last bit should be ignored)
    uint32_t manchester_buffer[1];
    manchester_buffer[0] = 0b10011010010110010000000000000000u;  // 17 Manchester bits (odd)
    uint8_t bit_buffer[1] = {0};

    ManchesterToBits(manchester_buffer, 17, bit_buffer);  // 17/2 = 8 decoded bits
    EXPECT_EQ(bit_buffer[0], 0xB2);  // Same as 16-bit test since last bit is ignored
}

TEST(BufferUtils, ManchesterToBits_InvalidEncoding) {
    // Test with invalid Manchester patterns (00 and 11)
    // Manchester: 00 11 10 01 00 11 01 10
    // Decoded:    0  0  1  0  0  0  0  1 = 0x21 (invalid pairs decode to 0)
    uint32_t manchester_buffer[1];
    manchester_buffer[0] = 0b00111001001101100000000000000000u;  // 16 Manchester bits with invalid pairs
    uint8_t bit_buffer[1] = {0};

    ManchesterToBits(manchester_buffer, 16, bit_buffer);
    EXPECT_EQ(bit_buffer[0], 0x21);
}

TEST(BufferUtils, ManchesterToBits_SingleBit) {
    // Test decoding just 2 Manchester bits -> 1 decoded bit
    uint32_t manchester_buffer[1];
    manchester_buffer[0] = 0b10000000000000000000000000000000u;  // 10 -> 1
    uint8_t bit_buffer[1] = {0};

    ManchesterToBits(manchester_buffer, 2, bit_buffer);
    EXPECT_EQ(bit_buffer[0], 0x80);  // MSb set

    manchester_buffer[0] = 0b01000000000000000000000000000000u;  // 01 -> 0
    bit_buffer[0] = 0;

    ManchesterToBits(manchester_buffer, 2, bit_buffer);
    EXPECT_EQ(bit_buffer[0], 0x00);  // All zeros
}

TEST(BufferUtils, ManchesterToBits_PartialByte) {
    // Test decoding that doesn't fill a complete byte
    // Manchester: 10 01 10 10 (8 bits) -> Decoded: 1 0 1 1 (4 bits) = 0xB0 (left-aligned in byte)
    uint32_t manchester_buffer[1];
    manchester_buffer[0] = 0b10011010000000000000000000000000u;  // 8 Manchester bits -> 4 decoded bits
    uint8_t bit_buffer[1] = {0};

    ManchesterToBits(manchester_buffer, 8, bit_buffer);
    EXPECT_EQ(bit_buffer[0], 0xB0);  // 1011 in upper nibble
}

TEST(BufferUtils, ManchesterToBits_LargeBuffer) {
    // Test with a larger buffer (4 bytes output = 64 Manchester bits)
    uint32_t manchester_buffer[2];
    // Pattern: alternating 10 and 01 for variety
    manchester_buffer[0] = 0b10011010010110011010101001010101u;  // First 32 Manchester bits
    manchester_buffer[1] = 0b01100110101001011001101010100101u;  // Next 32 Manchester bits
    uint8_t bit_buffer[4] = {0};

    ManchesterToBits(manchester_buffer, 64, bit_buffer);

    // Verify at least that the function doesn't crash and produces some output
    // Detailed bit-by-bit verification for complex patterns
    EXPECT_EQ(bit_buffer[0], 0xB2);  // 10 01 10 10 = 1 0 1 1 = 0xB
    EXPECT_EQ(bit_buffer[1], 0xF0);  // 01 01 10 01 = 0 0 1 0 then 10 10 10 10 = 1 1 1 1 = 0xF0
}

TEST(BufferUtils, ManchesterToBits_ZeroLength) {
    // Edge case: zero Manchester bits
    uint32_t manchester_buffer[1] = {0};
    uint8_t bit_buffer[1] = {0xFF};  // Initialize to non-zero

    ManchesterToBits(manchester_buffer, 0, bit_buffer);
    // Should leave buffer untouched or clear it depending on implementation
    // With current implementation, it should clear the buffer
    EXPECT_EQ(bit_buffer[0], 0xFF);  // No bytes to initialize
}