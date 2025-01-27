#include "buffer_utils.hh"
#include "gtest/gtest.h"

TEST(BufferUtils, GetNBitWordFromBuffer) {
    uint32_t packet_buffer[4];
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x0000504Du;

    EXPECT_EQ(GetNBitWordFromBuffer(1, 0, packet_buffer), 0b1u);
    EXPECT_EQ(GetNBitWordFromBuffer(1, 1, packet_buffer), 0b0u);

    EXPECT_EQ(GetNBitWordFromBuffer(8, 0, packet_buffer), 0x8Du);
    EXPECT_EQ(GetNBitWordFromBuffer(16, 0, packet_buffer), 0x8D76u);
    EXPECT_EQ(GetNBitWordFromBuffer(24, 0, packet_buffer), 0x8D76CEu);
    EXPECT_EQ(GetNBitWordFromBuffer(32, 0, packet_buffer), 0x8D76CE88u);

    // first bit index = 4
    EXPECT_EQ(GetNBitWordFromBuffer(32, 4, packet_buffer), 0xD76CE882u);
    EXPECT_EQ(GetNBitWordFromBuffer(24, 4, packet_buffer), 0xD76CE8u);
    EXPECT_EQ(GetNBitWordFromBuffer(16, 4, packet_buffer), 0xD76Cu);
    EXPECT_EQ(GetNBitWordFromBuffer(8, 4, packet_buffer), 0xD7u);

    // first bit index = 8
    EXPECT_EQ(GetNBitWordFromBuffer(32, 8, packet_buffer), 0x76CE8820u);
    EXPECT_EQ(GetNBitWordFromBuffer(24, 8, packet_buffer), 0x76CE88u);
    EXPECT_EQ(GetNBitWordFromBuffer(16, 8, packet_buffer), 0x76CEu);
    EXPECT_EQ(GetNBitWordFromBuffer(8, 8, packet_buffer), 0x76u);

    // first bit index = 12
    EXPECT_EQ(GetNBitWordFromBuffer(32, 12, packet_buffer), 0x6CE88204u);

    // first bit index = 16
    EXPECT_EQ(GetNBitWordFromBuffer(32, 16, packet_buffer), 0xCE88204Cu);

    // make sure it doesn't fall off the end; can use some printfs to double check this
    EXPECT_EQ(GetNBitWordFromBuffer(16, 32 * 3 + 16, packet_buffer), 0x504Du);
}

TEST(BufferUtils, SetNBitWordInBuffer) {
    uint32_t packet_buffer[4];
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x0000504Du;

    SetNBitWordInBuffer(8, 0xDEu, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0xDE76CE88u);

    // set with word that is too long
    SetNBitWordInBuffer(8, 0x1DEu, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0xDE76CE88u);

    // zero a byte
    SetNBitWordInBuffer(8, 0x00u, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0x0076CE88u);
    // set single bit
    SetNBitWordInBuffer(1, 0b1, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0x8076CE88u);

    // test clipping
    packet_buffer[0] = 0x00000000u;
    SetNBitWordInBuffer(24, 0xFFFFFFFFu, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0xFFFFFF00u);

    // basic wraparound
    packet_buffer[0] = 0x8D76CE88u;  // reset from last test
    SetNBitWordInBuffer(16, 0xBEEFu, 24, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0x8D76CEBEu);
    EXPECT_EQ(packet_buffer[1], 0xEF4C9072u);

    // wraparound with full word
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    SetNBitWordInBuffer(32, 0x0000FEEFu, 32 + 24, packet_buffer);
    EXPECT_EQ(packet_buffer[1], 0x204C9000u);
    EXPECT_EQ(packet_buffer[2], 0x00FEEF9Au);

    // make sure it doesn't fall off the end; can use some printfs to double check this
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x0000504Du;
    SetNBitWordInBuffer(24, 0xFFBEBEu, 32 * 3 + 8, packet_buffer);
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