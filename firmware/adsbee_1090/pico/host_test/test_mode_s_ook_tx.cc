#include <cstring>

#include "crc.hh"
#include "gtest/gtest.h"
#include "mode_s_ook_tx.hh"
#include "mode_s_packet.hh"

namespace {
// Reads a single chip (bit) from an MSB-first packed buffer.
uint8_t GetChip(const uint8_t* buf, uint32_t idx) { return (buf[idx >> 3] >> (7 - (idx & 0x7))) & 0x1; }
}  // namespace

TEST(ModeSOokTx, ChipStreamLength) {
    EXPECT_EQ(ModeSOokChipStreamLenBytes(56), 16);   // 16 preamble + 56*2 = 128 chips = 16 bytes.
    EXPECT_EQ(ModeSOokChipStreamLenBytes(112), 30);  // 16 preamble + 112*2 = 240 chips = 30 bytes.
    EXPECT_EQ(ModeSOokChipStreamLenBytes(0), 0);
    EXPECT_EQ(ModeSOokChipStreamLenBytes(57), 0);
}

TEST(ModeSOokTx, Preamble) {
    uint8_t msg[14] = {0};
    uint8_t chips[30] = {0};
    ASSERT_EQ(BuildModeSOokChipStream(msg, 112, chips, sizeof(chips)), 30);
    // 8 us Mode S preamble: pulses at chips 0/2/7/9 -> 1010'0001'0100'0000 = {0xA1, 0x40}.
    EXPECT_EQ(chips[0], 0xA1);
    EXPECT_EQ(chips[1], 0x40);
}

TEST(ModeSOokTx, PpmAllZerosAllOnes) {
    // All-zero data bits -> each bit encodes as "01" -> 0x55 after the 2-byte preamble.
    uint8_t msg_zero[7] = {0};
    uint8_t chips[16] = {0};
    ASSERT_EQ(BuildModeSOokChipStream(msg_zero, 56, chips, sizeof(chips)), 16);
    for (int i = 2; i < 16; i++) EXPECT_EQ(chips[i], 0x55) << "byte " << i;

    // All-one data bits -> each bit encodes as "10" -> 0xAA.
    uint8_t msg_one[7];
    memset(msg_one, 0xFF, sizeof(msg_one));
    uint8_t chips_one[16] = {0};
    ASSERT_EQ(BuildModeSOokChipStream(msg_one, 56, chips_one, sizeof(chips_one)), 16);
    for (int i = 2; i < 16; i++) EXPECT_EQ(chips_one[i], 0xAA) << "byte " << i;
}

TEST(ModeSOokTx, BufferTooSmall) {
    uint8_t msg[14] = {0};
    uint8_t chips[10] = {0};
    EXPECT_EQ(BuildModeSOokChipStream(msg, 112, chips, sizeof(chips)), 0);
}

// Build a DF17 extended squitter with a valid appended CRC, encode to the OOK chip stream, decode
// the PPM back to bytes, and confirm the CRC syndrome is zero — i.e. the on-air waveform carries a
// packet any Mode S receiver would accept.
TEST(ModeSOokTx, RoundTripExtendedSquitterCrc) {
    uint8_t packet[14] = {0x8D, 0x48, 0x41, 0x75, 0x58, 0x2F, 0x38, 0x2E, 0x39, 0x4A, 0x51, 0, 0, 0};
    uint32_t crc = crc24(packet, 11);
    packet[11] = (crc >> 16) & 0xFF;
    packet[12] = (crc >> 8) & 0xFF;
    packet[13] = crc & 0xFF;
    ASSERT_EQ(crc24_syndrome(packet, 14), 0u);  // Our appended CRC yields a zero syndrome.

    uint8_t chips[30] = {0};
    ASSERT_EQ(BuildModeSOokChipStream(packet, 112, chips, sizeof(chips)), 30);

    // Decode PPM: skip the 16-chip preamble; each bit is 2 chips ("10" -> 1, "01" -> 0).
    uint8_t decoded[14] = {0};
    for (uint16_t bit = 0; bit < 112; bit++) {
        uint32_t c = kModeSOokPreambleLenChips + bit * kModeSOokChipsPerBit;
        uint8_t first = GetChip(chips, c);
        uint8_t second = GetChip(chips, c + 1);
        ASSERT_NE(first, second) << "invalid PPM cell at bit " << bit;  // exactly one pulse per cell
        if (first) decoded[bit >> 3] |= (0x80 >> (bit & 0x7));
    }
    EXPECT_EQ(memcmp(decoded, packet, 14), 0);
    EXPECT_EQ(crc24_syndrome(decoded, 14), 0u);
}
