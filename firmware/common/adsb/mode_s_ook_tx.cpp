#include "mode_s_ook_tx.hh"

#include <cstring>  // for memset

#include "mode_s_packet.hh"  // for RawModeSPacket packet-length constants

namespace {

// Preamble pulse positions, in chip indices (0.5 us/chip): pulses at 0 / 1.0 / 3.5 / 4.5 us.
constexpr uint8_t kPreamblePulseChips[] = {0, 2, 7, 9};

// Sets a single chip (bit) to 1 in an MSB-first packed buffer. The buffer must be pre-zeroed.
inline void SetChip(uint8_t* buf, uint32_t chip_index) {
    buf[chip_index >> 3] |= static_cast<uint8_t>(0x80 >> (chip_index & 0x7));
}

}  // namespace

uint16_t ModeSOokChipStreamLenBytes(uint16_t msg_len_bits) {
    if (msg_len_bits != RawModeSPacket::kSquitterPacketLenBits &&
        msg_len_bits != RawModeSPacket::kExtendedSquitterPacketLenBits) {
        return 0;
    }
    uint32_t total_chips = kModeSOokPreambleLenChips + static_cast<uint32_t>(msg_len_bits) * kModeSOokChipsPerBit;
    return static_cast<uint16_t>((total_chips + 7) / 8);
}

uint16_t BuildModeSOokChipStream(const uint8_t* msg_bytes, uint16_t msg_len_bits, uint8_t* chips_out,
                                 uint16_t chips_out_size) {
    uint16_t out_len_bytes = ModeSOokChipStreamLenBytes(msg_len_bits);
    if (out_len_bytes == 0 || msg_bytes == nullptr || chips_out == nullptr || chips_out_size < out_len_bytes) {
        return 0;
    }

    memset(chips_out, 0, out_len_bytes);

    // Preamble: set the pulse chips (all other chips remain 0).
    for (uint8_t i = 0; i < sizeof(kPreamblePulseChips); i++) {
        SetChip(chips_out, kPreamblePulseChips[i]);
    }

    // Data: PPM, MSB first. bit == 1 -> pulse in the first half-chip ("10"); bit == 0 -> pulse in
    // the second half-chip ("01").
    uint32_t chip_index = kModeSOokPreambleLenChips;
    for (uint16_t bit = 0; bit < msg_len_bits; bit++) {
        uint8_t msg_bit = static_cast<uint8_t>((msg_bytes[bit >> 3] >> (7 - (bit & 0x7))) & 0x1);
        SetChip(chips_out, msg_bit ? chip_index : chip_index + 1);
        chip_index += kModeSOokChipsPerBit;
    }

    return out_len_bytes;
}
