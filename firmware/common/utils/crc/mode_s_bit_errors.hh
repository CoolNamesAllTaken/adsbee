#pragma once

// Finds the one or two bit errors that explain a Mode S CRC-24 syndrome. Bit indices count from the first transmitted
// bit. At 112 bits the code's minimum distance is 6, so a one or two bit solution is unique when it exists.

#include <cstdint>

#include "mode_s_single_bit_filter.hh"  // kBitSyndromes.

// The pair filter, read for every tracked aircraft, lives in RAM: a flash cache miss costs more than the lookup. The
// 64 kB pair table stays in flash.
#ifdef ON_PICO
#include "pico.h"
#define MODE_S_BIT_ERRORS_RAM_TABLE __not_in_flash("mode_s_bit_errors_tables")
#elif defined(ON_TI)
#define MODE_S_BIT_ERRORS_RAM_TABLE __attribute__((section(".data.mode_s_bit_errors_tables")))
#else
#define MODE_S_BIT_ERRORS_RAM_TABLE
#endif

namespace ModeSBitErrors {

static constexpr uint16_t kFrameLenBits = ModeSSingleBitFilter::kFrameLenBits;
static constexpr uint16_t kSlotBits = 8;
static constexpr uint16_t kNumSlots = 1 << kSlotBits;

// Fibonacci hashing: syndromes are linear in the error bits, so plain shifts and XORs cluster them.
constexpr uint32_t HashSlot(uint32_t syndrome, uint16_t slot_bits) {
    return static_cast<uint32_t>(syndrome * 0x9E3779B1u) >> (32 - slot_bits);
}

// Open addressing hash of the single bit syndromes: syndrome | (bit + 1) << 24, 0 for an empty slot.
struct Table {
    uint32_t slot[kNumSlots];
};
constexpr uint32_t SlotOf(uint32_t syndrome) { return HashSlot(syndrome, kSlotBits); }
constexpr Table MakeTable() {
    Table t{};
    for (uint16_t i = 0; i < kFrameLenBits; i++) {
        uint32_t syndrome = ModeSSingleBitFilter::kBitSyndromes.v[i];
        uint32_t s = SlotOf(syndrome);
        while (t.slot[s] != 0) {
            s = (s + 1) & (kNumSlots - 1);
        }
        t.slot[s] = syndrome | static_cast<uint32_t>(i + 1) << 24;
    }
    return t;
}
// A template, so the table is only built by the targets that use it, once.
template <typename T = void>
const Table& GetTable() {
    static constexpr Table kTable = MakeTable();
    return kTable;
}

/**
 * Index of the bit of a 112 bit frame whose error gives this syndrome, or -1.
 */
inline int16_t FindBit112(uint32_t syndrome) {
    const Table& table = GetTable();
    for (uint32_t s = SlotOf(syndrome);; s = (s + 1) & (kNumSlots - 1)) {
        uint32_t entry = table.slot[s];
        if (entry == 0) {
            return -1;
        }
        if ((entry & 0xFFFFFF) == syndrome) {
            return static_cast<int16_t>(entry >> 24) - 1;
        }
    }
}

/**
 * Syndrome of an error in bit i of a len_bits frame. A short frame's syndromes are those of a long frame's last bits.
 */
constexpr uint32_t BitSyndrome(uint16_t i, uint16_t len_bits) {
    return ModeSSingleBitFilter::kBitSyndromes.v[i + kFrameLenBits - len_bits];
}

/**
 * Index of the bit (first_bit or later) of a len_bits frame whose error gives this syndrome, or -1.
 */
inline int16_t FindBit(uint32_t syndrome, uint16_t len_bits, uint16_t first_bit) {
    int16_t i = FindBit112(syndrome);
    if (i < 0) {
        return -1;
    }
    i -= kFrameLenBits - len_bits;
    return i >= static_cast<int16_t>(first_bit) ? i : -1;
}

// Open addressing hash of the two bit syndromes, all distinct at 112 bits: syndrome | (first bit + 1) << 24.
static constexpr uint16_t kPairSlotBits = 14;
static constexpr uint32_t kNumPairSlots = 1 << kPairSlotBits;  // 6,216 pairs.
struct PairTable {
    uint32_t slot[kNumPairSlots];
};
constexpr uint32_t PairSlotOf(uint32_t syndrome) { return HashSlot(syndrome, kPairSlotBits); }
constexpr PairTable MakePairTable() {
    PairTable t{};
    for (uint16_t a = 0; a < kFrameLenBits; a++) {
        for (uint16_t b = a + 1; b < kFrameLenBits; b++) {
            uint32_t syndrome = ModeSSingleBitFilter::kBitSyndromes.v[a] ^ ModeSSingleBitFilter::kBitSyndromes.v[b];
            uint32_t s = PairSlotOf(syndrome);
            while (t.slot[s] != 0) {
                s = (s + 1) & (kNumPairSlots - 1);
            }
            t.slot[s] = syndrome | static_cast<uint32_t>(a + 1) << 24;
        }
    }
    return t;
}
template <typename T = void>
const PairTable& GetPairTable() {
    static constexpr PairTable kPairTable = MakePairTable();
    return kPairTable;
}

// One bit per hash of the two bit syndromes. A clear bit means the syndrome is no two bit error (about 9 % pass).
static constexpr uint16_t kPairFilterBits = 16;
struct PairFilter {
    uint32_t bits[(1u << kPairFilterBits) / 32];
    constexpr bool MayMatch(uint32_t syndrome) const {
        uint32_t h = HashSlot(syndrome, kPairFilterBits);
        return (bits[h >> 5] >> (h & 31)) & 1u;
    }
};
constexpr PairFilter MakePairFilter() {
    PairFilter f{};
    for (uint16_t a = 0; a < kFrameLenBits; a++) {
        for (uint16_t b = a + 1; b < kFrameLenBits; b++) {
            uint32_t h = HashSlot(ModeSSingleBitFilter::kBitSyndromes.v[a] ^ ModeSSingleBitFilter::kBitSyndromes.v[b],
                                  kPairFilterBits);
            f.bits[h >> 5] |= 1u << (h & 31);
        }
    }
    return f;
}
// GCC 13 (the TI toolchain) ignores section attributes in templates, so there it's a plain inline function.
#ifdef ON_TI
inline const PairFilter& GetPairFilter() {
#else
template <typename T = void>
const PairFilter& GetPairFilter() {
#endif
    MODE_S_BIT_ERRORS_RAM_TABLE static constexpr PairFilter kPairFilter = MakePairFilter();
    return kPairFilter;
}

/**
 * Whether a syndrome may be a one or two bit error. Cheap check before Find().
 */
inline bool MayBeOneOrTwoBitError(uint32_t syndrome) {
    return ModeSSingleBitFilter::kFilter.MayMatch(syndrome) || GetPairFilter().MayMatch(syndrome);
}

/**
 * Finds one or two bit errors, at index first_bit or later, that give this syndrome in a len_bits frame (56 or 112).
 * @param[out] bits Error positions, ascending.
 * @retval Number of bits in the error (1 or 2), 0 if no such error exists or max_bits is too small.
 */
inline uint16_t Find(uint32_t syndrome, uint16_t len_bits, uint16_t first_bit, uint16_t max_bits, uint16_t bits[2]) {
    if (syndrome == 0 || max_bits == 0) {
        return 0;
    }
    int16_t i = FindBit(syndrome, len_bits, first_bit);
    if (i >= 0) {
        bits[0] = static_cast<uint16_t>(i);
        return 1;
    }
    if (max_bits < 2) {
        return 0;
    }
    const PairTable& table = GetPairTable();
    for (uint32_t s = PairSlotOf(syndrome);; s = (s + 1) & (kNumPairSlots - 1)) {
        uint32_t entry = table.slot[s];
        if (entry == 0) {
            return 0;
        }
        if ((entry & 0xFFFFFF) != syndrome) {
            continue;
        }
        int16_t a = static_cast<int16_t>(entry >> 24) - 1;
        int16_t b = FindBit112(syndrome ^ ModeSSingleBitFilter::kBitSyndromes.v[a]);
        int16_t offset = kFrameLenBits - len_bits;
        if (a - offset < static_cast<int16_t>(first_bit) || b < 0) {
            return 0;
        }
        bits[0] = static_cast<uint16_t>(a - offset);
        bits[1] = static_cast<uint16_t>(b - offset);
        return 2;
    }
}

}  // namespace ModeSBitErrors
