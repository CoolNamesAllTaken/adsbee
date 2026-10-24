/**
 * Tests for AircraftDictionary's FixedPoolResource allocator.
 *
 * The core invariant under test: after any number of insert/erase cycles, the dictionary
 * can always accept up to kMaxNumAircraft live entries. A monotonic (non-reclaiming) allocator
 * would exhaust its pool after the first full fill and fail on the second cycle.
 */

#include "aircraft_dictionary.hh"
#include "gtest/gtest.h"

// Helper: build a unique ICAO address from a slot index, avoiding collisions.
static constexpr uint32_t SlotToICAO(uint16_t i) { return (static_cast<uint32_t>(i) + 1u) * 599u; }

/**
 * Fill the dictionary to capacity and verify every insert succeeds.
 * Returns false and adds a GTest failure if any insert fails.
 */
static bool FillDictionary(AircraftDictionary& dict) {
    for (uint16_t i = 0; i < AircraftDictionary::kMaxNumAircraft; ++i) {
        ModeSAircraft aircraft(SlotToICAO(i));
        if (!dict.InsertAircraft(aircraft)) {
            ADD_FAILURE() << "InsertAircraft failed at slot " << i << " (ICAO 0x" << std::hex << SlotToICAO(i) << ")";
            return false;
        }
    }
    return true;
}

/**
 * Remove every aircraft that was inserted by FillDictionary.
 * Returns false and adds a GTest failure if any removal fails.
 */
static bool DrainDictionary(AircraftDictionary& dict) {
    for (uint16_t i = 0; i < AircraftDictionary::kMaxNumAircraft; ++i) {
        if (!dict.RemoveAircraft(SlotToICAO(i))) {
            ADD_FAILURE() << "RemoveAircraft failed at slot " << i << " (ICAO 0x" << std::hex << SlotToICAO(i) << ")";
            return false;
        }
    }
    return true;
}

// ---------------------------------------------------------------------------
// Test: multiple full fill → drain cycles should all succeed.
//
// With the old monotonic_buffer_resource this fails on the second cycle because
// the pool memory is never reclaimed when aircraft are erased.
// ---------------------------------------------------------------------------
TEST(AircraftDictionaryAllocator, RepeatedFillDrainCycles) {
    AircraftDictionary dict;

    constexpr int kNumCycles = 3;
    for (int cycle = 0; cycle < kNumCycles; ++cycle) {
        ASSERT_EQ(dict.GetNumAircraft(), 0) << "dictionary not empty at start of cycle " << cycle;

        ASSERT_TRUE(FillDictionary(dict)) << "fill failed on cycle " << cycle;
        EXPECT_EQ(dict.GetNumAircraft(), AircraftDictionary::kMaxNumAircraft)
            << "wrong count after fill on cycle " << cycle;

        ASSERT_TRUE(DrainDictionary(dict)) << "drain failed on cycle " << cycle;
        EXPECT_EQ(dict.GetNumAircraft(), 0) << "wrong count after drain on cycle " << cycle;
    }
}

// ---------------------------------------------------------------------------
// Test: inserting beyond capacity must fail gracefully (nullptr / false),
// never fault, and leave the dictionary in a consistent state.
// ---------------------------------------------------------------------------
TEST(AircraftDictionaryAllocator, GracefulCapacityOverflow) {
    AircraftDictionary dict;
    ASSERT_TRUE(FillDictionary(dict));
    EXPECT_EQ(dict.GetNumAircraft(), AircraftDictionary::kMaxNumAircraft);

    // Commented out after adding automatic old aircraft removal to dictionary.
    // // Attempt to insert one more aircraft — must return nullptr without crashing.
    // ModeSAircraft overflow_aircraft(0xBEEFCAFE);
    // ModeSAircraft* result = dict.InsertAircraft(overflow_aircraft);
    // EXPECT_EQ(result, nullptr) << "InsertAircraft should return nullptr when dictionary is full";

    // // The dictionary should be unchanged.
    // EXPECT_EQ(dict.GetNumAircraft(), AircraftDictionary::kMaxNumAircraft);
    // EXPECT_FALSE(dict.ContainsAircraft(Aircraft::ICAOToUID(overflow_aircraft.icao_address,
    //                                                         Aircraft::kAircraftTypeModeS)));
}

// ---------------------------------------------------------------------------
// Test: partial remove followed by refill to capacity.
//
// Removes the lower half of the aircraft, then re-inserts them. The free-list
// pool must hand out the reclaimed slots so the dictionary stays at full capacity.
// ---------------------------------------------------------------------------
TEST(AircraftDictionaryAllocator, PartialRemoveAndRefill) {
    AircraftDictionary dict;
    ASSERT_TRUE(FillDictionary(dict));

    const uint16_t kHalf = AircraftDictionary::kMaxNumAircraft / 2;

    // Remove the lower half.
    for (uint16_t i = 0; i < kHalf; ++i) {
        ASSERT_TRUE(dict.RemoveAircraft(SlotToICAO(i))) << "RemoveAircraft failed at slot " << i;
    }
    EXPECT_EQ(dict.GetNumAircraft(), AircraftDictionary::kMaxNumAircraft - kHalf);

    // Re-insert the lower half — these must succeed (pool must have reclaimed the slots).
    for (uint16_t i = 0; i < kHalf; ++i) {
        ModeSAircraft aircraft(SlotToICAO(i));
        ASSERT_NE(dict.InsertAircraft(aircraft), nullptr) << "InsertAircraft failed after partial drain at slot " << i;
    }
    EXPECT_EQ(dict.GetNumAircraft(), AircraftDictionary::kMaxNumAircraft);

    // Commented out after adding automatic old aircraft removal to dictionary.
    // // An extra aircraft must still be rejected.
    // ModeSAircraft overflow_aircraft(0xDEAD1234);
    // EXPECT_EQ(dict.InsertAircraft(overflow_aircraft), nullptr);
}

// ---------------------------------------------------------------------------
// Test: overwriting an existing aircraft does not consume a new pool slot.
// ---------------------------------------------------------------------------
TEST(AircraftDictionaryAllocator, OverwriteDoesNotExhaustPool) {
    AircraftDictionary dict;
    ASSERT_TRUE(FillDictionary(dict));

    // Overwrite every aircraft many times — no new nodes should be allocated.
    for (int pass = 0; pass < 5; ++pass) {
        for (uint16_t i = 0; i < AircraftDictionary::kMaxNumAircraft; ++i) {
            ModeSAircraft aircraft(SlotToICAO(i));
            aircraft.emitter_category = ADSBTypes::kEmitterCategoryHeavy;
            ModeSAircraft* ptr = dict.InsertAircraft(aircraft);
            ASSERT_NE(ptr, nullptr) << "Overwrite failed at pass " << pass << " slot " << i;
            EXPECT_EQ(ptr->emitter_category, ADSBTypes::kEmitterCategoryHeavy);
        }
    }
    EXPECT_EQ(dict.GetNumAircraft(), AircraftDictionary::kMaxNumAircraft);
}

// host_test builds with the RP2040's dictionary size, host_test_fpu with the ESP32's.
TEST(AircraftDictionaryAllocator, SizeMatchesProcessor) {
#ifdef HAS_FPU
    EXPECT_EQ(AircraftDictionary::kMaxNumAircraft, 200);
#else
    EXPECT_EQ(AircraftDictionary::kMaxNumAircraft, 400);
#endif
}

// Offered three times its size in Mode S and UAT aircraft, a full dictionary keeps the newest ones and never rehashes.
TEST(AircraftDictionaryAllocator, FullDictionaryKeepsNewest) {
    for (int use_config = 0; use_config < 2; use_config++) {
        AircraftDictionary::AircraftDictionaryConfig config;
        AircraftDictionary dict_default;
        AircraftDictionary dict_config(config);
        AircraftDictionary& dict = use_config ? dict_config : dict_default;
        const size_t buckets = dict.dict.bucket_count();
        EXPECT_GE(buckets, AircraftDictionary::kMaxNumAircraft);

        const uint32_t kNumOffered = 3 * AircraftDictionary::kMaxNumAircraft;
        for (uint32_t i = 0; i < kNumOffered; i++) {
            uint32_t address = 0xBEE000 + i / 2;
            if (i % 2 == 0) {
                ModeSAircraft aircraft(address);
                aircraft.last_message_timestamp_ms = i + 1;
                ASSERT_NE(dict.InsertAircraft(aircraft), nullptr) << "Mode S insert " << i;
            } else {
                UATAircraft aircraft(address);
                aircraft.last_message_timestamp_ms = i + 1;
                ASSERT_NE(dict.InsertAircraft(aircraft), nullptr) << "UAT insert " << i;
            }
            ASSERT_LE(dict.GetNumAircraft(), AircraftDictionary::kMaxNumAircraft);
        }
        EXPECT_EQ(dict.GetNumAircraft(), AircraftDictionary::kMaxNumAircraft);
        EXPECT_EQ(dict.dict.bucket_count(), buckets);

        // Only the newest kMaxNumAircraft remain.
        for (const auto& [uid, entry] : dict.dict) {
            uint32_t t = std::visit([](const Aircraft& a) { return a.last_message_timestamp_ms; }, entry);
            EXPECT_GT(t, kNumOffered - AircraftDictionary::kMaxNumAircraft);
        }
    }
}

// Overflow warnings: at most one per interval, each with the evictions since the last one.
TEST(AircraftDictionaryAllocator, OverflowWarningRateLimited) {
    AircraftDictionary dict;
    ASSERT_TRUE(FillDictionary(dict));
    EXPECT_EQ(dict.TakeOverflowEvictionsToLog(1000), 0u);  // Full but nothing removed yet.

    uint32_t next_address = 0x100000;
    auto overflow = [&](uint32_t n) {
        for (uint32_t i = 0; i < n; i++) {
            ModeSAircraft aircraft(next_address++);
            ASSERT_NE(dict.InsertAircraft(aircraft), nullptr);
        }
    };
    overflow(5);
    EXPECT_EQ(dict.TakeOverflowEvictionsToLog(2000), 5u);
    overflow(7);
    EXPECT_EQ(dict.TakeOverflowEvictionsToLog(2001), 0u);
    EXPECT_EQ(dict.TakeOverflowEvictionsToLog(2000 + AircraftDictionary::kOverflowLogIntervalMs - 1), 0u);
    overflow(3);
    EXPECT_EQ(dict.TakeOverflowEvictionsToLog(2000 + AircraftDictionary::kOverflowLogIntervalMs), 10u);
    // Nothing removed since: no warning even after the interval.
    EXPECT_EQ(dict.TakeOverflowEvictionsToLog(2000 + 3 * AircraftDictionary::kOverflowLogIntervalMs), 0u);
    overflow(1);
    EXPECT_EQ(dict.TakeOverflowEvictionsToLog(2000 + 3 * AircraftDictionary::kOverflowLogIntervalMs + 1), 1u);

    // Update() takes the count and logs it.
    overflow(2);
    dict.Update(2000 + 5 * AircraftDictionary::kOverflowLogIntervalMs);
    EXPECT_EQ(dict.TakeOverflowEvictionsToLog(2000 + 7 * AircraftDictionary::kOverflowLogIntervalMs), 0u);
}
