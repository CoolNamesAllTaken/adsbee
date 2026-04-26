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
