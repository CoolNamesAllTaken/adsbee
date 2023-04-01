#include "gtest/gtest.h"
#include "aircraft_dictionary.hh"

TEST(AircraftDictionary, BasicInsertRemove) {
    AircraftDictionary dictionary = AircraftDictionary();
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);
    EXPECT_FALSE(dictionary.RemoveAircraft(12345));
    
    Aircraft test_aircraft = Aircraft();
    test_aircraft.wake_vortex = Aircraft::WV_ROTORCRAFT;
    test_aircraft.icao_address = 12345;
    dictionary.InsertAircraft(test_aircraft);
    EXPECT_EQ(dictionary.GetNumAircraft(), 1);
    EXPECT_TRUE(dictionary.ContainsAircraft(test_aircraft.icao_address));

    Aircraft aircraft_out;
    EXPECT_NE(aircraft_out.icao_address, test_aircraft.icao_address);
    EXPECT_NE(aircraft_out.wake_vortex, test_aircraft.wake_vortex);
    EXPECT_TRUE(dictionary.GetAircraft(test_aircraft.icao_address, aircraft_out));
    EXPECT_EQ(aircraft_out.icao_address, test_aircraft.icao_address);
    EXPECT_EQ(aircraft_out.wake_vortex, test_aircraft.wake_vortex);

    EXPECT_TRUE(dictionary.RemoveAircraft(12345));
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);
}

TEST(AircraftDictionary, InsertThenRemoveTooMany) {
    AircraftDictionary dictionary = AircraftDictionary();
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);

    Aircraft test_aircraft = Aircraft();
    test_aircraft.wake_vortex = Aircraft::WV_GLIDER_SAILPLANE;

    // Insert maximum number of aircraft.
    for (uint16_t i = 0; i < AircraftDictionary::kMaxNumAircraft; i++) {
        test_aircraft.icao_address = i*599;
        EXPECT_TRUE(dictionary.InsertAircraft(test_aircraft));
        EXPECT_EQ(dictionary.GetNumAircraft(), i+1);
    }

    // Changing an existing aircraft should be fine.
    test_aircraft.icao_address = 3 * 599;
    EXPECT_TRUE(dictionary.InsertAircraft(test_aircraft));

    // Adding a new aircraft should fail.
    test_aircraft.icao_address = 0xBEEB;
    EXPECT_FALSE(dictionary.InsertAircraft(test_aircraft));

    // Remove all aircraft.
    for (uint16_t i = 0; i < AircraftDictionary::kMaxNumAircraft; i++) {
        test_aircraft.icao_address = (AircraftDictionary::kMaxNumAircraft-1-i)*599;
        EXPECT_TRUE(dictionary.RemoveAircraft(test_aircraft.icao_address));
        EXPECT_EQ(dictionary.GetNumAircraft(), AircraftDictionary::kMaxNumAircraft-i-1);
    }

    // Removing a nonexistent aircraft with a previously valid ICAO address should fail.
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);
    EXPECT_FALSE(dictionary.RemoveAircraft(0));
}

TEST(AircraftDictionary, AccessFakeAircraft) {
    AircraftDictionary dictionary = AircraftDictionary();
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);

    Aircraft test_aircraft;
    EXPECT_FALSE(dictionary.GetAircraft(0, test_aircraft));
}