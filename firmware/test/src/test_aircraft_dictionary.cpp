#include "gtest/gtest.h"
#include "aircraft_dictionary.hh"
#include "ads_b_packet.hh"

TEST(AircraftDictionary, BasicInsertRemove) {
    AircraftDictionary dictionary = AircraftDictionary();
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);
    EXPECT_FALSE(dictionary.RemoveAircraft(12345));
    
    Aircraft test_aircraft = Aircraft(12345);
    test_aircraft.wake_vortex = Aircraft::WV_ROTORCRAFT;
    dictionary.InsertAircraft(test_aircraft);
    EXPECT_EQ(dictionary.GetNumAircraft(), 1);
    EXPECT_TRUE(dictionary.ContainsAircraft(test_aircraft.icao_address));

    Aircraft aircraft_out = Aircraft(0);
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

    Aircraft test_aircraft = Aircraft(0);
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
    EXPECT_TRUE(dictionary.GetAircraftPtr(test_aircraft.icao_address));

    // Adding a new aircraft should fail.
    test_aircraft.icao_address = 0xBEEB;
    EXPECT_FALSE(dictionary.InsertAircraft(test_aircraft));
    EXPECT_FALSE(dictionary.GetAircraftPtr(test_aircraft.icao_address));

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

TEST(AircraftDictionary, UseAircraftPtr) {
    AircraftDictionary dictionary = AircraftDictionary();
    Aircraft * aircraft = dictionary.GetAircraftPtr(12345);
    EXPECT_TRUE(aircraft); // aircraft should have been automatically inserted just fine
    aircraft->wake_vortex = Aircraft::WV_GROUND_OBSTRUCTION;
    Aircraft aircraft_out;
    ASSERT_TRUE(dictionary.GetAircraft(12345, aircraft_out));
    ASSERT_EQ(aircraft_out.wake_vortex, Aircraft::WV_GROUND_OBSTRUCTION);
    aircraft->wake_vortex = Aircraft::WV_HEAVY;
    ASSERT_TRUE(dictionary.GetAircraft(12345, aircraft_out));
    ASSERT_EQ(aircraft_out.wake_vortex, Aircraft::WV_HEAVY);
}

TEST(AircraftDictionary, AccessFakeAircraft) {
    AircraftDictionary dictionary = AircraftDictionary();
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);

    Aircraft test_aircraft = Aircraft(0);
    EXPECT_FALSE(dictionary.GetAircraft(0, test_aircraft));
}

TEST(AircraftDictionary, IngestAircraftIDMessage) {
    AircraftDictionary dictionary = AircraftDictionary();
    // ADSBPacket::packet = ADSBPacket({})
}