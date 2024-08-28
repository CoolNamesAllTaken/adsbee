#include "aircraft_dictionary.hh"
#include "csbee_utils.hh"
#include "gtest/gtest.h"

TEST(CSBeeUtils, AircraftToCSBeeString) {
    char message[kCSBeeMessageStrMaxLen];
    Aircraft aircraft;
    aircraft.flags = UINT32_MAX;  // Set allll the flags.
    aircraft.last_seen_timestamp_ms = 1000;
    aircraft.transponder_capability = ADSBPacket::Capability::kCALevel2PlusTransponderOnSurfaceCanSetCA7;
    aircraft.icao_address = 0x123456;
    strcpy(aircraft.callsign, "ABCDEFG");
    aircraft.squawk = 01234, aircraft.airframe_type = Aircraft::AirframeType::kAirframeTypeGliderSailplane;
}