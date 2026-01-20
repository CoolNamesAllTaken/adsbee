#include "aircraft_dictionary.hh"
#include "decode_utils.hh"  // for location calculation utility functions
#include "gtest/gtest.h"
#include "hal_god_powers.hh"  // for changing timestamp
#include "uat_packet.hh"

TEST(AircraftDictionary, IngestUATADSBPacket) {
    AircraftDictionary dictionary = AircraftDictionary();
    DecodedUATADSBPacket tpacket((char *)"00a66ef135445d525a0c0519119021204800");
    EXPECT_TRUE(tpacket.ReconstructWithoutFEC());
    EXPECT_EQ(tpacket.GetICAOAddress(), 0xA66EF1u);
    EXPECT_EQ(Aircraft::ICAOToUID(tpacket.GetICAOAddress(), Aircraft::kAircraftTypeUAT),
              0x10A66EF1u);  // UID is ICAO address with type shifted to the left.

    EXPECT_TRUE(tpacket.ReconstructWithoutFEC());
    EXPECT_TRUE(dictionary.IngestDecodedUATADSBPacket(tpacket));
    EXPECT_EQ(dictionary.GetNumAircraft(), 1);
    uint32_t aircraft_uid = Aircraft::ICAOToUID(tpacket.GetICAOAddress(), Aircraft::kAircraftTypeUAT);
    EXPECT_TRUE(dictionary.ContainsAircraft(aircraft_uid));

    UATAircraft aircraft;
    EXPECT_TRUE(dictionary.GetAircraft(aircraft_uid, aircraft));
}

TEST(AircraftDictionary, GetLowestAircraftPositionUAT) {
    AircraftDictionary dictionary = AircraftDictionary();
    float latitude_deg, longitude_deg;
    int32_t gnss_altitude_ft, baro_altitude_ft;

    // No aircraft in dictionary, should return false.
    EXPECT_FALSE(dictionary.GetLowestAircraftPosition(latitude_deg, longitude_deg, gnss_altitude_ft, baro_altitude_ft));
    EXPECT_EQ(dictionary.lowest_aircraft_entry, nullptr);

    // Add a UAT aircraft without GNSS altitude - should not be selected as lowest.
    UATAircraft aircraft1(0xA11111);
    aircraft1.latitude_deg = 37.0f;
    aircraft1.longitude_deg = -122.0f;
    aircraft1.baro_altitude_ft = 10000;
    aircraft1.WriteBitFlag(UATAircraft::BitFlag::kBitFlagPositionValid, true);
    aircraft1.WriteBitFlag(UATAircraft::BitFlag::kBitFlagBaroAltitudeValid, true);
    aircraft1.last_message_timestamp_ms = get_time_since_boot_ms();
    dictionary.InsertAircraft(aircraft1);

    // Update the dictionary to process the aircraft.
    dictionary.Update(get_time_since_boot_ms());

    // Still no valid GNSS altitude, so should return false.
    EXPECT_FALSE(dictionary.GetLowestAircraftPosition(latitude_deg, longitude_deg, gnss_altitude_ft, baro_altitude_ft));

    // Add a UAT aircraft with GNSS altitude at 3000ft.
    UATAircraft aircraft2(0xA22222);
    aircraft2.latitude_deg = 38.0f;
    aircraft2.longitude_deg = -121.0f;
    aircraft2.gnss_altitude_ft = 3000;
    aircraft2.baro_altitude_ft = 2900;
    aircraft2.WriteBitFlag(UATAircraft::BitFlag::kBitFlagPositionValid, true);
    aircraft2.WriteBitFlag(UATAircraft::BitFlag::kBitFlagGNSSAltitudeValid, true);
    aircraft2.WriteBitFlag(UATAircraft::BitFlag::kBitFlagBaroAltitudeValid, true);
    aircraft2.last_message_timestamp_ms = get_time_since_boot_ms();
    dictionary.InsertAircraft(aircraft2);

    // Update the dictionary.
    dictionary.Update(get_time_since_boot_ms());

    // Should now return the UAT aircraft with GNSS altitude.
    EXPECT_TRUE(dictionary.GetLowestAircraftPosition(latitude_deg, longitude_deg, gnss_altitude_ft, baro_altitude_ft));
    EXPECT_NEAR(latitude_deg, 38.0f, 0.0001f);
    EXPECT_NEAR(longitude_deg, -121.0f, 0.0001f);
    EXPECT_EQ(gnss_altitude_ft, 3000);
    EXPECT_EQ(baro_altitude_ft, 2900);

    // Add another UAT aircraft with lower GNSS altitude at 1500ft.
    UATAircraft aircraft3(0xA33333);
    aircraft3.latitude_deg = 39.0f;
    aircraft3.longitude_deg = -120.0f;
    aircraft3.gnss_altitude_ft = 1500;
    aircraft3.baro_altitude_ft = 1400;
    aircraft3.WriteBitFlag(UATAircraft::BitFlag::kBitFlagPositionValid, true);
    aircraft3.WriteBitFlag(UATAircraft::BitFlag::kBitFlagGNSSAltitudeValid, true);
    aircraft3.WriteBitFlag(UATAircraft::BitFlag::kBitFlagBaroAltitudeValid, true);
    aircraft3.last_message_timestamp_ms = get_time_since_boot_ms();
    dictionary.InsertAircraft(aircraft3);

    // Update the dictionary.
    dictionary.Update(get_time_since_boot_ms());

    // Should now return the lower UAT aircraft.
    EXPECT_TRUE(dictionary.GetLowestAircraftPosition(latitude_deg, longitude_deg, gnss_altitude_ft, baro_altitude_ft));
    EXPECT_NEAR(latitude_deg, 39.0f, 0.0001f);
    EXPECT_NEAR(longitude_deg, -120.0f, 0.0001f);
    EXPECT_EQ(gnss_altitude_ft, 1500);
    EXPECT_EQ(baro_altitude_ft, 1400);
}

TEST(AircraftDictionary, GetLowestAircraftPositionMixedModeSAndUAT) {
    AircraftDictionary dictionary = AircraftDictionary();
    float latitude_deg, longitude_deg;
    int32_t gnss_altitude_ft, baro_altitude_ft;

    // Add a Mode S aircraft with GNSS altitude at 4000ft.
    ModeSAircraft mode_s_aircraft(0x123456);
    mode_s_aircraft.latitude_deg = 37.0f;
    mode_s_aircraft.longitude_deg = -122.0f;
    mode_s_aircraft.gnss_altitude_ft = 4000;
    mode_s_aircraft.baro_altitude_ft = 3900;
    mode_s_aircraft.WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagPositionValid, true);
    mode_s_aircraft.WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagGNSSAltitudeValid, true);
    mode_s_aircraft.WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagBaroAltitudeValid, true);
    mode_s_aircraft.last_message_timestamp_ms = get_time_since_boot_ms();
    dictionary.InsertAircraft(mode_s_aircraft);

    // Add a UAT aircraft with GNSS altitude at 2000ft (lower than Mode S).
    UATAircraft uat_aircraft(0xA44444);
    uat_aircraft.latitude_deg = 38.0f;
    uat_aircraft.longitude_deg = -121.0f;
    uat_aircraft.gnss_altitude_ft = 2000;
    uat_aircraft.baro_altitude_ft = 1900;
    uat_aircraft.WriteBitFlag(UATAircraft::BitFlag::kBitFlagPositionValid, true);
    uat_aircraft.WriteBitFlag(UATAircraft::BitFlag::kBitFlagGNSSAltitudeValid, true);
    uat_aircraft.WriteBitFlag(UATAircraft::BitFlag::kBitFlagBaroAltitudeValid, true);
    uat_aircraft.last_message_timestamp_ms = get_time_since_boot_ms();
    dictionary.InsertAircraft(uat_aircraft);

    // Update the dictionary.
    dictionary.Update(get_time_since_boot_ms());

    // Should return the UAT aircraft since it has lower altitude.
    EXPECT_TRUE(dictionary.GetLowestAircraftPosition(latitude_deg, longitude_deg, gnss_altitude_ft, baro_altitude_ft));
    EXPECT_NEAR(latitude_deg, 38.0f, 0.0001f);
    EXPECT_NEAR(longitude_deg, -121.0f, 0.0001f);
    EXPECT_EQ(gnss_altitude_ft, 2000);
    EXPECT_EQ(baro_altitude_ft, 1900);

    // Add another Mode S aircraft with even lower GNSS altitude at 500ft.
    ModeSAircraft mode_s_aircraft2(0x234567);
    mode_s_aircraft2.latitude_deg = 39.0f;
    mode_s_aircraft2.longitude_deg = -120.0f;
    mode_s_aircraft2.gnss_altitude_ft = 500;
    mode_s_aircraft2.WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagPositionValid, true);
    mode_s_aircraft2.WriteBitFlag(ModeSAircraft::BitFlag::kBitFlagGNSSAltitudeValid, true);
    mode_s_aircraft2.last_message_timestamp_ms = get_time_since_boot_ms();
    dictionary.InsertAircraft(mode_s_aircraft2);

    // Update the dictionary.
    dictionary.Update(get_time_since_boot_ms());

    // Should now return the Mode S aircraft with 500ft altitude.
    EXPECT_TRUE(dictionary.GetLowestAircraftPosition(latitude_deg, longitude_deg, gnss_altitude_ft, baro_altitude_ft));
    EXPECT_NEAR(latitude_deg, 39.0f, 0.0001f);
    EXPECT_NEAR(longitude_deg, -120.0f, 0.0001f);
    EXPECT_EQ(gnss_altitude_ft, 500);
    EXPECT_EQ(baro_altitude_ft, INT32_MIN);  // No baro altitude available.
}