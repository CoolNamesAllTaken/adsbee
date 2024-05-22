#include "gtest/gtest.h"
#include "aircraft_dictionary.hh"
#include "ads_b_packet.hh"
#include "decode_utils.hh"   // for location calculation utility functions
#include "hal_god_powers.hh" // for changing timestamp

TEST(AircraftDictionary, BasicInsertRemove)
{
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

TEST(AircraftDictionary, InsertThenRemoveTooMany)
{
    AircraftDictionary dictionary = AircraftDictionary();
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);

    Aircraft test_aircraft = Aircraft(0);
    test_aircraft.wake_vortex = Aircraft::WV_GLIDER_SAILPLANE;

    // Insert maximum number of aircraft.
    for (uint16_t i = 0; i < AircraftDictionary::kMaxNumAircraft; i++)
    {
        test_aircraft.icao_address = i * 599;
        EXPECT_TRUE(dictionary.InsertAircraft(test_aircraft));
        EXPECT_EQ(dictionary.GetNumAircraft(), i + 1);
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
    for (uint16_t i = 0; i < AircraftDictionary::kMaxNumAircraft; i++)
    {
        test_aircraft.icao_address = (AircraftDictionary::kMaxNumAircraft - 1 - i) * 599;
        EXPECT_TRUE(dictionary.RemoveAircraft(test_aircraft.icao_address));
        EXPECT_EQ(dictionary.GetNumAircraft(), AircraftDictionary::kMaxNumAircraft - i - 1);
    }

    // Removing a nonexistent aircraft with a previously valid ICAO address should fail.
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);
    EXPECT_FALSE(dictionary.RemoveAircraft(0));
}

TEST(AircraftDictionary, UseAircraftPtr)
{
    AircraftDictionary dictionary = AircraftDictionary();
    Aircraft *aircraft = dictionary.GetAircraftPtr(12345);
    EXPECT_TRUE(aircraft); // aircraft should have been automatically inserted just fine
    aircraft->wake_vortex = Aircraft::WV_GROUND_OBSTRUCTION;
    Aircraft aircraft_out;
    ASSERT_TRUE(dictionary.GetAircraft(12345, aircraft_out));
    ASSERT_EQ(aircraft_out.wake_vortex, Aircraft::WV_GROUND_OBSTRUCTION);
    aircraft->wake_vortex = Aircraft::WV_HEAVY;
    ASSERT_TRUE(dictionary.GetAircraft(12345, aircraft_out));
    ASSERT_EQ(aircraft_out.wake_vortex, Aircraft::WV_HEAVY);
}

TEST(AircraftDictionary, AccessFakeAircraft)
{
    AircraftDictionary dictionary = AircraftDictionary();
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);

    Aircraft test_aircraft = Aircraft(0);
    EXPECT_FALSE(dictionary.GetAircraft(0, test_aircraft));
}

TEST(AircraftDictionary, IngestAircraftIDMessage)
{
    AircraftDictionary dictionary = AircraftDictionary();
    ADSBPacket packet = ADSBPacket((char *)"8D76CE88204C9072CB48209A504D");
    EXPECT_TRUE(dictionary.IngestADSBPacket(packet));
    EXPECT_EQ(dictionary.GetNumAircraft(), 1);
    Aircraft aircraft;
    EXPECT_TRUE(dictionary.GetAircraft(0x76CE88, aircraft));
    EXPECT_EQ(aircraft.icao_address, 0x76CE88u);
    EXPECT_EQ(aircraft.transponder_capability, 5);
    EXPECT_EQ(aircraft.wake_vortex, Aircraft::WV_NO_CATEGORY_INFO);
    EXPECT_STREQ(aircraft.callsign, "SIA224");

    packet = ADSBPacket((char *)"8D7C7181215D01A08208204D8BF1");
    EXPECT_TRUE(dictionary.IngestADSBPacket(packet));
    EXPECT_EQ(dictionary.GetNumAircraft(), 2);
    EXPECT_TRUE(dictionary.GetAircraft(0x7C7181, aircraft));
    EXPECT_EQ(aircraft.icao_address, 0x7C7181u);
    EXPECT_EQ(aircraft.transponder_capability, 5);
    EXPECT_EQ(aircraft.wake_vortex, Aircraft::WV_LIGHT);
    EXPECT_STREQ(aircraft.callsign, "WPF");

    packet = ADSBPacket((char *)"8D7C7745226151A08208205CE9C2");
    EXPECT_TRUE(dictionary.IngestADSBPacket(packet));
    EXPECT_EQ(dictionary.GetNumAircraft(), 3);
    EXPECT_TRUE(dictionary.GetAircraft(0x7C7745, aircraft));
    EXPECT_EQ(aircraft.icao_address, 0x7C7745u);
    EXPECT_EQ(aircraft.transponder_capability, 5);
    EXPECT_EQ(aircraft.wake_vortex, Aircraft::WV_MEDIUM_1);
    EXPECT_STREQ(aircraft.callsign, "XUF");

    packet = ADSBPacket((char *)"8D7C80AD2358F6B1E35C60FF1925");
    EXPECT_TRUE(dictionary.IngestADSBPacket(packet));
    EXPECT_EQ(dictionary.GetNumAircraft(), 4);
    EXPECT_TRUE(dictionary.GetAircraft(0x7C80AD, aircraft));
    EXPECT_EQ(aircraft.icao_address, 0x7C80ADu);
    EXPECT_EQ(aircraft.transponder_capability, 5);
    EXPECT_EQ(aircraft.wake_vortex, Aircraft::WV_MEDIUM_2);
    EXPECT_STREQ(aircraft.callsign, "VOZ1851");

    packet = ADSBPacket((char *)"8D7C146525446074DF5820738E90");
    EXPECT_TRUE(dictionary.IngestADSBPacket(packet));
    EXPECT_EQ(dictionary.GetNumAircraft(), 5);
    EXPECT_TRUE(dictionary.GetAircraft(0x7C1465, aircraft));
    EXPECT_EQ(aircraft.icao_address, 0x7C1465u);
    EXPECT_EQ(aircraft.transponder_capability, 5);
    EXPECT_EQ(aircraft.wake_vortex, Aircraft::WV_HEAVY);
    EXPECT_STREQ(aircraft.callsign, "QFA475");
}

TEST(AircraftDictionary, IngestInvalidAircrfaftIDMessage)
{
    AircraftDictionary dictionary = AircraftDictionary();
    ADSBPacket packet = ADSBPacket((char *)"7D76CE88204C9072CB48209A504D");
    EXPECT_FALSE(dictionary.IngestADSBPacket(packet));
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);
}

TEST(decode_utils, calc_nl_cpr_from_lat)
{
    EXPECT_EQ(calc_nl_cpr_from_lat(0), 59);
    EXPECT_EQ(calc_nl_cpr_from_lat(87), 2);
    EXPECT_EQ(calc_nl_cpr_from_lat(-87), 2);
    EXPECT_EQ(calc_nl_cpr_from_lat(88), 1);
    EXPECT_EQ(calc_nl_cpr_from_lat(-88), 1);
}

TEST(Aircraft, SetCPRLatLon)
{
    Aircraft aircraft;
    EXPECT_FALSE(aircraft.position_valid);

    // Send n_lat_cpr out of bounds (bigger than 2^17 bits max value).
    EXPECT_FALSE(aircraft.SetCPRLatLon(0xFFFFFF, 53663, true));
    EXPECT_FALSE(aircraft.SetCPRLatLon(0xFFFFFF, 53663, false));
    // Send n_lon_cpr out of bounds (bigger than 2^17 bits max value).
    EXPECT_FALSE(aircraft.SetCPRLatLon(52455, 0xFFFFFF, false));
    EXPECT_FALSE(aircraft.SetCPRLatLon(52455, 0xFFFFFF, true));

    // Send two even packets at startup, no odd packets.
    aircraft = Aircraft(); // clear everything
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(578, 13425, false));
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(578, 4651, false));
    EXPECT_FALSE(aircraft.DecodePosition());
    EXPECT_FALSE(aircraft.position_valid);

    // Send two odd packets at startup, no even packets.
    aircraft = Aircraft(); // clear everything
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(236, 13425, true));
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(236, 857, true));
    EXPECT_FALSE(aircraft.DecodePosition());
    EXPECT_FALSE(aircraft.position_valid);

    // Send one odd packet and one even packet at startup.
    aircraft = Aircraft(); // clear everything
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(74158, 50194, true));
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(93000, 51372, false));
    EXPECT_TRUE(aircraft.DecodePosition());
    EXPECT_TRUE(aircraft.position_valid);
    EXPECT_NEAR(aircraft.latitude, 52.25720f, 1e-4); // even latitude
    EXPECT_NEAR(aircraft.longitude, 3.91937f, 1e-4); // longitude calculated from even latitude

    // Send one even packet and one odd packet at startup.
    aircraft = Aircraft(); // clear everything
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(93000, 51372, false));
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(74158, 50194, true));
    EXPECT_TRUE(aircraft.DecodePosition());
    EXPECT_TRUE(aircraft.position_valid);
    EXPECT_NEAR(aircraft.latitude, 52.26578f, 1e-4); // odd latitude
    // don't have a test value available for the longitude calculated from odd latitude

    // Straddle two position packets between different latitude
    aircraft = Aircraft(); // clear everything
    EXPECT_TRUE(aircraft.SetCPRLatLon(93006, 50194, true));
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(93000, 51372, false));
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.DecodePosition());
    inc_time_since_boot_ms();
    // Position established, now send the curveball.
    EXPECT_TRUE(aircraft.SetCPRLatLon(93000 - 5000, 50194, true));
    inc_time_since_boot_ms();
    EXPECT_FALSE(aircraft.DecodePosition());

    // EXPECT_NEAR(aircraft.latitude, 52.25720f, 1e-4);
    // EXPECT_NEAR(aircraft.longitude, 3.91937f, 1e-4);

    // Another test message.
    // aircraft = Aircraft(); // clear everything
    // inc_time_since_boot_ms();
    // EXPECT_TRUE(aircraft.SetCPRLatLon(74158, 50194, true));
    // inc_time_since_boot_ms();
    // EXPECT_TRUE(aircraft.SetCPRLatLon(93000, 51372, false));
    // EXPECT_TRUE(aircraft.position_valid);
    // EXPECT_FLOAT_EQ(aircraft.latitude, 52.25720f);
    // EXPECT_FLOAT_EQ(aircraft.longitude, 3.91937f);

    // Send even / odd latitude pair

    /** Test Longitude **/
}