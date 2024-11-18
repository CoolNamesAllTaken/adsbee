#include "aircraft_dictionary.hh"
#include "decode_utils.hh"  // for location calculation utility functions
#include "gtest/gtest.h"
#include "hal_god_powers.hh"  // for changing timestamp
#include "transponder_packet.hh"

constexpr float kLatDegCloseEnough = 0.001f;
constexpr float kLonDegCloseEnough = 0.0001f;
constexpr float kFloatCloseEnough = 0.0001f;  // FOr generic floats.

TEST(AircraftDictionary, BasicInsertRemove) {
    AircraftDictionary dictionary = AircraftDictionary();
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);
    EXPECT_FALSE(dictionary.RemoveAircraft(12345));

    Aircraft test_aircraft = Aircraft(12345);
    test_aircraft.category = Aircraft::kCategoryRotorcraft;
    dictionary.InsertAircraft(test_aircraft);
    EXPECT_EQ(dictionary.GetNumAircraft(), 1);
    EXPECT_TRUE(dictionary.ContainsAircraft(test_aircraft.icao_address));

    Aircraft aircraft_out = Aircraft(0);
    EXPECT_NE(aircraft_out.icao_address, test_aircraft.icao_address);
    EXPECT_NE(aircraft_out.category, test_aircraft.category);
    EXPECT_TRUE(dictionary.GetAircraft(test_aircraft.icao_address, aircraft_out));
    EXPECT_EQ(aircraft_out.icao_address, test_aircraft.icao_address);
    EXPECT_EQ(aircraft_out.category, test_aircraft.category);

    EXPECT_TRUE(dictionary.RemoveAircraft(12345));
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);
}

TEST(AircraftDictionary, InsertThenRemoveTooMany) {
    AircraftDictionary dictionary = AircraftDictionary();
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);

    Aircraft test_aircraft = Aircraft(0);
    test_aircraft.category = Aircraft::kCategoryGliderSailplane;

    // Insert maximum number of aircraft.
    for (uint16_t i = 0; i < AircraftDictionary::kMaxNumAircraft; i++) {
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
    for (uint16_t i = 0; i < AircraftDictionary::kMaxNumAircraft; i++) {
        test_aircraft.icao_address = (AircraftDictionary::kMaxNumAircraft - 1 - i) * 599;
        EXPECT_TRUE(dictionary.RemoveAircraft(test_aircraft.icao_address));
        EXPECT_EQ(dictionary.GetNumAircraft(), AircraftDictionary::kMaxNumAircraft - i - 1);
    }

    // Removing a nonexistent aircraft with a previously valid ICAO address should fail.
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);
    EXPECT_FALSE(dictionary.RemoveAircraft(0));
}

TEST(AircraftDictionary, UseAircraftPtr) {
    AircraftDictionary dictionary = AircraftDictionary();
    Aircraft *aircraft = dictionary.GetAircraftPtr(12345);
    EXPECT_TRUE(aircraft);  // aircraft should have been automatically inserted just fine
    aircraft->category = Aircraft::kCategoryGroundObstruction;
    Aircraft aircraft_out;
    ASSERT_TRUE(dictionary.GetAircraft(12345, aircraft_out));
    ASSERT_EQ(aircraft_out.category, Aircraft::kCategoryGroundObstruction);
    aircraft->category = Aircraft::kCategoryHeavy;
    ASSERT_TRUE(dictionary.GetAircraft(12345, aircraft_out));
    ASSERT_EQ(aircraft_out.category, Aircraft::kCategoryHeavy);
}

TEST(AircraftDictionary, AccessFakeAircraft) {
    AircraftDictionary dictionary = AircraftDictionary();
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);

    Aircraft test_aircraft = Aircraft(0);
    EXPECT_FALSE(dictionary.GetAircraft(0, test_aircraft));
}

TEST(AircraftDictionary, ApplyAircraftIDMessage) {
    AircraftDictionary dictionary = AircraftDictionary();
    DecodedTransponderPacket tpacket = DecodedTransponderPacket((char *)"8D76CE88204C9072CB48209A504D");
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_EQ(dictionary.GetNumAircraft(), 1);
    Aircraft aircraft;
    EXPECT_TRUE(dictionary.GetAircraft(0x76CE88, aircraft));
    EXPECT_EQ(aircraft.icao_address, 0x76CE88u);
    EXPECT_EQ(aircraft.transponder_capability, 5);
    EXPECT_EQ(aircraft.category, Aircraft::kCategoryNoCategoryInfo);
    EXPECT_STREQ(aircraft.callsign, "SIA224");

    tpacket = DecodedTransponderPacket((char *)"8D7C7181215D01A08208204D8BF1");
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_EQ(dictionary.GetNumAircraft(), 2);
    EXPECT_TRUE(dictionary.GetAircraft(0x7C7181, aircraft));
    EXPECT_EQ(aircraft.icao_address, 0x7C7181u);
    EXPECT_EQ(aircraft.transponder_capability, 5);
    EXPECT_EQ(aircraft.category, Aircraft::kCategoryLight);
    EXPECT_STREQ(aircraft.callsign, "WPF");

    tpacket = DecodedTransponderPacket((char *)"8D7C7745226151A08208205CE9C2");
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_EQ(dictionary.GetNumAircraft(), 3);
    EXPECT_TRUE(dictionary.GetAircraft(0x7C7745, aircraft));
    EXPECT_EQ(aircraft.icao_address, 0x7C7745u);
    EXPECT_EQ(aircraft.transponder_capability, 5);
    EXPECT_EQ(aircraft.category, Aircraft::kCategoryMedium1);
    EXPECT_STREQ(aircraft.callsign, "XUF");

    tpacket = DecodedTransponderPacket((char *)"8D7C80AD2358F6B1E35C60FF1925");
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_EQ(dictionary.GetNumAircraft(), 4);
    EXPECT_TRUE(dictionary.GetAircraft(0x7C80AD, aircraft));
    EXPECT_EQ(aircraft.icao_address, 0x7C80ADu);
    EXPECT_EQ(aircraft.transponder_capability, 5);
    EXPECT_EQ(aircraft.category, Aircraft::kCategoryMedium2);
    EXPECT_STREQ(aircraft.callsign, "VOZ1851");

    tpacket = DecodedTransponderPacket((char *)"8D7C146525446074DF5820738E90");
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_EQ(dictionary.GetNumAircraft(), 5);
    EXPECT_TRUE(dictionary.GetAircraft(0x7C1465, aircraft));
    EXPECT_EQ(aircraft.icao_address, 0x7C1465u);
    EXPECT_EQ(aircraft.transponder_capability, 5);
    EXPECT_EQ(aircraft.category, Aircraft::kCategoryHeavy);
    EXPECT_STREQ(aircraft.callsign, "QFA475");
}

TEST(AircraftDictionary, IngestInvalidAircrfaftIDMessage) {
    AircraftDictionary dictionary = AircraftDictionary();
    DecodedTransponderPacket tpacket = DecodedTransponderPacket((char *)"7D76CE88204C9072CB48209A504D");
    EXPECT_FALSE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_EQ(dictionary.GetNumAircraft(), 0);
}

TEST(decode_utils, CalcNLCPRFromLat) {
    EXPECT_EQ(CalcNLCPRFromLat(0), 59);
    EXPECT_EQ(CalcNLCPRFromLat(87), 2);
    EXPECT_EQ(CalcNLCPRFromLat(-87), 2);
    EXPECT_EQ(CalcNLCPRFromLat(88), 1);
    EXPECT_EQ(CalcNLCPRFromLat(-88), 1);
}

TEST(Aircraft, SetCPRLatLon) {
    Aircraft aircraft;
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagPositionValid));

    // Send n_lat_cpr out of bounds (bigger than 2^17 bits max value).
    EXPECT_FALSE(aircraft.SetCPRLatLon(0xFFFFFF, 53663, true));
    EXPECT_FALSE(aircraft.SetCPRLatLon(0xFFFFFF, 53663, false));
    // Send n_lon_cpr out of bounds (bigger than 2^17 bits max value).
    EXPECT_FALSE(aircraft.SetCPRLatLon(52455, 0xFFFFFF, false));
    EXPECT_FALSE(aircraft.SetCPRLatLon(52455, 0xFFFFFF, true));

    // Send two even packets at startup, no odd packets.
    aircraft = Aircraft();  // clear everything
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedPosition));
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(578, 13425, false));
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(578, 4651, false));
    EXPECT_FALSE(aircraft.DecodePosition());
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagPositionValid));

    // Send two odd packets at startup, no even packets.
    aircraft = Aircraft();  // clear everything
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(236, 13425, true));
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(236, 857, true));
    EXPECT_FALSE(aircraft.DecodePosition());
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagPositionValid));

    // Send one odd packet and one even packet at startup.
    aircraft = Aircraft();  // clear everything
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(74158, 50194, true));
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(93000, 51372, false));
    EXPECT_TRUE(aircraft.DecodePosition());
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagPositionValid));
    EXPECT_NEAR(aircraft.latitude_deg, 52.25720f, 1e-4);  // even latitude
    EXPECT_NEAR(aircraft.longitude_deg, 3.91937f, 1e-4);  // longitude calculated from even latitude

    // Send one even packet and one odd packet at startup.
    aircraft = Aircraft();  // clear everything
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(93000, 51372, false));
    inc_time_since_boot_ms();
    EXPECT_TRUE(aircraft.SetCPRLatLon(74158, 50194, true));
    EXPECT_TRUE(aircraft.DecodePosition());
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagPositionValid));
    EXPECT_NEAR(aircraft.latitude_deg, 52.26578f, 1e-4);  // odd latitude
    // don't have a test value available for the longitude calculated from odd latitude

    // Straddle two position packets between different latitude
    aircraft = Aircraft();  // clear everything
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

TEST(AircraftDictionary, ApplyAirbornePositionMessage) {
    AircraftDictionary dictionary = AircraftDictionary();
    DecodedTransponderPacket even_tpacket = DecodedTransponderPacket((char *)"8da6147f5859f18cdf4d244ac6fa");
    ASSERT_TRUE(even_tpacket.IsValid());
    DecodedTransponderPacket odd_tpacket = DecodedTransponderPacket((char *)"8da6147f585b05533e2ba73e43cb");
    ASSERT_TRUE(odd_tpacket.IsValid());

    ASSERT_EQ(dictionary.GetNumAircraft(), 0);

    // Set time since boot to something positive so packet ingestion time looks legit.
    set_time_since_boot_ms(1e3);

    // Ingest even packet.
    ASSERT_TRUE(dictionary.IngestDecodedTransponderPacket(even_tpacket));
    ASSERT_EQ(dictionary.GetNumAircraft(), 1);
    auto itr = dictionary.dict.begin();
    auto &aircraft = itr->second;

    // Aircraft should exist but not have its location filled out.
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIsAirborne));
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedPosition));
    ASSERT_EQ(aircraft.icao_address, (uint32_t)0xA6147F);
    EXPECT_FLOAT_EQ(aircraft.latitude_deg, 0.0f);
    EXPECT_FLOAT_EQ(aircraft.longitude_deg, 0.0f);
    // Altitude should be filled out.
    EXPECT_EQ(aircraft.altitude_source, Aircraft::AltitudeSource::kAltitudeSourceBaro);
    EXPECT_EQ(aircraft.baro_altitude_ft, 16975);

    inc_time_since_boot_ms(1e3);  // Simulate time passing between odd and even packet ingestion.

    // Ingest odd packet.
    ASSERT_TRUE(dictionary.IngestDecodedTransponderPacket(odd_tpacket));

    // Aircraft should now have a valid location.
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedPosition));
    ASSERT_EQ(aircraft.icao_address, 0xA6147Fu);
    EXPECT_NEAR(aircraft.latitude_deg, 20.326522568524894f, kLatDegCloseEnough);
    EXPECT_NEAR(aircraft.longitude_deg, -156.5328535600142f, kLonDegCloseEnough);
    // Altitude should be filled out.
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedBaroAltitude));
    EXPECT_EQ(aircraft.altitude_source, Aircraft::AltitudeSource::kAltitudeSourceBaro);
    EXPECT_EQ(aircraft.baro_altitude_ft, 17000);
}

// TODO: Add test case for ingesting Airborne Position message with GNSS altitude.

TEST(AircraftDictionary, IngestAirborneVelocityMessage) {
    AircraftDictionary dictionary = AircraftDictionary();
    DecodedTransponderPacket tpacket = DecodedTransponderPacket((char *)"8dae56bc99246508b8080b6c230f");
    ASSERT_TRUE(tpacket.IsValid());
    ADSBPacket packet = ADSBPacket(tpacket);
    ASSERT_EQ(packet.GetTypeCodeEnum(), ADSBPacket::TypeCode::kTypeCodeAirborneVelocities);

    // Ingest the airborne velocities packet.
    ASSERT_TRUE(dictionary.IngestADSBPacket(packet));
    ASSERT_EQ(dictionary.GetNumAircraft(), 1);
    auto itr = dictionary.dict.begin();
    auto &aircraft = itr->second;  // NOTE: Aircraft is a mutable reference until we get to Message A!

    // Aircraft should now have velocities populated.
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedTrack));
    EXPECT_NEAR(aircraft.direction_deg, 304.2157021324374, kFloatCloseEnough);
    // Velocity should actually evaluate to 120 when evaluated with doubles, but there is some float error with the sqrt
    // that I think gets pretty nasty.
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedHorizontalVelocity));
    EXPECT_NEAR(aircraft.velocity_kts, 120.930, 0.01);
    EXPECT_EQ(aircraft.velocity_source, Aircraft::VelocitySource::kVelocitySourceGroundSpeed);
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedVerticalVelocity));
    EXPECT_NEAR(aircraft.vertical_rate_fpm, -64.0f, kFloatCloseEnough);
    EXPECT_EQ(aircraft.vertical_rate_source, Aircraft::VerticalRateSource::kVerticalRateSourceBaro);

    // Test Message A from https://mode-s.org/decode/content/ads-b/5-airborne-velocity.html
    tpacket = DecodedTransponderPacket((char *)"8D485020994409940838175B284F");
    ASSERT_TRUE(tpacket.IsValid());
    packet = ADSBPacket(tpacket);
    ASSERT_EQ(packet.GetTypeCodeEnum(), ADSBPacket::TypeCode::kTypeCodeAirborneVelocities);
    ASSERT_TRUE(dictionary.IngestADSBPacket(packet));
    uint32_t message_a_icao = 0x485020;
    ASSERT_TRUE(dictionary.ContainsAircraft(message_a_icao));
    ASSERT_TRUE(dictionary.GetAircraft(message_a_icao, aircraft));  // NOTE: Aircraft is read-only now!

    // Check values for Message A
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedVerticalVelocity));
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedHorizontalVelocity));
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedTrack));
    EXPECT_EQ(aircraft.vertical_rate_fpm, -832);
    EXPECT_EQ(aircraft.velocity_source, Aircraft::VelocitySource::kVelocitySourceGroundSpeed);
    EXPECT_NEAR(aircraft.direction_deg, 182.88f, 0.01);
    EXPECT_NEAR(aircraft.velocity_kts, 159.20f, 0.01);

    // Test altitude difference between baro and GNSS altitude for Message A by re-ingesting.
    Aircraft *aircraft_ptr = dictionary.GetAircraftPtr(0x485020);
    aircraft_ptr->baro_altitude_ft = 2000;
    aircraft_ptr->altitude_source = Aircraft::AltitudeSource::kAltitudeSourceBaro;
    // Re-ingest message A to make sure the GNSS altitude gets corrected.
    ASSERT_TRUE(dictionary.IngestADSBPacket(packet));
    EXPECT_FALSE(aircraft_ptr->HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedBaroAltitude));
    EXPECT_TRUE(aircraft_ptr->HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedGNSSAltitude));
    ASSERT_EQ(aircraft_ptr->gnss_altitude_ft, 2000 + 550);  // GNSS altitude is 550ft above baro altitude.

    // Test Message B from https://mode-s.org/decode/content/ads-b/5-airborne-velocity.html
    tpacket = DecodedTransponderPacket((char *)"8DA05F219B06B6AF189400CBC33F");
    ASSERT_TRUE(tpacket.IsValid());
    packet = ADSBPacket(tpacket);
    ASSERT_EQ(packet.GetTypeCodeEnum(), ADSBPacket::TypeCode::kTypeCodeAirborneVelocities);
    ASSERT_TRUE(dictionary.IngestADSBPacket(packet));
    uint32_t message_b_icao = 0xA05F21;
    ASSERT_TRUE(dictionary.ContainsAircraft(message_b_icao));
    ASSERT_TRUE(dictionary.GetAircraft(message_b_icao, aircraft));

    // Check values for Message B
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedVerticalVelocity));
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedHorizontalVelocity));
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagUpdatedTrack));
    EXPECT_EQ(aircraft.vertical_rate_fpm, -2304);
    EXPECT_EQ(aircraft.velocity_source, Aircraft::VelocitySource::kVelocitySourceAirspeedTrue);
    EXPECT_NEAR(aircraft.direction_deg, 243.98f, 0.01);
    EXPECT_NEAR(aircraft.velocity_kts, 375.0f, 0.01);
}

TEST(AircraftDictionary, IngestModeC) {
    // Try ingesting a Mode C packet that's marked as valid so that it doesn't require a cross-check with the
    // dictionary.
    AircraftDictionary dictionary = AircraftDictionary();
    DecodedTransponderPacket tpacket = DecodedTransponderPacket((char *)"200006A2DE8B1C");
    EXPECT_EQ(tpacket.GetICAOAddress(), 0x7C1B28u);
    dictionary.InsertAircraft(Aircraft(0x7C1B28u));  // Put aircraft in the dictionary so the packet can be ingested.
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_TRUE(dictionary.ContainsAircraft(0x7C1B28u));

    // Check that the aircraft has the right altitude.
    Aircraft aircraft;
    EXPECT_TRUE(dictionary.GetAircraft(0x7C1B28u, aircraft));
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIdent));
    EXPECT_EQ(aircraft.baro_altitude_ft, 10000);
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIsAirborne));
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIdent));
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagAlert));

    // Ingest a Mode C packet with an alert and ident.
    tpacket = DecodedTransponderPacket((char *)"24000E3956BBA1");
    // Add aircraft to dictioanry so packet can be ingested.
    dictionary.InsertAircraft(Aircraft(tpacket.GetICAOAddress()));
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_TRUE(dictionary.GetAircraft(0xD3CCBFu, aircraft));
    EXPECT_EQ(aircraft.baro_altitude_ft, 22025);
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIsAirborne));
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIdent));
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagAlert));

    // Ingest a Mode C packet with aircraft on the ground.
    tpacket = DecodedTransponderPacket((char *)"210000992F8C48");
    // Add aircraft to dictioanry so packet can be ingested.
    dictionary.InsertAircraft(Aircraft(tpacket.GetICAOAddress()));
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_TRUE(dictionary.GetAircraft(0x7C7539u, aircraft));
    EXPECT_EQ(aircraft.baro_altitude_ft, 25);
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIsAirborne));
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIdent));
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagAlert));
}

TEST(AircraftDictionary, IngestModeA) {
    // Ingest a Mode A packet with an alert and ident.
    AircraftDictionary dictionary = AircraftDictionary();
    DecodedTransponderPacket tpacket = DecodedTransponderPacket((char *)"2C0006A2DEE500");
    // Add aircraft to dictioanry so packet can be ingested.
    dictionary.InsertAircraft(Aircraft(tpacket.GetICAOAddress()));
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    Aircraft aircraft;
    EXPECT_TRUE(dictionary.GetAircraft(0x739EE9u, aircraft));
    EXPECT_EQ(aircraft.squawk, 06520u);
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagAlert));
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIdent));

    // Ingest a Mode A packet with an ident but no alert.
    tpacket = DecodedTransponderPacket((char *)"2D0006A2DEE500");
    // Add aircraft to dictioanry so packet can be ingested.
    dictionary.InsertAircraft(Aircraft(tpacket.GetICAOAddress()));
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_TRUE(dictionary.GetAircraft(0x5863BAu, aircraft));
    EXPECT_EQ(aircraft.squawk, 06520u);
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagAlert));
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIdent));

    // Ingest a Mode A packet with no ident and no alert. Aircraft is airborne.
    tpacket = DecodedTransponderPacket((char *)"28000D08CEE4C5");
    // Add aircraft to dictioanry so packet can be ingested.
    dictionary.InsertAircraft(Aircraft(tpacket.GetICAOAddress()));
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_TRUE(dictionary.GetAircraft(0xA8BBE7u, aircraft));
    EXPECT_EQ(aircraft.squawk, 01260);
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagAlert));
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIdent));
    EXPECT_TRUE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIsAirborne));

    // Ingest a Mode A packet with no ident and no alert. Aircraft is on ground.
    tpacket = DecodedTransponderPacket((char *)"29001E0D3CB4BF");
    // Add aircraft to dictioanry so packet can be ingested.
    dictionary.InsertAircraft(Aircraft(tpacket.GetICAOAddress()));
    EXPECT_TRUE(dictionary.IngestDecodedTransponderPacket(tpacket));
    EXPECT_TRUE(dictionary.GetAircraft(0x7C1471u, aircraft));
    EXPECT_EQ(aircraft.squawk, 03236);
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagAlert));
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIdent));
    EXPECT_FALSE(aircraft.HasBitFlag(Aircraft::BitFlag::kBitFlagIsAirborne));
}

TEST(AircraftDictionary, StatsToJSON) {
    AircraftDictionary::Stats stats = {.raw_squitter_frames = 10,
                                       .valid_squitter_frames = 7,
                                       .raw_extended_squitter_frames = 30,
                                       .valid_extended_squitter_frames = 16,
                                       .demods_1090 = 50,
                                       .raw_squitter_frames_by_source = {2, 3, 5},
                                       .valid_squitter_frames_by_source = {1, 2, 4},
                                       .raw_extended_squitter_frames_by_source = {10, 11, 9},
                                       .valid_extended_squitter_frames_by_source = {3, 5, 8},
                                       .demods_1090_by_source = {19, 10, 21}};
    char buf[AircraftDictionary::Stats::kStatsJSONMaxLen] = {'\0'};
    char * expected_result =
        (char *)"{ \"raw_squitter_frames\": 10, \
\"valid_squitter_frames\": 7, \
\"raw_extended_squitter_frames\": 30, \
\"valid_extended_squitter_frames\": 16, \
\"demods_1090\": 50, \
\"raw_squitter_frames_by_source\": [2, 3, 5], \
\"valid_squitter_frames_by_source\": [1, 2, 4], \
\"raw_extended_squitter_frames_by_source\": [10, 11, 9], \
\"valid_extended_squitter_frames_by_source\": [3, 5, 8], \
\"demods_1090_by_source\": [19, 10, 21] \
}";
    EXPECT_EQ(stats.ToJSON(buf, AircraftDictionary::Stats::kStatsJSONMaxLen), strlen(expected_result));
    EXPECT_STREQ(buf, expected_result);
}

TEST(Aircraft, AircraftStats) {
    Aircraft aircraft;
    aircraft.IncrementNumFramesReceived();
    EXPECT_EQ(aircraft.stats.valid_extended_squitter_frames + aircraft.stats.valid_squitter_frames, 0);
    aircraft.UpdateStats();
    EXPECT_EQ(aircraft.stats.valid_extended_squitter_frames + aircraft.stats.valid_squitter_frames, 1);
    EXPECT_EQ(aircraft.stats.valid_extended_squitter_frames, 0);
    EXPECT_EQ(aircraft.stats.valid_squitter_frames, 1);
    aircraft.IncrementNumFramesReceived(false);
    aircraft.IncrementNumFramesReceived(true);
    aircraft.UpdateStats();
    EXPECT_EQ(aircraft.stats.valid_extended_squitter_frames + aircraft.stats.valid_squitter_frames, 2);
    EXPECT_EQ(aircraft.stats.valid_extended_squitter_frames, 1);
    EXPECT_EQ(aircraft.stats.valid_squitter_frames, 1);
}