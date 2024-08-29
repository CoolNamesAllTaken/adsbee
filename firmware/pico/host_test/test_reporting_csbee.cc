#include "aircraft_dictionary.hh"
#include "csbee_utils.hh"
#include "gtest/gtest.h"

std::string_view GetNextToken(std::string_view* message_in = nullptr, char delimiter = ',') {
    static uint16_t token_start;
    static std::string_view* message;
    if (message_in != nullptr) {
        message = message_in;
        token_start = 0;
    }
    std::string_view token = message->substr(token_start, message->find(delimiter, token_start) - token_start);
    token_start += token.length() + 1;
    return token;
}

TEST(CSBeeUtils, AircraftToCSBeeString) {
    char message[kCSBeeMessageStrMaxLen];

    Aircraft aircraft;
    aircraft.flags = UINT32_MAX;  // Set allll the flags.
    aircraft.last_seen_timestamp_ms = 1000;
    aircraft.transponder_capability = ADSBPacket::Capability::kCALevel2PlusTransponderOnSurfaceCanSetCA7;
    aircraft.icao_address = 0x12345E;
    strcpy(aircraft.callsign, "ABCDEFG");
    aircraft.squawk = 01234;
    aircraft.airframe_type = Aircraft::AirframeType::kAirframeTypeGliderSailplane;
    aircraft.baro_altitude_ft = 1000;
    aircraft.gnss_altitude_ft = 997;
    aircraft.altitude_source = Aircraft::AltitudeSource::kAltitudeSourceBaro;
    aircraft.latitude_deg = -120.654321;
    aircraft.longitude_deg = -80.123456;
    aircraft.heading_deg = 300.5678;
    aircraft.velocity_kts = 123.45;
    aircraft.velocity_source = Aircraft::VelocitySource::kVelocitySourceAirspeedTrue;
    aircraft.vertical_rate_fpm = -200;
    aircraft.vertical_rate_source = Aircraft::VerticalRateSource::kVerticalRateSourceBaro;
    aircraft.navigation_integrity_category = static_cast<Aircraft::NICRadiusOfContainment>(0b1011);
    aircraft.navigation_integrity_category_baro = static_cast<Aircraft::NICBarometricAltitudeIntegrity>(0b1);
    aircraft.nac_velocity = static_cast<Aircraft::NACHorizontalVelocityError>(0b101);
    aircraft.nac_position = static_cast<Aircraft::NACEstimatedPositionUncertainty>(0b1101);
    aircraft.geometric_vertical_accuracy = static_cast<Aircraft::GVA>(0b11);
    aircraft.system_integrity_level = static_cast<Aircraft::SILProbabilityOfExceedingNICRadiusOfContainmnent>(
        Aircraft::kPOERCLessThanOrEqualTo1em5PerFlightHour);
    aircraft.system_design_assurance = static_cast<Aircraft::SystemDesignAssurance>(0b11);
    aircraft.gnss_antenna_offset_right_of_roll_axis_m = -6;
    aircraft.length_m = 10;
    aircraft.width_m = 20;
    aircraft.adsb_version = 3;

    WriteCSBeeAircraftMessageStr(message, aircraft);
    std::string_view message_view(message);
    std::string_view token = GetNextToken(&message_view);
    EXPECT_EQ(token.compare("#A:12345E"), 0);            // ICAO Address
    EXPECT_EQ(GetNextToken().compare("FFFFFFFF"), 0);    // Flags
    EXPECT_EQ(GetNextToken().compare("ABCDEFG"), 0);     // Callsign
    EXPECT_EQ(GetNextToken().compare("1234"), 0);        // Squawk
    EXPECT_EQ(GetNextToken().compare("-120.65432"), 0);  // Latitude
    EXPECT_EQ(GetNextToken().compare("-80.12345"), 0);   // Longitude
    EXPECT_EQ(GetNextToken().compare("1000"), 0);        // Baro Altitude
}