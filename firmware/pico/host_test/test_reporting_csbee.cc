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

    ModeSAircraft aircraft;
    aircraft.flags = UINT32_MAX;  // Set allll the flags.
    aircraft.last_message_timestamp_ms = 1000;
    aircraft.last_message_signal_strength_dbm = -75;
    aircraft.last_message_signal_quality_db = 2;
    aircraft.metrics.valid_squitter_frames = 1;
    aircraft.metrics.valid_extended_squitter_frames = 3;
    aircraft.transponder_capability = ADSBPacket::Capability::kCALevel2PlusTransponderOnSurfaceCanSetCA7;
    aircraft.icao_address = 0x12345E;
    strcpy(aircraft.callsign, "ABCDEFG");
    aircraft.squawk = 01234;
    aircraft.category = ModeSAircraft::Category::kCategoryGliderSailplane;
    aircraft.baro_altitude_ft = 1000;
    aircraft.gnss_altitude_ft = 997;
    aircraft.altitude_source = ModeSAircraft::AltitudeSource::kAltitudeSourceBaro;
    aircraft.latitude_deg = -120.654321;
    aircraft.longitude_deg = -80.123456;
    aircraft.direction_deg = 300.5678;
    aircraft.velocity_kts = 123.45;
    aircraft.velocity_source = ModeSAircraft::VelocitySource::kVelocitySourceAirspeedTrue;
    aircraft.vertical_rate_fpm = -200;
    aircraft.vertical_rate_source = ModeSAircraft::VerticalRateSource::kVerticalRateSourceBaro;
    aircraft.navigation_integrity_category = static_cast<ModeSAircraft::NICRadiusOfContainment>(0b1011);
    aircraft.navigation_integrity_category_baro = static_cast<ModeSAircraft::NICBarometricAltitudeIntegrity>(0b1);
    aircraft.navigation_accuracy_category_velocity = static_cast<ModeSAircraft::NACHorizontalVelocityError>(0b101);
    aircraft.navigation_accuracy_category_position =
        static_cast<ModeSAircraft::NACEstimatedPositionUncertainty>(0b1101);
    aircraft.geometric_vertical_accuracy = static_cast<ModeSAircraft::GVA>(0b11);
    aircraft.source_integrity_level = static_cast<ModeSAircraft::SILProbabilityOfExceedingNICRadiusOfContainmnent>(
        ModeSAircraft::kPOERCLessThanOrEqualTo1em5PerFlightHour);
    aircraft.system_design_assurance = static_cast<ModeSAircraft::SystemDesignAssurance>(0b11);
    aircraft.gnss_antenna_offset_right_of_roll_axis_m = -6;
    aircraft.length_m = 10;
    aircraft.width_m = 20;
    aircraft.adsb_version = 3;

    WriteCSBeeAircraftMessageStr(message, aircraft);
    std::string_view message_view(message);
    printf("%s\r\n", message_view.data());
    printf("%s\r\n", message_view.data());
    std::string_view token = GetNextToken(&message_view);
    EXPECT_EQ(token.compare("#A:12345E"), 0);            // ICAO Address
    EXPECT_EQ(GetNextToken().compare("FFFFFFFF"), 0);    // Flags
    EXPECT_EQ(GetNextToken().compare("ABCDEFG"), 0);     // Callsign
    EXPECT_EQ(GetNextToken().compare("1234"), 0);        // Squawk
    EXPECT_EQ(GetNextToken().compare("6"), 0);           // Emitter Category
    EXPECT_EQ(GetNextToken().compare("-120.65432"), 0);  // Latitude [deg]
    EXPECT_EQ(GetNextToken().compare("-80.12346"), 0);   // Longitude [deg]
    EXPECT_EQ(GetNextToken().compare("1000"), 0);        // Baro Altitude [ft]
    EXPECT_EQ(GetNextToken().compare("997"), 0);         // GNSS Altitude [ft]
    EXPECT_EQ(GetNextToken().compare("301"), 0);         // Track [deg]
    EXPECT_EQ(GetNextToken().compare("123"), 0);         // Velocity [kts]
    EXPECT_EQ(GetNextToken().compare("-200"), 0);        // Vertical Rate [fpm]
    EXPECT_EQ(GetNextToken().compare("-75"), 0);         // Signal Strength [dBm]
    EXPECT_EQ(GetNextToken().compare("2"), 0);           // Signal Qualtiy [dB]
    EXPECT_EQ(GetNextToken().compare("1"), 0);           // Squitter Frames Per Second
    EXPECT_EQ(GetNextToken().compare("3"), 0);           // Extended Squitter Frames Per Second
    // Use an std::string here as a hack, since we don't want to bother with copying the whole string to another buffer
    // and then finding just the SYSINFO field. Converting the std::string to a uint32_t with base 16 notation.
    uint32_t sysinfo = strtol(std::string(GetNextToken()).c_str(), NULL, 16);
    EXPECT_EQ(sysinfo & 0b1111, 0b1011u);                 // NIC
    EXPECT_EQ((sysinfo & (0b1 << 4)) >> 4, 0b1u);         // NIC_baro
    EXPECT_EQ((sysinfo & (0b111 << 5)) >> 5, 0b101u);     // NAC_v
    EXPECT_EQ((sysinfo & (0b1111 << 8)) >> 8, 0b1101u);   // NAC_p
    EXPECT_EQ((sysinfo & (0b11 << 12)) >> 12, 0b11u);     // GVA
    EXPECT_EQ((sysinfo & (0b11 << 14)) >> 14, 2u);        // SIL
    EXPECT_EQ((sysinfo & (0b11 << 16)) >> 16, 0b11u);     // SDA
    EXPECT_EQ((sysinfo & (0b1 << 18)) >> 18, 0b1u);       // GAOK
    EXPECT_EQ((sysinfo & (0b11 << 19)) >> 19, 6u >> 1);   // GAOD
    EXPECT_EQ((sysinfo & (0b11 << 19)) >> 19, 6u >> 1);   // GAOD
    EXPECT_EQ((sysinfo & (0b1 << 21)) >> 21, 0u);         // GAOR
    EXPECT_EQ((sysinfo & (0b1111111 << 22)) >> 22, 20u);  // MDIM
    // Check CRC
    std::string_view crc_str = GetNextToken();
    char calculated_crc_string[kCRCMaxNumChars + 1];
    sprintf(calculated_crc_string, "%X\r\n",
            CalculateCRC16((uint8_t*)message, message_view.length() - crc_str.length()));
    printf("Reported CRC=%s Calculated CRC=%s\r\n", std::string(crc_str).c_str(), calculated_crc_string);
    EXPECT_EQ(crc_str.compare(calculated_crc_string), 0);
}