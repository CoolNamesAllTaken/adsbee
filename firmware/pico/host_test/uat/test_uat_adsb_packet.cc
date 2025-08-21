#include "aircraft_dictionary.hh"
#include "buffer_utils.hh"
#include "gtest/gtest.h"
#include "uat_packet.hh"

TEST(DecodedUATADSBPacket, AirGroundState) {
    EXPECT_TRUE(ADSBTypes::AirGroundStateIsAirborne(static_cast<ADSBTypes::AirGroundState>(0)));
    EXPECT_FALSE(ADSBTypes::AirGroundStateIsSupersonic(static_cast<ADSBTypes::AirGroundState>(0)));

    EXPECT_TRUE(ADSBTypes::AirGroundStateIsAirborne(static_cast<ADSBTypes::AirGroundState>(1)));
    EXPECT_TRUE(ADSBTypes::AirGroundStateIsSupersonic(static_cast<ADSBTypes::AirGroundState>(1)));

    EXPECT_FALSE(ADSBTypes::AirGroundStateIsAirborne(static_cast<ADSBTypes::AirGroundState>(2)));
    EXPECT_FALSE(ADSBTypes::AirGroundStateIsSupersonic(static_cast<ADSBTypes::AirGroundState>(2)));
}

TEST(DecodedUATADSBPacket, HorizontalVelocityToNorthVelocityKts) {
    // Test with A/G state airborne and supersonic.
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(0 << 11,
                                                                         ADSBTypes::kAirGroundStateAirborneSupersonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1 << 11,
                                                                         ADSBTypes::kAirGroundStateAirborneSupersonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(2 << 11,
                                                                         ADSBTypes::kAirGroundStateAirborneSupersonic),
              4);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1022 << 11,
                                                                         ADSBTypes::kAirGroundStateAirborneSupersonic),
              4084);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1023 << 11,
                                                                         ADSBTypes::kAirGroundStateAirborneSupersonic),
              4088);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (0 << 11),
                                                                         ADSBTypes::kAirGroundStateAirborneSupersonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1 << 11),
                                                                         ADSBTypes::kAirGroundStateAirborneSupersonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (2 << 11),
                                                                         ADSBTypes::kAirGroundStateAirborneSupersonic),
              -4);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1022 << 11),
                                                                         ADSBTypes::kAirGroundStateAirborneSupersonic),
              -4084);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1023 << 11),
                                                                         ADSBTypes::kAirGroundStateAirborneSupersonic),
              -4088);

    // Test with A/G state airborne and subsonic.
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(0 << 11, ADSBTypes::kAirGroundStateAirborneSubsonic),
        INT32_MIN);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1 << 11, ADSBTypes::kAirGroundStateAirborneSubsonic),
        0);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(2 << 11, ADSBTypes::kAirGroundStateAirborneSubsonic),
        1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1022 << 11,
                                                                         ADSBTypes::kAirGroundStateAirborneSubsonic),
              1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1023 << 11,
                                                                         ADSBTypes::kAirGroundStateAirborneSubsonic),
              1022);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (0 << 11),
                                                                         ADSBTypes::kAirGroundStateAirborneSubsonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1 << 11),
                                                                         ADSBTypes::kAirGroundStateAirborneSubsonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (2 << 11),
                                                                         ADSBTypes::kAirGroundStateAirborneSubsonic),
              -1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1022 << 11),
                                                                         ADSBTypes::kAirGroundStateAirborneSubsonic),
              -1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1023 << 11),
                                                                         ADSBTypes::kAirGroundStateAirborneSubsonic),
              -1022);

    // Test on ground.
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(0 << 11, ADSBTypes::kAirGroundStateOnGround),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1 << 11, ADSBTypes::kAirGroundStateOnGround),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(2 << 11, ADSBTypes::kAirGroundStateOnGround),
              1);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1022 << 11, ADSBTypes::kAirGroundStateOnGround),
        1021);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1023 << 11, ADSBTypes::kAirGroundStateOnGround),
        1022);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (0 << 11),
                                                                         ADSBTypes::kAirGroundStateOnGround),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1 << 11),
                                                                         ADSBTypes::kAirGroundStateOnGround),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (2 << 11),
                                                                         ADSBTypes::kAirGroundStateOnGround),
              -1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1022 << 11),
                                                                         ADSBTypes::kAirGroundStateOnGround),
              -1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1023 << 11),
                                                                         ADSBTypes::kAirGroundStateOnGround),
              -1022);
}

TEST(DecodedUATADSBPacket, HorizontalVelocityToEastVelocityKts) {
    // Test with A/G state airborne and supersonic.
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(0, ADSBTypes::kAirGroundStateAirborneSupersonic),
        INT32_MIN);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1, ADSBTypes::kAirGroundStateAirborneSupersonic), 0);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(2, ADSBTypes::kAirGroundStateAirborneSupersonic), 4);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1022, ADSBTypes::kAirGroundStateAirborneSupersonic),
        4084);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1023, ADSBTypes::kAirGroundStateAirborneSupersonic),
        4088);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (0),
                                                                        ADSBTypes::kAirGroundStateAirborneSupersonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1),
                                                                        ADSBTypes::kAirGroundStateAirborneSupersonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (2),
                                                                        ADSBTypes::kAirGroundStateAirborneSupersonic),
              -4);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1022),
                                                                        ADSBTypes::kAirGroundStateAirborneSupersonic),
              -4084);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1023),
                                                                        ADSBTypes::kAirGroundStateAirborneSupersonic),
              -4088);

    // Test with A/G state airborne and subsonic.
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(0, ADSBTypes::kAirGroundStateAirborneSubsonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1, ADSBTypes::kAirGroundStateAirborneSubsonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(2, ADSBTypes::kAirGroundStateAirborneSubsonic),
              1);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1022, ADSBTypes::kAirGroundStateAirborneSubsonic),
        1021);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1023, ADSBTypes::kAirGroundStateAirborneSubsonic),
        1022);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (0),
                                                                        ADSBTypes::kAirGroundStateAirborneSubsonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1),
                                                                        ADSBTypes::kAirGroundStateAirborneSubsonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (2),
                                                                        ADSBTypes::kAirGroundStateAirborneSubsonic),
              -1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1022),
                                                                        ADSBTypes::kAirGroundStateAirborneSubsonic),
              -1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1023),
                                                                        ADSBTypes::kAirGroundStateAirborneSubsonic),
              -1022);

    // Test on ground.
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(0, ADSBTypes::kAirGroundStateOnGround),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1, ADSBTypes::kAirGroundStateOnGround), 0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(2, ADSBTypes::kAirGroundStateOnGround), 1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1022, ADSBTypes::kAirGroundStateOnGround),
              1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1023, ADSBTypes::kAirGroundStateOnGround),
              1022);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (0),
                                                                        ADSBTypes::kAirGroundStateOnGround),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1),
                                                                        ADSBTypes::kAirGroundStateOnGround),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (2),
                                                                        ADSBTypes::kAirGroundStateOnGround),
              -1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1022),
                                                                        ADSBTypes::kAirGroundStateOnGround),
              -1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1023),
                                                                        ADSBTypes::kAirGroundStateOnGround),
              -1022);
}

inline uint32_t EncodeOnGroundHorizontalVelocity(uint16_t ground_speed_encoded, uint16_t direction_encoded,
                                                 ADSBTypes::DirectionType direction_type) {
    return (ground_speed_encoded << 11) | (direction_encoded | (direction_type << 9));
}

struct OnGroundHorizontalVelocityTestCase {
    uint16_t direction_encoded;
    float expected_direction_deg;
    uint16_t ground_speed_encoded;
    int32_t expected_speed_kts;
    char *description;
};

const OnGroundHorizontalVelocityTestCase kOnGroundHorizontalVelocityTestCases[] = {
    {0, 0.0f, 0, INT32_MIN, (char *)"0.0 degrees, speed not available"},
    {1, 0.703125f, 1, 0, (char *)"0.703125 degrees, 0 kts"},
    {1, 0.703125f, 0, INT32_MIN, (char *)"0.703125 degrees, 0 speed not available"},
    {2, 1.40625f, 1, 0, (char *)"1.40625 degrees, 1 kts"},
    {3, 2.109375f, 2, 1, (char *)"2.109375 degrees, 2 kts"},
    {510, 358.593750f, 1022, 1021, (char *)"358.593750 degrees, 1022 kts"},
    {511, 359.296875f, 1023, 1022, (char *)"359.196875 degrees, 1023 kts"}};

TEST(DecodedUATADSBPacket, HorizontalVelocityToDirectionDegAndSpeedKtsOnGround) {
    ADSBTypes::AirGroundState air_ground_state = ADSBTypes::kAirGroundStateOnGround;

    for (const auto &test_case : kOnGroundHorizontalVelocityTestCases) {
        uint16_t direction_encoded = test_case.direction_encoded;
        float expected_direction_deg = test_case.expected_direction_deg;
        uint16_t ground_speed_encoded = test_case.ground_speed_encoded;
        int32_t expected_speed_kts = test_case.expected_speed_kts;

        float direction;
        int32_t speed;

        uint32_t horizontal_velocity = EncodeOnGroundHorizontalVelocity(ground_speed_encoded, direction_encoded,
                                                                        ADSBTypes::kDirectionTypeTrueTrackAngle);

        SCOPED_TRACE(test_case.description);
        EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToDirectionDegAndSpeedKts(horizontal_velocity,
                                                                                    air_ground_state, direction, speed),
                  ADSBTypes::kDirectionTypeTrueTrackAngle);
        EXPECT_FLOAT_EQ(direction, expected_direction_deg);
        EXPECT_EQ(speed, expected_speed_kts);
    }
}

TEST(DecodedUATADSBPacket, UATHeader) {
    uint8_t buf[] = {0x15, 0xa6, 0x6e, 0xf1, 0x35};
    DecodedUATADSBPacket::UATHeader header;
    DecodedUATADSBPacket::DecodeHeader(buf, header);
    EXPECT_EQ(header.mdb_type_code, 2);
    EXPECT_EQ(header.address_qualifier, 5);
    EXPECT_EQ(header.icao_address, 0xA66EF1u);
}

TEST(DecodedUATADSBPacket, ICAOAddress) {
    // ICAO address is 0 if the packet is invalid or has no header.
    DecodedUATADSBPacket packet((char *)"");
    packet.ReconstructWithoutFEC();
    EXPECT_EQ(packet.GetICAOAddress(), 0u);
}

uint32_t EncodeVerticalVelocity(int vertical_velocity, bool is_geometric) {
    uint32_t encoded_vertical_velocity = 0;
    if (vertical_velocity < 0) {
        encoded_vertical_velocity |= (1 << 10);
        encoded_vertical_velocity |= (-vertical_velocity & 0b111111111);
    } else {
        encoded_vertical_velocity |= (vertical_velocity & 0b111111111);
    }
    encoded_vertical_velocity |= (is_geometric ? 0 : (1 << 10));
    return encoded_vertical_velocity;
}

struct VerticalVelocityTestCase {
    uint32_t vertical_velocity_encoded;
    ADSBTypes::AirGroundState air_ground_state;

    int32_t expected_vertical_rate_fpm;
    ADSBTypes::VerticalRateSource expected_vertical_rate_source;
    char *description;
};

const VerticalVelocityTestCase kVerticalVelocityTestCases[] = {
    {0, ADSBTypes::AirGroundState::kAirGroundStateOnGround, INT32_MIN, ADSBTypes::kVerticalRateSourceNotAvailable,
     (char *)"on ground, vertical rate not available"},
    {1 << 10, ADSBTypes::AirGroundState::kAirGroundStateAirborneSupersonic, INT32_MIN,
     ADSBTypes::kVerticalRateSourceNotAvailable, (char *)"airborne supersonic, vertical rate not available"},
    {1 << 9, ADSBTypes::AirGroundState::kAirGroundStateAirborneSubsonic, INT32_MIN,
     ADSBTypes::kVerticalRateSourceNotAvailable, (char *)"airborne subsonic, vertical rate not available"},
    {1, ADSBTypes::AirGroundState::kAirGroundStateAirborneSupersonic, 0, ADSBTypes::kVerticalRateSourceGNSS,
     (char *)"0fpm gnss"},
    {(0b11 << 9) | 1, ADSBTypes::AirGroundState::kAirGroundStateAirborneSupersonic, 0,
     ADSBTypes::kVerticalRateSourceBaro, (char *)"-0fpm baro"},
    {2, ADSBTypes::AirGroundState::kAirGroundStateAirborneSubsonic, 64, ADSBTypes::kVerticalRateSourceGNSS,
     (char *)"64fpm gnss"},
    {(0b1 << 9) | 2, ADSBTypes::AirGroundState::kAirGroundStateAirborneSubsonic, -64,
     ADSBTypes::kVerticalRateSourceGNSS, (char *)"-64fpm gnss"},
    {(0b1 << 10) | 3, ADSBTypes::AirGroundState::kAirGroundStateAirborneSupersonic, 128,
     ADSBTypes::kVerticalRateSourceBaro, (char *)"128fpm baro"},
    {(0b11 << 9) | 510, ADSBTypes::AirGroundState::kAirGroundStateAirborneSupersonic, -32576,
     ADSBTypes::kVerticalRateSourceBaro, (char *)"-32576fpm baro"},
    {510, ADSBTypes::AirGroundState::kAirGroundStateAirborneSupersonic, 32576, ADSBTypes::kVerticalRateSourceGNSS,
     (char *)"32576fpm gnss"},

};

TEST(DecodedUATADBPacket, VerticalVelocity) {
    for (const auto &test_case : kVerticalVelocityTestCases) {
        int vertical_velocity_fpm;
        SCOPED_TRACE(test_case.description);
        EXPECT_EQ(test_case.expected_vertical_rate_source,
                  DecodedUATADSBPacket::VerticalVelocityToVerticalRateFpm(
                      test_case.vertical_velocity_encoded, test_case.air_ground_state, vertical_velocity_fpm));
        EXPECT_EQ(vertical_velocity_fpm, test_case.expected_vertical_rate_fpm);
    }
}

// Test cases for AV dimensions decoding.
struct AVDimensionTestCase {
    uint32_t av_dimensions_encoded;
    int16_t expected_width_m;
    int16_t expected_length_m;
    ADSBTypes::AVDimensionsType expected_dimensions_type;
    const char *description;
};

const AVDimensionTestCase kAVDimensionTestCases[] = {
    {0, 12, 15, ADSBTypes::kAVDimensionsTypeAVLengthWidth, "AV Length Width 0"},
    {1 << 6, 12, 15, ADSBTypes::kAVDimensionsTypeGNSSSensorOffset, "GNSS sensor offset 0"},
    {(1 << 6) | 12 << 7, 73, 75, ADSBTypes::kAVDimensionsTypeGNSSSensorOffset, "GNSS sensor offset 12"}

};

TEST(DecodedUATADSBPacket, AVDimensions) {
    for (const auto &test_case : kAVDimensionTestCases) {
        int16_t width_m, length_m;
        SCOPED_TRACE(test_case.description);
        EXPECT_EQ(test_case.expected_dimensions_type,
                  DecodedUATADSBPacket::DecodeAVDimensions(test_case.av_dimensions_encoded, width_m, length_m));
        EXPECT_EQ(width_m, test_case.expected_width_m);
        EXPECT_EQ(length_m, test_case.expected_length_m);
    }
}