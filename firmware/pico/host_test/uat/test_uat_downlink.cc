#include "aircraft_dictionary.hh"
#include "buffer_utils.hh"
#include "gtest/gtest.h"
#include "uat_packet.hh"

TEST(DecodedUATADSBPacket, AirGroundState) {
    EXPECT_TRUE(DecodedUATADSBPacket::AirGroundStateIsAirborne(static_cast<DecodedUATADSBPacket::AirGroundState>(0)));
    EXPECT_FALSE(
        DecodedUATADSBPacket::AirGroundStateIsSupersonic(static_cast<DecodedUATADSBPacket::AirGroundState>(0)));

    EXPECT_TRUE(DecodedUATADSBPacket::AirGroundStateIsAirborne(static_cast<DecodedUATADSBPacket::AirGroundState>(1)));
    EXPECT_TRUE(DecodedUATADSBPacket::AirGroundStateIsSupersonic(static_cast<DecodedUATADSBPacket::AirGroundState>(1)));

    EXPECT_FALSE(DecodedUATADSBPacket::AirGroundStateIsAirborne(static_cast<DecodedUATADSBPacket::AirGroundState>(2)));
    EXPECT_FALSE(
        DecodedUATADSBPacket::AirGroundStateIsSupersonic(static_cast<DecodedUATADSBPacket::AirGroundState>(2)));
}

TEST(DecodedUATADSBPacket, HorizontalVelocityToNorthVelocityKts) {
    // Test with A/G state airborne and supersonic.
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  0 << 11, DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  1 << 11, DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  2 << 11, DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              4);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  1022 << 11, DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              4084);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  1023 << 11, DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              4088);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  (0b1 << 21) | (0 << 11), DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  (0b1 << 21) | (1 << 11), DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  (0b1 << 21) | (2 << 11), DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              -4);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  (0b1 << 21) | (1022 << 11), DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              -4084);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  (0b1 << 21) | (1023 << 11), DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              -4088);

    // Test with A/G state airborne and subsonic.
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  0 << 11, DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  1 << 11, DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  2 << 11, DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  1022 << 11, DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  1023 << 11, DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              1022);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  (0b1 << 21) | (0 << 11), DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  (0b1 << 21) | (1 << 11), DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  (0b1 << 21) | (2 << 11), DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              -1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  (0b1 << 21) | (1022 << 11), DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              -1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(
                  (0b1 << 21) | (1023 << 11), DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              -1022);

    // Test on ground.
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(0 << 11,
                                                                         DecodedUATADSBPacket::kAirGroundStateOnGround),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1 << 11,
                                                                         DecodedUATADSBPacket::kAirGroundStateOnGround),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(2 << 11,
                                                                         DecodedUATADSBPacket::kAirGroundStateOnGround),
              1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1022 << 11,
                                                                         DecodedUATADSBPacket::kAirGroundStateOnGround),
              1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts(1023 << 11,
                                                                         DecodedUATADSBPacket::kAirGroundStateOnGround),
              1022);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (0 << 11),
                                                                         DecodedUATADSBPacket::kAirGroundStateOnGround),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1 << 11),
                                                                         DecodedUATADSBPacket::kAirGroundStateOnGround),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (2 << 11),
                                                                         DecodedUATADSBPacket::kAirGroundStateOnGround),
              -1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1022 << 11),
                                                                         DecodedUATADSBPacket::kAirGroundStateOnGround),
              -1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToNorthVelocityKts((0b1 << 21) | (1023 << 11),
                                                                         DecodedUATADSBPacket::kAirGroundStateOnGround),
              -1022);
}

TEST(DecodedUATADSBPacket, HorizontalVelocityToEastVelocityKts) {
    // Test with A/G state airborne and supersonic.
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  0, DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  1, DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  2, DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              4);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  1022, DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              4084);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  1023, DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              4088);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  (0b1 << 10) | (0), DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  (0b1 << 10) | (1), DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  (0b1 << 10) | (2), DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              -4);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  (0b1 << 10) | (1022), DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              -4084);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  (0b1 << 10) | (1023), DecodedUATADSBPacket::kAirGroundStateAirborneSupersonic),
              -4088);

    // Test with A/G state airborne and subsonic.
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  0, DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  1, DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  2, DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  1022, DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  1023, DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              1022);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  (0b1 << 10) | (0), DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  (0b1 << 10) | (1), DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  (0b1 << 10) | (2), DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              -1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  (0b1 << 10) | (1022), DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              -1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(
                  (0b1 << 10) | (1023), DecodedUATADSBPacket::kAirGroundStateAirborneSubsonic),
              -1022);

    // Test on ground.
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(0, DecodedUATADSBPacket::kAirGroundStateOnGround),
        INT32_MIN);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1, DecodedUATADSBPacket::kAirGroundStateOnGround), 0);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(2, DecodedUATADSBPacket::kAirGroundStateOnGround), 1);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1022, DecodedUATADSBPacket::kAirGroundStateOnGround),
        1021);
    EXPECT_EQ(
        DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts(1023, DecodedUATADSBPacket::kAirGroundStateOnGround),
        1022);

    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (0),
                                                                        DecodedUATADSBPacket::kAirGroundStateOnGround),
              INT32_MIN);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1),
                                                                        DecodedUATADSBPacket::kAirGroundStateOnGround),
              0);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (2),
                                                                        DecodedUATADSBPacket::kAirGroundStateOnGround),
              -1);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1022),
                                                                        DecodedUATADSBPacket::kAirGroundStateOnGround),
              -1021);
    EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToEastVelocityKts((0b1 << 10) | (1023),
                                                                        DecodedUATADSBPacket::kAirGroundStateOnGround),
              -1022);
}

inline uint32_t EncodeOnGroundHorizontalVelocity(uint16_t ground_speed_encoded, uint16_t direction_encoded,
                                                 DecodedUATADSBPacket::DirectionType direction_type) {
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
    DecodedUATADSBPacket::AirGroundState air_ground_state = DecodedUATADSBPacket::kAirGroundStateOnGround;

    for (const auto &test_case : kOnGroundHorizontalVelocityTestCases) {
        uint16_t direction_encoded = test_case.direction_encoded;
        float expected_direction_deg = test_case.expected_direction_deg;
        uint16_t ground_speed_encoded = test_case.ground_speed_encoded;
        int32_t expected_speed_kts = test_case.expected_speed_kts;

        float direction;
        int32_t speed;

        uint32_t horizontal_velocity = EncodeOnGroundHorizontalVelocity(
            ground_speed_encoded, direction_encoded, DecodedUATADSBPacket::kDirectionTypeTrueTrackAngle);

        SCOPED_TRACE(test_case.description);
        EXPECT_EQ(DecodedUATADSBPacket::HorizontalVelocityToDirectionDegAndSpeedKts(horizontal_velocity,
                                                                                    air_ground_state, direction, speed),
                  DecodedUATADSBPacket::kDirectionTypeTrueTrackAngle);
        EXPECT_EQ(direction, expected_direction_deg);
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

// TEST(RawUATADSBPacket, ShortADSBPackets) {
//     DecodedUATADSBPacket tpacket((char *)"00a66ef135445d525a0c0519119021204800");
//     EXPECT_TRUE(tpacket.ReconstructWithoutFEC());
//     EXPECT_EQ(tpacket.GetICAOAddress(), 0xA66EF1u);
//     EXPECT_EQ(Aircraft::ICAOToUID(tpacket.GetICAOAddress(), Aircraft::kAircraftTypeUAT),
//               0x10A66EF1u);  // UID is ICAO address with type shifted to the left.

//     EXPECT_FLOAT_EQ(DecodedUATADSBPacket::kDegPerAWBTick * tpacket.state_vector.latitude_awb, 37.4534f);
//     EXPECT_FLOAT_EQ(DecodedUATADSBPacket::kDegPerAWBTick * tpacket.state_vector.longitude_awb, -122.0964f);
//     EXPECT_FALSE(tpacket.state_vector.altitude_is_geometric_altitude);
//     EXPECT_EQ(DecodedUATADSBPacket::AltitudeEncodedToAltitudeFt(ttpacket.state_vector.altitude_encoded), 1000);
//     EXPECT_EQ(tpacket.state_vector.horizontal_velocity_kts, )
// }

TEST(DecodedUATADSBPacket, ICAOAddress) {
    // ICAO address is 0 if the packet is invalid or has no header.
    DecodedUATADSBPacket packet((char *)"");
    packet.ReconstructWithoutFEC();
    EXPECT_EQ(packet.GetICAOAddress(), 0u);
}