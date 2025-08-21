#include "aircraft_dictionary.hh"
#include "buffer_utils.hh"
#include "gtest/gtest.h"
#include "uat_packet.hh"
#include "uat_test_data.h"

// Test downlink frames
TEST(UATDecoderTest, DownlinkFrames) {
    int count = get_uat_downlink_test_frames_count();
    for (int i = 0; i < count; i++) {
        const uat_downlink_test_frame_t* frame = get_uat_downlink_test_frame(i);
        char message[200] = {"\0"};
        sprintf(message, "Test frame %d: %s, icao=%08X", i, frame->test_name, frame->address);
        SCOPED_TRACE(message);

        AircraftDictionary dictionary;
        UATAircraft aircraft;

        // Create the packet, force it as valid (no FEC included in test data), ingest into dictionary.
        DecodedUATADSBPacket packet(frame->frame_data_hex);
        packet.ReconstructWithoutFEC();
        EXPECT_TRUE(dictionary.IngestDecodedUATADSBPacket(packet));

        // Ensure the dictionary has a matching aircraft entry and extract it.
        EXPECT_TRUE(dictionary.GetAircraft(
            Aircraft::ICAOToUID(frame->address | (frame->address_qualifier << Aircraft::kAddressQualifierBitShift),
                                Aircraft::kAircraftTypeUAT),
            aircraft));

        // Compare fields in aircraft entry against fields in test data.
        if (frame->has_sv) {
            if (frame->position_valid) {
                EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagPositionValid));
                EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedPosition));
                EXPECT_FLOAT_EQ(aircraft.latitude_deg, frame->lat);
                EXPECT_FLOAT_EQ(aircraft.longitude_deg, frame->lon);
            } else {
                EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagPositionValid));
                EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedPosition));
            }

            // Subtract 1 from frame's altitude_type to convert to enum format.
            ADSBTypes::AltitudeSource altitude_source =
                static_cast<ADSBTypes::AltitudeSource>(frame->altitude_type - 1);
            switch (altitude_source) {
                case (ADSBTypes::kAltitudeSourceBaro):
                    EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagBaroAltitudeValid));
                    EXPECT_EQ(frame->has_auxsv && frame->sec_altitude != 0,
                              aircraft.HasBitFlag(UATAircraft::kBitFlagGNSSAltitudeValid));

                    EXPECT_EQ(aircraft.baro_altitude_ft, frame->altitude);

                    if (frame->has_auxsv) {
                        EXPECT_EQ(aircraft.gnss_altitude_ft, frame->sec_altitude);
                    }
                    break;
                case (ADSBTypes::kAltitudeSourceGNSS):
                    EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagGNSSAltitudeValid));
                    EXPECT_EQ(frame->has_auxsv && frame->sec_altitude != 0,
                              aircraft.HasBitFlag(UATAircraft::kBitFlagBaroAltitudeValid));

                    EXPECT_EQ(aircraft.gnss_altitude_ft, frame->altitude);

                    if (frame->has_auxsv) {
                        EXPECT_EQ(aircraft.baro_altitude_ft, frame->sec_altitude);
                    }
                    break;
                default:
                    // Handle kAltitudeSourceNotAvailable and kAltitudeSourceNotSet.
                    break;
            }

            // Check NIC
            EXPECT_EQ(aircraft.navigation_integrity_category, frame->nic);

            // Check Air/Ground State and Horizontal Velocity

            EXPECT_EQ(aircraft.HasBitFlag(UATAircraft::kBitFlagIsAirborne), (frame->airground_state & 0b10) == 0);

            if (frame->airground_state & 0b1) {
                // Aircraft is on ground. Reporting heading and ground speed.

                // WARNING: This test case doesn't get reached in the current data.
                EXPECT_TRUE(false);

                // Ground speed and heading format (aircraft on ground).
                EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagHorizontalVelocityValid));
                EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedHorizontalVelocity));

                EXPECT_EQ(aircraft.speed_kts, frame->speed);

                EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionValid));
                EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedDirection));

                EXPECT_NEAR(aircraft.direction_deg, frame->track, 0.5f);  // Test data is rounded.

                // TODO: Check length/width code.

            } else if (frame->ns_vel_valid && frame->ew_vel_valid) {
                // Airborne. Track provided in North Velocity + East Velocity format.
                EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagHorizontalVelocityValid));
                EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedHorizontalVelocity));

                EXPECT_EQ(aircraft.speed_kts, frame->speed);

                EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionValid));
                EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionIsHeading));
                EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedDirection));

                EXPECT_NEAR(aircraft.direction_deg, frame->track, 0.5f);  // Test data is rounded.

                // Vertical speed
                switch (frame->vert_rate_source) {
                    case UAT_ALT_BARO:
                        EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagBaroVerticalVelocityValid));
                        EXPECT_EQ(aircraft.baro_vertical_rate_fpm, frame->vert_rate);
                        EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedBaroVerticalVelocity));
                        EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagGNSSVerticalVelocityValid));
                        EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedGNSSVerticalVelocity));
                        break;
                    case UAT_ALT_GEO:
                        EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagGNSSVerticalVelocityValid));
                        EXPECT_EQ(aircraft.gnss_vertical_rate_fpm, frame->vert_rate);
                        EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedGNSSVerticalVelocity));
                        EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagBaroVerticalVelocityValid));
                        EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedBaroVerticalVelocity));
                        break;
                    default:
                        // No vertical speed information available.
                        EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagBaroVerticalVelocityValid));
                        EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagGNSSVerticalVelocityValid));
                        EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedBaroVerticalVelocity));
                        EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedGNSSVerticalVelocity));
                        break;
                }

            } else {
                // No horizontal velocity information available.
                EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagHorizontalVelocityValid));
                EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedHorizontalVelocity));
                EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionValid));
                EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagUpdatedDirection));
            }

            switch (frame->track_type) {
                case UAT_TT_TRACK:
                    EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionValid));
                    EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionIsHeading));
                    break;
                case UAT_TT_MAG_HEADING:
                    EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionValid));
                    EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionIsHeading));
                    EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagHeadingUsesMagneticNorth));
                    break;
                case UAT_TT_TRUE_HEADING:
                    EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionValid));
                    EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionIsHeading));
                    EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagHeadingUsesMagneticNorth));
                    break;
                default:
                    // UAT_TT_INVALID and others.
                    EXPECT_FALSE(aircraft.HasBitFlag(UATAircraft::kBitFlagDirectionValid));
                    break;
            }
        }
    }
}

// Helper function to convert hex string to bytes:
void hex_string_to_bytes(const char* hex_string, uint8_t* bytes, int length) {
    for (int i = 0; i < length; i++) {
        sscanf(hex_string + (i * 2), "%2hhx", &bytes[i]);
    }
}