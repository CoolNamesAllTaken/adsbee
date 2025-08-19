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
            EXPECT_FLOAT_EQ(aircraft.latitude_deg, frame->lat);
            EXPECT_FLOAT_EQ(aircraft.longitude_deg, frame->lon);

            // Subtract 1 from frame's altitude_type to convert to enum format.
            UATAircraft::AltitudeSource altitude_source =
                static_cast<UATAircraft::AltitudeSource>(frame->altitude_type - 1);
            switch (altitude_source) {
                case (UATAircraft::kAltitudeSourceBaro):
                    EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagBaroAltitudeValid));
                    EXPECT_EQ(frame->has_auxsv, aircraft.HasBitFlag(UATAircraft::kBitFlagGNSSAltitudeValid));

                    EXPECT_EQ(aircraft.baro_altitude_ft, frame->altitude);

                    if (frame->has_auxsv) {
                        EXPECT_EQ(aircraft.gnss_altitude_ft, frame->sec_altitude);
                    }
                    break;
                case (UATAircraft::kAltitudeSourceGNSS):
                    EXPECT_TRUE(aircraft.HasBitFlag(UATAircraft::kBitFlagGNSSAltitudeValid));
                    EXPECT_EQ(frame->has_auxsv, aircraft.HasBitFlag(UATAircraft::kBitFlagBaroAltitudeValid));

                    EXPECT_EQ(aircraft.gnss_altitude_ft, frame->altitude);

                    if (frame->has_auxsv) {
                        EXPECT_EQ(aircraft.baro_altitude_ft, frame->sec_altitude);
                    }
                    break;
                default:
                    // Handle kAltitudeSOurceNotAvailable and kAltitudeSourceNotSet
                    continue;
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