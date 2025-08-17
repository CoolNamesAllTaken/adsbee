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
        SCOPED_TRACE(frame->test_name);

        // Decode with your decoder
        AircraftDictionary dictionary;

        DecodedUATADSBPacket packet(frame->frame_data_hex);
        packet.ReconstructWithoutFEC();
        EXPECT_TRUE(dictionary.IngestDecodedUATADSBPacket(packet));

        UATAircraft aircraft;
        EXPECT_TRUE(dictionary.GetAircraft(Aircraft::ICAOToUID(frame->address, Aircraft::kAircraftTypeUAT), aircraft));

        // // Compare against expected values
        // EXPECT_EQ(result.mdb_type, frame->mdb_type);
        // EXPECT_EQ(result.address, frame->address);
        // if (frame->position_valid) {
        //     EXPECT_NEAR(result.lat, frame->lat, 0.0001);
        //     EXPECT_NEAR(result.lon, frame->lon, 0.0001);
        // }
        // // ... more assertions
    }
}

// Helper function to convert hex string to bytes:
void hex_string_to_bytes(const char* hex_string, uint8_t* bytes, int length) {
    for (int i = 0; i < length; i++) {
        sscanf(hex_string + (i * 2), "%2hhx", &bytes[i]);
    }
}