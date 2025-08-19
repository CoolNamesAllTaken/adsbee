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
        }
}

// Helper function to convert hex string to bytes:
void hex_string_to_bytes(const char* hex_string, uint8_t* bytes, int length) {
    for (int i = 0; i < length; i++) {
        sscanf(hex_string + (i * 2), "%2hhx", &bytes[i]);
    }
}