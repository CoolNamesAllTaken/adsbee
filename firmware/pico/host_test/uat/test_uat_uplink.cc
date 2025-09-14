#include "fec.hh"
#include "gtest/gtest.h"
#include "uat_packet.hh"
#include "uat_test_data.h"

TEST(UATDecoderTest, UplinkFrames) {
    int count = get_uat_uplink_test_frames_count();
    for (int i = 0; i < count; i++) {
        const uat_uplink_test_frame_t* frame = get_uat_uplink_test_frame(i);
        char message[200] = {"\0"};
        sprintf(message, "Test frame %d: %s, tisb_site_id=%08X", i, frame->test_name, frame->tisb_site_id);
        SCOPED_TRACE(message);

        // Create encoded data frame.
        uint8_t decoded_data_frame[RawUATUplinkPacket::kUplinkMessagePayloadNumBytes] = {0};
        HexStringToByteBuffer(decoded_data_frame, frame->frame_data_hex, frame->frame_length);
        uint8_t encoded_data_frame[RawUATUplinkPacket::kUplinkMessageNumBytes] = {0};
        uat_rs.EncodeUplinkMessage(encoded_data_frame, decoded_data_frame);
        int16_t sigs_dbm = -10;                // Dummy signal strength.
        int16_t sigq_bits = 0;                 // Dummy signal quality.
        uint64_t mlat_48mhz_64bit_counts = 0;  // Dummy timestamp.
        DecodedUATUplinkPacket packet(RawUATUplinkPacket(decoded_data_frame, RawUATUplinkPacket::kUplinkMessageNumBytes,
                                                         sigs_dbm, sigq_bits, mlat_48mhz_64bit_counts));
    }
}