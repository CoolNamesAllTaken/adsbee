#include "fec.hh"
#include "gtest/gtest.h"
#include "uat_packet.hh"
#include "uat_test_data.h"

TEST(UATDecoderTest, UplinkEncodeDecode) {
    uint8_t decoded_data_frame[RawUATUplinkPacket::kUplinkMessagePayloadNumBytes] = {0};
    HexStringToByteBuffer(decoded_data_frame, "1234567890", 5);
    uint8_t encoded_data_frame[RawUATUplinkPacket::kUplinkMessageNumBytes] = {0};
    uat_rs.EncodeUplinkMessage(encoded_data_frame, decoded_data_frame);
    int16_t sigs_dbm = -10;                // Dummy signal strength.
    int16_t sigq_bits = 0;                 // Dummy signal quality.
    uint64_t mlat_48mhz_64bit_counts = 0;  // Dummy timestamp.

    // Ensure encoded packet with no errors is valid.
    EXPECT_EQ(encoded_data_frame[0], 0x12);
    EXPECT_EQ(encoded_data_frame[6], 0x34);
    EXPECT_EQ(encoded_data_frame[12], 0x56);
    EXPECT_EQ(encoded_data_frame[18], 0x78);
    EXPECT_EQ(encoded_data_frame[24], 0x90);
    DecodedUATUplinkPacket packet(RawUATUplinkPacket(decoded_data_frame, RawUATUplinkPacket::kUplinkMessageNumBytes,
                                                     sigs_dbm, sigq_bits, mlat_48mhz_64bit_counts));
    EXPECT_TRUE(packet.is_valid);

    // Ensure encoded packet with too many errors is invalid.
    const uint16_t kNumBytesToCorrupt = 20;
    for (uint16_t i = 0; i < kNumBytesToCorrupt; i++) {
        // Hop skip around to bypass interleaving.
        encoded_data_frame[i * RawUATUplinkPacket::kUplinkMessageNumBlocks] ^=
            0xFF;  // Invert all bits in byte to simulate error.
    }
    DecodedUATUplinkPacket bad_packet(RawUATUplinkPacket(encoded_data_frame, RawUATUplinkPacket::kUplinkMessageNumBytes,
                                                         sigs_dbm, sigq_bits, mlat_48mhz_64bit_counts));
    EXPECT_FALSE(bad_packet.is_valid);
}

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
        EXPECT_TRUE(packet.is_valid);
    }
}