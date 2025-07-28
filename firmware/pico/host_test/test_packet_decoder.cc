#include "gtest/gtest.h"
#include "packet_decoder.hh"

TEST(PacketDecoder, HandleNoBitErrors) {
    PacketDecoder decoder(PacketDecoder::PacketDecoderConfig{.enable_1090_error_correction = true});

    RawModeSPacket raw_packet((char *)"8D40621D58C382D690C8AC2863A7");
    decoder.raw_1090_packet_in_queue.Push(raw_packet);
    decoder.UpdateDecoderLoop();
    EXPECT_EQ(decoder.decoded_1090_packet_out_queue.Length(), 1);

    DecodedModeSPacket decoded_packet;
    EXPECT_TRUE(decoder.decoded_1090_packet_out_queue.Pop(decoded_packet));
    EXPECT_EQ(decoded_packet.GetICAOAddress(), 0x40621Du);
}

TEST(PacketDecoder, HandleSingleBitError) {
    PacketDecoder decoder_no_corrections(PacketDecoder::PacketDecoderConfig{.enable_1090_error_correction = false});
    PacketDecoder decoder(PacketDecoder::PacketDecoderConfig{.enable_1090_error_correction = true});

    RawModeSPacket raw_packet((char *)"8D40621D58C382D690C8AC2863A6");
    decoder_no_corrections.raw_1090_packet_in_queue.Push(raw_packet);
    decoder_no_corrections.UpdateDecoderLoop();
    EXPECT_EQ(decoder_no_corrections.decoded_1090_packet_out_queue.Length(), 0);

    decoder.raw_1090_packet_in_queue.Push(raw_packet);
    decoder.UpdateDecoderLoop();
    EXPECT_EQ(decoder.decoded_1090_packet_out_queue.Length(), 1);

    DecodedModeSPacket decoded_packet;
    EXPECT_TRUE(decoder.decoded_1090_packet_out_queue.Pop(decoded_packet));
    EXPECT_EQ(decoded_packet.GetICAOAddress(), 0x40621Du);
}

TEST(PacketDecoder, RejectDuplicateMessages) {
    // Packet decoder should not re-process the same message if it's caught by multiple state machines.
    PacketDecoder decoder(PacketDecoder::PacketDecoderConfig{.enable_1090_error_correction = true});
    RawModeSPacket raw_packet((char *)"8D40621D58C382D690C8AC2863A7");
    raw_packet.source = 0;
    raw_packet.mlat_48mhz_64bit_counts = 123456;
    decoder.raw_1090_packet_in_queue.Push(raw_packet);
    decoder.UpdateDecoderLoop();
    EXPECT_EQ(decoder.decoded_1090_packet_out_queue.Length(), 1);
    DecodedModeSPacket decoded_packet;
    EXPECT_TRUE(decoder.decoded_1090_packet_out_queue.Pop(decoded_packet));
    EXPECT_EQ(decoder.decoded_1090_packet_out_queue.Length(), 0);
    EXPECT_EQ(decoded_packet.GetICAOAddress(), 0x40621Du);

    // Push the same packet again within 2ms, it should not be re-processed.
    raw_packet.source = 1;
    raw_packet.mlat_48mhz_64bit_counts = 123456 + 48000 * 2;  // Different timestamp.
    decoder.raw_1090_packet_in_queue.Push(raw_packet);
    decoder.UpdateDecoderLoop();
    EXPECT_EQ(decoder.decoded_1090_packet_out_queue.Length(), 0);

    // Push the same packet again after kMinSameAircraftMessageIntervalMs, it should be re-processed.
    raw_packet.mlat_48mhz_64bit_counts += 48000 * PacketDecoder::kMinSameAircraftMessageIntervalMs;
    decoder.raw_1090_packet_in_queue.Push(raw_packet);
    decoder.UpdateDecoderLoop();
    EXPECT_EQ(decoder.decoded_1090_packet_out_queue.Length(), 1);
    EXPECT_TRUE(decoder.decoded_1090_packet_out_queue.Pop(decoded_packet));
    EXPECT_EQ(decoded_packet.GetICAOAddress(), 0x40621Du);
    EXPECT_EQ(decoded_packet.GetRaw().source, 1);  // Should have the source.
}