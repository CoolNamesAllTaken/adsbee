#include "gtest/gtest.h"
#include "packet_decoder.hh"

TEST(PacketDecoder, HandleNoBitErrors) {
    PacketDecoder decoder(PacketDecoder::PacketDecoderConfig{.enable_1090_error_correction = true});

    Raw1090Packet raw_packet((char *)"8D40621D58C382D690C8AC2863A7");
    decoder.raw_1090_packet_in_queue.Push(raw_packet);
    decoder.UpdateDecoderLoop();
    EXPECT_EQ(decoder.decoded_1090_packet_out_queue.Length(), 1);

    Decoded1090Packet decoded_packet;
    EXPECT_TRUE(decoder.decoded_1090_packet_out_queue.Pop(decoded_packet));
    EXPECT_EQ(decoded_packet.GetICAOAddress(), 0x40621Du);
}

TEST(PacketDecoder, HandleSingleBitError) {
    PacketDecoder decoder_no_corrections(PacketDecoder::PacketDecoderConfig{.enable_1090_error_correction = false});
    PacketDecoder decoder(PacketDecoder::PacketDecoderConfig{.enable_1090_error_correction = true});

    Raw1090Packet raw_packet((char *)"8D40621D58C382D690C8AC2863A6");
    decoder_no_corrections.raw_1090_packet_in_queue.Push(raw_packet);
    decoder_no_corrections.UpdateDecoderLoop();
    EXPECT_EQ(decoder_no_corrections.decoded_1090_packet_out_queue.Length(), 0);

    decoder.raw_1090_packet_in_queue.Push(raw_packet);
    decoder.UpdateDecoderLoop();
    EXPECT_EQ(decoder.decoded_1090_packet_out_queue.Length(), 1);

    Decoded1090Packet decoded_packet;
    EXPECT_TRUE(decoder.decoded_1090_packet_out_queue.Pop(decoded_packet));
    EXPECT_EQ(decoded_packet.GetICAOAddress(), 0x40621Du);
}