#include "gtest/gtest.h"
#include "ads_b_packet.hh"

TEST(TransponderPacket, get_n_bit_word_from_buffer)
{
    uint32_t packet_buffer[TransponderPacket::kMaxPacketLenWords32];
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x0000504Du;

    EXPECT_EQ(get_n_bit_word_from_buffer(1, 0, packet_buffer), 0b1u);
    EXPECT_EQ(get_n_bit_word_from_buffer(1, 1, packet_buffer), 0b0u);

    EXPECT_EQ(get_n_bit_word_from_buffer(8, 0, packet_buffer), 0x8Du);
    EXPECT_EQ(get_n_bit_word_from_buffer(16, 0, packet_buffer), 0x8D76u);
    EXPECT_EQ(get_n_bit_word_from_buffer(24, 0, packet_buffer), 0x8D76CEu);
    EXPECT_EQ(get_n_bit_word_from_buffer(32, 0, packet_buffer), 0x8D76CE88u);

    // first bit index = 4
    EXPECT_EQ(get_n_bit_word_from_buffer(32, 4, packet_buffer), 0xD76CE882u);
    EXPECT_EQ(get_n_bit_word_from_buffer(24, 4, packet_buffer), 0xD76CE8u);
    EXPECT_EQ(get_n_bit_word_from_buffer(16, 4, packet_buffer), 0xD76Cu);
    EXPECT_EQ(get_n_bit_word_from_buffer(8, 4, packet_buffer), 0xD7u);

    // first bit index = 8
    EXPECT_EQ(get_n_bit_word_from_buffer(32, 8, packet_buffer), 0x76CE8820u);
    EXPECT_EQ(get_n_bit_word_from_buffer(24, 8, packet_buffer), 0x76CE88u);
    EXPECT_EQ(get_n_bit_word_from_buffer(16, 8, packet_buffer), 0x76CEu);
    EXPECT_EQ(get_n_bit_word_from_buffer(8, 8, packet_buffer), 0x76u);

    // first bit index = 12
    EXPECT_EQ(get_n_bit_word_from_buffer(32, 12, packet_buffer), 0x6CE88204u);

    // first bit index = 16
    EXPECT_EQ(get_n_bit_word_from_buffer(32, 16, packet_buffer), 0xCE88204Cu);

    // make sure it doesn't fall off the end; can use some printfs to double check this
    EXPECT_EQ(get_n_bit_word_from_buffer(16, 32 * 3 + 16, packet_buffer), 0x504Du);
}

TEST(TransponderPacket, set_n_bit_word_in_buffer)
{
    uint32_t packet_buffer[TransponderPacket::kMaxPacketLenWords32];
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x0000504Du;

    set_n_bit_word_in_buffer(8, 0xDEu, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0xDE76CE88u);

    // set with word that is too long
    set_n_bit_word_in_buffer(8, 0x1DEu, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0xDE76CE88u);

    // zero a byte
    set_n_bit_word_in_buffer(8, 0x00u, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0x0076CE88u);
    // set single bit
    set_n_bit_word_in_buffer(1, 0b1, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0x8076CE88u);

    // test clipping
    packet_buffer[0] = 0x00000000u;
    set_n_bit_word_in_buffer(24, 0xFFFFFFFFu, 0, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0xFFFFFF00u);

    // basic wraparound
    packet_buffer[0] = 0x8D76CE88u; // reset from last test
    set_n_bit_word_in_buffer(16, 0xBEEFu, 24, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0x8D76CEBEu);
    EXPECT_EQ(packet_buffer[1], 0xEF4C9072u);

    // wraparound with full word
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    set_n_bit_word_in_buffer(32, 0x0000FEEFu, 32 + 24, packet_buffer);
    EXPECT_EQ(packet_buffer[1], 0x204C9000u);
    EXPECT_EQ(packet_buffer[2], 0x00FEEF9Au);

    // make sure it doesn't fall off the end; can use some printfs to double check this
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x0000504Du;
    set_n_bit_word_in_buffer(24, 0xFFBEBEu, 32 * 3 + 8, packet_buffer);
    EXPECT_EQ(packet_buffer[0], 0x8D76CE88u); // untouched
    EXPECT_EQ(packet_buffer[1], 0x204C9072u); // untouched
    EXPECT_EQ(packet_buffer[2], 0xCB48209Au); // untouched
    EXPECT_EQ(packet_buffer[3], 0x00FFBEBEu);
}

// Example packets taken from http://jasonplayne.com:8080/. Thanks, Jason!

TEST(TransponderPacket, PacketBuffer)
{
    uint32_t packet_buffer[TransponderPacket::kMaxPacketLenWords32];

    // Nominal packet.
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x504D0000u;

    TransponderPacket packet = TransponderPacket(packet_buffer, 4);

    // Check that packet was ingested and conditioned properly.
    uint32_t check_buffer[TransponderPacket::kMaxPacketLenWords32];
    EXPECT_EQ(112 / 8, packet.DumpPacketBuffer(check_buffer));
    EXPECT_EQ(check_buffer[0], 0x8D76CE88u);
    EXPECT_EQ(check_buffer[1], 0x204C9072u);
    EXPECT_EQ(check_buffer[2], 0xCB48209Au);
    EXPECT_EQ(check_buffer[3], 0x504D0000u);

    EXPECT_EQ(packet.Get24BitWordFromPacketBuffer(0 * 24), 0x8D76CEu);
    EXPECT_EQ(packet.Get24BitWordFromPacketBuffer(1 * 24), 0x88204Cu);
    EXPECT_EQ(packet.Get24BitWordFromPacketBuffer(2 * 24), 0x9072CBu);
    EXPECT_EQ(packet.Get24BitWordFromPacketBuffer(3 * 24), 0x48209Au);
    EXPECT_EQ(packet.Get24BitWordFromPacketBuffer(4 * 24), 0x504D00u);

    // Nominal packet with extra bit ingested.
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x504D0000u | 0b1; // not realistic anymore since last word is left aligned now
    // TODO: make this test!
}

TEST(TransponderPacket, RxStringConstructor)
{
    TransponderPacket packet = TransponderPacket((char *)"8D4840D6202CC371C32CE0576098");
    uint32_t packet_buffer[TransponderPacket::kMaxPacketLenWords32];
    packet.DumpPacketBuffer(packet_buffer);

    EXPECT_EQ(packet_buffer[0], 0x8D4840D6u);
    EXPECT_EQ(packet_buffer[1], 0x202CC371u);
    EXPECT_EQ(packet_buffer[2], 0xC32CE057u);
    EXPECT_EQ(packet_buffer[3], 0x60980000u);
}

TEST(TransponderPacket, CRC24Checksum)
{
    uint32_t packet_buffer[TransponderPacket::kMaxPacketLenWords32]; // note: may contain garbage
    const uint16_t packet_buffer_used_len = 4;                       // number of 32 bit words populated in the packet buffer

    // Test packet from https://mode-s.org/decode/book-the_1090mhz_riddle-junzi_sun.pdf pg. 91.
    // 0x8D406B902015A678D4D220u[000000] (stripped off parity and replaced with 0's for testing)
    packet_buffer[0] = 0x8D406B90u;
    packet_buffer[1] = 0x2015A678u;
    packet_buffer[2] = 0xD4D22000u;
    packet_buffer[3] = 0x00000000u;

    TransponderPacket packet = TransponderPacket(packet_buffer, packet_buffer_used_len);

    EXPECT_EQ(packet.CalculateCRC24(), 0xAA4BDAu);

    // Test Packet: 8D76CE88 204C9072 CB48209A 504D
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x504D0000u;
    packet = TransponderPacket(packet_buffer, packet_buffer_used_len);
    EXPECT_TRUE(packet.IsValid());

    // Check CRC performance with error injection.
    packet_buffer[0] = 0x7D76CE88u; // error at beginning
    packet = TransponderPacket(packet_buffer, packet_buffer_used_len);
    EXPECT_FALSE(packet.IsValid());
    packet_buffer[0] = 0x8D76CE88u; // reset first word

    packet_buffer[3] = 0x504E0000u; // error near end
    packet = TransponderPacket(packet_buffer, packet_buffer_used_len);
    EXPECT_FALSE(packet.IsValid());
    packet_buffer[3] = 0x504D0000u; // reset last word

    // Extra bit ingestion (last word eats preamble from subsequent packet).
    packet_buffer[3] = 0x504D0001u; // error where it should be ignored
    TransponderPacket tpacket = TransponderPacket(packet_buffer, packet_buffer_used_len);
    EXPECT_TRUE(tpacket.IsValid());
    packet_buffer[3] = 0x504D0000u; // reset last word
}

TEST(TransponderPacket, PacketFields)
{
    uint32_t packet_buffer[TransponderPacket::kMaxPacketLenWords32]; // note: may contain garbage
    const uint16_t packet_buffer_used_len = 4;                       // number of 32 bit words populated in the packet buffer

    // Test Packet: 8D76CE88 204C9072 CB48209A 504D
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x504D0000u;
    TransponderPacket tpacket = TransponderPacket(packet_buffer, packet_buffer_used_len);
    EXPECT_TRUE(tpacket.IsValid());
    ADSBPacket packet = ADSBPacket(tpacket);

    EXPECT_EQ(packet.GetDownlinkFormat(), static_cast<uint16_t>(TransponderPacket::kDownlinkFormatExtendedSquitter));
    EXPECT_EQ(packet.GetCapability(), 5u);
    EXPECT_EQ(packet.GetICAOAddress(), 0x76CE88u);
    EXPECT_EQ(packet.GetTypeCode(), 4u);
    EXPECT_EQ(packet.GetNBitWordFromMessage(3, 5), 0u); // CAT = 0
}

TEST(ADSBPacket, ConstructFromTransponderPacket)
{
    TransponderPacket tpacket = TransponderPacket((char *)"8D7C80AD2358F6B1E35C60FF1925");
    ADSBPacket packet = ADSBPacket(tpacket);
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C80ADu);
    EXPECT_EQ(packet.GetTypeCode(), 4);
}

TEST(TransponderPacket, ConstructValidShortFrame)
{
    TransponderPacket packet = TransponderPacket((char *)"00050319AB8C22");
    EXPECT_FALSE(packet.IsValid()); // Automatically marked as invalid since not confirmable with CRC.
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C7B5A);
    EXPECT_EQ(packet.GetDownlinkFormat(), static_cast<uint16_t>(TransponderPacket::kDownlinkFormatShortRangeAirSurveillance));
}

TEST(TransponderPacket, ConstructInvalidShortFrame)
{
    TransponderPacket packet = TransponderPacket((char *)"00050219AB8C22");
    EXPECT_FALSE(packet.IsValid()); // Automatically marking all 56-bit packets with unknown ICAO as invalid for now.
}