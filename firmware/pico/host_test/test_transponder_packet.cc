#include "gtest/gtest.h"
#include "mode_s_packet.hh"

// Example packets taken from http://jasonplayne.com:8080/. Thanks, Jason!

TEST(DecodedModeSPacket, PacketBuffer) {
    uint32_t packet_buffer[DecodedModeSPacket::kMaxPacketLenWords32];

    // Nominal packet.
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x504D0000u;

    DecodedModeSPacket packet = DecodedModeSPacket(packet_buffer, 4);

    // Check that packet was ingested and conditioned properly.
    uint32_t check_buffer[DecodedModeSPacket::kMaxPacketLenWords32];
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
    packet_buffer[3] = 0x504D0000u | 0b1;  // not realistic anymore since last word is left aligned now
    // TODO: make this test!
}

TEST(DecodedModeSPacket, RxStringConstructor) {
    DecodedModeSPacket packet = DecodedModeSPacket((char *)"8D4840D6202CC371C32CE0576098");
    uint32_t packet_buffer[DecodedModeSPacket::kMaxPacketLenWords32];
    packet.DumpPacketBuffer(packet_buffer);

    EXPECT_EQ(packet_buffer[0], 0x8D4840D6u);
    EXPECT_EQ(packet_buffer[1], 0x202CC371u);
    EXPECT_EQ(packet_buffer[2], 0xC32CE057u);
    EXPECT_EQ(packet_buffer[3], 0x60980000u);
}

TEST(DecodedModeSPacket, CRC24Checksum) {
    uint32_t packet_buffer[DecodedModeSPacket::kMaxPacketLenWords32];  // note: may contain garbage
    const uint16_t packet_buffer_used_len = 4;  // number of 32 bit words populated in the packet buffer

    // Test packet from https://mode-s.org/decode/book-the_1090mhz_riddle-junzi_sun.pdf pg. 91.
    // 0x8D406B902015A678D4D220u[000000] (stripped off parity and replaced with 0's for testing)
    packet_buffer[0] = 0x8D406B90u;
    packet_buffer[1] = 0x2015A678u;
    packet_buffer[2] = 0xD4D22000u;
    packet_buffer[3] = 0x00000000u;

    DecodedModeSPacket packet = DecodedModeSPacket(packet_buffer, packet_buffer_used_len);

    EXPECT_EQ(packet.CalculateCRC24(), 0xAA4BDAu);

    // Test Packet: 8D76CE88 204C9072 CB48209A 504D
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x504D0000u;
    packet = DecodedModeSPacket(packet_buffer, packet_buffer_used_len);
    EXPECT_TRUE(packet.IsValid());

    // Check CRC performance with error injection.
    packet_buffer[0] = 0x7D76CE88u;  // error at beginning
    packet = DecodedModeSPacket(packet_buffer, packet_buffer_used_len);
    EXPECT_FALSE(packet.IsValid());
    packet_buffer[0] = 0x8D76CE88u;  // reset first word

    packet_buffer[3] = 0x504E0000u;  // error near end
    packet = DecodedModeSPacket(packet_buffer, packet_buffer_used_len);
    EXPECT_FALSE(packet.IsValid());
    packet_buffer[3] = 0x504D0000u;  // reset last word

    // Extra bit ingestion (last word eats preamble from subsequent packet).
    packet_buffer[3] = 0x504D0001u;  // error where it should be ignored
    DecodedModeSPacket tpacket = DecodedModeSPacket(packet_buffer, packet_buffer_used_len);
    EXPECT_TRUE(tpacket.IsValid());
    packet_buffer[3] = 0x504D0000u;  // reset last word
}

TEST(DecodedModeSPacket, PacketFields) {
    uint32_t packet_buffer[DecodedModeSPacket::kMaxPacketLenWords32];  // note: may contain garbage
    const uint16_t packet_buffer_used_len = 4;  // number of 32 bit words populated in the packet buffer

    // Test Packet: 8D76CE88 204C9072 CB48209A 504D
    packet_buffer[0] = 0x8D76CE88u;
    packet_buffer[1] = 0x204C9072u;
    packet_buffer[2] = 0xCB48209Au;
    packet_buffer[3] = 0x504D0000u;
    DecodedModeSPacket tpacket = DecodedModeSPacket(packet_buffer, packet_buffer_used_len);
    EXPECT_TRUE(tpacket.IsValid());
    ADSBPacket packet = ADSBPacket(tpacket);

    EXPECT_EQ(packet.GetDownlinkFormat(), static_cast<uint16_t>(DecodedModeSPacket::kDownlinkFormatExtendedSquitter));
    EXPECT_EQ(packet.GetCapability(), 5u);
    EXPECT_EQ(packet.GetICAOAddress(), 0x76CE88u);
    EXPECT_EQ(packet.GetTypeCode(), 4u);
    EXPECT_EQ(packet.GetNBitWordFromMessage(3, 5), 0u);  // CAT = 0
}

TEST(ADSBPacket, ConstructFromTransponderPacket) {
    DecodedModeSPacket tpacket = DecodedModeSPacket((char *)"8D7C80AD2358F6B1E35C60FF1925");
    ADSBPacket packet = ADSBPacket(tpacket);
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C80ADu);
    EXPECT_EQ(packet.GetTypeCode(), 4);
}

TEST(DecodedModeSPacket, ConstructValidShortFrame) {
    DecodedModeSPacket packet = DecodedModeSPacket((char *)"00050319AB8C22");
    EXPECT_FALSE(packet.IsValid());  // Automatically marked as invalid since not confirmable with CRC.
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C7B5Au);
    EXPECT_EQ(packet.GetDownlinkFormat(),
              static_cast<uint16_t>(DecodedModeSPacket::kDownlinkFormatShortRangeAirToAirSurveillance));
}

TEST(DecodedModeSPacket, ConstructInvalidShortFrame) {
    DecodedModeSPacket packet = DecodedModeSPacket((char *)"00050219AB8C22");
    EXPECT_FALSE(packet.IsValid());  // Automatically marking all 56-bit packets with unknown ICAO as invalid for now.
}

TEST(DecodedModeSPacket, DumpPacketBufferBytes) {
    // Dumping packet buffer to a byte buffer (instead of a 32-bit word buffer) was added after the fact, and its
    // implementation needs to be checked for accuracy. Nominal packet.
    uint32_t packet_buffer_words[DecodedModeSPacket::kMaxPacketLenWords32];
    packet_buffer_words[0] = 0x8D76CE88u;
    packet_buffer_words[1] = 0x204C9072u;
    packet_buffer_words[2] = 0xCB48209Au;
    packet_buffer_words[3] = 0x504D0000u;

    DecodedModeSPacket packet = DecodedModeSPacket(packet_buffer_words, 4);

    uint8_t check_buffer_bytes[DecodedModeSPacket::kMaxPacketLenWords32 * kBytesPerWord];
    ASSERT_EQ(packet.DumpPacketBuffer(check_buffer_bytes), 112 / kBitsPerByte);
    for (uint16_t i = 0; i < DecodedModeSPacket::kMaxPacketLenWords32; i++) {
        EXPECT_EQ(packet_buffer_words[i] >> 24, check_buffer_bytes[i * kBytesPerWord]);
        EXPECT_EQ((packet_buffer_words[i] >> 16) & 0xFF, check_buffer_bytes[i * kBytesPerWord + 1]);
        EXPECT_EQ((packet_buffer_words[i] >> 8) & 0xFF, check_buffer_bytes[i * kBytesPerWord + 2]);
        EXPECT_EQ(packet_buffer_words[i] & 0xFF, check_buffer_bytes[i * kBytesPerWord + 3]);
    }
}

TEST(RawModeSPacket, GetTimestampMs) {
    // Check that the divide logic within RawModeSPacket works OK.
    RawModeSPacket raw_packet = RawModeSPacket((char *)"dedbef");
    raw_packet.mlat_48mhz_64bit_counts = 48'000;
    EXPECT_EQ(raw_packet.GetTimestampMs(), 1u);
    raw_packet.mlat_48mhz_64bit_counts = 97'325;
    EXPECT_EQ(raw_packet.GetTimestampMs(), 2u);
    raw_packet.mlat_48mhz_64bit_counts = 0xEAD'BEEF'DEAD'BEEFu;
    // raw_packet.mlat_48mhz_64bit_counts = 1'057'711'424'944'324'335u;
    EXPECT_EQ(raw_packet.GetTimestampMs(), 0x140A'935E'B684u);
}