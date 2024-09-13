#include "gtest/gtest.h"
#include "transponder_packet.hh"

TEST(ModeCPacket, JasonPlaynePackets) {
    ModeCPacket packet = ModeCPacket(DecodedTransponderPacket((char *)"200006A2DE8B1C"));
    EXPECT_FALSE(packet.IsValid());
    packet.ForceValid();
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.GetUtilityMessage(), 0);
    EXPECT_FALSE(packet.HasAlert());
    EXPECT_EQ(packet.GetAltitudeFt(), 10000);
    EXPECT_TRUE(packet.IsAirborne());
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C1B28u);

    packet = ModeCPacket(DecodedTransponderPacket((char *)"210000992F8C48"));
    EXPECT_FALSE(packet.IsValid());
    packet.ForceValid();
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.GetUtilityMessage(), 0);
    EXPECT_FALSE(packet.HasAlert());
    EXPECT_EQ(packet.GetAltitudeFt(), 25);
    EXPECT_FALSE(packet.IsAirborne());
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C7539u);
}

TEST(ModeAPacket, JasonPlaynePackets) {
    ModeAPacket packet = ModeAPacket(DecodedTransponderPacket((char *)"29001B3AF47E76"));
    EXPECT_FALSE(packet.IsValid());
    packet.ForceValid();
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.GetUtilityMessage(), ModeAPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_FALSE(packet.HasAlert());
    EXPECT_EQ(packet.GetSquawk(), 03751u);
    EXPECT_FALSE(packet.IsAirborne());
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C1474u);
    EXPECT_FALSE(packet.HasIdent());

    packet = ModeAPacket(DecodedTransponderPacket((char *)"2820050BD0D698"));
    EXPECT_FALSE(packet.IsValid());
    packet.ForceValid();
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.GetUtilityMessage(), ModeAPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_EQ(packet.GetDownlinkRequest(),
              ModeAPacket::DownlinkRequest::kDownlinkRequestCommBBroadcastMessage1Available);
    EXPECT_FALSE(packet.HasAlert());
    EXPECT_EQ(packet.GetSquawk(), 00664u);
    EXPECT_TRUE(packet.IsAirborne());
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C7181u);
    EXPECT_FALSE(packet.HasIdent());

    // Edit the previous packet to force an ident.
    packet = ModeAPacket(DecodedTransponderPacket((char *)"2D20050BD0D698"));
    EXPECT_EQ(packet.GetUtilityMessage(), ModeAPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_EQ(packet.GetDownlinkRequest(),
              ModeAPacket::DownlinkRequest::kDownlinkRequestCommBBroadcastMessage1Available);
    EXPECT_FALSE(packet.HasAlert());
    EXPECT_EQ(packet.GetSquawk(), 00664u);
    EXPECT_FALSE(packet.IsAirborne());  // Not sure if in air or on ground, default to on ground.
    EXPECT_TRUE(packet.HasIdent());

    // Edit the previous packet to force an ident and alert.
    packet = ModeAPacket(DecodedTransponderPacket((char *)"2C20050BD0D698"));
    EXPECT_EQ(packet.GetUtilityMessage(), ModeAPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_EQ(packet.GetDownlinkRequest(),
              ModeAPacket::DownlinkRequest::kDownlinkRequestCommBBroadcastMessage1Available);
    EXPECT_TRUE(packet.HasAlert());
    EXPECT_EQ(packet.GetSquawk(), 00664u);
    EXPECT_FALSE(packet.IsAirborne());  // Not sure if in air or on ground, default to on ground.
    EXPECT_TRUE(packet.HasIdent());
}