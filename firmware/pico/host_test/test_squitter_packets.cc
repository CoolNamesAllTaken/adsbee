#include "gtest/gtest.h"
#include "mode_s_packet.hh"

TEST(AltitudeReplyPacket, JasonPlaynePackets) {
    AltitudeReplyPacket packet = AltitudeReplyPacket(DecodedModeSPacket((char *)"200006A2DE8B1C"));
    EXPECT_FALSE(packet.IsValid());
    packet.ForceValid();
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.GetUtilityMessage(), 0);
    EXPECT_FALSE(packet.HasAlert());
    EXPECT_EQ(packet.GetAltitudeFt(), 10000);
    EXPECT_TRUE(packet.IsAirborne());
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C1B28u);

    packet = AltitudeReplyPacket(DecodedModeSPacket((char *)"210000992F8C48"));
    EXPECT_FALSE(packet.IsValid());
    packet.ForceValid();
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.GetUtilityMessage(), 0);
    EXPECT_FALSE(packet.HasAlert());
    EXPECT_EQ(packet.GetAltitudeFt(), 25);
    EXPECT_FALSE(packet.IsAirborne());
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C7539u);
}

TEST(IdentityReplyPacket, JasonPlaynePackets) {
    IdentityReplyPacket packet = IdentityReplyPacket(DecodedModeSPacket((char *)"29001B3AF47E76"));
    EXPECT_FALSE(packet.IsValid());
    packet.ForceValid();
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.GetUtilityMessage(), IdentityReplyPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_FALSE(packet.HasAlert());
    EXPECT_EQ(packet.GetSquawk(), 03751u);
    EXPECT_FALSE(packet.IsAirborne());
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C1474u);
    EXPECT_FALSE(packet.HasIdent());

    packet = IdentityReplyPacket(DecodedModeSPacket((char *)"2820050BD0D698"));
    EXPECT_FALSE(packet.IsValid());
    packet.ForceValid();
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.GetUtilityMessage(), IdentityReplyPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_EQ(packet.GetDownlinkRequest(),
              IdentityReplyPacket::DownlinkRequest::kDownlinkRequestCommBBroadcastMessage1Available);
    EXPECT_FALSE(packet.HasAlert());
    EXPECT_EQ(packet.GetSquawk(), 00664u);
    EXPECT_TRUE(packet.IsAirborne());
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C7181u);
    EXPECT_FALSE(packet.HasIdent());

    // Edit the previous packet to force an ident.
    packet = IdentityReplyPacket(DecodedModeSPacket((char *)"2D20050BD0D698"));
    EXPECT_EQ(packet.GetUtilityMessage(), IdentityReplyPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_EQ(packet.GetDownlinkRequest(),
              IdentityReplyPacket::DownlinkRequest::kDownlinkRequestCommBBroadcastMessage1Available);
    EXPECT_FALSE(packet.HasAlert());
    EXPECT_EQ(packet.GetSquawk(), 00664u);
    EXPECT_FALSE(packet.IsAirborne());  // Not sure if in air or on ground, default to on ground.
    EXPECT_TRUE(packet.HasIdent());

    // Edit the previous packet to force an ident and alert.
    packet = IdentityReplyPacket(DecodedModeSPacket((char *)"2C20050BD0D698"));
    EXPECT_EQ(packet.GetUtilityMessage(), IdentityReplyPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_EQ(packet.GetDownlinkRequest(),
              IdentityReplyPacket::DownlinkRequest::kDownlinkRequestCommBBroadcastMessage1Available);
    EXPECT_TRUE(packet.HasAlert());
    EXPECT_EQ(packet.GetSquawk(), 00664u);
    EXPECT_FALSE(packet.IsAirborne());  // Not sure if in air or on ground, default to on ground.
    EXPECT_TRUE(packet.HasIdent());
}

TEST(AllCallReplyPacket, JasonPlaynePackets) {
    AllCallReplyPacket packet = AllCallReplyPacket(DecodedModeSPacket((char *)"5D7C0B6DB05076"));
    EXPECT_TRUE(packet.IsValid());
    EXPECT_EQ(packet.GetCapability(), 5);
    EXPECT_EQ(packet.GetICAOAddress(), 0x7C0B6Du);

    // Flip one bit and watch it fail.
    packet = AllCallReplyPacket(DecodedModeSPacket((char *)"5D7C0B6DB05075"));
    EXPECT_FALSE(packet.IsValid());
}