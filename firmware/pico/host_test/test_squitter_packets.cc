#include "gtest/gtest.h"
#include "mode_s_packet.hh"

TEST(ModeSAltitudeReplyPacket, JasonPlaynePackets) {
    ModeSAltitudeReplyPacket packet = ModeSAltitudeReplyPacket(DecodedModeSPacket((char *)"200006A2DE8B1C"));
    EXPECT_FALSE(packet.is_valid);
    packet.is_valid = true;
    EXPECT_TRUE(packet.is_valid);
    EXPECT_EQ(packet.utility_message, 0);
    EXPECT_FALSE(packet.has_alert);
    EXPECT_EQ(packet.altitude_ft, 10000);
    EXPECT_TRUE(packet.is_airborne);
    EXPECT_EQ(packet.icao_address, 0x7C1B28u);

    packet = ModeSAltitudeReplyPacket(DecodedModeSPacket((char *)"210000992F8C48"));
    EXPECT_FALSE(packet.is_valid);
    packet.is_valid = true;
    EXPECT_TRUE(packet.is_valid);
    EXPECT_EQ(packet.utility_message, 0);
    EXPECT_FALSE(packet.has_alert);
    EXPECT_EQ(packet.altitude_ft, 25);
    EXPECT_FALSE(packet.is_airborne);
    EXPECT_EQ(packet.icao_address, 0x7C7539u);
}

TEST(ModeSIdentityReplyPacket, JasonPlaynePackets) {
    ModeSIdentityReplyPacket packet = ModeSIdentityReplyPacket(DecodedModeSPacket((char *)"29001B3AF47E76"));
    EXPECT_FALSE(packet.is_valid);
    packet.is_valid = true;
    EXPECT_TRUE(packet.is_valid);
    EXPECT_EQ(packet.utility_message, ModeSIdentityReplyPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_FALSE(packet.has_alert);
    EXPECT_EQ(packet.squawk, 03751u);
    EXPECT_FALSE(packet.is_airborne);
    EXPECT_EQ(packet.icao_address, 0x7C1474u);
    EXPECT_FALSE(packet.has_ident);

    packet = ModeSIdentityReplyPacket(DecodedModeSPacket((char *)"2820050BD0D698"));
    EXPECT_FALSE(packet.is_valid);
    packet.is_valid = true;
    EXPECT_TRUE(packet.is_valid);
    EXPECT_EQ(packet.utility_message, ModeSIdentityReplyPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_EQ(packet.downlink_request,
              ModeSIdentityReplyPacket::DownlinkRequest::kDownlinkRequestCommBBroadcastMessage1Available);
    EXPECT_FALSE(packet.has_alert);
    EXPECT_EQ(packet.squawk, 00664u);
    EXPECT_TRUE(packet.is_airborne);
    EXPECT_EQ(packet.icao_address, 0x7C7181u);
    EXPECT_FALSE(packet.has_ident);

    // Edit the previous packet to force an ident.
    packet = ModeSIdentityReplyPacket(DecodedModeSPacket((char *)"2D20050BD0D698"));
    EXPECT_EQ(packet.utility_message, ModeSIdentityReplyPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_EQ(packet.downlink_request,
              ModeSIdentityReplyPacket::DownlinkRequest::kDownlinkRequestCommBBroadcastMessage1Available);
    EXPECT_FALSE(packet.has_alert);
    EXPECT_EQ(packet.squawk, 00664u);
    EXPECT_FALSE(packet.is_airborne);  // Not sure if in air or on ground, default to on ground.
    EXPECT_TRUE(packet.has_ident);

    // Edit the previous packet to force an ident and alert.
    packet = ModeSIdentityReplyPacket(DecodedModeSPacket((char *)"2C20050BD0D698"));
    EXPECT_EQ(packet.utility_message, ModeSIdentityReplyPacket::UtilityMessageType::kUtilityMessageNoInformation);
    EXPECT_EQ(packet.downlink_request,
              ModeSIdentityReplyPacket::DownlinkRequest::kDownlinkRequestCommBBroadcastMessage1Available);
    EXPECT_TRUE(packet.has_alert);
    EXPECT_EQ(packet.squawk, 00664u);
    EXPECT_FALSE(packet.is_airborne);  // Not sure if in air or on ground, default to on ground.
    EXPECT_TRUE(packet.has_ident);
}

TEST(ModeSAllCallReplyPacket, JasonPlaynePackets) {
    ModeSAllCallReplyPacket packet = ModeSAllCallReplyPacket(DecodedModeSPacket((char *)"5D7C0B6DB05076"));
    EXPECT_TRUE(packet.is_valid);
    EXPECT_EQ(packet.ca_cf.capability, 5);
    EXPECT_EQ(packet.icao_address, 0x7C0B6Du);

    // Flip one bit and watch it fail.
    packet = ModeSAllCallReplyPacket(DecodedModeSPacket((char *)"5D7C0B6DB05075"));
    EXPECT_FALSE(packet.is_valid);
}