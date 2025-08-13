#include "buffer_utils.hh"
#include "gtest/gtest.h"
#include "uat_packet.hh"

TEST(RawUATADSBPacket, ShortADSBPackets) {}

TEST(DecodedUATADSBPacket, ICAOAddress) {
    // ICAO address is 0 if the packet is invalid or has no header.
    DecodedUATADSBPacket packet((char *)"");
    EXPECT_EQ(packet.GetICAOAddress(), 0);
}