#include "aircraft_dictionary.hh"
#include "decode_utils.hh"  // for location calculation utility functions
#include "gtest/gtest.h"
#include "hal_god_powers.hh"  // for changing timestamp
#include "uat_packet.hh"

TEST(AircraftDictionary, IngestUATADSBPacket) {
    AircraftDictionary dictionary = AircraftDictionary();
    DecodedUATADSBPacket tpacket((char *)"00a66ef135445d525a0c0519119021204800");
    EXPECT_TRUE(tpacket.ReconstructWithoutFEC());
    EXPECT_EQ(tpacket.GetICAOAddress(), 0xA66EF1u);
    EXPECT_EQ(Aircraft::ICAOToUID(tpacket.GetICAOAddress(), Aircraft::kAircraftTypeUAT),
              0x10A66EF1u);  // UID is ICAO address with type shifted to the left.

    EXPECT_TRUE(tpacket.ReconstructWithoutFEC());
    EXPECT_TRUE(dictionary.IngestDecodedUATADSBPacket(tpacket));
    EXPECT_EQ(dictionary.GetNumAircraft(), 1);
    EXPECT_TRUE(dictionary.ContainsAircraft(Aircraft::ICAOToUID(tpacket.GetICAOAddress(), Aircraft::kAircraftTypeUAT)));

    UATAircraft aircraft;
    EXPECT_TRUE(dictionary.GetAircraft(tpacket.GetICAOAddress(), aircraft));
}