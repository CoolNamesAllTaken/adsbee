#include "../application/r1090_rssi.hh"
#include "gtest/gtest.h"

using namespace r1090_rssi;

TEST(R1090RSSI, StaticLevelsFollowTheCWCalibration) {
    // Bench CW readings from a 1090U rev G: {mV, dBm commanded}.
    const int cw[][2] = {{1021, -88}, {1076, -84}, {1137, -80}, {1204, -76}, {1271, -72}, {1341, -68}, {1412, -64},
                         {1489, -60}, {1564, -56}, {1642, -52}, {1680, -50}, {1715, -48}, {1740, -46}, {1759, -44}};
    for (const auto& point : cw) {
        EXPECT_NEAR(DetectorMilliVoltsTodBm(point[0]), point[1], 1) << point[0] << " mV";
    }
    // Idle noise floors: the rev G bench unit and a rev D (front end v1) unit on an antenna.
    EXPECT_EQ(DetectorMilliVoltsTodBm(948), -91);
    EXPECT_EQ(DetectorMilliVoltsTodBm(754), -102);
}

TEST(R1090RSSI, SaturatesAtDetectorFullScale) {
    EXPECT_EQ(DetectorMilliVoltsTodBm(1770), kMaxdBm);
    EXPECT_EQ(DetectorMilliVoltsTodBm(1897), kMaxdBm);
    EXPECT_EQ(DetectorMilliVoltsTodBm(3300), kMaxdBm);
    EXPECT_EQ(PacketMilliVoltsTodBm(1600, 948), kMaxdBm);
    EXPECT_EQ(PacketMilliVoltsTodBm(1500, 754), kMaxdBm);
}

TEST(R1090RSSI, IsMonotonic) {
    int last_dbm = DetectorMilliVoltsTodBm(600);
    for (int mv = 601; mv <= 2000; mv++) {
        int dbm = DetectorMilliVoltsTodBm(mv);
        EXPECT_GE(dbm, last_dbm) << mv << " mV";
        EXPECT_LE(dbm - last_dbm, 1) << mv << " mV";
        last_dbm = dbm;
    }
}

TEST(R1090RSSI, PacketsFollowTheBenchCalibration) {
    // Mid-message samples from the bench: {sample mV, noise floor mV, dBm commanded}. The floor above 948 mV is the
    // signal generator's carrier leak at the higher levels.
    const int packets[][3] = {{1043, 948, -80}, {1079, 948, -76}, {1118, 948, -72}, {1160, 947, -68},
                              {1199, 948, -64}, {1240, 949, -60}, {1285, 951, -56}, {1362, 1016, -52}};
    for (const auto& packet : packets) {
        EXPECT_NEAR(PacketMilliVoltsTodBm(packet[0], packet[1]), packet[2], 2) << packet[2] << " dBm";
    }
}

TEST(R1090RSSI, PacketScalesWithHeightAboveTheFloor) {
    // The same pulse power on a board with a lower noise floor: the sample is lower, the result is the same.
    // Pulse at 1341 mV (-68 dBm): 53 % of the way up from each floor.
    EXPECT_NEAR(PacketMilliVoltsTodBm(948 + (1341 - 948) * 53 / 100, 948), -68, 1);
    EXPECT_NEAR(PacketMilliVoltsTodBm(754 + (1341 - 754) * 53 / 100, 754), -68, 1);
}

TEST(R1090RSSI, PacketAtOrBelowTheFloorReadsTheFloor) {
    EXPECT_EQ(PacketMilliVoltsTodBm(948, 948), DetectorMilliVoltsTodBm(948));
    EXPECT_EQ(PacketMilliVoltsTodBm(900, 948), DetectorMilliVoltsTodBm(948));
    EXPECT_EQ(PacketMilliVoltsTodBm(700, 754), DetectorMilliVoltsTodBm(754));
}

TEST(R1090RSSI, LegacyConversionForTheTLOffsetText) {
    EXPECT_EQ(LegacyMilliVoltsTodBm(600), -104);  // The default trigger level offset as the settings UI shows it.
    EXPECT_EQ(LegacyMilliVoltsTodBm(1600), -44);
}
