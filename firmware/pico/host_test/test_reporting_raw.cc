#include "gtest/gtest.h"
#include "raw_utils.hh"

TEST(RawUtils, BuildRaw1090Frame) {
    // Test with squitter packet.
    Raw1090Packet raw_packet = Raw1090Packet((char *)"2D0006A2DEE500", 3, -68, 9, 0xFEED'BEEF'BEFE'BEEB);

    char constructed_frame[kRaw1090FrameMaxNumChars];
    char *expected_frame = (char *)"#S*2D0006A2DEE500;(3,-68,9,FEEDBEEFBEFEBEEB)";
    EXPECT_EQ(BuildRaw1090Frame(raw_packet, constructed_frame), strlen(expected_frame));
    EXPECT_STREQ(expected_frame, constructed_frame);

    // Test with extended squitter packet.
    raw_packet = Raw1090Packet((char *)"8D48C22D60AB00DEABC5DB78FCD6", 1, -90, 3, 0xDEAD);
    expected_frame = (char *)"#S*8D48C22D60AB00DEABC5DB78FCD6;(1,-90,3,000000000000DEAD)";
    EXPECT_EQ(BuildRaw1090Frame(raw_packet, constructed_frame), strlen(expected_frame));
    EXPECT_STREQ(expected_frame, constructed_frame);
}